module
public meta import LPTactic.LP.Atomic
public meta import LPTactic.LP.BackendOption
public meta import LPTactic.LP.Exists

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-- Find the carrier `α` of a hypothesis: the comparison type of an atomic
`a ≤ b`/`a < b`/`a = b`, descending through `∧`. Used to discharge a goal that is
not itself a comparison (e.g. `False`) from inconsistent hypotheses. Inspects the
RAW type — `whnfR` may unfold `LE.le` for `Rat` into a `Bool` equality and hide
the real carrier. -/
partial def hypCarrier? (ty : Expr) : MetaM (Option Expr) := do
  if let some (l, r) := isAnd? ty then
    match ← hypCarrier? l with
    | some α => return some α
    | none => return ← hypCarrier? r
  match relCarrier? ty with
  | some α => if ← isCarrierType α then return some α else return none
  | none => return none

/-- Every supported carrier appearing in `ty`, descending through `∧` (so a conjunction
mixing carriers, e.g. `(0 < n) ∧ ((1 : Rat) < 0)`, contributes ALL of them). Used to find
the carrier a `False`/`≠` goal's contradiction lives over. -/
partial def hypCarriers (ty : Expr) : MetaM (Array Expr) := do
  if let some (l, r) := isAnd? ty then
    return (← hypCarriers l) ++ (← hypCarriers r)
  match relCarrier? ty with
  | some α => if ← isCarrierType α then return #[α] else return #[]
  | none => return #[]

/-- Discharge a goal that is not `∃`/`∧`/an atomic comparison (paradigmatically
`False`) by certifying the hypotheses inconsistent. The carrier comes from the
hypotheses (the goal carries none); the Farkas probe builds the goal via
`False.elim`. Errors cleanly if no supported-carrier hypothesis is present or the
hypotheses are consistent. -/
def solveInconsistent (g : MVarId) (target : Expr) : TacticM Unit := g.withContext do
  -- Gather EVERY distinct supported carrier present in the hypotheses, not just the first:
  -- a mixed-carrier context can have a consistent hypothesis over one carrier (e.g. `Int`)
  -- masking the contradiction that lives over another (e.g. the `Rat` hypotheses plus the
  -- `a = b` introduced from a `≠` goal). We try each carrier until one is inconsistent.
  let mut carriers : Array Expr := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail then
      if ← isProp decl.type then
        for c in ← hypCarriers decl.type do
          unless ← carriers.anyM (isDefEq c ·) do
            carriers := carriers.push c
  if carriers.isEmpty then
    throwError "lp: goal{indentExpr target}\nis not an atomic comparison or `∃`, and no {
        ""}linear hypothesis over a supported carrier was found to derive it from"
  for carrier in carriers do
    let ops ← mkCarrierOps carrier
    let (rows, st) ← (collectHyps).run { carrier, allowAtoms := true }
    let atoms : AtomTable := { fvarToAtom := st.fvarToAtom, atomToFVar := st.atomToFVar }
    if let some proof ← tryHypsInconsistent ops rows st.vars target atoms then
      g.assign proof
      return
  throwError "lp: goal{indentExpr target}\nis not an atomic comparison, and the hypotheses {
      ""}over {carriers.toList} are not inconsistent"

partial def solveGoal (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  g.withContext do
    let target ← whnfR (← g.getType)
    if ← isExistsRat? target then
      solveExistential solveGoal g
    else if let some (left, right) := isAnd? target then
      let leftProof ← mkFreshExprMVar left
      let rightProof ← mkFreshExprMVar right
      let proof ← mkAppM ``And.intro #[leftProof, rightProof]
      g.assign proof
      solveGoal leftProof.mvarId!
      solveGoal rightProof.mvarId!
    else
      -- Atomic comparison → the normal discharger; otherwise (e.g. `False`) fall
      -- back to certifying the hypotheses inconsistent. Decide on the RAW goal
      -- type (the `whnfR` `target` may have unfolded a `Rat` `≤` to a `Bool` `=`).
      let rawGoal ← instantiateMVars (← g.getType)
      match relCarrier? rawGoal with
      | some _ => solveAtomic g
      | none =>
          -- A negation / `≠` goal `¬P` (`Ne`/`Not` need default-transparency `whnf` to expose
          -- the `P → False` arrow that reducible `intros` left intact): introduce `P` as a
          -- hypothesis and prove `False`, so the strict-aware inconsistency check can use it.
          let ty ← whnf rawGoal
          if ty.isArrow && ty.bindingBody!.isConstOf ``False then
            let (_, g') ← g.intro1
            solveGoal g'
          else
            solveInconsistent g rawGoal

/-- The `lp` tactic. Optional `(backend := <name>)` argument pins a
    specific backend by name for this call only, overriding any
    ambient `set_option lp.backend` and the registry's
    priority-based default. -/
syntax (name := lpTactic) "lp" (" (" &"backend" " := " ident ")")? (&" only")? (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| lp $[(backend := $b:ident)]? $[only%$_o]? $[[$args,*]]?) => do
    let backendOverride? : Option String := b.map (·.getId.toString)
    let withBackend (act : TacticM Unit) : TacticM Unit :=
      match backendOverride? with
      | some name =>
        withTheReader Core.Context (fun ctx =>
          { ctx with options :=
              LP.Tactic.LP.lp.backend.set ctx.options name }) act
      | none => act
    -- Extra facts `lp [t₁, …]`: elaborate each and add it as a local hypothesis, so
    -- `collectHyps` uses it (matches `linarith [..]`). `only` is accepted but ignored —
    -- lp also reads the local context, which is sound (extra hypotheses cannot mislead it).
    let argTerms : Array Term := (args.map (·.getElems)).getD #[]
    withBackend do
      let goals ← getGoals
      match goals with
      | [] => throwError "lp: no goals"
      | g :: rest =>
          let g ← g.withContext do
            let mut g := g
            for t in argTerms do
              let p ← Term.elabTermAndSynthesize t none
              let ty ← inferType (← instantiateMVars p)
              let (_, g') ← (← g.assert (← mkFreshUserName `lpArg) ty p).intro1P
              g := g'
            pure g
          setGoals [g]
          solveGoal g
          let newGoals ← getGoals
          setGoals (newGoals ++ rest)

end LP.Tactic.LP.Internal
