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
  -- Look through a negated comparison (`¬ (a ≤ b)`, `a ≠ b`, …) to the carrier underneath.
  let rel := (← notInner? ty).getD ty
  match relCarrier? rel with
  | some α => if ← isCarrierType α then return some α else return none
  | none => return none

/-- Every supported carrier appearing in `ty`, descending through `∧` (so a conjunction
mixing carriers, e.g. `(0 < n) ∧ ((1 : Rat) < 0)`, contributes ALL of them). Used to find
the carrier a `False`/`≠` goal's contradiction lives over. -/
partial def hypCarriers (ty : Expr) : MetaM (Array Expr) := do
  if let some (l, r) := isAnd? ty then
    return (← hypCarriers l) ++ (← hypCarriers r)
  -- Look through a negated comparison (`¬ (a ≤ b)`, `a ≠ b`, …) to the carrier underneath.
  let rel := (← notInner? ty).getD ty
  match relCarrier? rel with
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

/-- A comparison goal `lhs op ?m` (or `?m op rhs`) one side of which is a bare unassigned
metavariable: `linarith` closes these by *assigning* the metavariable, rather than by
proving an entailment. Faced with `concrete = ?m` it picks the value `v` the hypotheses
force `concrete` to equal and assigns `?m := v`; faced with the strict `m < ?m` it finds a
hypothesis-derived upper bound `v` (`m < v`) and assigns `?m := v`. The chosen `v` is always
an existing context term (e.g. `?m := p` when `n + n' = p` reduces `m + -1 + n'` to `p`, or
`?m := d` for `m < d`), NOT the verbatim `concrete` side. That distinction matters: the
assigned value flows on into the surrounding elaboration (e.g. it fixes the degree of a
cochain a later `simp` lemma must match), so a verbatim assignment would type-check the
comparison yet derail the surrounding proof. `lp` otherwise atomizes `?m` as an opaque
carrier term and rejects it.

We mirror `linarith` by *searching* the carrier-typed local variables for a `v` making the
oriented comparison (`concrete = v`, `concrete < v`/`v < concrete`, or the `≤` analogue)
provable, reusing `solveAtomic` as the prover (so the strict witness search inherits the
ℕ→ℤ cast bridging that proves `m < d` from `ℤ`-cast hypotheses), then assigning `?m := v`.
Returns `true` when handled. Each attempt runs inside a saved state that is rolled back on
failure, so a candidate that partially solves (or whose defeq checks assign shared
metavariables) before throwing cannot leak that into the next attempt or the surrounding
proof. -/
def solveRelMVar? (g : MVarId) (rawGoal : Expr) : TacticM Bool := g.withContext do
  let goal := rawGoal.consumeMData
  let args := goal.getAppArgs
  -- The relations `linarith` assigns a goal metavariable for: `=`, `≤`, `<`.
  let some (rel, α, lhs0, rhs0) :=
      match goal.getAppFn with
      | .const ``Eq _    => if args.size == 3 then some (Rel.eq, args[0]!, args[1]!, args[2]!) else none
      | .const ``LE.le _ => if args.size == 4 then some (Rel.le, args[0]!, args[2]!, args[3]!) else none
      | .const ``LT.lt _ => if args.size == 4 then some (Rel.lt, args[0]!, args[2]!, args[3]!) else none
      | _ => none
    | return false
  unless ← isCarrierType α do return false
  let lhs ← instantiateMVars lhs0
  let rhs ← instantiateMVars rhs0
  -- Exactly one side a bare unassigned metavariable, the other metavariable-free.
  let some (mvarOnRight, mvarSide, concrete) :=
      if rhs.isMVar && !lhs.hasExprMVar then some (true, rhs, lhs)
      else if lhs.isMVar && !rhs.hasExprMVar then some (false, lhs, rhs)
      else none
    | return false
  -- Candidate values: the carrier-typed local variables (`linarith` only ever assigns the
  -- metavariable to such an existing term). For each, prove the oriented comparison with the
  -- full `solveAtomic` machinery on a throwaway goal; the first `v` that closes is the
  -- assignment. The probe keeps the metavariable's side: `concrete op v` (metavariable on the
  -- right) or `v op concrete` (on the left), so after `?m := v` the probe's type is defeq the
  -- original goal.
  let s ← saveState
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let v := decl.toExpr
    -- A data variable of the carrier (skip props and other types). `withNewMCtxDepth` keeps the
    -- type check from assigning `mvarSide` (or any goal metavariable) as a side effect.
    unless ← withNewMCtxDepth (isDefEq (← inferType v) α) do continue
    let progressed ← (do
        let (pl, pr) := if mvarOnRight then (concrete, v) else (v, concrete)
        let probeType ← match rel with
          | .eq => mkAppM ``Eq #[pl, pr]
          | .le => mkAppM ``LE.le #[pl, pr]
          | .lt => mkAppM ``LT.lt #[pl, pr]
        let probe ← mkFreshExprMVar probeType
        solveAtomic probe.mvarId!
        -- Comparison proved. Pin the metavariable to `v` (defeq assignment) and discharge
        -- the original goal with that proof (its type is now defeq to the goal).
        unless ← isDefEq mvarSide v do return false
        g.assign (← instantiateMVars probe)
        return true) <|> pure false
    if progressed then return true
    s.restore
  return false

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
      -- A comparison goal (`=`, `≤`, `<`) with an unassigned metavariable on one side:
      -- `linarith` closes it by assigning the metavariable. Do the same before the atomic
      -- dispatch (which would otherwise atomize `?m` and reject it as an `unsupported
      -- expression`).
      if ← solveRelMVar? g rawGoal then return
      -- Treat the goal as an atom only when its relation type ACTUALLY carries the
      -- arithmetic structure: a comparison/`Eq` whose carrier is a non-arithmetic type
      -- (e.g. `x = y` for `x y : X` a topological space) is not an `lp` atom — committing
      -- to `X` would later throw a raw `failed to synthesize HAdd X X X` from carrier
      -- detection. Such a goal is instead discharged (ex falso) from inconsistent
      -- arithmetic hypotheses, exactly like `False`.
      if let some α := relCarrier? rawGoal then
        if ← isCarrierType α then
          -- Does the goal parse as an atomic comparison? A goal that PARSES but fails to
          -- SOLVE may still hold ex falso from inconsistent hypotheses (e.g. a `D u = 0`
          -- goal under a `1 < 0` hypothesis), so we fall back to the inconsistency path.
          -- But a goal that fails to PARSE (e.g. `x / 0`) is a genuine blocker and must
          -- throw its precise error — no fallback (see Issue45).
          let goalParses ← (do
              let (p, _) ← (parseAtomic? rawGoal).run { carrier := α, allowAtoms := true }
              pure p.isSome) <|> pure false
          if goalParses then
            try
              return ← solveAtomic g
            catch eAtomic =>
              try return ← solveInconsistent g rawGoal
              catch _ => throw eAtomic
          else
            return ← solveAtomic g
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
