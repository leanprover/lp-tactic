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

/-- Discharge a goal that is not `∃`/`∧`/an atomic comparison (paradigmatically
`False`) by certifying the hypotheses inconsistent. The carrier comes from the
hypotheses (the goal carries none); the Farkas probe builds the goal via
`False.elim`. Errors cleanly if no supported-carrier hypothesis is present or the
hypotheses are consistent. -/
def solveInconsistent (g : MVarId) (target : Expr) : TacticM Unit := g.withContext do
  let mut carrier? : Option Expr := none
  for decl in (← getLCtx) do
    if carrier?.isNone && !decl.isImplementationDetail then
      if ← isProp decl.type then
        carrier? ← hypCarrier? decl.type
  let some carrier := carrier?
    | throwError "lp: goal{indentExpr target}\nis not an atomic comparison or `∃`, and no {
        ""}linear hypothesis over a supported carrier was found to derive it from"
  let fctx ← mkFrontendCtx carrier
  let (rows, st) ← (collectHyps).run { carrier, allowAtoms := true }
  let atoms : AtomTable := { fvarToAtom := st.fvarToAtom, atomToFVar := st.atomToFVar }
  match ← tryHypsInconsistent fctx rows st.vars target atoms with
  | some proof => g.assign proof
  | none =>
      throwError "lp: goal{indentExpr target}\nis not an atomic comparison, and the {
        ""}hypotheses over {carrier} are not inconsistent"

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
      match relCarrier? (← instantiateMVars (← g.getType)) with
      | some _ => solveAtomic g
      | none => solveInconsistent g (← instantiateMVars (← g.getType))

/-- The `lp` tactic. Optional `(backend := <name>)` argument pins a
    specific backend by name for this call only, overriding any
    ambient `set_option lp.backend` and the registry's
    priority-based default. -/
syntax (name := lpTactic) "lp" (" (" &"backend" " := " ident ")")? : tactic

elab_rules : tactic
  | `(tactic| lp $[(backend := $b:ident)]?) => do
    let backendOverride? : Option String := b.map (·.getId.toString)
    let withBackend (act : TacticM Unit) : TacticM Unit :=
      match backendOverride? with
      | some name =>
        withTheReader Core.Context (fun ctx =>
          { ctx with options :=
              LP.Tactic.LP.lp.backend.set ctx.options name }) act
      | none => act
    withBackend do
      let goals ← getGoals
      match goals with
      | [] => throwError "lp: no goals"
      | g :: rest =>
          setGoals [g]
          solveGoal g
          let newGoals ← getGoals
          setGoals (newGoals ++ rest)

end LP.Tactic.LP.Internal
