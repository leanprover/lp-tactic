import LPTactic.LP.Atomic
import LPTactic.LP.BackendOption
import LPTactic.LP.Exists

open Lean Meta Elab Tactic
open Soplex Soplex.Verify
open Soplex.Tactic (Q)

namespace Soplex.Tactic.LP.Internal

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
      solveAtomic g

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
              Soplex.Tactic.LP.lp.backend.set ctx.options name }) act
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

end Soplex.Tactic.LP.Internal
