/-
  Tests for issue #55: comparison goals wrapped in `Expr.mdata` misrouted to the
  inconsistency path.

  Lean wraps most elaborated goals in `Expr.mdata`. `solveGoal` dispatched on the carrier
  read off the RAW goal type via `relCarrier?`, which called `getAppFn` on the mdata node,
  saw `.mdata` rather than `LT.lt`/`LE.le`/`Eq`, and shunted the goal to `solveInconsistent`
  — where an ordinary comparison like `0 < f x + g x` died as `not an atomic comparison`.
  The Mathlib `linarith` resurvey hit ~80 such goals (`linarith` is mdata-robust here).

  The fix strips mdata (`consumeMData`) in `relCarrier?` and `parseAtomic?`, and adds a
  `solveAtomic`→`solveInconsistent` fallback for comparison goals that PARSE but only hold
  ex falso from inconsistent hypotheses (which the old misrouting reached by accident). The
  fallback is gated on the goal parsing, so a genuine goal-side parse error still throws.

  `wrap_mdata` reproduces the metadata annotation in this dependency-free suite. The cases
  below all have trivial certificates (reflexive `a ≤ a`, a constant, or a closed
  contradiction), so they exercise the mdata-stripping dispatch and the ex-falso fallback
  WITHOUT a registered LP backend; the real-solver sites are exercised against Mathlib.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean Elab Tactic Meta

namespace LPTacticTest.Issue55

/-- Wrap the main goal's type in `Expr.mdata`, mimicking the metadata annotation Lean
attaches to elaborated goals. Without `consumeMData` at the dispatch sites, `lp` then
reads `.mdata` as the goal head and misroutes the goal. -/
elab "wrap_mdata" : tactic => do
  let g ← getMainGoal
  let t' := Expr.mdata (KVMap.empty.insert `lpTest (DataValue.ofNat 1)) (← g.getType)
  let g' ← mkFreshExprMVar t'
  g.assign g'
  replaceMainGoal [g'.mvarId!]

/-! ## An mdata-wrapped comparison reaches `solveAtomic` (was: `not an atomic comparison`). -/

example (a : Rat) : a ≤ a := by wrap_mdata; lp
example (a : Int) : a ≤ a := by wrap_mdata; lp
example (a : Nat) : a ≤ a := by wrap_mdata; lp
example : (0 : Rat) ≤ 1 := by wrap_mdata; lp
example (a : Rat) : a < a + 1 := by wrap_mdata; lp

/-! ## Fallback: an mdata-wrapped comparison that does NOT solve atomically still closes
ex falso from inconsistent hypotheses (the path the old misrouting reached by accident). -/

example (a b : Rat) (h : (2 : Rat) ≤ 1) : a ≤ b := by wrap_mdata; lp
example (a b : Int) (h : (2 : Int) ≤ 1) : a ≤ b := by wrap_mdata; lp

end LPTacticTest.Issue55
