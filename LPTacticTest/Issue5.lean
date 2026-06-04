/-
  Goal-shape tests for issue #5: closing `False` and bare `Prop` goals
  from inconsistent hypotheses.

  These exercise the goal-shape extractor (`solveInconsistent` in
  `LPTactic.LP.Frontend`) and the `False.elim`-based wiring through
  `tryHypsInconsistent` and the per-carrier `mkContradiction`. The
  zero-variable / closed-row branch of `tryHypsInconsistent` lets these
  fire without a registered LP backend, so they belong in this package's
  test suite (rather than in `soplex` / `lp-backend-pure`).

  Multi-variable Farkas-style inconsistency cases for the same goal
  shapes live in the consumer test suites
  (`SoplexTest/LP.lean`, `LPBackendPureTest/LPParity.lean`), where a
  backend is registered.
-/

import LPTactic

namespace LPTacticTest.Issue5

/-! ## `: False` from a closed contradictory row. -/

example (_h : (1 : Rat) ≤ 0) : False := by lp
example (_h : (1 : Int) ≤ 0) : False := by lp
example (_h : (1 : Nat) + 1 ≤ 1) : False := by lp

/-! ## `(p : Prop) : p` from a closed contradictory row. -/

example (p : Prop) (_h : (1 : Rat) ≤ 0) : p := by lp
example (p : Prop) (_h : (1 : Int) ≤ 0) : p := by lp
example (p : Prop) (_h : (1 : Nat) + 1 ≤ 1) : p := by lp

/-! ## Carrier read from a `∧`-hypothesis (descended via `hypCarrier?`). -/

example (_h : (1 : Rat) ≤ 0 ∧ True) : False := by lp
example (p : Prop) (_h : True ∧ (1 : Rat) ≤ 0) : p := by lp

/-! ## Irrelevant `Prop` hypotheses (a goal-binder `p : Prop`, `True`)
    do not interfere with carrier detection from the row hypothesis. -/

example (q : Prop) (_hq : q) (_h : (1 : Rat) ≤ 0) : False := by lp
example (q : Prop) (p : Prop) (_hq : q) (_h : (1 : Rat) ≤ 0) : p := by lp

end LPTacticTest.Issue5
