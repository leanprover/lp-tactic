/-
  Tests for issue #47: atomize `Nat.sub` / `Nat.div` / `Int.div` (and `%`) subterms
  instead of rejecting the call.

  Previously the carrier scalar-caps check HARD-rejected any expression containing
  ℕ-subtraction or ℤ/ℕ-division, with a `use cutsat` hint at PARSE time. That is the right
  answer only when the goal's arithmetic genuinely depends on truncation. `linarith`
  demonstrates a cheaper sound move that wins in practice: treat the offending subterm as an
  OPAQUE ATOM. The surrounding reasoning is then linear in that atom, and bracketed facts
  supply whatever properties of it are needed.

  Stage 1 (this change): in `parseInto`, a truncating `HSub` over ℕ and an `HDiv`/`HMod`
  over ℤ/ℕ atomize the whole subterm via the existing opaque-atom machinery (#14) rather
  than throwing. The certificate normalizer (`normalizeR`) is made caps-aware to match
  (descending would build a `Neg` that ℕ lacks, or mis-linearize ℤ's `x / 2`). The `cutsat`
  hint is kept as the FAILURE diagnostic, surfaced by `solveAtomic` only when the residual
  linear problem does not close — and still thrown at parse time by the binder frontends,
  where atomization is off.

  The atomic cases below all have trivial certificates (the residual closes with zero rows
  via the atom appearing identically on both sides), so they exercise the atomization +
  normalization path WITHOUT a registered LP backend. The three resurvey sites in the issue
  (`NthRootLemmas`, `HomComplexShift`, `JacobsonNoether`) close the same way but through a
  Farkas combination of bracketed hypotheses, which needs the solver and so is exercised
  where `lp` is used against Mathlib, not in this dependency-free suite.
-/

import LPTactic

namespace LPTacticTest.Issue47

/-! ## ℕ-subtraction atomized (was a hard parse rejection). -/

example (a b : Nat) : a - b ≤ a - b + 1 := by lp
example (a b : Nat) : a - b ≤ (a - b) + 2 := by lp
example (a b c : Nat) : (a - b) + c ≤ c + (a - b) + 1 := by lp
example (a b : Nat) : (a - b) * 1 ≤ a - b + 1 := by lp
-- A compound ℕ-difference `(2 + s) - 1` atomizes as one opaque atom (its value is lost —
-- that is the stage-2 `zify` class; here it only needs to cancel against an identical copy).
example (s : Nat) : (2 + s) - 1 ≤ (2 + s) - 1 + 1 := by lp

/-! ## ℕ-division and ℕ-`%` atomized. -/

example (a b : Nat) : a / b ≤ a / b + 1 := by lp
example (a b : Nat) : a / b ≤ (a / b) * 1 + 1 := by lp
example (a b : Nat) : a % b ≤ a % b + 1 := by lp
example (a b c d : Nat) : (a - b) + c / d ≤ c / d + (a - b) + 5 := by lp

/-! ## ℤ-division / ℤ-`%` atomized; ℤ-subtraction stays exact (descended). -/

example (a b : Int) : a / b ≤ a / b + 1 := by lp
example (a b : Int) : a / b - a / b ≤ 1 := by lp
example (a b : Int) : a % b ≤ a % b + 1 := by lp
-- `x / 2` over ℤ is FLOOR division, so it atomizes (it is NOT the rational `(1/2)•x`).
example (a : Int) : a / 2 ≤ a / 2 + 1 := by lp
-- ℤ subtraction is exact, so this descends and cancels linearly (no atom needed).
example (a b : Int) : (a - b) + (b - a) ≤ 1 := by lp

/-! ## Closed ℤ/ℕ division: `5 / 2` is FLOOR division (`= 2`), not the rational `2.5`. The
    parser atomizes it; the normalizer's scalar recognizer must agree and NOT fold it to a
    rational literal (a `5 / 2 = Int.ofNat 5` mis-render was the bug this guards). -/

example : (5 / 2 : Int) ≤ 5 / 2 + 1 := by lp
example : (5 / 2 : Nat) ≤ 5 / 2 + 1 := by lp
example (x : Int) : x + 5 / 2 ≤ 5 / 2 + x + 1 := by lp
example : (4 / 2 : Int) ≤ 4 / 2 + 1 := by lp
-- Closed ℕ-subtraction `5 - 3` (`= 2`) likewise atomizes consistently on both sides.
example : (5 - 3 : Nat) ≤ 5 - 3 + 1 := by lp
example (x : Nat) : (5 - 3) * x ≤ (5 - 3) * x + 1 := by lp

/-! ## Regressions: field/`Rat` division still LINEARIZES (not atomized). If `x / 2` were
    atomized here, `x / 2 + x / 2` would not cancel to `x` and these would need the solver. -/

example (x : Rat) : x / 2 + x / 2 ≤ x + 1 := by lp
example (x : Rat) : (2 : Rat) * (x / 2) ≤ x + 1 := by lp

/-! ## The `cutsat` hint is preserved where it belongs: the binder frontends (atomization
    off) still reject a truncating objective at parse time, with the hint. -/

/-- error: lp: subtraction over `Nat` is truncating (`Nat.sub`) and is not supported by `lp`; use `cutsat` (or `omega`) for goals involving `Nat` subtraction -/
#guard_msgs in
example (n : Nat) : True := by
  maximize n - 1
  trivial

/-- error: lp: division/`%` over `Nat` is integer/truncating division and is not supported by `lp`; use `cutsat` (or `omega`) for goals involving `Int`/`Nat` division -/
#guard_msgs in
example (n : Nat) : True := by
  maximize n / 2
  trivial

end LPTacticTest.Issue47
