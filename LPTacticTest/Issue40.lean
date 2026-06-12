/-
  Tests for issue #40: integer strengthening for strict hypotheses and goals over ℤ/ℕ.

  `linarith` strengthens a strict integer fact `a < b` to `a + 1 ≤ b` before running
  Fourier–Motzkin; `lp` used to keep it as a strict ℚ-row, which is sound but strictly
  weaker — a chain of `k` strict facts lost `k − 1` units of slack, surfacing as an
  off-by-`k` residual (the `residual -2 not ≥ 0` and `infeasible residual 0 not > 0`
  failure sites).

  The fix (`Parse.collectHypProof`, `Atomic.solveAtomic`) strengthens, at parse time and
  on the discrete carriers `ℤ`/`ℕ` only:

  * strict hypothesis rows `a < b ⟶ a + 1 ≤ b` (`add_one_le_of_lt`), so every strict
    fact contributes a full unit of slack to the Farkas residual; and
  * a non-strict goal `lhs ≤ rhs`, on a residual miss, is reproved as the equivalent
    strict `lhs < rhs + 1` (`le_of_lt_add_one`) — `linarith`'s strict-negated-goal
    preprocessing, which closes the integer-rounding gap (`a ≤ b − 1/2 ⟹ a ≤ b` over ℤ).

  The dense carriers (`Rat`/`Dyadic`/`ℝ`) are untouched: there `a < b` does NOT imply
  `a + 1 ≤ b`, so they keep the genuine strict-row machinery.

  The behavioral repros from the issue are multi-row (a goal plus hypothesis rows), so
  they need a registered LP backend and live in the consumer suites (`lp-backend-pure`,
  `lp`, the Mathlib resurvey). The repo's own dependency-free suite has no backend, so
  the cases below are goal-only (the residual closes with zero rows): they pin the ℤ/ℕ
  strict/`≤` dispatch the strengthening relies on, and confirm the new closing lemmas.
  The multi-row repros are reproduced verbatim in comments for reference.
-/

import LPTactic

namespace LPTacticTest.Issue40

open LP.Tactic.LP.Internal.IntC LP.Tactic.LP.Internal.NatC

/-! ## The strengthening closing lemmas (the `linarith` preprocessing facts). -/

example (a b : Int) (h : a < b) : a + 1 ≤ b := add_one_le_of_lt h
example (a b : Int) (h : a < b + 1) : a ≤ b := le_of_lt_add_one h
example (a b : Nat) (h : a < b) : a + 1 ≤ b := add_one_le_of_lt h
example (a b : Nat) (h : a < b + 1) : a ≤ b := le_of_lt_add_one h

/-! ## Goal-only ℤ/ℕ comparisons close with zero rows (no backend needed). -/

example (a : Int) : a < a + 1 := by lp
example (a : Int) : a ≤ a := by lp
example (a : Int) : a + 1 ≤ a + 1 := by lp
example (a : Int) : a ≤ a + 3 := by lp
example (a b : Int) : a + b ≤ b + a := by lp

example (a : Nat) : a < a + 1 := by lp
example (a : Nat) : a ≤ a := by lp
example (a : Nat) : a ≤ a + 5 := by lp
example (a b : Nat) : a + b < a + b + 1 := by lp

/-! ## The issue's behavioral repros (multi-row — need a backend; verified downstream).

```
example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a + 2 ≤ c := by lp
example (a b : Int) (h : a < b) : a + 1 ≤ b := by lp
example (n : Nat) (i j : Fin n) (h : i.val ≤ j.val) : i.val < j.val + 1 := by lp
example (n : Nat) (a b : Fin n) (h : (a:Nat) < (b:Nat)) : (a:Nat) + 1 ≤ (b:Nat) := by lp
-- strict goals over ℤ/ℕ close via residual positivity (no strict-tagged rows needed):
example (a b : Int) (h : a < b) : a < b := by lp
example (a b c : Int) (h1 : a < b) (h2 : b < c) : a + 1 < c := by lp
example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a + 1 < c := by lp
-- negated-goal strengthening (integer rounding of a fractional bound):
example (a b : Int) (h : 2*a ≤ 2*b + 1) : a ≤ b := by lp
example (a b : Int) (h : 2*a < 2*b) : a < b := by lp
-- strict infeasibility (a chain of strict facts, residual now > 0):
example (a b : Int) (h1 : a < b) (h2 : b < a) : False := by lp
```
-/

end LPTacticTest.Issue40
