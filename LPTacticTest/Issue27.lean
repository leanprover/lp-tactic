/-
  Tests for issue #27: compound closed scalar coefficients/divisors.

  The parser's recursive `parseScalar?` folds compound closed scalars like
  `(2 - 1)` in coefficient position, but the certificate normalizer's quick
  `scalarLit?` deliberately rejects `HAdd`/`HSub` heads, so these products
  used to fall through to `normalizeAtom` and fail with "atom not registered
  during parsing". The fix bridges them via `CarrierMethods.normalizeScalar?`
  (full normalization, accepted iff it closes to a constant).

  All cases here have trivial certificates (the residual closes with zero
  rows), so they exercise the normalizer without a registered LP backend.
-/

import LPTactic

namespace LPTacticTest.Issue27

/-! ## The issue's repros. -/

example (x : Rat) : (2 - 1 : Rat) * x ≤ x + 1 := by lp
example (x : Int) : (2 - 1 : Int) * x ≤ x + 1 := by lp

/-! ## Compound scalars across carriers and positions. -/

example (x : Rat) : (2 + 1 : Rat) * x ≤ 3 * x + 1 := by lp
example (x : Rat) : x * (2 - 1 : Rat) ≤ x + 1 := by lp
example (x : Int) : x * (2 - 1 : Int) ≤ x + 1 := by lp
example (x : Nat) : (2 + 1 : Nat) * x ≤ 3 * x + 1 := by lp
example (x : Dyadic) : (2 - 1 : Dyadic) * x ≤ x + 1 := by lp
example (x : Rat) : ((1 : Rat) / 2 + 1 / 2) * x ≤ x + 1 := by lp

/-! ## Compound closed divisor (the `HDiv` branch has the same gap). -/

example (x : Rat) : x / (3 - 1 : Rat) ≤ x / 2 + 1 := by lp

/-! ## Regressions: nonlinear products (no closed-scalar side) still atomize. -/

example (x y : Rat) : x * y ≤ x * y + 1 := by lp
example (x y : Int) : x * y ≤ x * y + 1 := by lp
example (x y : Rat) : (x + 2) * y ≤ (x + 2) * y + 1 := by lp

/-! ## A side that the parser atomized but that normalizes CLOSED via cancellation:
    the normalizer folds it to a constant; both models agree on the residual. -/

example (x y : Rat) : (x - x) * y ≤ (x - x) * y + 1 := by lp

end LPTacticTest.Issue27
