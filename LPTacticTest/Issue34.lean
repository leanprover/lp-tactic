/-
  Tests for issue #34: inverse numeral literals (`2⁻¹`) in the field carrier.

  The parser's `quickScalarLit?` already accepts `Inv.inv` (reading `c⁻¹` as the
  rational `1/c`), so an inverse-coefficient goal solves; but the field certificate's
  `CCtx.proveLitEq` used to handle only `OfNat`/`Neg`/`HAdd`/`HSub`/`HMul`/`HDiv`, so
  certificate construction threw `lp(field): unrecognized numeral literal` on `2⁻¹`.
  The fix adds an `Inv.inv` case mirroring `Neg.neg`, lifting via the core lemma
  `Lean.Grind.Field.NormNum.inv_eq` (`Field`-only, no `IsCharP` side condition).

  The field engine engages only for carriers other than `Rat`/`Int`/`Dyadic`/`Nat`,
  and the dependency-free test suites have no such carrier in scope. `TestField` below
  is a minimal stand-in: an `irreducible` synonym for `Rat`, so `detectCarrierKind`
  (default-transparency `isDefEq` against `Rat`) does NOT see through it and routes to
  the `.field` engine, while every instance is `Rat`'s, transported by `unfold`.

  All cases have trivial certificates (the residual closes with zero rows), so they
  exercise the literal bridge without a registered LP backend.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue34

/-! ## A non-core ordered field, so `lp` dispatches to the field certificate engine. -/

@[irreducible] def TestField : Type := Rat

namespace TestField
instance : Inv TestField           := by unfold TestField; exact (inferInstance : Inv Rat)
instance : Field TestField         := by unfold TestField; exact (inferInstance : Field Rat)
instance : LE TestField            := by unfold TestField; exact (inferInstance : LE Rat)
instance : LT TestField            := by unfold TestField; exact (inferInstance : LT Rat)
instance : IsPreorder TestField    := by unfold TestField; exact (inferInstance : IsPreorder Rat)
instance : LawfulOrderLT TestField := by unfold TestField; exact (inferInstance : LawfulOrderLT Rat)
instance : IsLinearOrder TestField := by unfold TestField; exact (inferInstance : IsLinearOrder Rat)
instance : OrderedRing TestField   := by unfold TestField; exact (inferInstance : OrderedRing Rat)
instance : IsCharP TestField 0     := by unfold TestField; exact (inferInstance : IsCharP Rat 0)
end TestField

/-! ## The issue's literal (`2⁻¹`), in constant and coefficient position. -/

example : (2⁻¹ : TestField) ≤ 1 := by lp
example (x : TestField) : (2⁻¹ : TestField) * x ≤ 2⁻¹ * x + 1 := by lp
example (x : TestField) : x * (2⁻¹ : TestField) ≤ x * 2⁻¹ + 1 := by lp

/-! ## The other reported bases (`3⁻¹`, `4⁻¹`, `5⁻¹`, `6⁻¹`, `10⁻¹`, `16⁻¹`). -/

example (x : TestField) : (3⁻¹ : TestField) * x ≤ 3⁻¹ * x + 1 := by lp
example (x : TestField) : (4⁻¹ : TestField) * x ≤ 4⁻¹ * x + 1 := by lp
example (x : TestField) : (5⁻¹ : TestField) * x ≤ 5⁻¹ * x + 1 := by lp
example (x : TestField) : (6⁻¹ : TestField) * x ≤ 6⁻¹ * x + 1 := by lp
example (x : TestField) : (10⁻¹ : TestField) * x ≤ 10⁻¹ * x + 1 := by lp
example (x : TestField) : (16⁻¹ : TestField) * x ≤ 16⁻¹ * x + 1 := by lp

/-! ## Inverse nested under the other recognized heads (`Neg`, `HMul`, `HSub`). -/

example (x : TestField) : (-(2⁻¹) : TestField) * x ≤ -(2⁻¹) * x + 1 := by lp
example (x : TestField) : (2⁻¹ * 3⁻¹ : TestField) * x ≤ 2⁻¹ * 3⁻¹ * x + 1 := by lp
example (x : TestField) : ((2⁻¹ : TestField) - 3⁻¹) * x ≤ (2⁻¹ - 3⁻¹) * x + 1 := by lp

/-! ## Regression: `0⁻¹` is rejected by the recognizer (the `r = 0` guard), so it
    atomizes rather than becoming a literal coefficient; the residual still closes. -/

example (x : TestField) : (0⁻¹ : TestField) * x ≤ 0⁻¹ * x + 1 := by lp

end LPTacticTest.Issue34
