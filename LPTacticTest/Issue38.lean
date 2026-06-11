/-
  Tests for issue #38: `div_eq_inv_mul`'s auto-bound section variables broke the
  fixed-arity applier.

  The field engine's fixed-arity applier (`CCtx.ring`) builds every
  `Internal.Field` lemma application as `mkAppN (mkConst name [u]) (#[α, fieldInst] ++ args)`,
  relying on the convention that each lemma's prefix is exactly `{α} [Field α]`.
  `div_eq_inv_mul` lived in the ordered section and silently picked up five unused
  auto-bound order instances (`[LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α]
  [OrderedRing α]`) ahead of the explicit args, so the constructed `div_eq_inv_mul α
  fieldInst dividend divisor` fed `dividend : α` where the kernel expected `[LE α]` —
  a kernel application-type mismatch, surfacing only at check time (the tactic builds
  raw `mkAppN` Exprs, no elaboration re-check). The divisor path that reaches the
  applier became live over `ℝ` only after #34. The fix moves `div_eq_inv_mul` to the
  `[Field α]`-only ring section, so the prefix matches the kernel signature again.

  As in `Issue34`, `TestField` is an `irreducible` `Rat` synonym so `lp` routes to the
  `.field` engine; every divisor case below hits the `HDiv.hDiv` branch of
  `normalizeR`, which fires `div_eq_inv_mul`. All certificates are trivial (the
  residual closes with zero rows), so the path runs without a registered LP backend.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue38

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

/-! ## Division by a literal divisor — the path that fires `div_eq_inv_mul`. -/

example (x : TestField) : x / 2 ≤ x / 2 + 1 := by lp
example (x : TestField) : x / 3 ≤ x / 3 + 1 := by lp
example (x : TestField) : (x / 2 : TestField) ≤ x / 2 + 1 := by lp

/-! ## Division nested with the recognized scalar heads. -/

example (x : TestField) : x / 2 + x / 3 ≤ x / 2 + x / 3 + 1 := by lp
example (x : TestField) : (2 : TestField) * (x / 2) ≤ 2 * (x / 2) + 1 := by lp

end LPTacticTest.Issue38
