/-
  Tests for issue #42: carrier misdetection on goals whose ambient type is not the
  arithmetic type.

  Two failure shapes from the Mathlib resurvey, both leaking a raw
  `failed to synthesize …` from carrier detection:

  (a) A comparison/`Eq` goal whose RELATION type is a non-arithmetic type — e.g.
      `x = y` for `x y : X` a topological space. `relCarrier?` reads `X` off the `Eq`
      head and the dispatcher committed to it as the carrier, so `mkCarrierOps X` threw
      `failed to synthesize HAdd X X X`. The fix gates the atomic dispatch on
      `isCarrierType`: a non-arithmetic relation type is NOT an `lp` atom, so the goal
      falls through to the inconsistency path (discharge ex falso from inconsistent
      arithmetic hypotheses), exactly like `False`.

  (c) The field engine's numeral builder synthesized a bare `OfNat α 0` / `OfNat α 1`.
      For an abstract field reached through the Mathlib→Grind bridge this can fail
      (`failed to synthesize OfNat K 0`) even though every Grind field carries the
      `Semiring.ofNat : ∀ n, OfNat α n` numeral map. The fix builds `0`/`1`/numerals
      through `Semiring.ofNat`, which is exactly the instance the generic field lemmas'
      `(0 : α)` already resolves to.

  `TestField` is an `irreducible` `Rat` synonym (as in `Issue34`/`Issue38`) so `lp`
  routes to the `.field` engine; `K` below is a fully abstract ordered Grind field. All
  certificates here are trivial (closed contradictions or zero-row residuals), so the
  cases run without a registered LP backend.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue42

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

/-- A non-arithmetic ambient type, standing in for a topological space. -/
class Topo (X : Type) where

/-! ## Shape (a): a goal over a non-arithmetic relation type.

The `x = y` goal is over `X`, which carries no arithmetic structure. Detection must NOT
commit to `X` (which would throw `failed to synthesize HAdd X X X`); instead the goal is
discharged ex falso from the closed inconsistent `TestField` hypothesis. -/

example (X : Type) [Topo X] (x y : X) (h : (2 : TestField) ≤ 1) : x = y := by lp
example (X : Type) [Topo X] (x y : X) (h : (3 : TestField) < 2) : x = y := by lp

-- Even with a (consistent) arithmetic local in scope, an `Eq` over `X` whose context is
-- NOT inconsistent reports a clean in-fragment diagnostic — no `failed to synthesize`.
/-- error: lp: goal
  x = y
is not an atomic comparison or `∃`, and no linear hypothesis over a supported carrier was found to derive it from -/
#guard_msgs in
example (X : Type) [Topo X] (x y : X) : x = y := by lp

/-- error: lp: goal
  x = y
is not an atomic comparison, and the hypotheses over [TestField] are not inconsistent -/
#guard_msgs in
example (X : Type) [Topo X] (x y : X) (a : TestField) (h : a ≤ 1) : x = y := by lp

/-! ## Shape (c): the field numeral path over a fully abstract ordered Grind field.

`0`/`1` and `Nat`-numeral literals must be built through `Semiring.ofNat` (which every
Grind field carries) rather than a bare `OfNat K n`. These zero-row certificates exercise
`c.zero` and the literal builder. -/

section AbstractField
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K]
  [OrderedRing K] [IsCharP K 0]

example (x : K) : x ≤ x := by lp
example (x : K) : x ≤ x + 1 := by lp
example (x : K) : x - 1 ≤ x := by lp
-- A non-arithmetic-relation goal over an abstract field context, discharged ex falso.
example (Y : Type) [Topo Y] (p q : Y) (h : (5 : K) ≤ 2) : p = q := by lp

end AbstractField

end LPTacticTest.Issue42
