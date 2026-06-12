/-
  Tests for issue #41: canonicalize ring-equal opaque atoms (commuted products)
  to one LP column.

  Opaque non-affine subterms are atomized and keyed by their `Expr`. Before this
  change, ring-equal but not defeq forms — `f x * y` vs `y * f x` — got *separate*
  LP columns, so a hypothesis row never constrained the goal column and the
  refutation LP was unbounded. The parser now canonicalizes a product atom by
  flattening its carrier-`*` chain and sorting the factors (`mulCanonKey?`), so
  both commuted forms share one key; the certificate normalizer proves
  `original = canonical` from `mul_comm`/`mul_assoc` (`mulCanon?`) and chains it
  with `atom_norm` (`normalizeAtom`).

  These cases run without a registered LP backend: a goal `commuted ≤ original`
  shares a single column on both sides, so it collapses to the closed row
  `0 ≤ 0` and is discharged by the tactic alone (the same zero-variable path the
  Issue5 cases use). The multi-row Farkas variants that genuinely need a solve
  (e.g. `(h : f x * y ≤ 1) : y * f x ≤ 1`) live in the backend test suites'
  parity sweeps.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue41

/-! ## Commuted products of two opaque factors (the minimal repro shape). -/

example (f : Rat → Rat) (x y : Rat) : y * f x ≤ f x * y := by lp
example (f : Rat → Rat) (x y : Rat) : f x * y ≤ y * f x := by lp
example (g c : Rat) : c * g ≤ g * c := by lp

/-! ## Strict goals carry through the same atom column. -/

example (f : Rat → Rat) (x y : Rat) : y * f x < f x * y + 1 := by lp

/-! ## Three opaque factors: reversed order and re-association both canonicalize. -/

example (f g h : Rat) : h * (g * f) ≤ f * g * h := by lp
example (f g h : Rat) : (h * f) * g ≤ (f * g) * h := by lp

/-! ## Compound factors (`b - a`): the `Convex/Slope.lean` family's atom shape.

These also guard the `normalizeScalar?` fix: without distinct fallback indices
for the unregistered factors `a`/`b`, the certificate normalizer mis-read
`b - a` as the scalar `0` and produced an ill-typed proof. -/

example (a b c : Rat) : c * (b - a) ≤ (b - a) * c := by lp
example (p q r s : Rat) : (r - s) * (p - q) ≤ (p - q) * (r - s) := by lp

/-! ## Compound closed scalars still fold (`normalizeScalar?` regression guard). -/

example (x : Rat) : (2 - 1) * x ≤ x := by lp

/-! ## An algebraically-zero coefficient (`a - a`) folds to `0` soundly: identical
factors share an index in `normalizeScalar?`'s trial, so the cancellation (and its
`combine_zero` proof) is genuine, unlike the distinct-factor `b - a` collision. -/

example (a x : Rat) : (a - a) * x ≤ (a - a) * x + 1 := by lp

/-! ## The computable ring/semiring carriers canonicalize too. -/

example (f : Int → Int) (x y : Int) : y * f x ≤ f x * y := by lp
example (a b c : Int) : c * (b - a) ≤ (b - a) * c := by lp
example (f : Nat → Nat) (x y : Nat) : y * f x ≤ f x * y := by lp
example (f : Dyadic → Dyadic) (x y : Dyadic) : y * f x ≤ f x * y := by lp

/-! ## The field (`ofRat`) certificate path, via a carrier defeq to `Rat`.

Mirrors `Issue38`'s `TestField`: a non-`Rat` carrier that still carries the
ordered-field bundle, so the shared `CarrierCertificate` normalizer runs its
field assembly (`Field.NormNum.ofRat` literals) over the canonicalized atom. -/

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

example (f : TestField → TestField) (x y : TestField) : y * f x ≤ f x * y := by lp
example (f g h : TestField) : h * (g * f) ≤ f * g * h := by lp
example (a b c : TestField) : c * (b - a) ≤ (b - a) * c := by lp

end LPTacticTest.Issue41
