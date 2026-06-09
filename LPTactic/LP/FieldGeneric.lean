/-
Generic ordered-FIELD certificate lemmas for the `lp` tactic — the
carrier-polymorphic port of the `Rat`-specific lemmas in `Types.lean`.

The field path keeps the existing engine shape verbatim: rational coefficients
stay rational (rendered via `Lean.Grind.Field.NormNum.ofRat`), the closers are
unscaled (`rhs - lhs + s = c`), and `0 ≤ c` lifts to the carrier via ordered-field
positivity. No `zsmul`, no integer clearing. Stated over Lean core's `Lean.Grind`
ordered-field bundle (no Mathlib): instantiates at `Rat` (core) and `ℝ` (Mathlib)
and any ordered field of characteristic zero.

These are static lemmas, so the proofs may use `grind`/`simp` (the prohibition on
tactic calls applies only to the per-certificate *tactic runtime*, not here).
-/
module
public import Init.Grind.Ordered.Field
public import Init.Grind.Ordered.Linarith
public import Init.Grind.FieldNormNum

@[expose] public section

namespace LP.Tactic.LP.Internal.Field

open Std
open Lean.Grind

/-! ## Entailment / closing arithmetic (unscaled) — needs the order -/

section Ordered
variable {α : Type u}
  [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

theorem le_of_sub_nonpos {a b : α} (h : a - b ≤ 0) : a ≤ b := by grind
theorem sub_nonpos_of_le {a b : α} (h : a ≤ b) : a - b ≤ 0 := by grind
/-- Strict-hypothesis relaxation: `a < b` used as the weaker `a - b ≤ 0`. -/
theorem sub_nonpos_of_lt {a b : α} (h : a < b) : a - b ≤ 0 := by grind
theorem sub_nonpos_of_eq {a b : α} (h : a = b) : a - b ≤ 0 := by grind
/-- Rewrite `a / c` as `c⁻¹ * a` so the normalizer reuses the scalar-mul path
(true even at `c = 0`). Args explicit to match `applyLemma`. -/
theorem div_eq_inv_mul (a b : α) : a / b = b⁻¹ * a := by grind
theorem lt_of_sub_neg {a b : α} (h : a - b < 0) : a < b := by grind
theorem le_of_nonneg_sub {a b : α} (h : 0 ≤ b - a) : a ≤ b := by grind
theorem lt_of_pos_sub {a b : α} (h : 0 < b - a) : a < b := by grind

/-- A nonnegative scalar of a nonpositive value is nonpositive. -/
theorem smul_nonpos {a lam : α} (ha : a ≤ 0) (hlam : 0 ≤ lam) : lam * a ≤ 0 :=
  OrderedRing.mul_nonpos_of_nonneg_of_nonpos hlam ha

theorem add_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 := by grind

theorem zero_self_le : (0 : α) ≤ 0 := by grind

omit [Field α] [LT α] [LawfulOrderLT α] [OrderedRing α] in
/-- Antisymmetry, for the `=`-goal split (`lhs ≤ rhs` ∧ `rhs ≤ lhs` ⇒ `lhs = rhs`). -/
theorem le_antisymm {a b : α} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by grind

/-- A nonnegative rational lifts to a nonnegative carrier element. The residual
sign discharge and the multiplier-nonneg facts both go through this. -/
theorem ofRat_nonneg {r : Rat} (h : 0 ≤ r) : 0 ≤ (Field.NormNum.ofRat r : α) := by
  rw [Field.NormNum.ofRat, Field.div_eq_mul_inv]
  refine OrderedRing.mul_nonneg ?_ ?_
  · exact OrderedRing.nonneg_intCast_of_nonneg _ (Rat.num_nonneg.mpr h)
  · rw [Field.IsOrdered.inv_nonneg_iff]; exact OrderedRing.natCast_nonneg

/-- A positive rational lifts to a positive carrier element (strict closers). -/
theorem ofRat_pos {r : Rat} (h : 0 < r) : 0 < (Field.NormNum.ofRat r : α) := by
  rw [Field.NormNum.ofRat, Field.div_eq_mul_inv]
  refine OrderedRing.mul_pos ?_ ?_
  · apply OrderedRing.pos_intCast_of_pos
    have h1 : 0 ≤ r.num := Rat.num_nonneg.mpr (le_of_lt h)
    have h2 : r.num ≠ 0 := by rw [ne_eq, Rat.num_eq_zero]; exact (ne_of_lt h).symm
    omega
  · rw [Field.IsOrdered.inv_pos_iff]; exact OrderedRing.pos_natCast_of_pos _ r.den_pos

/-! ## Final closers -/

theorem direct_le_close {lhs rhs s c : α}
    (hSum : s ≤ 0) (hC : 0 ≤ c) (hIdent : rhs - lhs + s = c) : lhs ≤ rhs := by grind

theorem direct_lt_close {lhs rhs s c : α}
    (hSum : s ≤ 0) (hC : 0 < c) (hIdent : rhs - lhs + s = c) : lhs < rhs := by grind

theorem direct_infeasible_close {s c : α}
    (hSum : s ≤ 0) (hC : 0 < c) (hIdent : s = c) : False := by grind

end Ordered

/-! ## Ring-only layer: `ofRat` literal helpers + normalizer fixed-arity lemmas.
These carry only `[Field α]`, so applying them on the hot path synthesizes no
order instances. -/

section Ring
variable {α : Type u} [Field α]

/-! ### `ofRat` literal helpers (uniform rendering of coefficients/constants) -/

theorem ofRat_zero : (Field.NormNum.ofRat 0 : α) = 0 := by
  simp [Field.NormNum.ofRat, Ring.intCast_zero, Field.div_eq_mul_inv, Semiring.zero_mul]

theorem ofRat_one : (Field.NormNum.ofRat 1 : α) = 1 := by
  simp [Field.NormNum.ofRat, Ring.intCast_one, Semiring.natCast_one, Field.div_eq_mul_inv,
    Field.inv_one, Semiring.mul_one]

theorem ofRat_neg_one : (Field.NormNum.ofRat (-1) : α) = -1 := by
  simp [Field.NormNum.ofRat, Field.div_eq_mul_inv, Ring.intCast_neg_one,
    Semiring.natCast_one, Field.inv_one, Semiring.mul_one]

/-! ## Normalizer fixed-arity lemmas

CommRing identities (a `+`/`-`/`*` rearrangement). Explicit `subst` + ring
rewrites, with a targeted `grind [...]` only for the two merge steps that need
distributivity+AC — mirroring `Types.lean`'s `combine`/`combine_zero`. -/

theorem atom_norm (x : α) : x = Field.NormNum.ofRat 1 * x + Field.NormNum.ofRat 0 := by
  rw [ofRat_one, ofRat_zero, Semiring.one_mul, AddCommMonoid.add_zero]

theorem mul_atom_norm (k x : α) : k * x = k * x + Field.NormNum.ofRat 0 := by
  rw [ofRat_zero, AddCommMonoid.add_zero]

theorem neg_atom_norm (x : α) : -x = Field.NormNum.ofRat (-1) * x + Field.NormNum.ofRat 0 := by
  rw [ofRat_neg_one, ofRat_zero, AddCommMonoid.add_zero, Ring.neg_mul, Semiring.one_mul]

theorem ofRat_zero_mul (x : α) : Field.NormNum.ofRat 0 * x = Field.NormNum.ofRat 0 := by
  rw [ofRat_zero, Semiring.zero_mul]

theorem take_left (h ta b res : α) (e : ta + b = res) : (h + ta) + b = h + res := by
  subst e; exact AddCommMonoid.add_assoc h ta b

theorem take_right (a h tb res : α) (e : a + tb = res) : a + (h + tb) = h + res := by
  subst e
  rw [AddCommMonoid.add_comm a (h + tb), AddCommMonoid.add_assoc, AddCommMonoid.add_comm tb a]

theorem combine (x ta tb res c' c m : α) (e : ta + tb = res) (hm : c' + c = m) :
    (c' * x + ta) + (c * x + tb) = m * x + res := by
  subst e; subst hm; grind [Semiring.right_distrib, AddCommMonoid.add_assoc,
    AddCommMonoid.add_comm, AddCommMonoid.add_left_comm]

theorem combine_zero (x ta tb res c' c : α) (e : ta + tb = res)
    (hm : c' + c = Field.NormNum.ofRat 0) : (c' * x + ta) + (c * x + tb) = res := by
  subst e
  -- `hm` lands on `ofRat 0` (the unified `proveMerge` passes the rendered literal, which is
  -- defeq to `0` over `Rat` but NOT over `ℝ`); bridge through `ofRat_zero`.
  have hm0 : c' + c = 0 := by rw [hm, ofRat_zero]
  have hzero : c' * x + c * x = 0 := by rw [← Semiring.right_distrib, hm0, Semiring.zero_mul]
  grind [AddCommMonoid.add_assoc, AddCommMonoid.add_comm, AddCommMonoid.add_left_comm,
    AddCommMonoid.add_zero, AddCommMonoid.zero_add]

theorem smul_cons (k x c m rest rest' : α) (hm : k * c = m) (e : k * rest = rest') :
    k * (c * x + rest) = m * x + rest' := by
  subst hm; subst e; rw [Semiring.left_distrib, Semiring.mul_assoc]

theorem neg_cons (x c m rest rest' : α) (hm : -c = m) (e : -rest = rest') :
    -(c * x + rest) = m * x + rest' := by
  subst hm; subst e; rw [AddCommGroup.neg_add, Ring.neg_mul]

theorem add_congr_eq (a A b B : α) (ha : a = A) (hb : b = B) : a + b = A + B := by
  subst ha; subst hb; rfl

theorem sub_congr_eq (a A b B : α) (ha : a = A) (hb : b = B) : a - b = A - B := by
  subst ha; subst hb; rfl

theorem mul_congr_eq_r (k a A : α) (e : a = A) : k * a = k * A := by subst e; rfl

theorem mul_congr_eq_l (a A k : α) (e : a = A) : a * k = A * k := by subst e; rfl

theorem neg_congr_eq (a A : α) (e : a = A) : -a = -A := by subst e; rfl

theorem sub_to_add_neg (a b : α) : a - b = a + (-b) := AddCommGroup.sub_eq_add_neg a b

end Ring

end LP.Tactic.LP.Internal.Field
