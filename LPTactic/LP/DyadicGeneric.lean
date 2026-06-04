/-
`Dyadic`-monomorphic certificate lemmas for the unified `lp` engine. `Dyadic` (Lean core,
`Init/Data/Dyadic/`) is a computable ordered commutative ring (NOT a field — dyadics have no
inverses), so like `Int` it gets native kernel-reducible literals + `Eq.refl` leaves; only the
structural lemmas + scaled closers are needed here. Stated over concrete `Dyadic`; proofs are
static (`grind` over the core `CommRing`/`OrderedRing Dyadic` instances is fine here).
-/
module
public import Init.Data.Dyadic.Instances
public import Init.Grind.Ordered.Ring

@[expose] public section

namespace LP.Tactic.LP.Internal.DyadicC

open Lean.Grind

/-! ## Scaled closers (native `Dyadic` `*`). -/

theorem mul_nonneg_back {L z : Dyadic} (hL : 0 < L) (h : 0 ≤ L * z) : 0 ≤ z := by
  grind [OrderedRing.mul_nonneg_iff]

theorem mul_pos_back {L z : Dyadic} (hL : 0 < L) (h : 0 < L * z) : 0 < z := by
  grind [OrderedRing.mul_pos_iff]

theorem scaled_le_close {L lhs rhs s C : Dyadic}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 ≤ C)
    (hIdent : L * (rhs - lhs) + s = C) : lhs ≤ rhs := by
  have h : 0 ≤ L * (rhs - lhs) := by
    have : L * (rhs - lhs) = C - s := by grind
    rw [this]; grind
  have hz := mul_nonneg_back hL h
  grind

theorem scaled_lt_close {L lhs rhs s C : Dyadic}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 < C)
    (hIdent : L * (rhs - lhs) + s = C) : lhs < rhs := by
  have h : 0 < L * (rhs - lhs) := by
    have : L * (rhs - lhs) = C - s := by grind
    rw [this]; grind
  have hz := mul_pos_back hL h
  grind

theorem scaled_infeasible_close {s C : Dyadic}
    (hSum : s ≤ 0) (hC : 0 < C) (hIdent : s = C) : False := by grind

theorem le_close {lhs rhs s C : Dyadic}
    (hSum : s ≤ 0) (hC : 0 ≤ C) (hIdent : rhs - lhs + s = C) : lhs ≤ rhs := by grind

theorem lt_close {lhs rhs s C : Dyadic}
    (hSum : s ≤ 0) (hC : 0 < C) (hIdent : rhs - lhs + s = C) : lhs < rhs := by grind

theorem le_antisymm {a b : Dyadic} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by grind

/-! ## Row closure + weighted-sum sign lemmas. -/

theorem sub_nonpos_of_le {a b : Dyadic} (h : a ≤ b) : a - b ≤ 0 := by grind

theorem sub_nonpos_of_eq {a b : Dyadic} (h : a = b) : a - b ≤ 0 := by grind

theorem dyadic_smul_nonpos {a k : Dyadic} (ha : a ≤ 0) (hk : 0 ≤ k) : k * a ≤ 0 :=
  OrderedRing.mul_nonpos_of_nonneg_of_nonpos hk ha

theorem dyadic_add_nonpos {a b : Dyadic} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 := by grind

/-! ## Normalizer fixed-arity lemmas (native `Dyadic`). -/

theorem atom_norm (x : Dyadic) : x = 1 * x + 0 := by grind

theorem mul_atom_norm (k x : Dyadic) : k * x = k * x + 0 := by grind

theorem neg_atom_norm (x : Dyadic) : -x = (-1) * x + 0 := by grind

theorem take_left (h ta b res : Dyadic) (e : ta + b = res) : (h + ta) + b = h + res := by grind

theorem take_right (a h tb res : Dyadic) (e : a + tb = res) : a + (h + tb) = h + res := by grind

theorem combine (x ta tb res c' c m : Dyadic) (e : ta + tb = res) (hm : c' + c = m) :
    (c' * x + ta) + (c * x + tb) = m * x + res := by grind

theorem combine_zero (x ta tb res c' c : Dyadic) (e : ta + tb = res) (hm : c' + c = 0) :
    (c' * x + ta) + (c * x + tb) = res := by grind

theorem smul_cons (k x c m rest rest' : Dyadic) (hm : k * c = m) (e : k * rest = rest') :
    k * (c * x + rest) = m * x + rest' := by grind

theorem neg_cons (x c m rest rest' : Dyadic) (hm : -c = m) (e : -rest = rest') :
    -(c * x + rest) = m * x + rest' := by grind

theorem add_congr_eq (a A b B : Dyadic) (ha : a = A) (hb : b = B) : a + b = A + B := by grind

theorem sub_congr_eq (a A b B : Dyadic) (ha : a = A) (hb : b = B) : a - b = A - B := by grind

theorem mul_congr_eq_r (k a A : Dyadic) (e : a = A) : k * a = k * A := by grind

theorem mul_congr_eq_l (a A k : Dyadic) (e : a = A) : a * k = A * k := by grind

theorem neg_congr_eq (a A : Dyadic) (e : a = A) : -a = -A := by grind

theorem sub_to_add_neg (a b : Dyadic) : a - b = a + (-b) := by grind

theorem zero_self_le : (0 : Dyadic) ≤ 0 := by grind

end LP.Tactic.LP.Internal.DyadicC
