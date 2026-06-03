/-
Int-monomorphic certificate lemmas for the `lp` tactic — the de-risking prototype's
static layer. Concrete `Int` (no carrier variable), stated in NATIVE `Int` operations
(`Int.add`/`Int.mul`/`Int.neg`), NOT `zsmul`/`IntModule` `•` — so the produced proof
term carries no `intCast` bridge (`Ring.zsmul_eq_intCast_mul`), which is the whole perf
point. `Int` is a computable ordered commutative ring: leaf coefficient equalities close
by `Eq.refl` (validated), and these structural lemmas are static so the proofs may use
`grind`/`omega` (the runtime-tactic prohibition applies to the tactic, not to these).
-/
import Init.Grind.Ordered.Int

namespace Soplex.Tactic.LP.Internal.IntC

/-! ## Scaled closers (native `Int.mul`).

SoPlex's rational Farkas multipliers are cleared to integers by scaling the certificate
by a positive `L`, so the closing identity is `L * (rhs - lhs) + s = C`. The backward
step `0 < L → 0 ≤ L * z → 0 ≤ z` is the load-bearing sign lemma. -/

theorem mul_nonneg_back {L z : Int} (hL : 0 < L) (h : 0 ≤ L * z) : 0 ≤ z := by
  apply Classical.byContradiction; intro hz
  have hz' : z < 0 := by omega
  have : L * z < 0 := Int.mul_neg_of_pos_of_neg hL hz'
  omega

theorem mul_pos_back {L z : Int} (hL : 0 < L) (h : 0 < L * z) : 0 < z := by
  apply Classical.byContradiction; intro hz
  have hz' : z ≤ 0 := by omega
  have : L * z ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hz'
  omega

theorem scaled_le_close {L lhs rhs s C : Int}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 ≤ C)
    (hIdent : L * (rhs - lhs) + s = C) : lhs ≤ rhs := by
  have h : 0 ≤ L * (rhs - lhs) := by omega
  have := mul_nonneg_back hL h
  omega

theorem scaled_lt_close {L lhs rhs s C : Int}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 < C)
    (hIdent : L * (rhs - lhs) + s = C) : lhs < rhs := by
  have h : 0 < L * (rhs - lhs) := by omega
  have := mul_pos_back hL h
  omega

theorem scaled_infeasible_close {s C : Int}
    (hSum : s ≤ 0) (hC : 0 < C) (hIdent : s = C) : False := by omega

/-- Unscaled closers for the common `L = 1` case (integer multipliers): no `L *` factor,
so the normalizer skips a whole `proveSmul` pass over the objective. -/
theorem le_close {lhs rhs s C : Int}
    (hSum : s ≤ 0) (hC : 0 ≤ C) (hIdent : rhs - lhs + s = C) : lhs ≤ rhs := by omega

theorem lt_close {lhs rhs s C : Int}
    (hSum : s ≤ 0) (hC : 0 < C) (hIdent : rhs - lhs + s = C) : lhs < rhs := by omega

theorem le_antisymm {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by omega

/-! ## Row closure (hypothesis `a ≤ b`/`a = b` → `a - b ≤ 0`). -/

theorem sub_nonpos_of_le {a b : Int} (h : a ≤ b) : a - b ≤ 0 := by omega

theorem sub_nonpos_of_eq {a b : Int} (h : a = b) : a - b ≤ 0 := by omega

/-! ## Weighted-sum sign lemmas (native `Int.mul`). -/

theorem int_smul_nonpos {a k : Int} (ha : a ≤ 0) (hk : 0 ≤ k) : k * a ≤ 0 :=
  Int.mul_nonpos_of_nonneg_of_nonpos hk ha

theorem int_add_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 := by omega

/-! ## Normalizer fixed-arity lemmas (native `Int`, exact copies of `Types.lean`'s Rat
shapes). Coefficient arithmetic happens host-side; the `hm`/`e` hypotheses are discharged
by `Eq.refl` at the call site (Int leaf equalities are defeq). -/

theorem atom_norm (x : Int) : x = 1 * x + 0 := by grind

theorem mul_atom_norm (k x : Int) : k * x = k * x + 0 := by grind

theorem neg_atom_norm (x : Int) : -x = (-1) * x + 0 := by grind

theorem take_left (h ta b res : Int) (e : ta + b = res) : (h + ta) + b = h + res := by grind

theorem take_right (a h tb res : Int) (e : a + tb = res) : a + (h + tb) = h + res := by grind

theorem combine (x ta tb res c' c m : Int) (e : ta + tb = res) (hm : c' + c = m) :
    (c' * x + ta) + (c * x + tb) = m * x + res := by grind

theorem combine_zero (x ta tb res c' c : Int) (e : ta + tb = res) (hm : c' + c = 0) :
    (c' * x + ta) + (c * x + tb) = res := by grind

theorem smul_cons (k x c m rest rest' : Int) (hm : k * c = m) (e : k * rest = rest') :
    k * (c * x + rest) = m * x + rest' := by grind

theorem neg_cons (x c m rest rest' : Int) (hm : -c = m) (e : -rest = rest') :
    -(c * x + rest) = m * x + rest' := by grind

theorem add_congr_eq (a A b B : Int) (ha : a = A) (hb : b = B) : a + b = A + B := by grind

theorem sub_congr_eq (a A b B : Int) (ha : a = A) (hb : b = B) : a - b = A - B := by grind

theorem mul_congr_eq_r (k a A : Int) (e : a = A) : k * a = k * A := by grind

theorem mul_congr_eq_l (a A k : Int) (e : a = A) : a * k = A * k := by grind

theorem neg_congr_eq (a A : Int) (e : a = A) : -a = -A := by grind

theorem sub_to_add_neg (a b : Int) : a - b = a + (-b) := by grind

theorem zero_self_le : (0 : Int) ≤ 0 := by omega

end Soplex.Tactic.LP.Internal.IntC
