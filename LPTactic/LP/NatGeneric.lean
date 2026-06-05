/-
`Nat`-monomorphic certificate lemmas. `Nat` is an ordered commutative SEMIRING with NO
negation, so the ring `(rhs-lhs)+s=c` certificate is impossible. Instead, from a weighted
hypothesis sum `Wl ≤ Wr` (`Wl = Σkᵢ·lhsᵢ`, `Wr = Σkᵢ·rhsᵢ`) and the no-subtraction semiring
IDENTITY `L·rhs + Wl = L·lhs + Wr + C`, add-cancellation (`Wl`/`Wr`) and mul-cancellation
(`L>0`) give `lhs ≤ rhs`. Native kernel-reducible `Nat` literals (`Eq.refl` leaves). The
normalizer never hits neg/sub on `Nat` exprs, so only the `+`/`*`/atom lemmas are needed.
-/
module
public import Init.Grind.Tactics

@[expose] public section

namespace LP.Tactic.LP.Internal.NatC

/-! ## Closers (no subtraction). `C` is the nonneg Farkas residual; `Wl ≤ Wr` the weighted hyp
sum; the identity moves the ring negatives across `=`. -/

theorem le_close {lhs rhs Wl Wr C : Nat}
    (hW : Wl ≤ Wr) (hId : rhs + Wl = lhs + Wr + C) : lhs ≤ rhs := by omega

theorem lt_close {lhs rhs Wl Wr C : Nat}
    (hW : Wl ≤ Wr) (hC : 0 < C) (hId : rhs + Wl = lhs + Wr + C) : lhs < rhs := by omega

theorem infeasible_close {Wl Wr C : Nat}
    (hW : Wl ≤ Wr) (hC : 0 < C) (hId : Wl = Wr + C) : False := by omega

theorem scaled_le_close {L lhs rhs Wl Wr C : Nat}
    (hL : 0 < L) (hW : Wl ≤ Wr) (hId : L * rhs + Wl = L * lhs + Wr + C) : lhs ≤ rhs := by
  have h : L * lhs ≤ L * rhs := by omega
  exact Nat.le_of_mul_le_mul_left h hL

theorem scaled_lt_close {L lhs rhs Wl Wr C : Nat}
    (_hL : 0 < L) (hW : Wl ≤ Wr) (hC : 0 < C) (hId : L * rhs + Wl = L * lhs + Wr + C) :
    lhs < rhs := by
  -- `Nat.lt_of_mul_lt_mul_left` needs no `0 < L`: `L * lhs < L * rhs` already forces it.
  have h : L * lhs < L * rhs := by omega
  exact Nat.lt_of_mul_lt_mul_left h

theorem le_antisymm {a b : Nat} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by omega

/-! ## Monotonicity for the two-sided weighted sum. -/

theorem nat_nsmul_le (k a b : Nat) (h : a ≤ b) : k * a ≤ k * b := Nat.mul_le_mul_left k h

theorem nat_add_le (a b c d : Nat) (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by omega

theorem zero_self_le : (0 : Nat) ≤ 0 := by omega

/-! ## Normalizer fixed-arity lemmas (semiring `+`/`*` only — NO neg/sub). -/

theorem atom_norm (x : Nat) : x = 1 * x + 0 := by grind

theorem mul_atom_norm (k x : Nat) : k * x = k * x + 0 := by grind

theorem take_left (h ta b res : Nat) (e : ta + b = res) : (h + ta) + b = h + res := by grind

theorem take_right (a h tb res : Nat) (e : a + tb = res) : a + (h + tb) = h + res := by grind

theorem combine (x ta tb res c' c m : Nat) (e : ta + tb = res) (hm : c' + c = m) :
    (c' * x + ta) + (c * x + tb) = m * x + res := by grind

theorem combine_zero (x ta tb res c' c : Nat) (e : ta + tb = res) (hm : c' + c = 0) :
    (c' * x + ta) + (c * x + tb) = res := by grind

theorem smul_cons (k x c m rest rest' : Nat) (hm : k * c = m) (e : k * rest = rest') :
    k * (c * x + rest) = m * x + rest' := by grind

theorem add_congr_eq (a A b B : Nat) (ha : a = A) (hb : b = B) : a + b = A + B := by grind

theorem mul_congr_eq_r (k a A : Nat) (e : a = A) : k * a = k * A := by grind

theorem mul_congr_eq_l (a A k : Nat) (e : a = A) : a * k = A * k := by grind

end LP.Tactic.LP.Internal.NatC
