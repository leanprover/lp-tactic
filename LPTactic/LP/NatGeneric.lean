/-
`Nat`-monomorphic certificate lemmas. `Nat` is an ordered commutative SEMIRING with NO
negation, so the ring `(rhs-lhs)+s=c` certificate is impossible. Instead, from a weighted
hypothesis sum `Wl ≤ Wr` (`Wl = Σkᵢ·lhsᵢ`, `Wr = Σkᵢ·rhsᵢ`) and the no-subtraction semiring
IDENTITY `L·rhs + Wl = L·lhs + Wr + C`, add-cancellation (`Wl`/`Wr`) and mul-cancellation
(`L>0`) give `lhs ≤ rhs`. Native kernel-reducible `Nat` literals (`Eq.refl` leaves). The
normalizer never hits neg/sub on `Nat` exprs, so only the semiring normalizer block
(stamped out by `declare_lp_normalizer_semiring_lemmas`) is needed.
-/
module
public import Init.Grind.Tactics
meta import LPTactic.LP.CarrierLemmas

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

declare_lp_normalizer_semiring_lemmas Nat

end LP.Tactic.LP.Internal.NatC
