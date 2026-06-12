/-
Command macros that stamp out the per-carrier monomorphic certificate lemma blocks.

`Nat`, `Int`, `Dyadic`, and `Rat` all need the same fixed-arity normalizer lemmas, and
`Int`/`Dyadic` additionally share the ordered-comm-ring closers and sign lemmas. The
blocks are deliberately MONOMORPHIC: the `lp` certificate engine applies them with
`mkAppN` and explicit arguments, so a carrier-variable statement would put instance
arguments (and instance-path mismatches against the engine's cached operator Exprs)
back on the proof-term hot path. Instead of copy-pasting the block per carrier, each
carrier file stamps it out with these macros inside its own namespace.

The proofs are static (`grind` over the carrier's core ordered-ring instances); the
prohibition on runtime tactic calls applies to the per-certificate construction, not
to these one-time declarations.
-/
module

public meta section

/-- Declare the semiring fixed-arity normalizer lemma block for the carrier `α`:
the `+`/`*`/atom lemmas the shared structural normalizer (`CarrierMethods.normalizeR`)
applies with explicit arguments. The `e`/`hm`/`ha`/`hb` hypotheses are discharged at
the call site (recursively, or by `Eq.refl` for kernel-reducible literal leaves). -/
macro "declare_lp_normalizer_semiring_lemmas" α:ident : command => `(
theorem $(Lean.mkIdent `atom_norm) (x : $α) : x = 1 * x + 0 := by grind

theorem $(Lean.mkIdent `mul_atom_norm) (k x : $α) : k * x = k * x + 0 := by grind

/-- Dense-row fast-path step: appending a fresh trailing atom `h` to an
already-rendered `a` is `take_right` fed with `a + 0 = a`. -/
theorem $(Lean.mkIdent `add_zero_norm) (a : $α) : a + 0 = a := by grind

theorem $(Lean.mkIdent `take_left) (h ta b res : $α) (e : ta + b = res) : (h + ta) + b = h + res := by grind

theorem $(Lean.mkIdent `take_right) (a h tb res : $α) (e : a + tb = res) : a + (h + tb) = h + res := by grind

theorem $(Lean.mkIdent `combine) (x ta tb res c' c m : $α) (e : ta + tb = res) (hm : c' + c = m) :
    (c' * x + ta) + (c * x + tb) = m * x + res := by grind

theorem $(Lean.mkIdent `combine_zero) (x ta tb res c' c : $α) (e : ta + tb = res) (hm : c' + c = 0) :
    (c' * x + ta) + (c * x + tb) = res := by grind

theorem $(Lean.mkIdent `smul_cons) (k x c m rest rest' : $α) (hm : k * c = m) (e : k * rest = rest') :
    k * (c * x + rest) = m * x + rest' := by grind

theorem $(Lean.mkIdent `smul_cons_zero) (k x c rest rest' : $α) (hm : k * c = 0) (e : k * rest = rest') :
    k * (c * x + rest) = rest' := by grind

theorem $(Lean.mkIdent `add_congr_eq) (a A b B : $α) (ha : a = A) (hb : b = B) : a + b = A + B := by grind

theorem $(Lean.mkIdent `mul_congr_eq_r) (k a A : $α) (e : a = A) : k * a = k * A := by grind

theorem $(Lean.mkIdent `mul_congr_eq_l) (a A k : $α) (e : a = A) : a * k = A * k := by grind

/-! ### Ring-normalization (distributivity / reassociation) lemmas.

The product preprocessing (`distributeMul?`) pushes a `*` of two non-scalar factors
through the additive structure of its operands and reassociates left-nested products,
so the linear part becomes visible (`p * (n + 1) ↝ p * n + p`). Each lemma rewrites one
product node to its distributed/reassociated form; the normalizer recurses on the result. -/

theorem $(Lean.mkIdent `add_mul) (a b c : $α) : (a + b) * c = a * c + b * c := by grind

theorem $(Lean.mkIdent `mul_add) (a b c : $α) : a * (b + c) = a * b + a * c := by grind

theorem $(Lean.mkIdent `mul_reassoc) (a b c : $α) : (a * b) * c = a * (b * c) := by grind
)

/-- The semiring block plus the ring (neg/sub) normalizer lemmas. -/
macro "declare_lp_normalizer_ring_lemmas" α:ident : command => `(
declare_lp_normalizer_semiring_lemmas $α

theorem $(Lean.mkIdent `neg_atom_norm) (x : $α) : -x = (-1) * x + 0 := by grind

theorem $(Lean.mkIdent `neg_cons) (x c m rest rest' : $α) (hm : -c = m) (e : -rest = rest') :
    -(c * x + rest) = m * x + rest' := by grind

theorem $(Lean.mkIdent `neg_congr_eq) (a A : $α) (e : a = A) : -a = -A := by grind

theorem $(Lean.mkIdent `sub_to_add_neg) (a b : $α) : a - b = a + (-b) := by grind

/-- Ring distributivity through subtraction / negation (the additive cases the
semiring block omits): the product preprocessing reaches these on the ring carriers. -/
theorem $(Lean.mkIdent `sub_mul) (a b c : $α) : (a - b) * c = a * c - b * c := by grind

theorem $(Lean.mkIdent `mul_sub) (a b c : $α) : a * (b - c) = a * b - a * c := by grind

theorem $(Lean.mkIdent `neg_mul) (a c : $α) : (-a) * c = -(a * c) := by grind

theorem $(Lean.mkIdent `mul_neg) (a c : $α) : a * (-c) = -(a * c) := by grind
)

/-- Declare the full ordered-comm-ring certificate lemma block for the carrier `α`
(`Int` and `Dyadic`): the ring normalizer block, the scaled/unscaled closers (rational
Farkas multipliers are cleared to integers by a positive scale `L`, so the closing
identity is `L * (rhs - lhs) + s = C`; the backward step `0 < L → 0 ≤ L * z → 0 ≤ z`
is the load-bearing sign lemma), the row-closure lemmas, and the weighted-sum sign
lemmas. -/
macro "declare_lp_ordered_ring_lemmas" α:ident : command => `(
declare_lp_normalizer_ring_lemmas $α

theorem $(Lean.mkIdent `mul_nonneg_back) {L z : $α} (hL : 0 < L) (h : 0 ≤ L * z) : 0 ≤ z := by
  apply Classical.byContradiction
  intro hz
  have hz' : z < 0 := by grind
  have : L * z < 0 := Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg hL hz'
  grind

theorem $(Lean.mkIdent `mul_pos_back) {L z : $α} (hL : 0 < L) (h : 0 < L * z) : 0 < z := by
  apply Classical.byContradiction
  intro hz
  have hz' : z ≤ 0 := by grind
  have hL' : (0 : $α) ≤ L := by grind
  have : L * z ≤ 0 := Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos hL' hz'
  grind

theorem $(Lean.mkIdent `scaled_le_close) {L lhs rhs s C : $α}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 ≤ C)
    (hIdent : L * (rhs - lhs) + s = C) : lhs ≤ rhs := by
  have h : 0 ≤ L * (rhs - lhs) := by
    have : L * (rhs - lhs) = C - s := by grind
    rw [this]; grind
  have hz := $(Lean.mkIdent `mul_nonneg_back) hL h
  grind

theorem $(Lean.mkIdent `scaled_lt_close) {L lhs rhs s C : $α}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 < C)
    (hIdent : L * (rhs - lhs) + s = C) : lhs < rhs := by
  have h : 0 < L * (rhs - lhs) := by
    have : L * (rhs - lhs) = C - s := by grind
    rw [this]; grind
  have hz := $(Lean.mkIdent `mul_pos_back) hL h
  grind

theorem $(Lean.mkIdent `scaled_infeasible_close) {s C : $α}
    (hSum : s ≤ 0) (hC : 0 < C) (hIdent : s = C) : False := by grind

/-- Strict-row closers: a strictly negative weighted sum (`s < 0`, from a strict row
carrying a positive multiplier) proves the strict goal / contradiction even at
residual `0 ≤ C`. -/
theorem $(Lean.mkIdent `scaled_lt_close_strict) {L lhs rhs s C : $α}
    (hL : 0 < L) (hSum : s < 0) (hC : 0 ≤ C)
    (hIdent : L * (rhs - lhs) + s = C) : lhs < rhs := by
  have h : 0 < L * (rhs - lhs) := by
    have : L * (rhs - lhs) = C - s := by grind
    rw [this]; grind
  have hz := $(Lean.mkIdent `mul_pos_back) hL h
  grind

theorem $(Lean.mkIdent `scaled_infeasible_close_strict) {s C : $α}
    (hSum : s < 0) (hC : 0 ≤ C) (hIdent : s = C) : False := by grind

/-- Unscaled closers for the common `L = 1` case (integer multipliers): no `L *`
factor, so the normalizer skips a whole `proveSmul` pass over the objective. -/
theorem $(Lean.mkIdent `le_close) {lhs rhs s C : $α}
    (hSum : s ≤ 0) (hC : 0 ≤ C) (hIdent : rhs - lhs + s = C) : lhs ≤ rhs := by grind

theorem $(Lean.mkIdent `lt_close) {lhs rhs s C : $α}
    (hSum : s ≤ 0) (hC : 0 < C) (hIdent : rhs - lhs + s = C) : lhs < rhs := by grind

theorem $(Lean.mkIdent `lt_close_strict) {lhs rhs s C : $α}
    (hSum : s < 0) (hC : 0 ≤ C) (hIdent : rhs - lhs + s = C) : lhs < rhs := by grind

theorem $(Lean.mkIdent `le_antisymm) {a b : $α} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by grind

theorem $(Lean.mkIdent `sub_nonpos_of_le) {a b : $α} (h : a ≤ b) : a - b ≤ 0 := by grind

/-- Strict-hypothesis relaxation: `a < b` used as the weaker `a - b ≤ 0`. -/
theorem $(Lean.mkIdent `sub_nonpos_of_lt) {a b : $α} (h : a < b) : a - b ≤ 0 := by grind

theorem $(Lean.mkIdent `sub_neg_of_lt) {a b : $α} (h : a < b) : a - b < 0 := by grind

theorem $(Lean.mkIdent `sub_nonpos_of_eq) {a b : $α} (h : a = b) : a - b ≤ 0 := by grind

theorem $(Lean.mkIdent `smul_nonpos) {a k : $α} (ha : a ≤ 0) (hk : 0 ≤ k) : k * a ≤ 0 :=
  Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos hk ha

theorem $(Lean.mkIdent `add_nonpos) {a b : $α} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 := by grind

theorem $(Lean.mkIdent `smul_neg) {a k : $α} (ha : a < 0) (hk : 0 < k) : k * a < 0 :=
  Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg hk ha

theorem $(Lean.mkIdent `add_neg_nonpos) {a b : $α} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 := by grind

theorem $(Lean.mkIdent `add_nonpos_neg) {a b : $α} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 := by grind

theorem $(Lean.mkIdent `le_of_lt) {a b : $α} (h : a < b) : a ≤ b := by grind

theorem $(Lean.mkIdent `zero_self_le) : (0 : $α) ≤ 0 := by grind
)
