/-
Int-monomorphic certificate lemmas for the `lp` tactic. Concrete `Int` (no carrier
variable), stated in native `Int` operations (`Int.add`/`Int.mul`/`Int.neg`), not
`zsmul`/`IntModule` `•` — so the produced proof term carries no `intCast` bridge
(`Ring.zsmul_eq_intCast_mul`), which is the whole perf point. `Int` is a computable
ordered commutative ring: leaf coefficient equalities close by `Eq.refl`, and the
whole block is stamped out by `declare_lp_ordered_ring_lemmas` (shared with `Dyadic`).
-/
module
public import Init.Grind.Ordered.Int
meta import LPTactic.LP.CarrierLemmas

@[expose] public section

namespace LP.Tactic.LP.Internal.IntC

declare_lp_ordered_ring_lemmas Int

end LP.Tactic.LP.Internal.IntC
