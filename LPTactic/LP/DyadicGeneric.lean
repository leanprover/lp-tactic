/-
`Dyadic`-monomorphic certificate lemmas for the unified `lp` engine. `Dyadic` (Lean core,
`Init/Data/Dyadic/`) is a computable ordered commutative ring (NOT a field — dyadics have
no inverses), so like `Int` it gets native kernel-reducible literals + `Eq.refl` leaves.
The whole block is stamped out by `declare_lp_ordered_ring_lemmas` (shared with `Int`).
-/
module
public import Init.Data.Dyadic.Instances
public import Init.Grind.Ordered.Ring
meta import LPTactic.LP.CarrierLemmas

@[expose] public section

namespace LP.Tactic.LP.Internal.DyadicC

declare_lp_ordered_ring_lemmas Dyadic

end LP.Tactic.LP.Internal.DyadicC
