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

/-- Integer strengthening: a strict `a < b` over `ℤ` is the `+1`-slack non-strict
`a + 1 ≤ b`. The parser uses this to relax strict hypothesis rows to non-strict rows
that retain a full unit of slack (the `linarith` preprocessing step), so a chain of `k`
strict facts keeps all `k` units instead of collapsing to one strict ℚ-row. -/
theorem add_one_le_of_lt {a b : Int} (h : a < b) : a + 1 ≤ b := by omega

/-- Integer negated-goal strengthening: over `ℤ` the non-strict `a ≤ b` is the strict
`a < b + 1`. A non-strict `ℤ` goal whose direct ℚ residual lands in `(-1, 0)` (an
integer-rounding gap) is reproved as the equivalent strict goal, then closed back to
`a ≤ b` by this lemma. -/
theorem le_of_lt_add_one {a b : Int} (h : a < b + 1) : a ≤ b := by omega

end LP.Tactic.LP.Internal.IntC
