/-
Forward monotone-cast lemmas for the `lp` tactic's `zify` hypothesis lift.

The Grind ordered-ring library ships the REVERSE direction of the integer cast
(`Lean.Grind.OrderedRing.le_of_intCast_le_intCast` / `lt_of_intCast_lt_intCast`:
`(↑a ≤ ↑b : R) → a ≤ b`), and the forward `ℕ` direction
(`natCast_le_natCast_of_le` / `natCast_lt_natCast_of_lt`), but NOT the forward `ℤ`
direction. `zifyHyp?` (in `LP/Parse.lean`) needs `a ≤ b → (↑a ≤ ↑b : R)` to lift an
`ℤ` comparison hypothesis into a higher ring carrier `R` (ℝ/ℚ) so it constrains the
goal's `↑(z)` columns. These two lemmas supply it.

Both go through the existing Grind sign lemmas (`nonneg_intCast_of_nonneg` /
`pos_intCast_of_pos`) on `b - a` and `Ring.intCast_sub`, so the conclusion's cast is the
Grind `Ring.intCast` (the `IntCast R` core class does NOT synthesize from `[Ring R]`
alone — the Grind `Ring` exposes the cast through the class, so we make `Ring.intCast` a
local instance and let the conclusion elaborate `(a : R)` through it). The lifted column
then lines up defeq with the goal's `↑z` casts.

These are static lemmas, so the proofs may use `omega`/`rw` (the prohibition on tactic
calls applies only to the per-certificate *tactic runtime*, not here).
-/
module
public import Init.Grind.Ordered.Ring

@[expose] public section

namespace LP.Tactic.LP.Internal

open Std
open Lean.Grind

section Cast
variable {R : Type u}
  [Ring R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

attribute [local instance] Ring.intCast

/-- Forward integer-cast monotonicity (the `ℤ` analogue of
`OrderedRing.natCast_le_natCast_of_le`, which Grind omits): a `ℤ` inequality lifts to the
ring carrier `R`. Used by `zifyHyp?` to lift an `ℤ` hypothesis into a higher carrier. -/
theorem intCast_le_of_le {a b : Int} (h : a ≤ b) : (a : R) ≤ (b : R) := by
  have hsub : (0 : Int) ≤ b - a := by omega
  have hcast := OrderedRing.nonneg_intCast_of_nonneg (R := R) _ hsub
  rw [Ring.intCast_sub] at hcast
  exact OrderedAdd.sub_nonneg_iff.mp hcast

/-- Forward strict integer-cast monotonicity (the `ℤ` analogue of
`OrderedRing.natCast_lt_natCast_of_lt`): a strict `ℤ` inequality lifts to `R`. -/
theorem intCast_lt_of_lt {a b : Int} (h : a < b) : (a : R) < (b : R) := by
  have hsub : (0 : Int) < b - a := by omega
  have hcast := OrderedRing.pos_intCast_of_pos (R := R) _ hsub
  rw [Ring.intCast_sub] at hcast
  exact OrderedAdd.sub_pos_iff.mp hcast

set_option linter.unusedSectionVars false in
/-- Integer-cast congruence for the `=` case: a `ℤ` equality lifts to `R`. Stated with the
Grind `Ring.intCast` (rather than core `congrArg Int.cast`) so it resolves for an abstract
Grind ring carrier with no core `IntCast` instance, and so the lifted cast lines up defeq
with the `le`/`lt` paths. Keeps the full ordered bundle (only `Ring` is needed) so `zifyHyp?`
applies all three relations with the same positional argument shape. -/
theorem intCast_eq_of_eq {a b : Int} (h : a = b) : (a : R) = (b : R) := by rw [h]

end Cast

end LP.Tactic.LP.Internal
