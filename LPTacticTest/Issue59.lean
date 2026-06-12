/-
  Tests for issue #59: an abstract field accepted by `isCarrierType` but rejected at
  solve with `failed to synthesize Lean.Grind.IsCharP α 0`.

  `isCarrierType` used to accept any `α` carrying `Lean.Grind.Field`, so a goal/hypothesis
  over a non-ordered field (`ℂ`, a `NormedField`, the fraction field of a valuation ring)
  dispatched to the field certificate engine. Assembly then synthesized `IsCharP α 0` — the
  numeral-faithfulness instance the `Field.NormNum.ofRat` lemmas (`add_eq`, `mul_eq`,
  `ofRat_add`, …) carry, false in positive characteristic — and a bare field has no such
  instance, so the raw `failed to synthesize Lean.Grind.IsCharP α 0` leaked out of the
  tactic. The three resurvey sites (`AbsoluteValue/Equivalence`, `Normed/Field/Approximation`,
  `EllipticCurve/Reduction`) all hit this: their real `linarith` obligation is over `ℝ`, but
  carrier gathering picked up the incidental non-ordered field carrier.

  The fix gates the field branch of `isCarrierType` on `IsCharP α 0`. An ordered Grind
  field supplies it for free (core's `OrderedRing → IsCharP` instance), so genuinely ordered
  fields (`ℝ`, any abstract ordered field) still dispatch and close exactly as before. A
  non-ordered field is now declined cleanly: it falls through to the standard "no supported
  carrier" diagnostic rather than leaking the synth failure. `(6 : K) ≠ 0` over a general
  field is anyway not a theorem (`6 = 0` in `ℤ/2ℤ`/`ℤ/3ℤ`), so declining it is correct.

  These exercise the dispatch gate only and need no LP backend.
-/

import LPTactic

namespace LPTacticTest.Issue59

open Std Lean.Grind

universe u

/-! ## An ordered Grind field still dispatches to the field engine.

`IsCharP α 0` is automatic from the order, so the tightened gate is transparent here: the
trivial `x ≤ x` certificate (zero rows, residual `0`) closes without a backend. -/

example {α : Type u}
    [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]
    (x : α) : x ≤ x := by lp

example {α : Type u}
    [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]
    (x y : α) : x + y ≤ y + x := by lp

/-! ## A bare (non-ordered) field is declined cleanly.

Previously this leaked `failed to synthesize Lean.Grind.IsCharP K 0` from certificate
assembly; now `isCarrierType` rejects `K`, the `≠` goal introduces `6 = 0` and falls through
to the inconsistency path, which reports the clean "no supported carrier" diagnostic. -/

/--
error: lp: goal
  False
is not an atomic comparison or `∃`, and no linear hypothesis over a supported carrier was found to derive it from
-/
#guard_msgs in
example {K : Type u} [Field K] : (6 : K) ≠ 0 := by lp

end LPTacticTest.Issue59
