/-
  Tests for issue #46: preprocess negated comparisons (linarith's `removeNegations`).

  `lp`'s hypothesis scan only recognized positive comparisons, so a negated one
  (`¬ (a ≤ b)`, written as `Not`, an `→ False` arrow, or `a ≠ b`) was invisible. The
  fix recognizes `¬ (s ⋈ t)` in `collectHyps` (contributing the flipped row, wrapped
  with the core `Lean.Grind.Order.not_le`/`not_lt` conversions) and in the `False`-goal
  carrier scan (`hypCarriers`/`hypCarrier?`), with the flips
    `¬ (a ≤ b)` ⟶ `b < a`  (strict),    `¬ (a < b)` ⟶ `b ≤ a`,
  and `¬ (a ≥ b)`/`¬ (a > b)` flipping the same way. A bare `a ≠ b` is a disequality
  with no single linear row, so it registers its carrier but contributes no row.

  The multi-variable repro (`¬ a ≤ b`, `a ≤ b ⊢ False`, two variables) needs a registered
  LP backend, so it lives in a consumer suite. The cases here are closed contradictions
  (a negated hypothesis that is itself false) and carrier-detection diagnostics, both of
  which fire on the zero-variable / closed-row branch without a backend.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue46

/-! ## `¬ ≤` ⟶ strict `>`: a negated `≤` whose negation is itself false closes `False`. -/

example (h : ¬ ((0 : Rat) ≤ 1)) : False := by lp       -- ⟶ `1 < 0`
example (h : ¬ ((0 : Int) ≤ 1)) : False := by lp
example (h : ¬ ((0 : Nat) ≤ 1)) : False := by lp
-- The `≥` form flips the same way (`¬ (1 ≥ 0)` is `¬ (0 ≤ 1)` ⟶ `1 < 0`).
example (h : ¬ ((1 : Rat) ≥ 0)) : False := by lp

/-! ## `¬ <` ⟶ `≥`: a negated `<` whose negation is itself false closes `False`. -/

example (h : ¬ ((0 : Rat) < 1)) : False := by lp       -- ⟶ `1 ≤ 0`
example (h : ¬ ((0 : Int) < 1)) : False := by lp
example (h : ¬ ((1 : Rat) > 0)) : False := by lp       -- `1 > 0` is `0 < 1` ⟶ `1 ≤ 0`

/-! ## The `→ False` arrow form is recognized exactly like `Not`. -/

example (h : (0 : Rat) ≤ 1 → False) : False := by lp
example (p : Prop) (h : (0 : Rat) < 1 → False) : p := by lp

/-! ## Carrier detection sees a negated comparison for a `False` goal.

A context whose only arithmetic hypothesis is a negated comparison must still be scanned
over the right carrier. When the negated hypothesis is consistent the diagnostic reports
the carrier it found (proving detection fired) rather than "no supported carrier". -/

/-- error: lp: goal
  False
is not an atomic comparison, and the hypotheses over [Rat] are not inconsistent -/
#guard_msgs in
example (a b : Rat) (h : ¬ a ≤ b) : False := by lp

-- A bare disequality registers its carrier but contributes no linear row (as `≠` always has).
/-- error: lp: goal
  False
is not an atomic comparison, and the hypotheses over [Rat] are not inconsistent -/
#guard_msgs in
example (a b : Rat) (h : a ≠ b) : False := by lp

/-! ## Abstract ordered Grind field: the `not_le`/`not_lt` conversions resolve their
`IsLinearPreorder`/`LawfulOrderLT` instances over a fully abstract carrier too. -/

section AbstractField
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K]
  [OrderedRing K] [IsCharP K 0]

example (h : ¬ ((0 : K) ≤ 1)) : False := by lp
example (h : ¬ ((0 : K) < 1)) : False := by lp

end AbstractField

end LPTacticTest.Issue46
