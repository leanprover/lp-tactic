/-
  Tests for issue #45: a throwing hypothesis parse must not kill the whole call.

  Hypothesis collection (`collectHyps`) parses every local proposition against the
  goal's carrier. Certain shapes lie OUTSIDE the supported fragment and make the
  per-hypothesis parse THROW rather than return `none`:

    * truncating `Nat` subtraction (`a - b`, modelled by `Nat.sub`),
    * `Int`/`Nat` floor division (`a / b`),
    * division by a non-constant.

  Before the fix a single such hypothesis aborted the entire atomic path — even when
  the hypothesis was IRRELEVANT and a surviving hypothesis (or the goal itself) proved
  the goal. The thrown error then misattributed the blame, e.g. reporting `Nat`
  subtraction for a goal that contained none, in violation of the documented contract
  that "hypotheses outside the fragment are silently ignored".

  The fix makes `collectHyps` fail-open: a per-hypothesis parse error drops that
  hypothesis (restoring the parse state so its partial registrations don't leak) and
  collection continues. Throws are reserved for the goal side, which each caller parses
  itself.

  These certificates are all trivial (closed-true goals via the empty-sum shortcut, or
  closed contradictions), so the cases run without a registered LP backend.
-/

import LPTactic

set_option linter.unusedVariables false

namespace LPTacticTest.Issue45

/-! ## The offending hypothesis is dropped; the goal proves on its own. -/

-- The headline shape: a `Nat`-subtraction hypothesis is irrelevant to a goal that
-- holds reflexively. Previously the `a - b` parse threw "subtraction over `Nat` is
-- truncating"; now `h` is dropped and the reflexive goal proves.
example (a b c : Nat) (h : a - b ≤ c) : c ≤ c := by lp
example (a b : Nat) (h : a - b ≤ 5) : (3 : Nat) ≤ 5 := by lp

-- `Int`/`Nat` floor division in a hypothesis is dropped the same way.
example (a b : Nat) (h : a / b ≤ 5) : (3 : Nat) ≤ 5 := by lp
example (x y : Int) (h : x / y ≤ 0) : (0 : Int) ≤ 0 := by lp

-- Several out-of-fragment hypotheses at once, none of them fatal.
example (a b x y : Int) (h₁ : x / y ≤ 3) (h₂ : a / b ≤ 7) : (1 : Int) ≤ 1 := by lp

/-! ## A surviving hypothesis discharges the goal past a dropped one. -/

-- `h` (out of fragment) is dropped; the closed contradiction `h2` certifies `False`.
example (a b : Nat) (h : a - b ≤ 5) (h2 : (2 : Nat) ≤ 1) : False := by lp
example (x y z : Int) (h : x / y ≤ 3) (h2 : (5 : Int) ≤ 2) : False := by lp

/-! ## When nothing in the fragment survives, the error names the real situation. -/

-- The only hypothesis is out of fragment, so once it is dropped no inconsistency
-- remains. The diagnostic reports exactly that — it does NOT re-raise the dropped
-- hypothesis's `Nat`-subtraction parse error.
/-- error: lp: goal
  False
is not an atomic comparison, and the hypotheses over [Nat] are not inconsistent -/
#guard_msgs in
example (a b : Nat) (h : a - b ≤ 5) : False := by lp

/-! ## Throws are reserved for the goal side. -/

-- Fail-open is for HYPOTHESES only. An out-of-fragment shape in the GOAL itself is a
-- genuine blocker and must still throw, naming it precisely — even with a usable
-- (here closed-contradictory) hypothesis in scope that a swallowed error would hide.
/-- error: lp: subtraction over `Nat` is truncating (`Nat.sub`) and is not supported by `lp`; use `cutsat` (or `omega`) for goals involving `Nat` subtraction -/
#guard_msgs in
example (a b : Nat) (h2 : (2 : Nat) ≤ 1) : a - b ≤ 5 := by lp

end LPTacticTest.Issue45
