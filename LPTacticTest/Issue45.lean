/-
  Tests for issue #45: a throwing hypothesis parse must not kill the whole call.

  Hypothesis collection (`collectHyps`) parses every local proposition against the goal's
  carrier. Some shapes make the per-hypothesis parse THROW rather than return `none`; the
  fix makes `collectHyps` fail-open (drop that hypothesis, restore the parse state so its
  partial registrations don't leak, and continue). Throws are reserved for the goal side,
  which each caller parses itself.

  Issue #47 narrowed which shapes throw: a truncating `Nat` subtraction (`a - b`) and an
  `Int`/`Nat` floor division (`a / b`) are now ATOMIZED (kept as opaque LP variables) on
  the atomic path rather than rejected. So those hypotheses are no longer dropped — they
  survive harmlessly as spectator atoms when the goal does not depend on them. The
  fail-open path still fires for shapes that remain genuine parse errors, e.g. division by
  a zero literal (`x / 0`), exercised below.

  These certificates are all trivial (closed-true goals via the empty-sum shortcut, or
  closed contradictions — including past an atomized spectator atom), so the cases run
  without a registered LP backend.
-/

import LPTactic

set_option linter.unusedVariables false

namespace LPTacticTest.Issue45

/-! ## A truncating hypothesis is atomized (#47), not fatal; the goal proves on its own. -/

-- The headline shape: a `Nat`-subtraction hypothesis is irrelevant to a goal that holds
-- reflexively. Previously the `a - b` parse threw "subtraction over `Nat` is truncating";
-- now `h` is atomized to a spectator variable and the reflexive goal still proves.
example (a b c : Nat) (h : a - b ≤ c) : c ≤ c := by lp
example (a b : Nat) (h : a - b ≤ 5) : (3 : Nat) ≤ 5 := by lp

-- `Int`/`Nat` floor division in a hypothesis is atomized the same way.
example (a b : Nat) (h : a / b ≤ 5) : (3 : Nat) ≤ 5 := by lp
example (x y : Int) (h : x / y ≤ 0) : (0 : Int) ≤ 0 := by lp

-- Several out-of-fragment hypotheses at once, none of them fatal.
example (a b x y : Int) (h₁ : x / y ≤ 3) (h₂ : a / b ≤ 7) : (1 : Int) ≤ 1 := by lp

/-! ## A genuinely-throwing hypothesis (`x / 0`) is dropped fail-open. -/

-- Division by a zero literal is NOT atomized (it is a real parse error); `collectHyps`
-- drops it and the reflexive goal proves on its own.
example (x : Rat) (h : x / (0 : Rat) ≤ 5) : (3 : Rat) ≤ 5 := by lp

/-! ## A closed-contradiction hypothesis discharges the goal past a spectator atom. -/

-- `h` (out of fragment) is atomized to a spectator variable; the closed contradiction `h2`
-- still certifies `False` — the closed-contradictory-row probe ignores the spectator
-- column, so this stays backend-free (it does not regress to needing an LP solve).
example (a b : Nat) (h : a - b ≤ 5) (h2 : (2 : Nat) ≤ 1) : False := by lp
example (x y z : Int) (h : x / y ≤ 3) (h2 : (5 : Int) ≤ 2) : False := by lp

/-! ## When nothing certifies a contradiction, the error names the real situation. -/

-- The only hypothesis is the atomized `a - b ≤ 5` (no contradiction), so no inconsistency
-- remains. The diagnostic reports exactly that — it does NOT re-raise a parse error.
/-- error: lp: goal
  False
is not an atomic comparison, and the hypotheses over [Nat] are not inconsistent -/
#guard_msgs in
example (a b : Nat) (h : a - b ≤ 5) : False := by lp

/-! ## Throws are reserved for the goal side. -/

-- Fail-open is for HYPOTHESES only. A genuine parse error in the GOAL itself is a real
-- blocker and must still throw, naming it precisely — even with a usable (here
-- closed-contradictory) hypothesis in scope that a swallowed error would hide. (Under #47 a
-- truncating goal term atomizes rather than throwing, so the blocker here is `x / 0`, which
-- is not atomized.)
/-- error: lp: division by the zero constant -/
#guard_msgs in
example (x : Rat) (h2 : (2 : Rat) ≤ 1) : x / (0 : Rat) ≤ 5 := by lp

end LPTacticTest.Issue45
