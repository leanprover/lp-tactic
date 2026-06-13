/-
  Tests for issue #65: strict comparison goals with an unassigned metavariable, and the
  ℕ→ℤ cast bridging the resurvey sites need.

  Two pieces land here, both mirroring `linarith`:

  1. **Strict (and `≤`) metavariable goals.** #63 (`solveEqMVar?`) closed an *equality* goal
     `concrete = ?m` by searching the carrier-typed locals for a `v` with `concrete = v`
     provable and assigning `?m := v`. This generalises that (`solveRelMVar?`) to the oriented
     comparisons `linarith` also assigns a goal metavariable for: `m < ?m` (find a
     hypothesis-derived upper bound `v` with `m < v`, assign `?m := v`) and the `≤` analogue.
     The chosen `v` is always an existing context term, never the verbatim `concrete` side, so
     the assigned value flows on into the surrounding elaboration the way `linarith`'s does.

  2. **ℕ→ℤ cast bridging.** `lp` collects hypotheses per carrier, so a `Nat` goal whose bound
     only follows through `ℤ`-cast hypotheses (`n < D`, `n + ↑s = ↑m`, `D + ↑s = ↑d`, giving
     `↑m < ↑d` hence `m < d`) was unprovable: over `ℕ` it never saw the `ℤ` facts relating
     `m` and `d`. When the native `Nat` solve fails, `lp` now recasts the goal to
     `(↑lhs op ↑rhs : ℤ)` (and asserts each `Nat` hypothesis's `ℤ` cast), solves over `ℤ`
     where the cast facts are visible (with `0 ≤ ↑n` from `castNonnegRows`), and maps the
     proof back with `Int.ofNat_lt`/`Int.ofNat_le`/`Int.natCast_inj`. This is `linarith`'s
     `natToInt` preprocessing, useful well beyond the metavariable feature.

  The resurvey sites this unblocks are `RingTheory/LaurentSeries.lean:536` (`m < ?m` with
  `n + ↑s = ↑m`, `D + ↑s = ↑d`) and `:545` (the `-↑s` analogue). Both close the strict
  metavariable goal with `?m := d` proved through the `ℤ` cast bridge — a genuine Farkas
  combination, so they need a registered LP backend. They are exercised end to end against
  the SoPlex backend in the umbrella `lp` package; the cases below need no backend (the
  reflexive `≤`/`=` certificates close on the empty-sum shortcut), so they exercise the
  generalised metavariable dispatch in this dependency-free suite.
-/

import LPTactic

set_option linter.unusedVariables false

namespace LPTacticTest.Issue65

/-- No-op consumers whose last argument fixes the goal `lp` must close by assigning the
metavariable: `concrete op ?x` (metavariable on the right) or `?x op concrete` (on the left),
with `?x` an unassigned metavariable (the `_`). -/
private def probeLeR {α : Type} [LE α] (_concrete _x : α) (_h : _concrete ≤ _x) : Unit := ()
private def probeLeL {α : Type} [LE α] (_concrete _x : α) (_h : _x ≤ _concrete) : Unit := ()
private def probeEq  {α : Type} (_concrete _x : α) (_h : _concrete = _x) : Unit := ()

/-! ## `≤` metavariable goals: `lp` assigns the metavariable to an existing term making the
comparison hold — here the reflexive witness `?m := a` for `a ≤ ?m`. This is the new `≤` arm
of the generalised dispatch (was: `unsupported expression ?m`). Backend-free: the `a ≤ a`
certificate is the empty-sum shortcut. -/

example (a : Nat) : True := by have := probeLeR a _ (by lp); trivial
example (a : Int) : True := by have := probeLeR a _ (by lp); trivial
example (a : Rat) : True := by have := probeLeR a _ (by lp); trivial

/-! ## The metavariable on the left (`?m ≤ concrete`) is handled symmetrically (`?m := a`). -/

example (a : Nat) : True := by have := probeLeL a _ (by lp); trivial
example (a : Int) : True := by have := probeLeL a _ (by lp); trivial

/-! ## The `=` metavariable dispatch from #63 is preserved through the generalisation. -/

example (a : Nat) : True := by have := probeEq a _ (by lp); trivial
example (a : Int) : True := by have := probeEq (a + 1 - 1) _ (by lp); trivial

/-! ## A fully concrete comparison is unaffected (not misrouted by the metavariable dispatch).
The strict `<` arm shares the dispatch; with both sides metavariable-free it falls straight
through to the ordinary atomic discharger. -/

example (a : Int) : a < a + 1 := by lp
example (a : Nat) : a < a + 1 := by lp

end LPTacticTest.Issue65
