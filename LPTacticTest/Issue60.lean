/-
  Tests for issue #60: equality goals one side of which is an unassigned metavariable.

  `linarith` closes a goal like `concrete = ?m` by *assigning* the metavariable to the value
  the hypotheses force `concrete` to equal — an existing context term — rather than by proving
  an entailment. `lp` instead atomized `?m` as an opaque carrier term and threw
  `unsupported expression ?m`. On the Mathlib `linarith`→`lp` resurvey this is the
  `MappingCone.lean:554` (`m + -1 + n' = ?m`) and `DegreewiseSplit.lean:136`
  (`p + 1 + -1 = ?m`) failures.

  The fix (`solveEqMVar?`) mirrors `linarith`: with a bare metavariable on one side it searches
  the carrier-typed local variables for a `v` with `concrete = v` provable, proves that with the
  ordinary `solveAtomic` machinery, and assigns `?m := v`. Crucially the assigned value is the
  existing atom (`?m := p`), NOT the verbatim `concrete` side: that value flows on into the
  surrounding elaboration (e.g. it fixes the degree of a cochain a later `simp` lemma must
  match), so a verbatim `?m := concrete` would type-check the equality yet derail the proof. The
  value-correctness is exercised against the real Mathlib sites; the cases below need no LP
  backend (reflexive and ring-cancelling certificates), so they exercise the metavariable
  dispatch and the atom search in this dependency-free suite.

  Out of scope (still throws): the strict witness case `m < ?m` (`linarith` picks a
  hypothesis-derived upper bound), which over the resurvey (`LaurentSeries.lean:536/545`) also
  needs ℕ↔ℤ cast bridging `lp` does not yet do.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

namespace LPTacticTest.Issue60

/-- A no-op consumer whose last argument has the exact shape `lp` must close by assigning the
metavariable: `concrete = ?x` with `?x` an unassigned metavariable (the `_`). -/
private def probe {α : Type} (_concrete _x : α) (_h : _concrete = _x) : Unit := ()

/-! ## `concrete = ?m`: `lp` assigns the metavariable to the matching atom (was: `unsupported
expression ?m`). The reflexive `a = ?m` closes with `?m := a` over every computable carrier. -/

example (a : Int) : True := by have := probe a _ (by lp); trivial
example (a : Rat) : True := by have := probe a _ (by lp); trivial
example (a : Nat) : True := by have := probe a _ (by lp); trivial

/-! ## The metavariable on the left (`?m = concrete`) is handled symmetrically. -/

example (a : Int) : True := by have := probe _ a (by lp); trivial

/-! ## `a + 1 - 1 = ?m` (the `DegreewiseSplit` shape): `lp` must assign the atom `a`, not the
verbatim `a + 1 - 1`. The certificate is the ring cancellation, so no LP backend is needed. -/

example (a : Int) : True := by have := probe (a + 1 - 1) _ (by lp); trivial
example (a : Rat) : True := by have := probe (a + 1 - 1) _ (by lp); trivial

/-! ## A fully concrete equality is unaffected (not misrouted by the metavariable dispatch). -/

example (a : Int) : a = a := by lp
example (a : Int) : a + 1 - 1 = a := by lp

end LPTacticTest.Issue60
