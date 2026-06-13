/-
  Tests for issue #58 stage 2: `zify`-style cast normalization of hypotheses.

  The cast bucket of the Mathlib `linarith`→`lp` resurvey is dominated by goals over a ring
  carrier `R` (ℝ/ℚ/ℤ) whose `↑(·)` columns (cardinalities `↑(#A)`, counts, casts of `ℕ`
  terms) are constrained by `ℕ` hypotheses — which `lp` previously dropped, because a
  hypothesis over a carrier different from the goal's is skipped. `linarith` lifts such
  facts with `zify`/`push_cast`; this is `lp`'s.

  `zifyHyp?` (in `LP/Parse.lean`) lifts a `ℕ` comparison `a ≤ b` / `a < b` / `a = b` to
  the goal carrier `R` via the monotone cast (`Lean.Grind.OrderedRing.natCast_le_natCast_of_le`
  / `natCast_lt_natCast_of_lt`, and cast congruence for `=`), producing a proof of
  `↑a (rel) ↑b : R` that `collectHypProof` then parses on the normal path — so the lifted
  `↑a`, `↑b` land on the SAME LP columns as the goal's casts. The lift is fail-open: it sits
  in `collectHyps`' per-hypothesis `try`/`catch`, and `zifyHyp?` itself catches a failed
  cast-lemma synthesis, so a carrier without the monotone cast simply drops the hypothesis
  rather than failing the call. lp stays sound by construction either way — a mis-lift would
  make the certificate identity fail, never prove a false goal.

  The behavioral payoff is multi-row (a goal column constrained by a lifted row), so — like
  every multi-row case in this dependency-free suite — it needs a registered LP backend and
  is verified downstream / by the resurvey re-measurement; the repros are in comments. What
  IS validated here, backend-free: that `zifyHyp?` actually constructs a well-typed lifted
  proof (the risky part — cast-lemma name / instance resolution), exercised directly via
  `run_meta` and pinned by `by exact` signature checks over ℤ and an abstract `Grind` field.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean Lean.Meta Lean.Grind Std
open LP.Tactic.LP.Internal

namespace LPTacticTest.Issue58Casts

/-! ## The monotone-cast lift lemmas resolve for lp's ring carriers (the exact lemmas and
instances `zifyHyp?` applies). -/

example (a b : Nat) (h : a ≤ b) : (a : Int) ≤ (b : Int) :=
  OrderedRing.natCast_le_natCast_of_le a b h
example (a b : Nat) (h : a < b) : (a : Int) < (b : Int) :=
  OrderedRing.natCast_lt_natCast_of_lt a b h
example (a b : Nat) (h : a = b) : (a : Int) = (b : Int) := congrArg _ h

section Field
variable {α : Type} [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α]
  [OrderedRing α] [IsCharP α 0]

-- No cast type ascription: abstract `Grind` fields expose the cast through the class, not a
-- core `NatCast` instance, so we let the lemma's conclusion define the type.
example (a b : Nat) (h : a ≤ b) := OrderedRing.natCast_le_natCast_of_le (R := α) a b h
example (a b : Nat) (h : a < b) := OrderedRing.natCast_lt_natCast_of_lt (R := α) a b h

end Field

/-! ## `zifyHyp?` actually constructs a well-typed lifted proof over ℤ for each relation
(direct, backend-free validation of the lift — the part most prone to a wrong lemma name or
unresolved instance). A failure here is a compile error. -/

run_meta do
  let nat := mkConst ``Nat
  withLocalDeclD `a nat fun a => do
  withLocalDeclD `b nat fun b => do
    let checks : List (Name × (Expr → Expr → MetaM Expr)) :=
      [ (`le, fun a b => mkAppM ``LE.le #[a, b]),
        (`lt, fun a b => mkAppM ``LT.lt #[a, b]),
        (`eq, fun a b => mkAppM ``Eq #[a, b]) ]
    -- Validate the lift for both an integer carrier (ℤ) and a field carrier (ℚ), so
    -- `mkAppOptM`'s instance resolution is exercised on both kinds.
    for carrier in [mkConst ``Int, mkConst ``Rat] do
      for (tag, mkTy) in checks do
        let ty ← mkTy a b
        withLocalDeclD `h ty fun h => do
          let (res, _) ← (zifyHyp? h ty).run { carrier, allowAtoms := true }
          match res with
          | none => throwError "zify ({tag}) over {carrier}: failed to lift a ℕ hypothesis"
          | some lifted =>
              -- The lifted proof must type-check, and its statement must be the cast
              -- comparison over the carrier (so it lands on the goal's `↑(·)` columns).
              let lty ← instantiateMVars (← inferType lifted)
              let head := lty.getAppFn.constName?.getD `unknown
              unless head == ``LE.le || head == ``LT.lt || head == ``Eq do
                throwError "zify ({tag}) over {carrier}: lifted statement is not a comparison: {lty}"

/-! ## No regression: a ℕ hypothesis present under a ring-carrier goal does not break a goal
that closes on its own (the lift adds a row; the goal still proves with zero rows). -/

example (a b : Nat) (_h : a ≤ b) : (1 : Int) ≤ 2 := by lp
example (a b : Nat) (_h : a < b) : (0 : Int) ≤ 5 := by lp
example (a b : Nat) (_h : a = b) (x : Int) : x ≤ x := by lp

/-! ## Behavioral multi-row repros from the issue (need a backend; verified downstream).

```
-- a ℕ bound constrains a cast column in a ℝ/ℤ goal:
example (t : Nat) (h : 1 ≤ t) : (1 : Int) ≤ 2 * ↑t := by lp
-- Mathlib cardinality shape (VerySmallDoubling): a ℕ cardinality inequality lifts to ℝ:
example (A B : Nat) (h : B ≤ 2 * A) : (↑B : Int) ≤ 2 * ↑A := by lp
```
-/

end LPTacticTest.Issue58Casts
