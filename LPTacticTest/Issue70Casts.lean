/-
  Tests for issue #70: `zify` an `ℤ` hypothesis into a higher ring carrier (ℤ→R cast lift).

  Stage 2 (#66, `LPTacticTest/Issue58Casts.lean`) lifted a `ℕ` comparison into a ring-carrier
  goal. This is the orthogonal `ℤ` direction: an `ℤ` hypothesis `a ≤ b` / `a < b` / `a = b`
  constraining `↑(z) : ℝ`/`ℚ` columns in a goal over a strictly-higher ring carrier `R`.

  Two pieces were missing for `ℤ` that `ℕ` already had:

  1. Grind ships only the REVERSE cast lemma (`OrderedRing.le_of_intCast_le_intCast`,
     `lt_of_intCast_lt_intCast`); the FORWARD `a ≤ b → (↑a ≤ ↑b : R)` is supplied by
     `intCast_le_of_le` / `intCast_lt_of_lt` (`LP/CastLift.lean`), with `intCast_eq_of_eq`
     for `=`.
  2. `IntCast R` does NOT synthesize from `[Grind.Ring R]` alone — the Grind `Ring` exposes
     the cast through the class, not a core `IntCast` instance. The helpers make
     `Ring.intCast` a local instance, so their conclusion's `↑(·)` is the Grind cast; on a
     concrete carrier (ℚ) that cast is DEFEQ to the core `Int.cast`, so the lifted column
     merges (`findDefEqAtom`) onto the same LP column as the goal's `↑z`.

  `zifyHyp?` (in `LP/Parse.lean`) dispatches on the source carrier: `ℕ` via the core
  `natCast_*` lemmas (Stage 2), `ℤ` via these `intCast_*` helpers. The lift is fail-open: it
  sits in `collectHyps`' per-hypothesis `try`/`catch`, and `zifyHyp?` catches a failed
  cast-lemma synthesis, so a carrier without the monotone cast (e.g. an `ℤ` hypothesis under
  a `ℕ` goal — no `Ring` negation) simply drops the hypothesis. lp stays sound by
  construction either way — a mis-lift would make the certificate identity fail, never prove
  a false goal.

  The behavioral payoff is multi-row (a goal column constrained by a lifted row), so — like
  every multi-row case in this dependency-free suite — it needs a registered LP backend and
  is verified downstream / by the resurvey re-measurement; the repros are in comments. What
  IS validated here, backend-free: that the forward helpers type-check and resolve for lp's
  ring carriers, that `zifyHyp?` constructs a well-typed lifted proof over ℤ for each
  relation, and that the lifted cast is DEFEQ to the goal-side core `Int.cast` (the
  column-merge precondition) — all exercised via `run_meta` and pinned by `by exact`
  signature checks.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean Lean.Meta Lean.Grind Std
open LP.Tactic.LP.Internal

namespace LPTacticTest.Issue70Casts

/-! ## The forward integer-cast lift lemmas resolve for lp's ring carriers (the exact lemmas
and instances `zifyHyp?` applies for an `ℤ` source). A concrete carrier (ℚ) pins the
defeq line-up with the core `Int.cast`; the lemma's conclusion type-checking against the
core-cast ascription IS that defeq. -/

example (a b : Int) (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := intCast_le_of_le h
example (a b : Int) (h : a < b) : (a : Rat) < (b : Rat) := intCast_lt_of_lt h
example (a b : Int) (h : a = b) : (a : Rat) = (b : Rat) := intCast_eq_of_eq h

section Field
variable {α : Type} [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α]
  [OrderedRing α] [IsCharP α 0]

-- No cast type ascription: an abstract `Grind` field exposes the cast through the class, not
-- a core `IntCast` instance, so we let the lemma's conclusion define the type.
example (a b : Int) (h : a ≤ b) := intCast_le_of_le (R := α) h
example (a b : Int) (h : a < b) := intCast_lt_of_lt (R := α) h
example (a b : Int) (h : a = b) := intCast_eq_of_eq (R := α) h

end Field

/-! ## `zifyHyp?` actually constructs a well-typed lifted proof over an ℤ hypothesis into a
higher carrier (ℚ) for each relation, AND the lifted cast is defeq to the goal-side core
`Int.cast` (so it lands on the goal's `↑z` columns). A failure here is a compile error. -/

run_meta do
  let int := mkConst ``Int
  let rat := mkConst ``Rat
  withLocalDeclD `a int fun a => do
  withLocalDeclD `b int fun b => do
    let checks : List (Name × (Expr → Expr → MetaM Expr)) :=
      [ (`le, fun a b => mkAppM ``LE.le #[a, b]),
        (`lt, fun a b => mkAppM ``LT.lt #[a, b]),
        (`eq, fun a b => mkAppM ``Eq #[a, b]) ]
    for (tag, mkTy) in checks do
      let ty ← mkTy a b
      withLocalDeclD `h ty fun h => do
        let (res, _) ← (zifyHyp? h ty).run { carrier := rat, allowAtoms := true }
        match res with
        | none => throwError "zify ℤ ({tag}) into ℚ: failed to lift an ℤ hypothesis"
        | some lifted =>
            -- The lifted proof must type-check, and its statement must be the cast
            -- comparison over the carrier.
            let lty ← instantiateMVars (← inferType lifted)
            let head := lty.getAppFn.constName?.getD `unknown
            unless head == ``LE.le || head == ``LT.lt || head == ``Eq do
              throwError "zify ℤ ({tag}) into ℚ: lifted statement is not a comparison: {lty}"
            -- Column-merge precondition: BOTH lifted casts (`↑a`, `↑b`) must be defeq to the
            -- goal-side core `Int.cast · : ℚ` (otherwise `findDefEqAtom` would split the
            -- columns). The lifted comparison's last two args are its operands.
            let args := lty.getAppArgs
            for (operand, side) in [(a, "lhs"), (b, "rhs")] do
              let coreCast ← mkAppOptM ``Int.cast #[some rat, none, some operand]
              let liftedCast := args[args.size - (if side == "lhs" then 2 else 1)]!
              unless ← isDefEq liftedCast coreCast do
                throwError "zify ℤ ({tag}) into ℚ: lifted {side} cast {liftedCast} is not defeq \
                  to the goal-side core Int.cast {coreCast} — columns would not merge"

/-! ## `zifyHyp?` does NOT lift an ℤ hypothesis into a `ℕ` goal (ℕ lacks the `Ring`
negation, so a possibly-negative ℤ must never sneak into ℕ): the `Ring ℕ` synthesis fails
and the hypothesis drops (fail-open). -/

run_meta do
  let int := mkConst ``Int
  let nat := mkConst ``Nat
  withLocalDeclD `a int fun a => do
  withLocalDeclD `b int fun b => do
    let ty ← mkAppM ``LE.le #[a, b]
    withLocalDeclD `h ty fun h => do
      let (res, _) ← (zifyHyp? h ty).run { carrier := nat, allowAtoms := true }
      unless res.isNone do
        throwError "zify ℤ into ℕ: must drop (ℕ has no Ring negation), but lifted: {res}"

/-! ## No regression: an ℤ hypothesis present under a higher ring-carrier goal does not break
a goal that closes on its own (the lift adds a row; the goal still proves with zero rows). -/

example (a b : Int) (_h : a ≤ b) : (1 : Rat) ≤ 2 := by lp
example (a b : Int) (_h : a < b) : (0 : Rat) ≤ 5 := by lp
example (a b : Int) (_h : a = b) (x : Rat) : x ≤ x := by lp

/-! ## Behavioral multi-row repros from the issue (need a backend; verified downstream).

```
-- an ℤ bound constrains a cast column in a ℚ/ℝ goal:
example (t : Int) (h : 1 ≤ t) : (1 : Rat) ≤ 2 * ↑t := by lp
-- an ℤ cardinality-style inequality lifts to ℚ:
example (A B : Int) (h : B ≤ 2 * A) : (↑B : Rat) ≤ 2 * ↑A := by lp
```
-/

end LPTacticTest.Issue70Casts
