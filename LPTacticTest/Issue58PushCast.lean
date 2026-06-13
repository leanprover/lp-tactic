/-
  Tests for issue #58 stage 3: `push_cast` normalization of casts.

  A cast `↑(a + b)` / `↑(a * b)` over `ℕ`/`ℤ` was one opaque atom for `lp`, so its linear
  structure — and any match against the goal's (or a lifted hypothesis') separately-cast
  columns — was invisible. `linarith` runs `push_cast` first; this is `lp`'s. It pairs with
  the stage-2 `zify` lift: a `ℕ` hypothesis `#B ≤ 2 * #A` lifts to `↑#B ≤ ↑(2 * #A)`, and
  `push_cast` then rewrites `↑(2 * #A) → 2 * ↑#A` so it lands on the goal's `2 * ↑#A` column.

  `pushCast?` (in `LP/Types.lean`) pushes a cast one step inward using the `Grind` ring cast
  lemmas — `↑(a + b) → ↑a + ↑b`, `↑(a * b) → ↑a * ↑b`, and for `ℤ` casts `↑(a - b) → ↑a - ↑b`,
  `↑(-a) → -↑a`, `↑↑n → ↑n` — and is shared by the parser (`parseInto`) and the certificate
  normalizer (`normalizeR`) in lockstep, like the stage-1 `distributeMul?`. The proof comes
  from the cast lemma and is `isDefEq`-checked against `↑inner = pushed`, so a cast whose
  instance does not line up with the lemma's fails closed to atomization (no unsoundness, no
  divergence between the two walks). A pushed product feeds the stage-1 distribution; a cast
  of a numeral folds through the existing scalar path (`↑(2 : ℕ)` is the scalar `2`).

  These are ring IDENTITIES over `ℤ` (the `.int` engine) and `ℚ` (the `.rat` engine): both
  sides `push_cast`-normalize to the same linear form, so the objective residual is closed
  and the goal proves with zero rows — the full parser → normalizer → certificate path that
  `pushCast?` feeds, kernel-checked, no backend.

  Two refinements are left for a follow-up: folding a cast of a numeral (`↑(2 : ℕ) → 2`,
  which needs the per-carrier `proveLitEq` to bridge a cast literal, so `↑(2 * #A)` collapses
  to `2 * ↑#A`), and `ℤ`→`R` hypothesis lifting (the `IntCast` Grind/core diamond and a
  missing forward monotone lemma). The abstract-field cast path reuses this same
  carrier-generic `pushCast?` and the cast-lemma resolution validated in `Issue58Casts.lean`.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue58PushCast

/-! ## `ℕ`-cast push: `↑(a + b)`, `↑(a * b)` (the `.int` engine, casting into ℤ). -/

example (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by lp
example (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by lp
example (a b c : Nat) : ((a + b + c : Nat) : Int) = (a : Int) + b + c := by lp

/-! ## `ℤ`-cast push, including subtraction / negation (the `.rat` engine, casting into ℚ). -/

example (a b : Int) : ((a + b : Int) : Rat) = (a : Rat) + (b : Rat) := by lp
example (a b : Int) : ((a - b : Int) : Rat) = (a : Rat) - (b : Rat) := by lp
example (a b : Int) : ((a * b : Int) : Rat) = (a : Rat) * (b : Rat) := by lp
example (a : Int) : ((-a : Int) : Rat) = -(a : Rat) := by lp

/-! ## Cast composition `↑↑n = ↑n` (an `Int` cast of a `ℕ` cast collapses). -/

example (n : Nat) : (((n : Int) : Rat)) = (n : Rat) := by lp

/-! ## Closed-residual inequalities: a pushed cast leaves a nonnegative constant residual. -/

example (a b : Int) : ((a + b : Int) : Rat) ≤ (a : Rat) + b + 1 := by lp
example (a b c : Int) : ((a + b - c : Int) : Rat) ≥ (a : Rat) + b - c := by lp

/-! ## No regression: an opaque cast leaf (`↑(f n)`, no inner arithmetic to push) still
atomizes and matches itself. -/

example (f : Nat → Nat) (n : Nat) : ((f n : Nat) : Int) = (f n : Int) := by lp
example (f : Nat → Nat) (n : Nat) : ((f n : Nat) : Int) ≤ (f n : Int) + 1 := by lp

end LPTacticTest.Issue58PushCast
