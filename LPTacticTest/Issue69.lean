/-
  Tests for issue #69: fold a cast of a numeral in `push_cast` (`↑(2 : ℕ) → 2`).

  `pushCast?` (in `LP/Types.lean`) decomposes `↑(a + b)`, `↑(a * b)`, `↑(a - b)`, `↑(-a)`,
  `↑↑n`, but a cast of a *closed numeral* `↑(2 : ℕ)` used to stay an opaque atom — so
  `↑(2 : ℕ) = 2` did not close (the cast atom ≠ the carrier literal). This adds the missing
  case: a cast of a closed numeral folds to the carrier numeral `↑(n : ℕ/ℤ) → (n : α)`, via
  the `Grind` lemmas `Semiring.natCast_eq_ofNat` / `Ring.intCast_ofNat`. The pushed form is
  read straight off the lemma's RHS (so it carries the lemma's own `OfNat` instance) and the
  `Eq` is `isDefEq`-checked against `↑inner = …`, failing closed to atomization exactly like
  the other `pushCast?` cases — keeping the parser and the certificate normalizer (which both
  call `pushCast?`) in lockstep automatically.

  Because the fold produces a plain carrier numeral `(n : α)` — which both walks already
  recognize as a scalar through the normal `scalarLit?`/`proveLitEq` path — it sidesteps the
  per-carrier literal bridge entirely: nothing new needs to teach `proveLitEq` about a cast
  literal. `pushCast?` is carrier-generic, so the same fold runs on the field carrier (`ℝ`,
  an abstract ordered field), where `(n : α)` lands on the `ofRat` bridge the field engine
  already uses — validated downstream / by the resurvey, as in `Issue58PushCast.lean`, since
  an abstract `Grind` field's `NatCast` is a `local` instance with no writable `↑` ascription
  to form a goal here.

  These are ring IDENTITIES / closed-residual comparisons over `ℤ` (the `.int` engine) and
  `ℚ` (the `.rat` engine): both sides normalize to the same linear form, the objective
  residual is closed, and the goal proves with zero rows — the full parser → normalizer →
  certificate path, kernel-checked, no backend.

  Deferred (the factor / coefficient-collapse case): `↑(2 * #A) → 2 * ↑#A`. After
  `pushCast?` pushes `↑(2 * n)` to `↑2 * ↑n`, the surviving `↑2` is reached as a *product
  factor* via `parseScalar?` (the `HMul` scalar check), NOT via the `pushCast?` hook — so
  folding it would require teaching every carrier's `proveLitEq` to bridge a cast literal
  `↑(2 : ℕ) = ⟦2⟧` (the broader "shape 2" of the issue). No site in the `linarith`→`lp`
  resurvey needs it (every cast there is an opaque cardinality leaf `↑(#A)`, and goals
  already carry their coefficients as carrier numerals `2 * ↑#A`), so it stays deferred:

  ```
  -- needs the per-carrier `proveLitEq` cast bridge; not handled by this localized fold:
  example (n : Int) : ((2 * n : Int) : Rat) = 2 * (n : Rat) := by lp
  ```
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue69

/-! ## The headline case: a cast of a numeral equals the carrier literal (`↑(2 : ℕ) = 2`). -/

example : ((2 : Nat) : Int) = 2 := by lp
example : ((2 : Nat) : Rat) = 2 := by lp
example : ((2 : Int) : Rat) = 2 := by lp

/-! ## Boundary numerals `0` / `1` fold too (distinct `OfNat` instances from `≥ 2`). -/

example : ((0 : Nat) : Int) = 0 := by lp
example : ((1 : Nat) : Int) = 1 := by lp
example : ((0 : Int) : Rat) = 0 := by lp
example : ((1 : Int) : Rat) = 1 := by lp

/-! ## A larger numeral, and the `ℤ`-cast of a numeral into `ℚ`. -/

example : ((42 : Nat) : Int) = 42 := by lp
example : ((7 : Int) : Rat) = 7 := by lp

/-! ## The folded numeral collapses into the additive constant, matching the goal's literal. -/

example (x : Int) : ((2 : Nat) : Int) + x = x + 2 := by lp
example (a b : Int) : ((3 : Nat) : Int) + a + b = a + b + 3 := by lp

/-! ## Folded numerals combine arithmetically (each cast folds, then the constants add). -/

example : ((2 : Nat) : Int) + ((3 : Nat) : Int) = 5 := by lp
example : ((10 : Nat) : Rat) - ((4 : Int) : Rat) = 6 := by lp

/-! ## Closed-residual comparisons: a folded numeral leaves a nonnegative constant residual. -/

example : ((2 : Nat) : Int) ≤ 3 := by lp
example : ((2 : Nat) : Int) ≥ 1 := by lp
example (x : Rat) : ((2 : Nat) : Rat) + x ≤ x + 3 := by lp

/-! ## No regression: an opaque cast leaf (`↑n` for a variable `n`, no numeral to fold) still
atomizes and matches itself; a cast of arithmetic still pushes as before. -/

example (n : Nat) : ((n : Nat) : Int) = (n : Int) := by lp
example (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + b := by lp

end LPTacticTest.Issue69
