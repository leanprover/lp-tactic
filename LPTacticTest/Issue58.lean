/-
  Tests for issue #58: a ring-normalization preprocessing layer for products / powers.

  `lp` atomized a product of two non-scalar factors opaquely, so the linear structure was
  invisible: `p * (n + 1)` became one atom instead of `p*n + p`. `linarith` runs a ring
  pass first; this is `lp`'s, and it was the dominant remaining bucket of the Mathlib
  `linarith`→`lp` resurvey (the 110 `unbounded` failures).

  The pass (`distributeMul?` in `LP/Types.lean`, wired into the parser `parseInto` and the
  certificate normalizer `normalizeR` in lockstep) pushes a `*` through the additive
  structure of either operand — `(a ± b) * c`, `a * (b ± c)`, `(-a) * c`, `a * (-c)` — and
  reassociates a left-nested product `(a * b) * c ↝ a * (b * c)` so a scalar buried at the
  head surfaces for the scalar-`*` path. What is left is a genuine product of atoms (e.g.
  `p*n`), atomized opaquely as before and canonicalized (`mulCanonKey?`) so commuted forms
  (`n*p`) share a column. The genuinely-nonlinear residue (a product of two non-constant
  atoms) stays one opaque atom — out of scope for a linear tactic — but every distributable
  case now exposes its linear part.

  Both the parser (which builds the LP) and the normalizer (which proves the certificate
  identity) distribute via the same deterministic `distributeMul?`, so their atom columns
  agree. The new monomorphic distributivity lemmas live in the `declare_lp_normalizer_*`
  blocks (`Int`/`Nat`/`Dyadic`/`Rat`) and in `LP/FieldGeneric.lean` (the abstract field).

  The cases below are ring IDENTITIES (and a few closed-residual inequalities): both sides
  ring-normalize to the same linear form, so the objective residual is closed and the goal
  proves with ZERO rows — no LP backend needed. They exercise the full parser → normalizer
  → certificate-identity path that distribution feeds. The behavioral multi-row repros from
  the issue (e.g. `p * n + 1 ≤ p * (n + 1)` given `1 ≤ p`, or the `n.centralBinom` site
  `4 * n * cb ≤ 2 * (2 * n + 1) * cb`) need a registered backend and are reproduced verbatim
  in comments; they are verified in the consumer suites / the resurvey.
-/

import LPTactic
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

open Lean.Grind Std

namespace LPTacticTest.Issue58

/-! ## (a) `atom × (affine)` — distribute over the right operand. -/

example (p n : Int) : p * (n + 1) = p * n + p := by lp
example (p n : Nat) : p * (n + 1) = p * n + p := by lp
example (a b c : Int) : a * (b + c) = a * b + a * c := by lp

/-! ## (b) `(affine) × atom` — distribute over the left operand (the issue's
`(p + 1) * y = y + p * y`). -/

example (p y : Int) : (p + 1) * y = y + p * y := by lp
example (p y : Nat) : (p + 1) * y = y + p * y := by lp
example (a b c : Int) : (a + b) * c = a * c + b * c := by lp

/-! ## (c) Subtraction / negation distribution (ring carriers only; `Nat` never reaches
these, its `-` being truncating and atomized upstream). -/

example (a b c : Int) : (a - b) * c = a * c - b * c := by lp
example (a b c : Int) : a * (b - c) = a * b - a * c := by lp
example (a b : Int) : (-a) * b = -(a * b) := by lp
example (a b : Int) : a * (-b) = -(a * b) := by lp

/-! ## (d) Left-nested scalar surfacing: `(k * x) * y ↝ k * (x * y)` via reassociation, so
`k` becomes a coefficient on the product atom rather than part of an opaque monomial. -/

example (n m : Int) : 4 * n * m = 4 * (n * m) := by lp
example (n m : Nat) : 4 * n * m = 4 * (n * m) := by lp

/-! ## (e) The `Nat.centralBinom` site's algebraic core (issue's Central.lean:100), as a
ring identity over both ℤ and ℕ: `2 * (2*n + 1) * c = 4 * n * c + 2 * c`. Combines
left-nested reassociation, `(sum) * atom` distribution, and scalar folding. -/

example (n c : Int) : 2 * (2 * n + 1) * c = 4 * n * c + 2 * c := by lp
example (n c : Nat) : 2 * (2 * n + 1) * c = 4 * n * c + 2 * c := by lp

/-! ## (f) Closed-residual inequalities: distribution exposes the linear part, leaving a
nonnegative constant residual (still zero rows, no backend). -/

example (n : Int) : 2 * (n + 1) ≤ 2 * n + 3 := by lp
example (n : Nat) : 2 * (n + 1) ≤ 2 * n + 3 := by lp
example (x y : Int) : (x + 1) * y ≤ x * y + y + 1 := by lp

/-! ## (g) The genuinely-nonlinear residue stays sound: a product of two non-constant atoms
is one opaque (canonicalized) column, so a reflexive goal still closes and commuted forms
match. -/

example (x y z : Int) : x * y * z = x * y * z := by lp
example (x y : Int) : x * y = y * x := by lp

/-! ## (h) Abstract ordered `Grind` field (the `ℝ`-like `.field` engine): distribution and
the certificate identity go through the generic `Field.*` distributivity lemmas. -/

section Field
variable {α : Type} [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α]
  [OrderedRing α] [IsCharP α 0]

example (p n : α) : p * (n + 1) = p * n + p := by lp
example (a b c : α) : (a + b) * c = a * c + b * c := by lp
example (a b c : α) : a * (b - c) = a * b - a * c := by lp
example (n c : α) : 2 * (2 * n + 1) * c = 4 * n * c + 2 * c := by lp

end Field

/-! ## Behavioral multi-row repros from the issue (need a backend; verified downstream).

```
-- linear after distributing (needs `1 ≤ p`):
example (p n : Int) (h : 1 ≤ p) : p * n + 1 ≤ p * (n + 1) := by lp
-- Mathlib `Data/Nat/Choose/Central.lean:100` (needs `cb ≥ 0`, the ℕ nonneg row):
example (n cb : Nat) : 4 * n * cb ≤ 2 * (2 * n + 1) * cb := by lp
```
-/

end LPTacticTest.Issue58
