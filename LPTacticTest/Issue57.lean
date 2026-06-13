/-
  Tests for issue #57: a `let`-bound local must get ONE LP column across the parser and
  the certificate normalizer.

  The parser's per-node `whnfR` zeta-expands a `let`-bound fvar to its value and atomizes
  that value (an opaque virtual column). The certificate normalizer's fast paths
  (`smulL`'s `rhsE.isFVar`, `neg`'s `aE.isFVar`) used to take a `let`-fvar operand as a
  RAW column instead, so the same `let` variable was columned two different ways — raw at
  an occurrence reached through `smulL` (e.g. `R` inside `4 * (R / 4)`) and atomized at a
  bare occurrence (e.g. `R` on its own). The two columns never cancelled, and the
  normalizer threw `lp: N surviving atom(s) after normalization` (or, on the `Nat` path,
  `lp(nat): identity sides disagree after normalization`) instead of a clean certificate.

  The fix (`rawColumnFVarId?`) makes the normalizer route a `let`-fvar through the general
  atomizing recursion, matching the parser. These goals' objectives cancel to a closed
  constant, so they exercise the certificate normalizer (the `surviving atom` check) on
  the empty-sum shortcut path, without a registered LP backend.

  Phrased over `Rat` (the test suite does not depend on Mathlib, so `ℝ` is unavailable);
  the carrier-agnostic `normalizeR` is the same code the Mathlib `ℝ` sites exercise.
-/

import LPTactic

set_option linter.unusedVariables false

namespace LPTacticTest.Issue57

-- The headline shape: `R` is `let`-bound to an opaque term (`f 0`), so the parser
-- atomizes it. `4 * (R / 4)` reaches `R` through the scalar-mul fast path; the bare `R`
-- reaches it through the general path. Pre-fix: `2 surviving atom(s) after normalization`.
example (f : Nat → Rat) : let R := f 0; R ≤ 4 * (R / 4) := by
  intro R; lp

-- The other direction, so the `smulL` operand sits on the other side.
example (f : Nat → Rat) : let R := f 0; 4 * (R / 4) ≤ R := by
  intro R; lp

-- A negated occurrence (`neg`'s `aE.isFVar` fast path): `-R` reached through the `Neg`
-- fast path and `R` through the general path.
example (f : Nat → Rat) : let R := f 0; R - R ≤ 4 * (R / 4) - R := by
  intro R; lp

end LPTacticTest.Issue57
