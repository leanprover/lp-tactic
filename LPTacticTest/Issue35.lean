/-
  Tests for issue #35: thread the atom table through the `Nat` certificate
  assembly.

  `CarrierMethods.normalizeAtom` resolves an atomized opaque subterm (e.g.
  `f n`) by looking it up in `m.atoms`. The Rat/Ring/Field assemblies inject
  the parsed atom table into the methods before normalization, but the `Nat`
  entry points (`NCtx.assembleLeProof` / `NCtx.assembleInfeasibleProof`) never
  grew the parameter, so `NCtx.proveEq`'s normalization ran against the empty
  default table and every atom lookup threw "atom not registered during
  parsing". The fix mirrors the Ring pattern: both entry points take the
  `atoms` table and inject it into the methods, and `Atomic.lean` threads it
  through the dispatch.

  These cases close from the goal alone (zero hypothesis rows), so they
  exercise the atom-table threading through `proveEq` without a registered LP
  backend. The issue's multi-row repro
  (`(f n + 1 ≤ 3) ⊢ f n ≤ 2`) needs a backend and lives in the consumer
  suites; the same threading covers it.
-/

import LPTactic

namespace LPTacticTest.Issue35

/-! ## Opaque `Nat` atoms under the goal-only (zero-row) certificate. -/

example (f : Nat → Nat) (n : Nat) : f n ≤ f n + 1 := by lp
example (f : Nat → Nat) (n : Nat) : f n + 1 ≤ f n + 2 := by lp
example (f : Nat → Nat) (n : Nat) : 2 * f n ≤ f n + f n + 1 := by lp

/-! ## Strict variant. -/

example (f : Nat → Nat) (n : Nat) : f n < f n + 1 := by lp

/-! ## Two distinct atoms. -/

example (f g : Nat → Nat) (n : Nat) : f n + g n ≤ g n + f n + 1 := by lp

end LPTacticTest.Issue35
