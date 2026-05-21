/-
  Verified-solve driver: `solveVerifiedWith`.

  Composes `validateOptions`, `validate`, an `LPBackend`-supplied
  `solveExact`, and `LPVerify.verifyOutcome` into a single
  `LPBackend → Options → Problem → IO (Except SolveError VerifiedSolve)` call.

  This file lives in `kim-em/lp-tactic` (alongside the `by lp` tactic)
  rather than in `lp-verify` because the driver actually invokes a
  solver. The verifier itself does no `IO` and knows nothing about
  `solveExact`.

  The synchronous, FFI-specialised entry point `Soplex.solveVerified`
  (`Except`-typed, no backend argument) lives in
  `kim-em/lp-backend-soplex-ffi`, where it can call
  `SoplexFFI.solveExact` directly. `lp-tactic` itself has no FFI
  dependency.
-/

import LPCore.Validate
import LPVerify
import LPTactic.Registry

namespace Soplex

open Soplex.LP

/-- Default `denomBudget` for verified-solve drivers: combined
    numerator + denominator bit length per rational coordinate.
    `10000` is comfortable headroom over what well-behaved LPs
    produce while still ruling out refinement runaway. -/
def defaultDenomBudget : Option Nat := some 10000

/-- Drive `validate`, an `LPBackend`'s `solveExact`, then the checker,
    packaged as a `VerifiedSolve` carrying a real soundness-lemma
    proof.

    * `validateOptions` and `validate` run first; either failure
      surfaces as `Except.error`.
    * `Options.presolve` is forced `false` internally: the checker must
      run against the normalized input LP, not whatever the backend's
      presolve transformed it into.
    * `denomBudget` is a ceiling on the bit length of every rational
      coordinate in the returned certificate; exceeding it yields
      `Verified.unchecked .budgetExceeded`. `none` disables the check.
    * The returned `normalized` field is `validate p`, the `Problem`
      the proof is indexed by. Downstream code reasons about that
      value, not about the raw user input.

    Lives in `IO` because backends are `IO`-typed (so a future
    subprocess or remote solver can plug in); synchronous backends
    like `Soplex.Backend.SoplexFFI.backend` just lift their `Except`
    result with `pure`. -/
def solveVerifiedWith {m n : Nat} (backend : LPBackend) (opts : Options)
    (p : Problem m n) (denomBudget : Option Nat := defaultDenomBudget) :
    IO (Except SolveError (Verify.VerifiedSolve (m := m) (n := n) opts.sense)) := do
  match validateOptions opts with
  | .error e => return .error (.invalidOptions e)
  | .ok _ =>
    match validate p with
    | .error e => return .error (.invalidProblem e)
    | .ok normalized =>
      let opts' := { opts with presolve := false }
      match ← backend.solveExact opts' normalized with
      | .error e => return .error e
      | .ok sol =>
        return .ok { normalized
                     verified := Verify.verifyOutcome opts denomBudget normalized sol }

end Soplex
