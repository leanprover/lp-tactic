/-
  Top-level entry point for `LPTactic`.

  Exports:
  * `LPTactic.Basic`     — `solveVerified`, `solveVerifiedWith`,
                           `defaultDenomBudget`.
  * `LPTactic.Registry`  — `registerBackend`, `resolveBackend`,
                           `availableBackends`.
  * `LPTactic.LP`        — the `lp` tactic frontend.
  * `LPTactic.Q`         — kernel-reducible rational literals used in
                           tactic-emitted proof terms.

  Re-exported by `kim-em/soplex` through `Soplex.Tactic.LP` so existing
  callers writing `import Soplex` or `import Soplex.Tactic.LP` keep
  working unchanged.
-/

import LPTactic.Basic
import LPTactic.Registry
import LPTactic.LP
import LPTactic.Q
