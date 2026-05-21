import Lake
open Lake DSL

/-! # `LPTactic` build configuration

  The `by lp` and `maximize` tactics, plus the `LPBackend` registry
  (`registerBackend`, `resolveBackend`, `availableBackends`) and the
  verified-solve drivers (`solveVerified`, `solveVerifiedWith`).

  No `moreLinkArgs`. The package depends on `kim-em/soplex-ffi`
  transitively for `Soplex.solveExact`, which the tactic still calls
  directly today; threading `LPBackend` through every call site
  (issue #50 step 3) is what removes the FFI dependency edge so a
  truly verifier-only-without-SoPlex consumer becomes possible.
-/

require LPCore from git "https://github.com/kim-em/lp-core" @
  "60fca2313ea3be14f578258dc6390f2fa07b26e7"

require LPVerify from git "https://github.com/kim-em/lp-verify" @
  "3726846a10bb875d133a52a2c4b137da2806e22e"

require SoplexFFI from git "https://github.com/kim-em/soplex-ffi" @
  "a1389a99c2345f9d72ffdc2941be350ad0f97fd7"

package LPTactic

@[default_target]
lean_lib LPTactic where
  roots := #[`LPTactic]
  globs := #[`LPTactic, `LPTactic.Basic, `LPTactic.Registry, `LPTactic.LP,
             `LPTactic.LP.+, `LPTactic.Q]
