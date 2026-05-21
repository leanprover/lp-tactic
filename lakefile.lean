import Lake
open Lake DSL

/-! # `LPTactic` build configuration

  The `by lp` and `maximize` tactics, plus the `LPBackend` registry
  (`registerBackend`, `resolveBackend`, `availableBackends`), the
  default-backend dispatcher (`Soplex.LP.dispatchSolveExact`), and
  the backend-pluggable verified-solve driver (`solveVerifiedWith`).

  **No FFI dependency.** All solver calls go through `LPBackend`
  values fetched from the registry. A consumer who wants to verify
  externally-produced certificates without ever building SoPlex
  depends on this package directly (plus `lp-verify`), with no
  native deps in the dependency graph.
-/

require LPCore from git "https://github.com/kim-em/lp-core" @
  "98669eee0fe05bcc1ed9aa2c7c7adff5d1aaf9ae"

require LPVerify from git "https://github.com/kim-em/lp-verify" @
  "3ff2a91582ed8b460021698804266cafbfda0aa5"

package LPTactic

@[default_target]
lean_lib LPTactic where
  roots := #[`LPTactic]
  globs := #[`LPTactic, `LPTactic.Basic, `LPTactic.Registry, `LPTactic.LP,
             `LPTactic.LP.+, `LPTactic.Q]
