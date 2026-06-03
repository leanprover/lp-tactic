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
  "8b694db5f88c65b06714de5488edefd238185f60"

require LPVerify from git "https://github.com/kim-em/lp-verify" @
  "b53657cc4743764487bbd02b7b333991825e4aec"

package LPTactic

@[default_target]
lean_lib LPTactic where
  roots := #[`LPTactic]
  globs := #[`LPTactic, `LPTactic.Basic, `LPTactic.Registry, `LPTactic.LP,
             `LPTactic.LP.+, `LPTactic.Q]

/-- Behavioral tests for the registry. Build via
    `lake build LPTacticTest` or run via `lake test`. -/
lean_lib LPTacticTest where
  roots := #[`LPTacticTest.Registry, `LPTacticTest.Runner]

lean_exe «registry-tests» where
  root := `LPTacticTest.Registry

/-- `lake test` entry point. Runs every test exe. -/
@[test_driver]
lean_exe «test-runner» where
  root := `LPTacticTest.Runner
