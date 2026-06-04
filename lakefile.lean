import Lake
open Lake DSL

/-! # `LPTactic` build configuration

  The `by lp` and `maximize` tactics, plus the `LPBackend` registry
  (`registerBackend`, `resolveBackend`, `availableBackends`), the
  default-backend dispatcher (`LP.dispatchSolveExact`), and
  the backend-pluggable verified-solve driver (`solveVerifiedWith`).

  **No FFI dependency.** All solver calls go through `LPBackend`
  values fetched from the registry. A consumer who wants to verify
  externally-produced certificates without ever building SoPlex
  depends on this package directly (plus `lp-verify`), with no
  native deps in the dependency graph.
-/

require LPCore from git "https://github.com/leanprover/lp-core" @ "ae9f7864b61c06e87fb994316ac8a7e092772adb"

require LPVerify from git "https://github.com/leanprover/lp-verify" @ "473f52be8e7ce4760b2603a5b00ee038db324036"

package LPTactic

@[default_target]
lean_lib LPTactic where
  roots := #[`LPTactic]
  globs := #[`LPTactic, `LPTactic.Basic, `LPTactic.Registry, `LPTactic.LP,
             `LPTactic.LP.+, `LPTactic.Q]

/-- Behavioral tests for the registry. Build via
    `lake build LPTacticTest` or run via `lake test`. -/
lean_lib LPTacticTest where
  roots := #[`LPTacticTest.Registry, `LPTacticTest.Runner, `LPTacticTest.Issue5]

lean_exe «registry-tests» where
  root := `LPTacticTest.Registry

/-- `lake test` entry point. Runs every test exe. -/
@[test_driver]
lean_exe «test-runner» where
  root := `LPTacticTest.Runner
