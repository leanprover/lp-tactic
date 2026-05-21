# LPTactic

[![Lean](https://img.shields.io/badge/Lean-4.29.1-blue.svg)](./lean-toolchain)
[![License](https://img.shields.io/github/license/kim-em/lp-tactic.svg)](./LICENSE)

The `by lp` and `maximize` tactics — Π₂ linear-rational-arithmetic
goals reduced to LP solves, with the dual multipliers reconstructed
into kernel-checked Lean proof terms — plus the `LPBackend` registry
(`registerBackend`, `resolveBackend`, `availableBackends`), the
default-backend dispatcher (`Soplex.LP.dispatchSolveExact`), and
the backend-pluggable verified-solve driver (`solveVerifiedWith`).

**No `moreLinkArgs`. No FFI dependency.** All solver calls go
through `LPBackend` values fetched from the registry. A consumer
who only wants to verify externally-produced certificates can
depend on this package plus
[`kim-em/lp-verify`](https://github.com/kim-em/lp-verify) with zero
native deps. For an actual default-FFI `by lp`, also depend on
[`kim-em/lp-backend-soplex-ffi`](https://github.com/kim-em/lp-backend-soplex-ffi)
(or use the meta-package
[`kim-em/soplex`](https://github.com/kim-em/soplex), which bundles
the FFI backend by default).

## Quickstart

```lean
require LPTactic from git "https://github.com/kim-em/lp-tactic" @ "main"
require LPBackendSoplexFFI from git
  "https://github.com/kim-em/lp-backend-soplex-ffi" @ "main"
```

```lean
import LPTactic
import LPBackendSoplexFFI  -- self-registers "soplex-ffi" at priority 10

example (a b : Rat) (_ : 2 * a + b ≤ 5) (_ : a - b ≤ 1) :
    3 * a ≤ 6 := by lp
```

Without any backend registered, `by lp` reports a structured
"no usable backend" diagnostic listing every registered backend and
its probe verdict — so the failure mode is obvious.

## Layout

```
LPTactic.lean              # top-level import
LPTactic/Basic.lean        # solveVerifiedWith, defaultDenomBudget
LPTactic/Registry.lean     # registerBackend, resolveBackend, availableBackends
LPTactic/Dispatch.lean     # dispatchSolveExact (registry-driven default)
LPTactic/Q.lean            # kernel-reducible rational literals
LPTactic/LP.lean           # `lp` and `maximize` tactic frontend
LPTactic/LP/Types.lean     # tactic state + telemetry
LPTactic/LP/Parse.lean     # goal parsing
LPTactic/LP/Problem.lean   # tactic-side Problem construction
LPTactic/LP/Atomic.lean    # direct-certificate path
LPTactic/LP/Exists.lean    # existential-witness LP path
LPTactic/LP/Forall.lean    # inner-∀ + Benders subproblem paths
LPTactic/LP/Maximize.lean  # `maximize` tactic body
LPTactic/LP/Certificate.lean
                           # certificate → kernel proof-term reconstruction
LPTactic/LP/Frontend.lean  # syntax elaboration entry point
```

Declarations remain under `namespace Soplex` (or `Soplex.LP`,
`Soplex.Tactic.LP`) so consumers writing `Soplex.solveVerifiedWith`
or `by lp` resolve to the same definitions regardless of which
package owns them. The synchronous, FFI-specialised
`Soplex.solveVerified` (`Except`-typed) lives in
`kim-em/lp-backend-soplex-ffi`, not here.

## Licence

[Apache License 2.0](./LICENSE).
