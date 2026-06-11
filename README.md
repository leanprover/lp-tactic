# LPTactic

[![Lean](https://img.shields.io/badge/Lean-4.31.0--rc1-blue.svg)](./lean-toolchain)
[![License](https://img.shields.io/github/license/leanprover/lp-tactic.svg)](./LICENSE)

> **New here? Start at [`leanprover/lp`](https://github.com/leanprover/lp)** — the entry
> point for the `lp` / `maximize` tactics and the verified LP solver. This repository is one
> package of that family: the tactics and the backend registry.

The `by lp` and `maximize` tactics — Π₂ linear-rational-arithmetic
goals reduced to LP solves, with the dual multipliers reconstructed
into kernel-checked Lean proof terms — plus the `LPBackend` registry
(`registerBackend`, `resolveBackend`, `availableBackends`), the
default-backend dispatcher (`LP.dispatchSolveExact`), and
the backend-pluggable verified-solve driver (`solveVerifiedWith`).

**No `moreLinkArgs`. No FFI dependency.** All solver calls go
through `LPBackend` values fetched from the registry. A consumer
who only wants to verify externally-produced certificates can
depend on this package plus
[`leanprover/lp-verify`](https://github.com/leanprover/lp-verify) with zero
native deps. For an actual default-FFI `by lp`, also depend on
[`leanprover/lp-backend-soplex-ffi`](https://github.com/leanprover/lp-backend-soplex-ffi)
(or use the meta-package
[`leanprover/lp`](https://github.com/leanprover/lp), which bundles
the FFI backend by default).

## Quickstart

```lean
require LPTactic from git "https://github.com/leanprover/lp-tactic" @ "main"
require LPBackendSoplexFFI from git
  "https://github.com/leanprover/lp-backend-soplex-ffi" @ "main"
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

## Fragment

`by lp` targets the Π₂ fragment of linear rational arithmetic: a goal
built from atomic comparisons (`≤`, `<`, `=`) under an outer
`∃ x₁ … xₙ` block whose body is a conjunction of atoms and inner
`∀ y₁ … yₘ, G₁ → … → atomic` subformulas, discharged against the local
linear hypotheses. A top-level `≠` goal is also handled (by splitting on
the antisymmetry it negates). Strictness runs through the fragment:
strict (`<`) atoms are supported as hypotheses, as goals, and under the
quantifiers — strict conjuncts in an existential body, and strict guards
or strict bodies in an inner universal whose guards do not mention the
existential witness. An existential witness that must satisfy a strict
atom is found by maximizing a slack margin so the returned rational point
clears the boundary; a strict universal is re-proved at the spliced
witness by the same strict-aware Farkas assembly that closes top-level
strict goals. Witness selection under strict universals is a sound
sufficient condition rather than a complete decision procedure, and
strictness inside an inner universal whose guard mentions the witness
(the Benders path) is not yet supported.

```lean
example : ∃ x : Rat, 0 < x ∧ x < 1 := by lp
example : ∃ x : Rat, 0 ≤ x ∧ ∀ y : Rat, 0 ≤ y → y < 1 → y < x + 1 := by lp
```

## Carriers

`by lp` and `maximize` work over a family of ordered carriers, not just `Rat`:

- **`Rat`, `Int`, `Dyadic`, `Nat`** — out of the box (core types).
- **`Real`, or any `Lean.Grind` ordered field of characteristic 0** — once
  Mathlib is imported (it supplies the instances).

```lean
example (a b : Int) (_ : 2 * a + b ≤ 5) (_ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a b : Nat) (_ : 2 * a + b ≤ 5) (_ : a + b ≤ 3) : 3 * a + 2 * b ≤ 8 := by lp
-- with `import Mathlib`:
example (a b : ℝ)  (_ : 2 * a + b ≤ 5) (_ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
```

The LP sent to the solver is always over ℚ; only the reconstructed proof term is
over the carrier. `lp` proves ℚ-valid (Farkas) implications — integrality and
cuts stay with `omega`/`cutsat`, so `Nat` subtraction (truncating) and `Int`/`Nat`
division are rejected rather than mis-modelled.

## Layout

```
LPTactic.lean              # top-level import
LPTactic/Basic.lean        # solveVerifiedWith, defaultDenomBudget
LPTactic/Registry.lean     # registerBackend, resolveBackend, availableBackends
LPTactic/Dispatch.lean     # dispatchSolveExact (registry-driven default)
LPTactic/Q.lean            # kernel-reducible rational literals
LPTactic/LP.lean           # `lp` and `maximize` tactic frontend
LPTactic/LP/Types.lean     # LinExpr + parser/normalizer lemma toolkit
LPTactic/LP/Parse.lean     # goal parsing
LPTactic/LP/Problem.lean   # tactic-side Problem construction
LPTactic/LP/Atomic.lean    # direct-certificate path + carrier dispatch
LPTactic/LP/Exists.lean    # existential-witness LP path
LPTactic/LP/Forall.lean    # inner-∀ + Benders subproblem paths
LPTactic/LP/Maximize.lean  # `maximize` tactic body
LPTactic/LP/BackendOption.lean
                           # the `lp.backend` option + per-call override
LPTactic/LP/Certificate.lean
                           # Q-literal rendering + residual helpers (Rat groundwork)
LPTactic/LP/CarrierCertificate.lean
                           # the carrier-parametrized certificate engine (CarrierMethods)
LPTactic/LP/CarrierLemmas.lean
                           # macros stamping out the per-carrier monomorphic lemma blocks
LPTactic/LP/RingCertificate.lean
                           # shared ordered-comm-ring assembly (Int, Dyadic)
LPTactic/LP/RatCertificate.lean,   (lemmas in Types.lean)
LPTactic/LP/IntCertificate.lean,   IntGeneric.lean
LPTactic/LP/NatCertificate.lean,   NatGeneric.lean
LPTactic/LP/DyadicCertificate.lean, DyadicGeneric.lean
LPTactic/LP/FieldCertificate.lean, FieldGeneric.lean
                           # per-carrier engine instances + their static lemmas
LPTactic/LP/Frontend.lean  # syntax elaboration entry point
LPTacticTest/              # `lake test` suites (registry + goal shapes)
```

Declarations live under `namespace LP` (public API such as
`LP.solveVerifiedWith` and the registry) and
`namespace LP.Tactic.LP` (tactic internals), so consumers writing
`LP.solveVerifiedWith` or `by lp` resolve to the same definitions
regardless of which package owns them. The synchronous,
FFI-specialised `LP.solveVerified` (`Except`-typed) lives in
`leanprover/lp-backend-soplex-ffi`, not here.

## Licence

[Apache License 2.0](./LICENSE).
