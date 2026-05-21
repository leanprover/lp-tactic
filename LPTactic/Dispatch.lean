/-
  Tactic-side default-backend dispatch.

  The `by lp` tactic calls into `dispatchSolveExact`, which selects
  the highest-priority registered backend whose probe succeeds. This
  decouples the tactic from any specific backend — the FFI, JSON
  subprocess, or pure-Lean backends can all serve the call.

  A backend must be `import`ed somewhere up the dependency chain for
  it to self-register and appear in `availableBackends`. The
  meta-package `kim-em/soplex` ensures this by transitively importing
  `LPBackendSoplexFFI`, but a downstream user wiring a different
  default (e.g. `kim-em/lp-backend-soplex-json`) just imports that
  package instead.
-/

import LPCore.Types
import LPTactic.Registry

namespace Soplex.LP

/-- Dispatch a `solveExact` call through the registry. Picks the
    first backend (in `availableBackends` priority order) whose probe
    succeeds and runs `b.solveExact` on it. Reports a structured
    error listing every considered backend and its probe verdict if
    no backend is usable. -/
def dispatchSolveExact {m n : Nat} (opts : Options) (p : Problem m n) :
    IO (Except SolveError (Solution m n)) := do
  let backends ← availableBackends (runProbe := true)
  let chosen : Option LPBackend :=
    backends.findSome? fun entry =>
      let (b, s) := entry
      match s with
      | some (.ok ()) => some b
      | _ => none
  match chosen with
  | some b => b.solveExact opts p
  | none =>
    let diag : String :=
      if backends.isEmpty then
        "lp: no backends are registered (did you `import Soplex` or another `lp-backend-*` package?)"
      else
        "lp: no registered backend was usable:\n" ++
          String.intercalate "\n" (backends.toList.map fun entry =>
            let (b, s) := entry
            match s with
            | some (.error e) => s!"  - {b.name} (priority {b.defaultPriority}): probe failed: {e}"
            | some (.ok ())   => s!"  - {b.name} (priority {b.defaultPriority}): probe OK (?!)"
            | none            => s!"  - {b.name} (priority {b.defaultPriority}): probe not run")
    return Except.error (SolveError.bridge diag)

end Soplex.LP
