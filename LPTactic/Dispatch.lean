/-
  Tactic-side default-backend dispatch.

  The `by lp` tactic calls into `dispatchSolveExact`, which selects
  the registered backend to run for this call. Three layers of
  resolution:

  1. **Explicit per-call name** (`?backendName`): caller passed a
     specific backend identifier; resolve via `resolveBackend` and
     fail with a structured error if no backend by that name is
     registered.
  2. **No explicit name**: walk `availableBackends` in priority
     order and pick the first one whose `probe` succeeds.

  This decouples the tactic from any specific backend — the FFI,
  JSON subprocess, or pure-Lean backends can all serve the call.
  A backend must be `import`ed somewhere up the dependency chain for
  it to self-register and appear in `availableBackends`.
-/

import LPCore.Types
import LPTactic.Registry

namespace Soplex.LP

/-- Diagnostic for "the registry's auto-fallback found no usable
    backend." Lists each registered backend and its probe verdict. -/
private def fallbackUnusableDiag
    (backends : Array (LPBackend × Option (Except String Unit))) :
    String :=
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

/-- Dispatch a `solveExact` call through the registry.

    * If `backendName?` is `some name`, resolves to that backend
      via `resolveBackend` and runs it (skipping any probe — the
      caller asked for this specific backend by name).
    * Otherwise picks the first backend (in `availableBackends`
      priority order) whose probe succeeds. -/
def dispatchSolveExact {m n : Nat} (opts : Options) (p : Problem m n)
    (backendName? : Option String := none) :
    IO (Except SolveError (Solution m n)) := do
  match backendName? with
  | some name =>
    match (← resolveBackend name) with
    | .ok b => b.solveExact opts p
    | .error msg => return Except.error (SolveError.bridge msg)
  | none =>
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
      return Except.error (SolveError.bridge (fallbackUnusableDiag backends))

end Soplex.LP
