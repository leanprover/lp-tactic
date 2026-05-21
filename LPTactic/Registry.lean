/-
  Process-global registry of installed `LPBackend`s.

  The registry lives in the tactic layer rather than `lp-core` so the
  abstraction is purely about backends, not about installation: a
  consumer that just wants the `Problem` / `Certificate` vocabulary can
  depend on `lp-core` without picking up the `IO.Ref` registry state.

  Backends call `registerBackend` from an `initialize` block, so only
  the backends a user has actually imported show up at runtime. The
  tactic's default-backend fallback walks `availableBackends` in
  priority order and picks the first one whose `probe` succeeds.
-/

import LPCore.Backend
import Std.Data.HashMap

open Std

namespace Soplex.LP

/-- Process-global registry of installed backends, keyed by `name`.

    Populated by each backend module's `initialize` block, so only
    backends the user has actually imported show up. Lookups produce a
    fresh sorted array; do not rely on `Std.HashMap` iteration order. -/
initialize backendRegistry : IO.Ref (HashMap String LPBackend) ←
  IO.mkRef ∅

/-- Register a backend under its `name`. Raises if a backend with the
    same name is already registered.

    Atomic via `IO.Ref.modifyGet`: concurrent register calls cannot
    lose updates. -/
def registerBackend (b : LPBackend) : IO Unit := do
  let alreadyExists ← backendRegistry.modifyGet fun m =>
    if m.contains b.name then
      (true, m)
    else
      (false, m.insert b.name b)
  if alreadyExists then
    throw <| IO.userError s!"lp: backend '{b.name}' is already registered"

/-- Remove a backend by name. No-op if no backend is registered under
    that name.

    Primarily intended for tests that need to roll back state between
    cases. Use `withBackendRegistrySnapshot` when possible — it
    handles the snapshot / restore pair safely under exceptions. -/
def unregisterBackend (name : String) : IO Unit :=
  backendRegistry.modify (fun m => m.erase name)

/-- Snapshot the current registry, run `action`, then restore the
    snapshot regardless of whether `action` succeeded or threw.

    This is the supported test-isolation primitive: a test can
    `registerBackend` dummy backends inside the action and trust that
    the global state will be back to what it was when the action
    returns. -/
def withBackendRegistrySnapshot {α : Type} (action : IO α) : IO α := do
  let snapshot ← backendRegistry.get
  try
    let result ← action
    backendRegistry.set snapshot
    pure result
  catch e =>
    backendRegistry.set snapshot
    throw e

/-- Look up a backend by name. -/
def resolveBackend (name : String) : IO (Except String LPBackend) := do
  let m ← backendRegistry.get
  match m[name]? with
  | some b => pure (.ok b)
  | none =>
    let names := (m.toList.map Prod.fst).toArray.qsort (· < ·) |>.toList
    pure (.error s!"lp: no backend named '{name}' (registered: {names})")

/-- Run a backend's probe, converting any unhandled `IO` exception into
    a probe failure. A misbehaving backend cannot abort the fallback
    search; it can only fail its own probe. -/
def safeProbe (b : LPBackend) : IO (Except String Unit) := do
  try
    b.probe
  catch e =>
    pure (.error s!"probe raised: {e}")

/-- Snapshot of registered backends, sorted by `(defaultPriority, name)`.

    The second component encodes probe state, deliberately distinct
    from "probe succeeded":

    * `none`               — probe not run (because `runProbe := false`);
    * `some (.ok ())`      — probe ran and succeeded;
    * `some (.error msg)`  — probe ran and reported `msg`.

    Fallback selection (e.g. in the tactic layer) picks the first
    backend whose entry is `some (.ok ())`. Probes have no caching:
    callers that want memoised results should wrap the result. -/
def availableBackends (runProbe : Bool := true) :
    IO (Array (LPBackend × Option (Except String Unit))) := do
  let m ← backendRegistry.get
  let sorted := (m.toList.map Prod.snd).toArray.qsort LPBackend.lt
  if runProbe then
    sorted.mapM (fun b => return (b, some (← safeProbe b)))
  else
    pure (sorted.map (fun b => (b, none)))

end Soplex.LP
