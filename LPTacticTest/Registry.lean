/-
  Behavioral tests for the `LPTactic` backend registry.

  Run via the `lean_exe «registry-tests»` target. Each case uses
  `withBackendRegistrySnapshot` so cases compose without leaking
  state through the process-global `backendRegistry`. The test
  fixture deliberately depends on `LPCore` only and constructs its
  own dummy `LPBackend` values — no FFI required.
-/

import LPCore
import LPTactic.Registry
import LPTactic.Dispatch

open Soplex Soplex.LP

namespace LPTacticTest.Registry

/-- Build a dummy `LPBackend` with a given name, priority, and probe
    result. `solveExact` always returns a structured "dummy" error
    so any code path that accidentally invokes it is obvious. -/
def mkDummy (name : String) (priority : Nat)
    (probe : IO (Except String Unit)) : LPBackend where
  name := name
  defaultPriority := priority
  solveExact := fun _ _ =>
    pure (Except.error (SolveError.bridge s!"dummy backend '{name}': solveExact called"))
  probe := probe

private def assertM (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

/-- Trivial dummy `Problem` used by `dispatchSolveExact` calls. The
    dispatch path does not look at the problem before deciding which
    backend to call, so any well-typed value will do. -/
private def dummyProblem : Problem 0 0 :=
  { c := Vector.mk #[] rfl
    a := #[]
    rowBounds := Vector.mk #[] rfl
    colBounds := Vector.mk #[] rfl }

/-- Case 1: a single registered, probe-OK backend is the one
    `dispatchSolveExact` reaches. -/
def case_singleBackend : IO Unit := withBackendRegistrySnapshot do
  registerBackend (mkDummy "only" 10 (pure (.ok ())))
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem
  match r with
  | .error (.bridge msg) =>
    assertM (msg.startsWith "dummy backend 'only'") s!"unexpected msg: {msg}"
  | _ => throw (IO.userError "case 1: expected dummy bridge error")

/-- Case 2: lower-priority backend with failing probe is skipped in
    favor of a higher-priority backend with passing probe. -/
def case_priorityFallback : IO Unit := withBackendRegistrySnapshot do
  registerBackend (mkDummy "ffi"  10 (pure (.error "down")))
  registerBackend (mkDummy "json" 50 (pure (.ok ())))
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem
  match r with
  | .error (.bridge msg) =>
    assertM (msg.startsWith "dummy backend 'json'")
      s!"case 2: expected json to be picked, got: {msg}"
  | _ => throw (IO.userError "case 2: expected dummy bridge error from json")

/-- Case 3: priority ties break by lexicographic name. -/
def case_priorityTieBreaksByName : IO Unit := withBackendRegistrySnapshot do
  registerBackend (mkDummy "z-backend" 10 (pure (.ok ())))
  registerBackend (mkDummy "a-backend" 10 (pure (.ok ())))
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem
  match r with
  | .error (.bridge msg) =>
    assertM (msg.startsWith "dummy backend 'a-backend'")
      s!"case 3: expected a-backend, got: {msg}"
  | _ => throw (IO.userError "case 3: expected dummy bridge error")

/-- Case 4: a probe that throws is treated as a probe failure, not
    propagated as an exception. The throwing backend is skipped. -/
def case_throwingProbe : IO Unit := withBackendRegistrySnapshot do
  registerBackend (mkDummy "boomy" 10 (throw (IO.userError "boom")))
  registerBackend (mkDummy "stable" 50 (pure (.ok ())))
  -- safeProbe is the layer that converts the throw to .error
  let probed ← safeProbe (mkDummy "boomy" 10 (throw (IO.userError "boom")))
  match probed with
  | .error msg =>
    assertM (msg.startsWith "probe raised:")
      s!"case 4a: expected 'probe raised:' prefix, got: {msg}"
  | _ => throw (IO.userError "case 4a: expected probe to fail")
  -- and dispatch still picks the next backend
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem
  match r with
  | .error (.bridge msg) =>
    assertM (msg.startsWith "dummy backend 'stable'")
      s!"case 4b: expected stable to be picked, got: {msg}"
  | _ => throw (IO.userError "case 4b: expected dummy bridge error from stable")

/-- Case 5: an empty registry gives the "no backends registered"
    diagnostic. -/
def case_emptyRegistry : IO Unit := withBackendRegistrySnapshot do
  -- Snapshot only preserves the registry at entry; we have to clear
  -- whatever was there to test the empty case.
  let m ← backendRegistry.get
  for (name, _) in m.toList do unregisterBackend name
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem
  match r with
  | .error (.bridge msg) =>
    assertM (msg.startsWith "lp: no backends are registered")
      s!"case 5: expected 'no backends are registered', got: {msg}"
  | _ => throw (IO.userError "case 5: expected empty-registry bridge error")

/-- Case 6: when all backends' probes fail, the diagnostic lists
    every backend's name, priority, and failure message. -/
def case_allProbesFail : IO Unit := withBackendRegistrySnapshot do
  -- Clear the snapshot baseline to a known-empty starting point.
  let m ← backendRegistry.get
  for (name, _) in m.toList do unregisterBackend name
  registerBackend (mkDummy "ffi"  10 (pure (.error "no libsoplex")))
  registerBackend (mkDummy "json" 50 (pure (.error "no soplex binary")))
  registerBackend (mkDummy "pure" 100 (pure (.error "intentional disable")))
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem
  match r with
  | .error (.bridge msg) =>
    assertM (msg.startsWith "lp: no registered backend was usable")
      s!"case 6: expected diag preamble, got: {msg}"
    assertM ((msg.splitOn "ffi").length > 1) "case 6: missing 'ffi' in diag"
    assertM ((msg.splitOn "json").length > 1) "case 6: missing 'json' in diag"
    assertM ((msg.splitOn "pure").length > 1) "case 6: missing 'pure' in diag"
    assertM ((msg.splitOn "no libsoplex").length > 1)
      "case 6: missing 'no libsoplex' error in diag"
    assertM ((msg.splitOn "no soplex binary").length > 1)
      "case 6: missing 'no soplex binary' error in diag"
  | _ => throw (IO.userError "case 6: expected all-probes-fail bridge error")

/-- Case 7: `resolveBackend` returns a registered backend by name. -/
def case_resolveHappyPath : IO Unit := withBackendRegistrySnapshot do
  registerBackend (mkDummy "x" 50 (pure (.ok ())))
  let r ← resolveBackend "x"
  match r with
  | .ok b => assertM (b.name = "x") s!"case 7: expected name 'x', got {b.name}"
  | .error msg => throw (IO.userError s!"case 7: expected ok, got error: {msg}")

/-- Case 8: `resolveBackend` on a missing name reports the registered
    names. -/
def case_resolveMissingName : IO Unit := withBackendRegistrySnapshot do
  let m ← backendRegistry.get
  for (name, _) in m.toList do unregisterBackend name
  registerBackend (mkDummy "x" 50 (pure (.ok ())))
  registerBackend (mkDummy "y" 60 (pure (.ok ())))
  let r ← resolveBackend "z"
  match r with
  | .error msg =>
    assertM (msg.startsWith "lp: no backend named 'z'") s!"case 8: unexpected: {msg}"
    -- The diagnostic formats the registered names via `s!{...}` on a
    -- `List String`, which renders as `[x, y]` — no quote chars.
    assertM ((msg.splitOn "x").length > 1) "case 8: missing 'x' in diag"
    assertM ((msg.splitOn "y").length > 1) "case 8: missing 'y' in diag"
  | _ => throw (IO.userError "case 8: expected error")

/-- Case 10: explicit per-call backend name reaches that backend
    even when its probe would fail (the override skips the probe
    check). -/
def case_explicitNameSkipsProbe : IO Unit := withBackendRegistrySnapshot do
  let m ← backendRegistry.get
  for (name, _) in m.toList do unregisterBackend name
  registerBackend (mkDummy "down" 10 (pure (.error "intentional disable")))
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem (some "down")
  match r with
  | .error (.bridge msg) =>
    assertM (msg.startsWith "dummy backend 'down'")
      s!"case 10: expected explicit 'down' backend, got: {msg}"
  | _ => throw (IO.userError "case 10: expected dummy bridge error")

/-- Case 11: explicit per-call name to an unregistered backend
    returns a structured error citing the registered names. -/
def case_explicitNameUnregistered : IO Unit := withBackendRegistrySnapshot do
  let m ← backendRegistry.get
  for (name, _) in m.toList do unregisterBackend name
  registerBackend (mkDummy "ffi" 10 (pure (.ok ())))
  let r ← dispatchSolveExact (m := 0) (n := 0) {} dummyProblem (some "ghost")
  match r with
  | .error (.bridge msg) =>
    assertM ((msg.splitOn "ghost").length > 1)
      s!"case 11: expected 'ghost' in diag, got: {msg}"
    assertM ((msg.splitOn "ffi").length > 1)
      s!"case 11: expected 'ffi' in registered list, got: {msg}"
  | _ => throw (IO.userError "case 11: expected explicit-name bridge error")

/-- Case 9: re-registering the same name raises. -/
def case_duplicateRegisterRejected : IO Unit := withBackendRegistrySnapshot do
  registerBackend (mkDummy "x" 50 (pure (.ok ())))
  let result ← try
    registerBackend (mkDummy "x" 50 (pure (.ok ())))
    pure (Except.ok ())
  catch e =>
    pure (Except.error e.toString)
  match result with
  | .error msg =>
    assertM ((msg.splitOn "already registered").length > 1)
      s!"case 9: expected 'already registered', got: {msg}"
  | _ => throw (IO.userError "case 9: expected duplicate register to throw")

/-- Run every case sequentially. Returns 0 on success, 1 on the first
    failing case. -/
def main : IO UInt32 := do
  let cases : List (String × IO Unit) :=
    [ ("singleBackend",             case_singleBackend),
      ("priorityFallback",          case_priorityFallback),
      ("priorityTieBreaksByName",   case_priorityTieBreaksByName),
      ("throwingProbe",             case_throwingProbe),
      ("emptyRegistry",             case_emptyRegistry),
      ("allProbesFail",             case_allProbesFail),
      ("resolveHappyPath",          case_resolveHappyPath),
      ("resolveMissingName",        case_resolveMissingName),
      ("explicitNameSkipsProbe",    case_explicitNameSkipsProbe),
      ("explicitNameUnregistered",  case_explicitNameUnregistered),
      ("duplicateRegisterRejected", case_duplicateRegisterRejected) ]
  let mut failures := 0
  for (name, action) in cases do
    IO.print s!"  [registry] {name} ... "
    try
      action
      IO.println "ok"
    catch e =>
      IO.println s!"FAIL: {e}"
      failures := failures + 1
  if failures = 0 then
    IO.println s!"All {cases.length} registry tests passed."
    pure 0
  else
    IO.println s!"{failures} of {cases.length} registry tests FAILED."
    pure 1

end LPTacticTest.Registry
