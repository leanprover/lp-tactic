/-
  The `lp.backend` Lean option: lets the user pin a specific backend
  by name for `by lp` and `by maximize`.

  Precedence (lowest binds tightest):
  - default fallback: highest-priority backend in `availableBackends`
    whose probe succeeds (today's behaviour).
  - `set_option lp.backend "<name>"`: pin a backend for everything
    in scope. Error if not registered.
  - per-call `(backend := <ident>)` (see `Frontend.lean`): override
    the option for a single call.
-/

import Lean

namespace LP.Tactic.LP

open Lean

/-- Name of the backend the next `by lp` / `by maximize` call should
    dispatch to. Empty string means "fall back to the registry's
    priority-based default." -/
register_option lp.backend : String := {
  defValue := ""
  descr    := "Backend name for `by lp` / `by maximize`. Resolved via \
               `LP.resolveBackend`. Empty string means the \
               registry's priority-based default."
}

/-- Read the `lp.backend` option from the current monad's options.
    Returns `none` if unset (i.e. set to the empty default). -/
def getBackendOverride [Monad m] [MonadOptions m] : m (Option String) := do
  let s := lp.backend.get (← getOptions)
  if s.isEmpty then return none else return (some s)

end LP.Tactic.LP
