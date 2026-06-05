/-
  Top-level entry point for `LPTactic`.

  Re-exported by `leanprover/lp` through `LP.Tactic.LP` so existing
  callers writing `import LP` or `import LP.Tactic.LP` keep
  working unchanged.
-/
module

public import LPTactic.Basic
public import LPTactic.Registry
public import LPTactic.Dispatch
public import LPTactic.LP
public import LPTactic.Q

@[expose] public section
