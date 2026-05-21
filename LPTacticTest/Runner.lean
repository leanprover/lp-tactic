/-
  `lake test` entry point for `kim-em/lp-tactic`. Runs every test
  suite in the package; today just `LPTacticTest.Registry`.
-/

import LPTacticTest.Registry

def main : IO UInt32 :=
  LPTacticTest.Registry.main
