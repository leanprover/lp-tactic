/-
  `lake test` entry point for `kim-em/lp-tactic`. Runs every test
  suite in the package and imports the example-only files so a
  successful compilation already counts as a passing test.
-/

import LPTacticTest.Registry
import LPTacticTest.Issue5

def main : IO UInt32 :=
  LPTacticTest.Registry.main
