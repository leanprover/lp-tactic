/-
  `lake test` entry point for `leanprover/lp-tactic`. Runs every test
  suite in the package and imports the example-only files so a
  successful compilation already counts as a passing test.
-/

import LPTacticTest.Registry
import LPTacticTest.Issue5
import LPTacticTest.Issue27
import LPTacticTest.Issue34
import LPTacticTest.Issue35
import LPTacticTest.Issue38

def main : IO UInt32 :=
  LPTacticTest.Registry.main
