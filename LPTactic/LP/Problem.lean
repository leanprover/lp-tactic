module
public meta import LPTactic.LP.Parse

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-! ## Building the LP problem fed to SoPlex.

The LP is `min (rhs - lhs)` over free `Rat` variables, with constraints
`eᵢ ≤ 0` for each parsed `≤`-row (`=`-rows expand to two `≤`-rows in
`collectHypProof`). SoPlex is only used as an oracle; the returned
dual multipliers are re-checked numerically at tactic time before any
proof term is built. -/

def mkEntries (rowDense : Array (Array Rat)) (n : Nat) :
    Array (Fin rowDense.size × Fin n × Rat) := Id.run do
  let mut out := #[]
  for i in [0:rowDense.size] do
    if hi : i < rowDense.size then
      let coeffs := rowDense[i]
      for j in [0:n] do
        if hj : j < n then
          let c := coeffs[j]!
          if c != 0 then
            out := out.push (⟨i, hi⟩, ⟨j, hj⟩, c)
  return out

def buildProblem (rowDense : Array (Array Rat)) (rowConsts : Array Rat)
    (objCoeffs : Array Rat) (objConst : Rat) (n : Nat)
    (h : rowDense.size = rowConsts.size := by rfl) :
    Problem rowDense.size n :=
  let rowBounds := rowConsts.map fun c => ((none : Option Rat), some (-c))
  { c := Vector.ofFn fun j => objCoeffs[j.val]!
    objOffset := objConst
    a := mkEntries rowDense n
    rowBounds := ⟨rowBounds, by simp [rowBounds, h]⟩
    colBounds := Vector.replicate n (none, none) }

/-- Like `mkEntries`, but appends a margin column `n` carrying `+1` on each strict row
(used to detect strict infeasibility). -/
def strictEntries (rowDense : Array (Array Rat)) (strictFlags : Array Bool) (n : Nat) :
    Array (Fin rowDense.size × Fin (n + 1) × Rat) := Id.run do
  let mut out := #[]
  for i in [0:rowDense.size] do
    if hi : i < rowDense.size then
      let coeffs := rowDense[i]
      for j in [0:n] do
        if hj : j < n then
          let c := coeffs[j]!
          if c != 0 then out := out.push (⟨i, hi⟩, ⟨j, by omega⟩, c)
      if strictFlags[i]! then
        out := out.push (⟨i, hi⟩, ⟨n, by omega⟩, 1)
  return out

/-- Strict-infeasibility probe LP. Adds a margin variable `s` (column `n`, bounded `s ≤ 1`)
that tightens each strict row to `aⱼ·x + s ≤ bⱼ`, and maximizes `s`. The strict hypothesis
system is infeasible iff the optimum is `s ≤ 0`; the dual then certifies `0 < 0`. The returned
multipliers are re-validated by the certificate assembly, so an `s > 0` (feasible) optimum
simply fails those checks. -/
def buildStrictProblem (rowDense : Array (Array Rat)) (rowConsts : Array Rat)
    (strictFlags : Array Bool) (n : Nat)
    (h : rowDense.size = rowConsts.size := by rfl) :
    Problem rowDense.size (n + 1) :=
  let rowBounds := rowConsts.map fun c => ((none : Option Rat), some (-c))
  { c := Vector.ofFn fun j => if j.val < n then 0 else 1
    objOffset := 0
    a := strictEntries rowDense strictFlags n
    rowBounds := ⟨rowBounds, by simp [rowBounds, h]⟩
    colBounds := Vector.ofFn fun j => if j.val < n then (none, none) else (none, some 1) }


end LP.Tactic.LP.Internal
