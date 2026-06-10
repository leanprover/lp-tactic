/-
`Rat` carrier instance for the unified certificate engine. Provides `mkRatCtx` (the
`CarrierMethods` whose `mkLit` produces the kernel-reducible `Q.toRat` literals and whose
numeral leaves are `ratlit_*` applications with `Eq.refl` side conditions — the original
`Q`-discharger shapes, so the unified engine pays no `ofRat` literal bridge on the `Rat`
fast path) and the thin `Rat`-specific assembly: rational multipliers stay rational
(no integer clearing) and the closers are the unscaled `direct_*_close` of `Types.lean`.
-/
module
public meta import LPTactic.LP.CarrierCertificate

public meta section

open Lean Meta

namespace LP.Tactic.LP.Internal

/-- Per-invocation `Rat` carrier: the `CarrierMethods` for the unified normalizer
(`Q.toRat` literals, `ratlit_*` leaves with `Eq.refl` side conditions) plus the
cached `LE`/`LT` operator Exprs for the sign-decide proofs. -/
structure RatCtx where
  m    : CarrierMethods
  leFn : Expr
  ltFn : Expr

def mkRatCtx : MetaM RatCtx := do
  -- Fetch the `ratlit_*` side-condition templates once; the leaf-proof closures stay pure.
  let addDom ← getRatlitAddDomain
  let mulDom ← getRatlitMulDomain
  let negDom ← getRatlitNegDomain
  let u := Level.zero
  let leFn := mkApp2 (mkConst ``LE.le [u]) ratType (← synthInstance (← mkAppM ``LE #[ratType]))
  let ltFn := mkApp2 (mkConst ``LT.lt [u]) ratType (← synthInstance (← mkAppM ``LT #[ratType]))
  let m : CarrierMethods := {
    α := ratType
    addFn := addRatFn, mulFn := mulRatFn, subFn := subRatFn, negFn := negRatFn
    mkLit := mkRatLit
    litAddPf := fun a b =>
      let qa := mkQLit a; let qb := mkQLit b; let qm := mkQLit (a + b)
      mkApp4 (mkConst ``ratlit_add) qa qb qm
        (mkEqReflProof (addDom.instantiate #[qm, qb, qa]))
    litMulPf := fun a b =>
      let qa := mkQLit a; let qb := mkQLit b; let qm := mkQLit (a * b)
      mkApp4 (mkConst ``ratlit_mul) qa qb qm
        (mkEqReflProof (mulDom.instantiate #[qm, qb, qa]))
    litNegPf := fun a =>
      let qa := mkQLit a; let qm := mkQLit (-a)
      mkApp3 (mkConst ``ratlit_neg) qa qm
        (mkEqReflProof (negDom.instantiate #[qm, qa]))
    scalarLit? := quickScalarLit?
    -- `mkRatLit r` and the user's literal Expr agree under closed-`Rat` kernel
    -- reduction, so a type-hinted `Eq.refl` is the whole literal bridge.
    proveLitEq := fun e r => do
      let lit := mkRatLit r
      mkExpectedTypeHint (← mkEqRefl lit) (← mkEq e lit)
    applyLemma := fun name args =>
      mkAppN (mkConst ((`LP.Tactic.LP.Internal).append name)) args
    mkEqTrans := fun aE bE cE p q =>
      mkApp6 (mkConst ``Eq.trans [Level.succ u]) ratType aE bE cE p q }
  return { m, leFn, ltFn }

/-- Optimal-branch certificate over `Rat`: `Σ λᵢ·rowᵢ ≤ 0` (or `< 0` via a strict row)
plus the identity `(rhs - lhs) + s = c`, closed by the unscaled `direct_*_close`. -/
def RatCtx.assembleLeProof (c : RatCtx) (rows : Array Row) (strict : Bool)
    (objLin : LinExpr) (mults : Array Rat) (vars : Array FVarId) (lhs rhs : Expr)
    (atoms : AtomTable := {}) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual objLin rowLins mults
  unless isLinExprClosed residual do
    throwError "lp: dual certificate did not algebraically cancel the goal{
      ""} (residual still depends on variables); refusing to build a proof"
  let cVal := residual.const
  let (sumExpr, sumProof, sumStrict) ←
    buildWeightedSumDecide c.m c.leFn c.ltFn (← collectEntries rows mults strict)
  -- Residual sign required: a strict goal needs `0 < c`, UNLESS a strict row made the sum
  -- strict (`sumStrict`), in which case `0 ≤ c` suffices.
  if strict then
    if sumStrict then
      unless decide (0 ≤ cVal) do
        throwError "lp: goal is not entailed; numerical residual is {cVal}, not ≥ 0"
    else
      unless decide (0 < cVal) do
        throwError "lp: goal is not entailed; numerical residual is {cVal}, not > 0 {
          ""}(no strict hypothesis available to upgrade it)"
  else
    unless decide (0 ≤ cVal) do
      throwError "lp: goal is not entailed; numerical residual is {cVal}, not ≥ 0"
  let cExpr := c.m.mkLit cVal
  let lhsId := c.m.mkAdd (c.m.mkSub rhs lhs) sumExpr
  let identProof ← ({ c.m with atoms }).proveCertificateIdentity vars lhsId cVal
  -- Build the final closer by explicit-argument application instead of `mkAppM`: the
  -- four implicits are in hand, and `isDefEq` over the deeply nested `sumProof`/
  -- `identProof` types can blow the elaborator's `maxRecDepth` on large LPs.
  if strict then
    if sumStrict then
      let hC ← mkDecideProof (mkApp2 c.leFn (c.m.mkLit 0) cExpr)
      return c.m.applyLemma `direct_lt_close_strict
        #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (mkApp2 c.ltFn (c.m.mkLit 0) cExpr)
      return c.m.applyLemma `direct_lt_close
        #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]
  else
    let hC ← mkDecideProof (mkApp2 c.leFn (c.m.mkLit 0) cExpr)
    return c.m.applyLemma `direct_le_close
      #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]

/-- Infeasible-branch (Farkas) certificate over `Rat`: the weighted hypothesis sum is
`≤ 0` (or `< 0` via a strict row) but equals a contradicting residual; the surrounding
`goalType` follows by `False.elim`. -/
def RatCtx.assembleInfeasibleProof (c : RatCtx) (rows : Array Row) (mults : Array Rat)
    (vars : Array FVarId) (goalType : Expr) (atoms : AtomTable := {}) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do
    throwError "lp: infeasible Farkas certificate did not algebraically cancel"
  let cVal := residual.const
  let (sumExpr, sumProof, sumStrict) ←
    buildWeightedSumDecide c.m c.leFn c.ltFn (← collectEntries rows mults true)
  -- `c > 0` always certifies infeasibility; a strict sum (`s < 0`) does so already at `0 ≤ c`.
  if sumStrict then
    unless decide (0 ≤ cVal) do
      throwError "lp: infeasible Farkas residual {cVal} is not ≥ 0"
  else
    unless decide (0 < cVal) do
      throwError "lp: infeasible Farkas residual {cVal} is not > 0"
  let cExpr := c.m.mkLit cVal
  let identProof ← ({ c.m with atoms }).proveCertificateIdentity vars sumExpr cVal
  let hFalse ←
    if sumStrict then
      let hC ← mkDecideProof (mkApp2 c.leFn (c.m.mkLit 0) cExpr)
      pure <| c.m.applyLemma `direct_infeasible_close_strict
        #[sumExpr, cExpr, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (mkApp2 c.ltFn (c.m.mkLit 0) cExpr)
      pure <| c.m.applyLemma `direct_infeasible_close
        #[sumExpr, cExpr, sumProof, hC, identProof]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

end LP.Tactic.LP.Internal
