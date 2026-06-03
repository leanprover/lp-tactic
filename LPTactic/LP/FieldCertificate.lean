/-
Ordered-field carrier instance for the unified certificate engine. Provides the per-field
`CCtx` (cached operator Exprs + `ofRat` literals + the `proveLitEq` literal bridge), its
`toMethods : CarrierMethods` for the shared normalizer (`CarrierCertificate.lean`), and the
field-specific assembly (rational multipliers stay rational, unscaled `direct_*_close`).
Also keeps the structural-numeral builders (`mkRatNumeral`) the ∃/maximize frontends use to
splice primal witnesses. Covers `Rat` (core) and `ℝ` (Mathlib) and any ordered field of char 0.
-/
import LPTactic.LP.CarrierCertificate
import LPTactic.LP.FieldGeneric

open Lean Meta
open Lean.Grind

namespace Soplex.Tactic.LP.Internal.Field

/-- Per-invocation field context: `α`, its universe level, cached operator Exprs, and the
field/char-0 instances passed to the `ofRat` norm-num lemmas. -/
structure CCtx where
  α : Expr
  u : Level
  addFn : Expr
  mulFn : Expr
  subFn : Expr
  divFn : Expr
  negFn : Expr
  ofRatFn : Expr
  zero : Expr
  one : Expr
  fieldInst : Expr
  charPInst : Expr

def mkCCtx (α : Expr) : MetaM CCtx := do
  let u := (← getLevel α).dec.getD Level.zero
  let hAddInst ← synthInstance (← mkAppM ``HAdd #[α, α, α])
  let hMulInst ← synthInstance (← mkAppM ``HMul #[α, α, α])
  let hSubInst ← synthInstance (← mkAppM ``HSub #[α, α, α])
  let hDivInst ← synthInstance (← mkAppM ``HDiv #[α, α, α])
  let negInst  ← synthInstance (← mkAppM ``Neg #[α])
  let fieldInst ← synthInstance (← mkAppM ``Lean.Grind.Field #[α])
  let addFn := mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) α α α hAddInst
  let mulFn := mkApp4 (mkConst ``HMul.hMul [u, u, u]) α α α hMulInst
  let subFn := mkApp4 (mkConst ``HSub.hSub [u, u, u]) α α α hSubInst
  let divFn := mkApp4 (mkConst ``HDiv.hDiv [u, u, u]) α α α hDivInst
  let negFn := mkApp2 (mkConst ``Neg.neg [u]) α negInst
  let ofRatFn := mkApp2 (mkConst ``Lean.Grind.Field.NormNum.ofRat [u]) α fieldInst
  let zeroIdx := mkRawNatLit 0
  let oneIdx  := mkRawNatLit 1
  let zeroInst ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α zeroIdx)
  let oneInst  ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α oneIdx)
  let zero := mkApp3 (mkConst ``OfNat.ofNat [u]) α zeroIdx zeroInst
  let one  := mkApp3 (mkConst ``OfNat.ofNat [u]) α oneIdx oneInst
  let charPInst ← synthInstance (← mkAppM ``IsCharP #[α, toExpr (0 : Nat)])
  return { α, u, addFn, mulFn, subFn, divFn, negFn, ofRatFn, zero, one, fieldInst, charPInst }

@[inline] def CCtx.mkAdd (c : CCtx) (a b : Expr) : Expr := mkApp2 c.addFn a b
@[inline] def CCtx.mkMul (c : CCtx) (a b : Expr) : Expr := mkApp2 c.mulFn a b
@[inline] def CCtx.mkSub (c : CCtx) (a b : Expr) : Expr := mkApp2 c.subFn a b
@[inline] def CCtx.mkNeg (c : CCtx) (a : Expr) : Expr := mkApp c.negFn a
@[inline] def CCtx.mkDiv (c : CCtx) (a b : Expr) : Expr := mkApp2 c.divFn a b
/-- `ofRat r : α` — a rational coefficient/constant literal. -/
@[inline] def CCtx.mkLit (c : CCtx) (r : Rat) : Expr := mkApp c.ofRatFn (toExpr r)

/-- `(OfNat.ofNat n : α)` — a carrier `Nat` numeral. -/
def CCtx.mkOfNatLit (c : CCtx) (n : Nat) : MetaM Expr := do
  let idx := mkRawNatLit n
  let inst ← synthInstance (mkApp2 (mkConst ``OfNat [c.u]) c.α idx)
  return mkApp3 (mkConst ``OfNat.ofNat [c.u]) c.α idx inst

/-- `(m : α)` as a structural numeral: `OfNat` for `m ≥ 0`, `Neg (OfNat …)` else. -/
def CCtx.mkIntNumeral (c : CCtx) (m : Int) : MetaM Expr := do
  if m ≥ 0 then c.mkOfNatLit m.toNat
  else return c.mkNeg (← c.mkOfNatLit (-m).toNat)

/-- `(v : α)` as a structural numeral (`OfNat`/`Neg`/`HDiv`, NOT `ofRat`) — the shape the
∃/maximize frontends splice as primal witnesses, recognized by `parseScalar?`/`proveLitEq`. -/
def CCtx.mkRatNumeral (c : CCtx) (v : Rat) : MetaM Expr := do
  let numE ← c.mkIntNumeral v.num
  if v.den == 1 then return numE
  return c.mkDiv numE (← c.mkOfNatLit v.den)

/-- Proof of `0 ≤ (ofRat lam : α)` from `0 ≤ lam` (decided on `Rat`). -/
def CCtx.mkLitNonneg (c : CCtx) (lam : Rat) : MetaM Expr := do
  let hRat ← mkDecideProof (← mkAppM ``LE.le #[toExpr (0 : Rat), toExpr lam])
  mkAppOptM ``Field.ofRat_nonneg <| #[some c.α] ++ (Array.replicate 7 none) ++ #[some hRat]

/-- Proof of `0 < (ofRat lam : α)` from `0 < lam`. -/
def CCtx.mkLitPos (c : CCtx) (lam : Rat) : MetaM Expr := do
  let hRat ← mkDecideProof (← mkAppM ``LT.lt #[toExpr (0 : Rat), toExpr lam])
  mkAppOptM ``Field.ofRat_pos <| #[some c.α] ++ (Array.replicate 7 none) ++ #[some hRat]

/-! ## Literal-faithfulness bridge: `userLit = ofRat r`. -/

partial def CCtx.scalarLit? (c : CCtx) (e : Expr) : MetaM (Option Rat) := do
  if e.isAppOfArity ``Lean.Grind.Field.NormNum.ofRat 3 then
    return ← c.scalarLit? e.appArg!
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n ← getNatValue? e.getAppArgs[1]! then
      return some (n : Rat)
  quickScalarLit? e

private def CCtx.applyEq (c : CCtx) (name : Name) (instArgs valArgs : Array Expr)
    (subProofs : Array Expr) : MetaM Expr := do
  let partialApp := mkAppN (mkConst name [c.u]) (instArgs ++ valArgs)
  let condTy := (← inferType partialApp).bindingDomain!
  let condPf ← mkDecideProof condTy
  return mkAppN partialApp (#[condPf] ++ subProofs)

/-- Build a proof `e = ofRat r` for a carrier numeral expression `e` of value `r`. -/
partial def CCtx.proveLitEq (c : CCtx) (e : Expr) (r : Rat) : MetaM Expr := do
  if e.isAppOfArity ``Lean.Grind.Field.NormNum.ofRat 3 then
    return ← mkEqRefl e
  if e.isFVar then
    if let some v ← fvarLetValue? e.fvarId! then
      return ← mkExpectedTypeHint (← c.proveLitEq v r) (← mkEq e (c.mkLit r))
    throwError "lp(field): non-literal in coefficient position{indentExpr e}"
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
    return mkAppN (mkConst ``Lean.Grind.Field.NormNum.ofNat_eq [c.u]) #[c.α, c.fieldInst, args[1]!]
  if fn.isConstOf ``Neg.neg && args.size == 3 then
    let v₁ := -r
    let h₁ ← c.proveLitEq args[2]! v₁
    return ← c.applyEq ``Lean.Grind.Field.NormNum.neg_eq #[c.α, c.fieldInst]
      #[args[2]!, toExpr v₁, toExpr r] #[h₁]
  let binArith (lemma : Name) (op : Rat → Rat → Rat) (a b : Expr) : MetaM Expr := do
    let some v₁ ← c.scalarLit? a | throwError "lp(field): non-numeral{indentExpr a}"
    let some v₂ ← c.scalarLit? b | throwError "lp(field): non-numeral{indentExpr b}"
    let h₁ ← c.proveLitEq a v₁
    let h₂ ← c.proveLitEq b v₂
    c.applyEq lemma #[c.α, c.fieldInst, c.charPInst]
      #[a, b, toExpr v₁, toExpr v₂, toExpr (op v₁ v₂)] #[h₁, h₂]
  if fn.isConstOf ``HAdd.hAdd && args.size == 6 then
    return ← binArith ``Lean.Grind.Field.NormNum.add_eq (· + ·) args[4]! args[5]!
  if fn.isConstOf ``HSub.hSub && args.size == 6 then
    return ← binArith ``Lean.Grind.Field.NormNum.sub_eq (· - ·) args[4]! args[5]!
  if fn.isConstOf ``HMul.hMul && args.size == 6 then
    return ← binArith ``Lean.Grind.Field.NormNum.mul_eq (· * ·) args[4]! args[5]!
  if fn.isConstOf ``HDiv.hDiv && args.size == 6 then
    return ← binArith ``Lean.Grind.Field.NormNum.div_eq (· / ·) args[4]! args[5]!
  throwError "lp(field): unrecognized numeral literal{indentExpr e}"

/-! ## `CarrierMethods` instance for the unified normalizer. -/

/-- `@Eq.symm α aE bE pf` (pf : aE = bE) → `bE = aE`, built without `isDefEq`. -/
@[inline] def CCtx.eqSymm (c : CCtx) (aE bE pf : Expr) : Expr :=
  mkApp4 (mkConst ``Eq.symm [Level.succ c.u]) c.α aE bE pf

/-- Apply a `[Field α]`-bundled normalizer lemma with the cached instance prefix. -/
@[inline] def CCtx.ring (c : CCtx) (name : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst ((`Soplex.Tactic.LP.Internal.Field).append name) [c.u]) (#[c.α, c.fieldInst] ++ args)

/-- The `CarrierMethods` for this field. Leaf proofs are PURE: `ofRat_{add,mul,neg}` (which
state `ofRat (a∘b) = ofRat a ∘ ofRat b`) symm'd into `ofRat a ∘ ofRat b = ofRat (a∘b)`. -/
def CCtx.toMethods (c : CCtx) : CarrierMethods :=
  let ofRatBin (lemma : Name) (a b : Rat) : Expr :=
    mkAppN (mkConst lemma [c.u]) #[c.α, c.fieldInst, c.charPInst, toExpr a, toExpr b]
  { α := c.α, addFn := c.addFn, mulFn := c.mulFn, subFn := c.subFn, negFn := c.negFn
    mkLit := c.mkLit
    litAddPf := fun a b =>
      c.eqSymm (c.mkLit (a + b)) (c.mkAdd (c.mkLit a) (c.mkLit b))
        (ofRatBin ``Lean.Grind.Field.NormNum.ofRat_add a b)
    litMulPf := fun a b =>
      c.eqSymm (c.mkLit (a * b)) (c.mkMul (c.mkLit a) (c.mkLit b))
        (ofRatBin ``Lean.Grind.Field.NormNum.ofRat_mul a b)
    litNegPf := fun a =>
      c.eqSymm (c.mkLit (-a)) (c.mkNeg (c.mkLit a))
        (mkAppN (mkConst ``Lean.Grind.Field.NormNum.ofRat_neg [c.u]) #[c.α, c.fieldInst, toExpr a])
    scalarLit? := c.scalarLit?
    proveLitEq := c.proveLitEq
    applyLemma := c.ring
    mkEqTrans := fun aE bE cE p q =>
      mkApp6 (mkConst ``Eq.trans [Level.succ c.u]) c.α aE bE cE p q }

/-! ## Weighted sum + assembly (field-specific: no clearing, unscaled `direct_*_close`). -/

def CCtx.buildWeightedSum (c : CCtx) (entries : Array (Rat × Expr × Expr)) :
    MetaM (Expr × Expr) := do
  if entries.size = 0 then
    let proof ← mkAppOptM ``Field.zero_self_le (#[some c.α] ++ Array.replicate 6 none)
    return (c.zero, proof)
  let n := entries.size
  let mkHead (lam : Rat) (term hRow : Expr) : MetaM (Expr × Expr) := do
    let head := c.mkMul (c.mkLit lam) term
    let hLam ← c.mkLitNonneg lam
    return (head, ← mkAppM ``Field.smul_nonpos #[hRow, hLam])
  let (lamₖ, termₖ, hRowₖ) := entries[n - 1]!
  let mut (sumExpr, sumProof) ← mkHead lamₖ termₖ hRowₖ
  for i in [0:n-1] do
    let (lam, term, hRow) := entries[n - 2 - i]!
    let (head, headProof) ← mkHead lam term hRow
    sumProof ← mkAppM ``Field.add_nonpos #[headProof, sumProof]
    sumExpr := c.mkAdd head sumExpr
  return (sumExpr, sumProof)

def collectEntries (rows : Array Row) (mults : Array Rat) :
    MetaM (Array (Rat × Expr × Expr)) := do
  let mut entries : Array (Rat × Expr × Expr) := #[]
  for h : i in [0:rows.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      entries := entries.push (lam, ← rows[i].term, ← rows[i].proof)
  return entries

/-- Optimal-branch certificate: `Σ λᵢ·rowᵢ ≤ 0` + `(rhs-lhs)+s = c` ⇒ `lhs ≤ rhs` (or `<`). -/
def CCtx.assembleLeProof (c : CCtx) (rows : Array Row) (strict : Bool)
    (objLin : LinExpr) (mults : Array Rat) (vars : Array FVarId) (lhs rhs : Expr) :
    MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual objLin rowLins mults
  unless isLinExprClosed residual do
    throwError "lp: dual certificate did not algebraically cancel the goal"
  let cVal := residual.const
  if strict then
    unless decide (0 < cVal) do throwError "lp: goal not entailed; residual {cVal} not > 0"
  else
    unless decide (0 ≤ cVal) do throwError "lp: goal not entailed; residual {cVal} not ≥ 0"
  let (sumExpr, sumProof) ← c.buildWeightedSum (← collectEntries rows mults)
  let lhsId := c.mkAdd (c.mkSub rhs lhs) sumExpr
  let identProof ← c.toMethods.proveCertificateIdentity vars lhsId cVal
  if strict then
    mkAppM ``Field.direct_lt_close #[sumProof, ← c.mkLitPos cVal, identProof]
  else
    mkAppM ``Field.direct_le_close #[sumProof, ← c.mkLitNonneg cVal, identProof]

/-- Infeasible-branch (Farkas) certificate. -/
def CCtx.assembleInfeasibleProof (c : CCtx) (rows : Array Row) (mults : Array Rat)
    (vars : Array FVarId) (goalType : Expr) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do throwError "lp: infeasible Farkas certificate did not cancel"
  let cVal := residual.const
  unless decide (0 < cVal) do throwError "lp: infeasible residual {cVal} not > 0"
  let (sumExpr, sumProof) ← c.buildWeightedSum (← collectEntries rows mults)
  let identProof ← c.toMethods.proveCertificateIdentity vars sumExpr cVal
  let hFalse ← mkAppM ``Field.direct_infeasible_close #[sumProof, ← c.mkLitPos cVal, identProof]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

end Soplex.Tactic.LP.Internal.Field
