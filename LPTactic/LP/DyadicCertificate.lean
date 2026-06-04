/-
`Dyadic` carrier instance for the unified certificate engine. Mirrors `IntCertificate` (native
kernel-reducible literals via `Dyadic.ofInt`/`ofIntWithPrec`, bare `Eq.refl` leaves, integer
multiplier clearing + native scaled/`L=1` closers) — `Dyadic` is a computable ordered comm
ring (no inverses). Scope: integer (and power-of-2) coefficients; the engine renders any
power-of-2 value via `ofIntWithPrec` (never division — dyadics have no `/`).
-/
import LPTactic.LP.CarrierCertificate
import LPTactic.LP.DyadicGeneric

open Lean Meta

namespace LP.Tactic.LP.Internal.DyadicC

/-- Build an `Int` literal Expr (`Int.ofNat`/`Int.negSucc`). -/
def mkIntLitE (n : Int) : Expr :=
  match n with
  | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkRawNatLit k)
  | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkRawNatLit k)

/-- `n` is `2 ^ k` for some `k`; return `k` (else `none`). -/
def pow2Log? (n : Nat) : Option Nat :=
  let k := n.log2
  if (1 <<< k) == n then some k else none

/-- Render a dyadic-valued `Rat` as a native `Dyadic` literal: `Dyadic.ofInt num` for integers,
`Dyadic.ofIntWithPrec num k` for `num / 2^k`. Defeq to the user's `OfNat`/native literal. -/
def mkDyadicNum (r : Rat) : Expr :=
  if r.den == 1 then
    mkApp (mkConst ``Dyadic.ofInt) (mkIntLitE r.num)
  else
    -- r = num / 2^k (caller guarantees dyadic; non-power-of-2 yields a term the identity
    -- check will reject). `Nat.log2` gives `k` when `den = 2^k`.
    mkApp2 (mkConst ``Dyadic.ofIntWithPrec) (mkIntLitE r.num) (mkIntLitE (r.den.log2 : Int))

@[inline] def dyadicRefl (t : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Dyadic) t

/-- Recognize a `Dyadic` scalar value: rendered `Dyadic.ofInt`/`ofIntWithPrec` + user `OfNat`
via `quickScalarLit?` (never the O(N²) `parseScalar?`). -/
partial def dyadicScalarLit? (e : Expr) : MetaM (Option Rat) := do
  if e.isAppOfArity ``Dyadic.ofInt 1 then
    return (← parseIntLit? e.appArg!).map (fun n => (n : Rat))
  if e.isAppOfArity ``Dyadic.ofIntWithPrec 2 then
    let args := e.getAppArgs
    let some n ← parseIntLit? args[0]! | return none
    let some k ← parseIntLit? args[1]! | return none
    -- value = n * 2^(-k); only nonneg prec `k` (denominator) is produced by `mkDyadicNum`.
    if k ≥ 0 then return some ((n : Rat) / ((2 ^ k.toNat : Nat) : Rat))
    else return some ((n : Rat) * ((2 ^ (-k).toNat : Nat) : Rat))
  quickScalarLit? e

@[inline] def dLemma (name : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst ((`LP.Tactic.LP.Internal.DyadicC).append name)) args

structure DCtx where
  m    : CarrierMethods
  leFn : Expr
  ltFn : Expr

def mkDCtx : MetaM DCtx := do
  let dy := mkConst ``Dyadic
  let u := Level.zero
  let mk2 (cls op : Name) : MetaM Expr := do
    let inst ← synthInstance (← mkAppM cls #[dy, dy, dy])
    return mkApp4 (mkConst op [u, u, u]) dy dy dy inst
  let addFn ← mk2 ``HAdd ``HAdd.hAdd
  let mulFn ← mk2 ``HMul ``HMul.hMul
  let subFn ← mk2 ``HSub ``HSub.hSub
  let negFn := mkApp2 (mkConst ``Neg.neg [u]) dy (← synthInstance (← mkAppM ``Neg #[dy]))
  let leFn  := mkApp2 (mkConst ``LE.le [u]) dy (← synthInstance (← mkAppM ``LE #[dy]))
  let ltFn  := mkApp2 (mkConst ``LT.lt [u]) dy (← synthInstance (← mkAppM ``LT #[dy]))
  let m : CarrierMethods := {
    α := dy, addFn, mulFn, subFn, negFn, mkLit := mkDyadicNum
    litAddPf := fun a b => dyadicRefl (mkApp2 addFn (mkDyadicNum a) (mkDyadicNum b))
    litMulPf := fun a b => dyadicRefl (mkApp2 mulFn (mkDyadicNum a) (mkDyadicNum b))
    litNegPf := fun a => dyadicRefl (mkApp negFn (mkDyadicNum a))
    scalarLit? := dyadicScalarLit?
    proveLitEq := fun e _r => pure (dyadicRefl e)
    applyLemma := dLemma
    mkEqTrans := fun aE bE cE p q =>
      mkApp6 (mkConst ``Eq.trans [Level.succ Level.zero]) dy aE bE cE p q }
  return { m, leFn, ltFn }

@[inline] def DCtx.mkLe (c : DCtx) (a b : Expr) : Expr := mkApp2 c.leFn a b
@[inline] def DCtx.mkLt (c : DCtx) (a b : Expr) : Expr := mkApp2 c.ltFn a b

/-- Clearing: integer multipliers `kᵢ`, dyadic scaled residual `C`. -/
def clearMultipliers (mults : Array Rat) (cst : Rat) : MetaM (Int × Array Int × Rat) := do
  let L : Nat := mults.foldl (fun acc lam => Nat.lcm acc lam.den) 1
  let Li : Int := (L : Int)
  let ks ← mults.mapM (fun lam => do
    let v := (Li : Rat) * lam
    unless v.den == 1 do throwError "lp(dyadic): cleared multiplier {v} not integral"
    pure v.num)
  let cV := (Li : Rat) * cst
  unless (pow2Log? cV.den).isSome do throwError "lp(dyadic): residual {cV} not dyadic"
  return (Li, ks, cV)

def collectEntries (rows : Array Row) (ks : Array Int) :
    MetaM (Array (Int × Expr × Expr)) := do
  let mut entries : Array (Int × Expr × Expr) := #[]
  for h : i in [0:rows.size] do
    let k := ks[i]!
    if k ≠ 0 then
      entries := entries.push (k, ← rows[i].term, ← rows[i].proof)
  return entries

def DCtx.buildWeightedSum (c : DCtx) (entries : Array (Int × Expr × Expr)) :
    MetaM (Expr × Expr) := do
  if entries.size = 0 then
    return (mkDyadicNum 0, dLemma `zero_self_le #[])
  let mkHead (k : Int) (term hRow : Expr) : MetaM (Expr × Expr) := do
    let kE := mkDyadicNum (k : Rat)
    let head := c.m.mkMul kE term
    let hk ← mkDecideProof (c.mkLe (mkDyadicNum 0) kE)
    return (head, dLemma `dyadic_smul_nonpos #[term, kE, hRow, hk])
  let n := entries.size
  let (kₖ, termₖ, hRowₖ) := entries[n - 1]!
  let mut (sumExpr, sumProof) ← mkHead kₖ termₖ hRowₖ
  for i in [0:n-1] do
    let (k, term, hRow) := entries[n - 2 - i]!
    let (head, headProof) ← mkHead k term hRow
    sumProof := dLemma `dyadic_add_nonpos #[head, sumExpr, headProof, sumProof]
    sumExpr := c.m.mkAdd head sumExpr
  return (sumExpr, sumProof)

def DCtx.assembleLeProof (c : DCtx) (rows : Array Row) (strict : Bool)
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
  let (Li, ks, C) ← clearMultipliers mults cVal
  let CE := mkDyadicNum C
  let (sumExpr, sumProof) ← c.buildWeightedSum (← collectEntries rows ks)
  if Li == 1 then
    let lhsId := c.m.mkAdd (c.m.mkSub rhs lhs) sumExpr
    let identProof ← c.m.proveCertificateIdentity vars lhsId C
    if strict then
      let hC ← mkDecideProof (c.mkLt (mkDyadicNum 0) CE)
      return dLemma `lt_close #[lhs, rhs, sumExpr, CE, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (c.mkLe (mkDyadicNum 0) CE)
      return dLemma `le_close #[lhs, rhs, sumExpr, CE, sumProof, hC, identProof]
  let LE := mkDyadicNum (Li : Rat)
  let lhsId := c.m.mkAdd (c.m.mkMul LE (c.m.mkSub rhs lhs)) sumExpr
  let identProof ← c.m.proveCertificateIdentity vars lhsId C
  let hL ← mkDecideProof (c.mkLt (mkDyadicNum 0) LE)
  if strict then
    let hC ← mkDecideProof (c.mkLt (mkDyadicNum 0) CE)
    return dLemma `scaled_lt_close #[LE, lhs, rhs, sumExpr, CE, hL, sumProof, hC, identProof]
  else
    let hC ← mkDecideProof (c.mkLe (mkDyadicNum 0) CE)
    return dLemma `scaled_le_close #[LE, lhs, rhs, sumExpr, CE, hL, sumProof, hC, identProof]

def DCtx.assembleInfeasibleProof (c : DCtx) (rows : Array Row) (mults : Array Rat)
    (vars : Array FVarId) (goalType : Expr) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do throwError "lp: infeasible Farkas did not cancel"
  let cVal := residual.const
  unless decide (0 < cVal) do throwError "lp: infeasible residual {cVal} not > 0"
  let (_, ks, C) ← clearMultipliers mults cVal
  let (sumExpr, sumProof) ← c.buildWeightedSum (← collectEntries rows ks)
  let identProof ← c.m.proveCertificateIdentity vars sumExpr C
  let hC ← mkDecideProof (c.mkLt (mkDyadicNum 0) (mkDyadicNum C))
  let hFalse := dLemma `scaled_infeasible_close #[sumExpr, mkDyadicNum C, sumProof, hC, identProof]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

end LP.Tactic.LP.Internal.DyadicC
