/-
`Int` carrier instance for the unified certificate engine. Provides `intMethods :
CarrierMethods` (native `Int.ofNat`/`negSucc` literals, bare `Eq.refl` leaves — validated
faster than the OLD Rat engine) and the thin `Int`-specific assembly (multiplier clearing +
native-`Int.mul` scaled/unscaled closers). The structural normalizer lives in
`CarrierCertificate.lean`; only the per-carrier strategy + assembly are here.
-/
import LPTactic.LP.CarrierCertificate
import LPTactic.LP.IntGeneric

open Lean Meta

namespace LP.Tactic.LP.Internal.IntC

/-- Render an `Int` value as a native literal (`Int.ofNat k` / `Int.negSucc k`), defeq to a
user `(k : Int)` `OfNat`/`Neg` literal. -/
def mkIntNum (n : Int) : Expr :=
  match n with
  | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkRawNatLit k)
  | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkRawNatLit k)

/-- `@Eq.refl Int t` — valid as a proof of `t = m` whenever `t ≡ m` by kernel reduction. -/
@[inline] def intRefl (t : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Int) t

/-- Recognize an `Int` scalar value: native `Int.ofNat`/`Int.negSucc` (the engine's own
rendered literals) plus user `OfNat`/`Neg`/`HMul`/`HDiv` via `quickScalarLit?`. Uses
`quickScalarLit?` (O(1) reject of `HAdd`/`HSub`), NEVER the O(N²) recursive `parseScalar?`. -/
partial def intScalarLit? (e : Expr) : MetaM (Option Rat) := do
  if e.isAppOfArity ``Int.ofNat 1 then
    return (← parseNatLit? e.appArg!).map (fun k => ((Int.ofNat k : Int) : Rat))
  if e.isAppOfArity ``Int.negSucc 1 then
    return (← parseNatLit? e.appArg!).map (fun k => ((Int.negSucc k : Int) : Rat))
  quickScalarLit? e

/-- Apply an `IntC` lemma by base name (monomorphic — no universe/instance args). -/
@[inline] def iLemma (name : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst ((`LP.Tactic.LP.Internal.IntC).append name)) args

/-- Per-invocation `Int` carrier: the `CarrierMethods` for the unified normalizer plus the
cached `LE`/`LT` operator Exprs for the O(N) sign-decide proofs. -/
structure ICtx where
  m    : CarrierMethods
  leFn : Expr
  ltFn : Expr

def mkICtx : MetaM ICtx := do
  let int := mkConst ``Int
  let u := Level.zero
  let mk2 (cls op : Name) : MetaM Expr := do
    let inst ← synthInstance (← mkAppM cls #[int, int, int])
    return mkApp4 (mkConst op [u, u, u]) int int int inst
  let addFn ← mk2 ``HAdd ``HAdd.hAdd
  let mulFn ← mk2 ``HMul ``HMul.hMul
  let subFn ← mk2 ``HSub ``HSub.hSub
  let negFn := mkApp2 (mkConst ``Neg.neg [u]) int (← synthInstance (← mkAppM ``Neg #[int]))
  let leFn  := mkApp2 (mkConst ``LE.le [u]) int (← synthInstance (← mkAppM ``LE #[int]))
  let ltFn  := mkApp2 (mkConst ``LT.lt [u]) int (← synthInstance (← mkAppM ``LT #[int]))
  let mkLit := fun (r : Rat) => mkIntNum r.num
  let m : CarrierMethods := {
    α := int, addFn, mulFn, subFn, negFn, mkLit
    litAddPf := fun a b => intRefl (mkApp2 addFn (mkLit a) (mkLit b))
    litMulPf := fun a b => intRefl (mkApp2 mulFn (mkLit a) (mkLit b))
    litNegPf := fun a => intRefl (mkApp negFn (mkLit a))
    scalarLit? := intScalarLit?
    proveLitEq := fun e _r => pure (intRefl e)
    applyLemma := iLemma
    mkEqTrans := fun aE bE cE p q =>
      mkApp6 (mkConst ``Eq.trans [Level.succ Level.zero]) int aE bE cE p q
  }
  return { m, leFn, ltFn }

@[inline] def ICtx.mkLe (c : ICtx) (a b : Expr) : Expr := mkApp2 c.leFn a b
@[inline] def ICtx.mkLt (c : ICtx) (a b : Expr) : Expr := mkApp2 c.ltFn a b
@[inline] def ICtx.mkLit (c : ICtx) (r : Rat) : Expr := c.m.mkLit r

/-! ### Clearing: rational multipliers → integer `(L, kᵢ, C)`. -/

def clearMultipliers (mults : Array Rat) (cst : Rat) : MetaM (Int × Array Int × Int) := do
  let L : Nat := mults.foldl (fun acc lam => Nat.lcm acc lam.den) 1
  let Li : Int := (L : Int)
  let ks ← mults.mapM (fun lam => do
    let v := (Li : Rat) * lam
    unless v.den == 1 do throwError "lp(int): cleared multiplier {v} not integral"
    pure v.num)
  let cV := (Li : Rat) * cst
  unless cV.den == 1 do throwError "lp(int): cleared residual {cV} not integral"
  return (Li, ks, cV.num)

def collectEntries (rows : Array Row) (ks : Array Int) :
    MetaM (Array (Int × Expr × Expr)) := do
  let mut entries : Array (Int × Expr × Expr) := #[]
  for h : i in [0:rows.size] do
    let k := ks[i]!
    if k ≠ 0 then
      entries := entries.push (k, ← rows[i].term, ← rows[i].proof)
  return entries

/-- `Σ kᵢ * termᵢ : Int` with a proof it is `≤ 0`. Sign lemmas applied with EXPLICIT implicit
args (no per-row typeclass inference); decide types built from the cached `leFn`. -/
def ICtx.buildWeightedSum (c : ICtx) (entries : Array (Int × Expr × Expr)) :
    MetaM (Expr × Expr) := do
  if entries.size = 0 then
    return (c.mkLit 0, iLemma `zero_self_le #[])
  let mkHead (k : Int) (term hRow : Expr) : MetaM (Expr × Expr) := do
    let kE := mkIntNum k
    let head := c.m.mkMul kE term
    let hk ← mkDecideProof (c.mkLe (mkIntNum 0) kE)
    return (head, iLemma `int_smul_nonpos #[term, kE, hRow, hk])
  let n := entries.size
  let (kₖ, termₖ, hRowₖ) := entries[n - 1]!
  let mut (sumExpr, sumProof) ← mkHead kₖ termₖ hRowₖ
  for i in [0:n-1] do
    let (k, term, hRow) := entries[n - 2 - i]!
    let (head, headProof) ← mkHead k term hRow
    sumProof := iLemma `int_add_nonpos #[head, sumExpr, headProof, sumProof]
    sumExpr := c.m.mkAdd head sumExpr
  return (sumExpr, sumProof)

/-- Optimal-branch certificate over `Int`. L=1 (the common integer-multiplier case): no goal
scaling, unscaled closer. L>1: scaled identity + scaled closer. -/
def ICtx.assembleLeProof (c : ICtx) (rows : Array Row) (strict : Bool)
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
  let CE := mkIntNum C
  let (sumExpr, sumProof) ← c.buildWeightedSum (← collectEntries rows ks)
  if Li == 1 then
    let lhsId := c.m.mkAdd (c.m.mkSub rhs lhs) sumExpr
    let identProof ← c.m.proveCertificateIdentity vars lhsId (C : Rat)
    if strict then
      let hC ← mkDecideProof (c.mkLt (mkIntNum 0) CE)
      return iLemma `lt_close #[lhs, rhs, sumExpr, CE, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (c.mkLe (mkIntNum 0) CE)
      return iLemma `le_close #[lhs, rhs, sumExpr, CE, sumProof, hC, identProof]
  let LE := mkIntNum Li
  let lhsId := c.m.mkAdd (c.m.mkMul LE (c.m.mkSub rhs lhs)) sumExpr
  let identProof ← c.m.proveCertificateIdentity vars lhsId (C : Rat)
  let hL ← mkDecideProof (c.mkLt (mkIntNum 0) LE)
  if strict then
    let hC ← mkDecideProof (c.mkLt (mkIntNum 0) CE)
    return iLemma `scaled_lt_close #[LE, lhs, rhs, sumExpr, CE, hL, sumProof, hC, identProof]
  else
    let hC ← mkDecideProof (c.mkLe (mkIntNum 0) CE)
    return iLemma `scaled_le_close #[LE, lhs, rhs, sumExpr, CE, hL, sumProof, hC, identProof]

/-- Infeasible-branch (Farkas) certificate over `Int`. -/
def ICtx.assembleInfeasibleProof (c : ICtx) (rows : Array Row) (mults : Array Rat)
    (vars : Array FVarId) (goalType : Expr) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do throwError "lp: infeasible Farkas did not cancel"
  let cVal := residual.const
  unless decide (0 < cVal) do throwError "lp: infeasible residual {cVal} not > 0"
  let (_, ks, C) ← clearMultipliers mults cVal
  let (sumExpr, sumProof) ← c.buildWeightedSum (← collectEntries rows ks)
  let identProof ← c.m.proveCertificateIdentity vars sumExpr (C : Rat)
  let hC ← mkDecideProof (c.mkLt (mkIntNum 0) (mkIntNum C))
  let hFalse := iLemma `scaled_infeasible_close #[sumExpr, mkIntNum C, sumProof, hC, identProof]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

end LP.Tactic.LP.Internal.IntC
