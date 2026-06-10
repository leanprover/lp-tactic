/-
`Nat` carrier instance for the unified engine. `Nat` is an ordered comm SEMIRING (no
negation), so the assembly is the no-subtraction Farkas: a two-sided weighted hypothesis sum
`Wl ≤ Wr` (`Wl = Σkᵢ·lhsᵢ`, `Wr = Σkᵢ·rhsᵢ`) plus the semiring IDENTITY `L·rhs + Wl =
L·lhs + Wr + C`, closed by add/mul-cancellation (`NatGeneric`). The unified `normalizeR` proves
the identity (both sides → same sorted form); native `Nat` literals give `Eq.refl` leaves.
-/
module
public meta import LPTactic.LP.CarrierCertificate
public import LPTactic.LP.NatGeneric

public meta section

open Lean Meta

namespace LP.Tactic.LP.Internal.NatC

/-- Render a nonneg integer-valued `Rat` as a raw `Nat` literal (defeq to `OfNat`). -/
def mkNatNum (r : Rat) : Expr := mkRawNatLit r.num.toNat

@[inline] def natRefl (t : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) t

partial def natScalarLit? (e : Expr) : MetaM (Option Rat) := do
  match e with
  | .lit (.natVal n) => return some (n : Rat)
  | _ => quickScalarLit? e

@[inline] def nLemma (name : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst ((`LP.Tactic.LP.Internal.NatC).append name)) args

structure NCtx where
  m    : CarrierMethods
  leFn : Expr
  ltFn : Expr

def mkNCtx : MetaM NCtx := do
  let nat := mkConst ``Nat
  let u := Level.zero
  let mk2 (cls op : Name) : MetaM Expr := do
    let inst ← synthInstance (← mkAppM cls #[nat, nat, nat])
    return mkApp4 (mkConst op [u, u, u]) nat nat nat inst
  let addFn ← mk2 ``HAdd ``HAdd.hAdd
  let mulFn ← mk2 ``HMul ``HMul.hMul
  let subFn ← mk2 ``HSub ``HSub.hSub   -- `Nat.sub`; never used (no sub in Nat certificate exprs)
  let leFn  := mkApp2 (mkConst ``LE.le [u]) nat (← synthInstance (← mkAppM ``LE #[nat]))
  let ltFn  := mkApp2 (mkConst ``LT.lt [u]) nat (← synthInstance (← mkAppM ``LT #[nat]))
  let m : CarrierMethods := {
    α := nat, addFn, mulFn, subFn, negFn := addFn /- placeholder; `Nat` has no `Neg`, unused -/
    mkLit := mkNatNum
    litAddPf := fun a b => natRefl (mkApp2 addFn (mkNatNum a) (mkNatNum b))
    litMulPf := fun a b => natRefl (mkApp2 mulFn (mkNatNum a) (mkNatNum b))
    litNegPf := fun _ => mkConst ``True.intro  -- never called (no neg)
    scalarLit? := natScalarLit?
    proveLitEq := fun e _r => pure (natRefl e)
    applyLemma := nLemma
    mkEqTrans := fun aE bE cE p q =>
      mkApp6 (mkConst ``Eq.trans [Level.succ Level.zero]) nat aE bE cE p q }
  return { m, leFn, ltFn }

@[inline] def NCtx.mkLe (c : NCtx) (a b : Expr) : Expr := mkApp2 c.leFn a b
@[inline] def NCtx.mkLt (c : NCtx) (a b : Expr) : Expr := mkApp2 c.ltFn a b

/-- Clearing for `Nat`: nonneg integer multipliers `kᵢ` and residual `C`. -/
def clearMultipliers (mults : Array Rat) (cst : Rat) : MetaM (Nat × Array Nat × Nat) := do
  let L : Nat := denLcm mults
  let Li : Rat := (L : Int)
  let ks ← mults.mapM (fun lam => do
    let v := Li * lam
    unless v.den == 1 && v.num ≥ 0 do throwError "lp(nat): cleared multiplier {v} not a Nat"
    pure v.num.toNat)
  let cV := Li * cst
  unless cV.den == 1 && cV.num ≥ 0 do throwError "lp(nat): residual {cV} not a Nat"
  return (L, ks, cV.num.toNat)

/-- `(kᵢ, lhsExprᵢ, rhsExprᵢ, leProofᵢ : lhsᵢ ≤ rhsᵢ)` for the nonzero multipliers. -/
def collectEntries (rows : Array Row) (ks : Array Nat) :
    MetaM (Array (Nat × Expr × Expr × Expr)) := do
  let mut entries := #[]
  for h : i in [0:rows.size] do
    let k := ks[i]!
    if k ≠ 0 then
      entries := entries.push (k, rows[i].lhsExpr, rows[i].rhsExpr, ← rows[i].leProof)
  return entries

/-- Two-sided weighted sum: `(Wl, Wr, hW : Wl ≤ Wr)` with `Wl = Σkᵢ·lhsᵢ`, `Wr = Σkᵢ·rhsᵢ`. -/
def NCtx.buildWeightedSum (c : NCtx) (entries : Array (Nat × Expr × Expr × Expr)) :
    MetaM (Expr × Expr × Expr) := do
  if entries.size = 0 then
    return (mkNatNum 0, mkNatNum 0, nLemma `zero_self_le #[])
  let mkHead (k : Nat) (lhsE rhsE leP : Expr) : Expr × Expr × Expr :=
    let kE := mkNatNum (k : Rat)
    (c.m.mkMul kE lhsE, c.m.mkMul kE rhsE, nLemma `nat_nsmul_le #[kE, lhsE, rhsE, leP])
  let n := entries.size
  let (kₖ, lₖ, rₖ, pₖ) := entries[n - 1]!
  let mut (Wl, Wr, hW) := mkHead kₖ lₖ rₖ pₖ
  for i in [0:n-1] do
    let (k, lE, rE, p) := entries[n - 2 - i]!
    let (hl, hr, hp) := mkHead k lE rE p
    hW := nLemma `nat_add_le #[hl, hr, Wl, Wr, hp, hW]
    Wl := c.m.mkAdd hl Wl
    Wr := c.m.mkAdd hr Wr
  return (Wl, Wr, hW)

/-- Prove `aExpr = bExpr` by normalizing both to the same sorted form. -/
def NCtx.proveEq (c : NCtx) (vars : Array FVarId) (aExpr bExpr : Expr) : MetaM Expr := do
  let vidx := mkVarIdx vars
  let (La, pa, _) ← c.m.normalizeR vidx aExpr
  let (Lb, pb, _) ← c.m.normalizeR vidx bExpr
  unless La.const == Lb.const && La.coeffs == Lb.coeffs do
    throwError "lp(nat): identity sides disagree after normalization"
  -- pa : aExpr = ⟦La⟧, pb : bExpr = ⟦La⟧  ⇒  aExpr = bExpr
  let rL := c.m.render La
  pure <| c.m.mkEqTrans aExpr rL bExpr pa
    (mkApp4 (mkConst ``Eq.symm [Level.succ Level.zero]) (mkConst ``Nat) bExpr rL pb)

/-- Optimal-branch certificate over `Nat`. -/
def NCtx.assembleLeProof (c : NCtx) (rows : Array Row) (strict : Bool)
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
  let (L, ks, C) ← clearMultipliers mults cVal
  let CE := mkNatNum (C : Rat)
  let (Wl, Wr, hW) ← c.buildWeightedSum (← collectEntries rows ks)
  -- identity LHS = L·rhs + Wl,  RHS = L·lhs + Wr + C  (drop `L·` when L = 1, so the no-scale
  -- closer's `rhs`/`lhs` match — `1 * x` does NOT reduce to `x` for a variable `x`).
  let scale (e : Expr) : Expr := if L == 1 then e else c.m.mkMul (mkNatNum (L : Rat)) e
  let lhsId := c.m.mkAdd (scale rhs) Wl
  let rhsId := c.m.mkAdd (c.m.mkAdd (scale lhs) Wr) CE
  let hId ← c.proveEq vars lhsId rhsId
  if L == 1 then
    if strict then
      let hC ← mkDecideProof (c.mkLt (mkNatNum 0) CE)
      return nLemma `lt_close #[lhs, rhs, Wl, Wr, CE, hW, hC, hId]
    else
      return nLemma `le_close #[lhs, rhs, Wl, Wr, CE, hW, hId]
  let LE := mkNatNum (L : Rat)
  let hL ← mkDecideProof (c.mkLt (mkNatNum 0) LE)
  if strict then
    let hC ← mkDecideProof (c.mkLt (mkNatNum 0) CE)
    return nLemma `scaled_lt_close #[LE, lhs, rhs, Wl, Wr, CE, hL, hW, hC, hId]
  else
    return nLemma `scaled_le_close #[LE, lhs, rhs, Wl, Wr, CE, hL, hW, hId]

/-- Infeasible-branch (Farkas) certificate over `Nat`: `Wl ≤ Wr` but `Wl = Wr + C`, `C > 0`. -/
def NCtx.assembleInfeasibleProof (c : NCtx) (rows : Array Row) (mults : Array Rat)
    (vars : Array FVarId) (goalType : Expr) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do throwError "lp: infeasible Farkas did not cancel"
  let cVal := residual.const
  unless decide (0 < cVal) do throwError "lp: infeasible residual {cVal} not > 0"
  let (_, ks, C) ← clearMultipliers mults cVal
  let CE := mkNatNum (C : Rat)
  let (Wl, Wr, hW) ← c.buildWeightedSum (← collectEntries rows ks)
  let hId ← c.proveEq vars Wl (c.m.mkAdd Wr CE)   -- Wl = Wr + C
  let hC ← mkDecideProof (c.mkLt (mkNatNum 0) CE)
  let hFalse := nLemma `infeasible_close #[Wl, Wr, CE, hW, hC, hId]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

end LP.Tactic.LP.Internal.NatC
