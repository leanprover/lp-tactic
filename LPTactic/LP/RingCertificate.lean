/-
Shared meta assembly for the computable ordered-comm-ring carriers (`Int`, `Dyadic`).

Both carriers clear SoPlex's rational Farkas multipliers to integers by a positive
scale `L`, render coefficients as native kernel-reducible literals (`Eq.refl` leaves),
and close with the scaled (`L * (rhs - lhs) + s = C`) or unscaled (`L = 1`) closers
their `declare_lp_ordered_ring_lemmas` block declares. Everything that varies per
carrier — the literal renderer, the scalar recognizer, the lemma namespace, and the
residual-representability check (`Int`: integral; `Dyadic`: power-of-two denominator)
— is injected through `mkRingCtx`; the assembly itself is written once here.
-/
module
public meta import LPTactic.LP.CarrierCertificate

public meta section

open Lean Meta

namespace LP.Tactic.LP.Internal

/-- Per-invocation context for a computable ordered-comm-ring carrier: the
`CarrierMethods` for the unified normalizer plus the cached `LE`/`LT` operator Exprs
for the O(N) sign-decide proofs, the error-message tag, and the carrier's
residual-representability check. -/
structure RingCtx where
  m    : CarrierMethods
  leFn : Expr
  ltFn : Expr
  /-- error-message tag (`"int"`, `"dyadic"`) -/
  tag : String
  /-- throw unless the cleared residual is representable in the carrier -/
  checkResidual : Rat → MetaM Unit

/-- Build the `RingCtx` for a concrete (universe-0) carrier `αName`: synthesize the
operator instances once, and wire the monomorphic lemma namespace `ns` (the
`declare_lp_ordered_ring_lemmas` block) into `applyLemma`. Leaf coefficient proofs are
bare `Eq.refl`s — the carrier's literals are kernel-reducible. -/
def mkRingCtx (αName : Name) (ns : Name) (tag : String) (mkLit : Rat → Expr)
    (scalarLit? : Expr → MetaM (Option Rat)) (checkResidual : Rat → MetaM Unit)
    (allowDiv : Bool := true) :
    MetaM RingCtx := do
  let α := mkConst αName
  let u := Level.zero
  let mk2 (cls op : Name) : MetaM Expr := do
    let inst ← synthInstance (← mkAppM cls #[α, α, α])
    return mkApp4 (mkConst op [u, u, u]) α α α inst
  let addFn ← mk2 ``HAdd ``HAdd.hAdd
  let mulFn ← mk2 ``HMul ``HMul.hMul
  let subFn ← mk2 ``HSub ``HSub.hSub
  let negFn := mkApp2 (mkConst ``Neg.neg [u]) α (← synthInstance (← mkAppM ``Neg #[α]))
  let leFn  := mkApp2 (mkConst ``LE.le [u]) α (← synthInstance (← mkAppM ``LE #[α]))
  let ltFn  := mkApp2 (mkConst ``LT.lt [u]) α (← synthInstance (← mkAppM ``LT #[α]))
  /- `@Eq.refl α t` — valid as a proof of `t = m` whenever `t ≡ m` by kernel reduction. -/
  let refl := fun (t : Expr) => mkApp2 (mkConst ``Eq.refl [Level.succ u]) α t
  let m : CarrierMethods := {
    α, addFn, mulFn, subFn, negFn, mkLit
    litAddPf := fun a b => refl (mkApp2 addFn (mkLit a) (mkLit b))
    litMulPf := fun a b => refl (mkApp2 mulFn (mkLit a) (mkLit b))
    litNegPf := fun a => refl (mkApp negFn (mkLit a))
    scalarLit?
    proveLitEq := fun e _r => pure (refl e)
    applyLemma := fun name args => mkAppN (mkConst (ns.append name)) args
    mkEqTrans := fun aE bE cE p q =>
      mkApp6 (mkConst ``Eq.trans [Level.succ u]) α aE bE cE p q
    -- `Int` floor-divides (`allowDiv := false` ⇒ `a / b` atomized); `Dyadic` has no `Div`,
    -- so the flag is moot there. Both subtract exactly (`allowSub` stays the default).
    allowDiv }
  return { m, leFn, ltFn, tag, checkResidual }

@[inline] def RingCtx.mkLe (c : RingCtx) (a b : Expr) : Expr := mkApp2 c.leFn a b
@[inline] def RingCtx.mkLt (c : RingCtx) (a b : Expr) : Expr := mkApp2 c.ltFn a b
@[inline] def RingCtx.mkLit (c : RingCtx) (r : Rat) : Expr := c.m.mkLit r

/-! ### Clearing: rational multipliers → integer `(L, kᵢ)` plus the scaled residual. -/

def RingCtx.clearMultipliers (c : RingCtx) (mults : Array Rat) (cst : Rat) :
    MetaM (Int × Array Int × Rat) := do
  let L : Nat := denLcm mults
  let Li : Int := (L : Int)
  let ks ← mults.mapM (fun lam => do
    let v := (Li : Rat) * lam
    unless v.den == 1 do throwError "lp({c.tag}): cleared multiplier {v} not integral"
    pure v.num)
  let cV := (Li : Rat) * cst
  c.checkResidual cV
  return (Li, ks, cV)

@[inline] def RingCtx.buildWeightedSum (c : RingCtx)
    (entries : Array (Rat × Expr × Expr × Option Expr)) : MetaM (Expr × Expr × Bool) :=
  buildWeightedSumDecide c.m c.leFn c.ltFn entries

/-- Optimal-branch certificate. `L = 1` (the common integer-multiplier case): no goal
scaling, unscaled closer. `L > 1`: scaled identity + scaled closer. -/
def RingCtx.assembleLeProof (c : RingCtx) (rows : Array Row) (strict : Bool)
    (objLin : LinExpr) (mults : Array Rat) (vars : Array FVarId) (lhs rhs : Expr)
    (atoms : AtomTable := {}) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual objLin rowLins mults
  unless isLinExprClosed residual do
    throwError "lp: dual certificate did not algebraically cancel the goal"
  let cVal := residual.const
  let (Li, ks, C) ← c.clearMultipliers mults cVal
  let CE := c.mkLit C
  let entries ← collectEntries rows (ks.map (fun (k : Int) => (k : Rat))) strict
  let (sumExpr, sumProof, sumStrict) ← c.buildWeightedSum entries
  -- Residual sign: a strict goal needs `0 < c`, UNLESS a strict row made the sum strict.
  if strict then
    if sumStrict then
      unless decide (0 ≤ cVal) do throwError "lp: goal not entailed; residual {cVal} not ≥ 0"
    else
      unless decide (0 < cVal) do throwError "lp: goal not entailed; residual {cVal} not > 0 {
        ""}(no strict hypothesis available to upgrade it)"
  else
    unless decide (0 ≤ cVal) do throwError "lp: goal not entailed; residual {cVal} not ≥ 0"
  if Li == 1 then
    let lhsId := c.m.mkAdd (c.m.mkSub rhs lhs) sumExpr
    let identProof ← ({ c.m with atoms }).proveCertificateIdentity vars lhsId C
    if strict then
      if sumStrict then
        let hC ← mkDecideProof (c.mkLe (c.mkLit 0) CE)
        return c.m.applyLemma `lt_close_strict #[lhs, rhs, sumExpr, CE, sumProof, hC, identProof]
      else
        let hC ← mkDecideProof (c.mkLt (c.mkLit 0) CE)
        return c.m.applyLemma `lt_close #[lhs, rhs, sumExpr, CE, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (c.mkLe (c.mkLit 0) CE)
      return c.m.applyLemma `le_close #[lhs, rhs, sumExpr, CE, sumProof, hC, identProof]
  let LE := c.mkLit (Li : Rat)
  let lhsId := c.m.mkAdd (c.m.mkMul LE (c.m.mkSub rhs lhs)) sumExpr
  let identProof ← ({ c.m with atoms }).proveCertificateIdentity vars lhsId C
  let hL ← mkDecideProof (c.mkLt (c.mkLit 0) LE)
  if strict then
    if sumStrict then
      let hC ← mkDecideProof (c.mkLe (c.mkLit 0) CE)
      return c.m.applyLemma `scaled_lt_close_strict
        #[LE, lhs, rhs, sumExpr, CE, hL, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (c.mkLt (c.mkLit 0) CE)
      return c.m.applyLemma `scaled_lt_close
        #[LE, lhs, rhs, sumExpr, CE, hL, sumProof, hC, identProof]
  else
    let hC ← mkDecideProof (c.mkLe (c.mkLit 0) CE)
    return c.m.applyLemma `scaled_le_close
      #[LE, lhs, rhs, sumExpr, CE, hL, sumProof, hC, identProof]

/-- Infeasible-branch (Farkas) certificate. -/
def RingCtx.assembleInfeasibleProof (c : RingCtx) (rows : Array Row) (mults : Array Rat)
    (vars : Array FVarId) (goalType : Expr) (atoms : AtomTable := {}) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do throwError "lp: infeasible Farkas did not cancel"
  let cVal := residual.const
  let (_, ks, C) ← c.clearMultipliers mults cVal
  let entries ← collectEntries rows (ks.map (fun (k : Int) => (k : Rat))) true
  let (sumExpr, sumProof, sumStrict) ← c.buildWeightedSum entries
  if sumStrict then
    unless decide (0 ≤ cVal) do throwError "lp: infeasible residual {cVal} not ≥ 0"
  else
    unless decide (0 < cVal) do throwError "lp: infeasible residual {cVal} not > 0"
  let identProof ← ({ c.m with atoms }).proveCertificateIdentity vars sumExpr C
  let CE := c.mkLit C
  let hFalse ←
    if sumStrict then
      let hC ← mkDecideProof (c.mkLe (c.mkLit 0) CE)
      pure <| c.m.applyLemma `scaled_infeasible_close_strict #[sumExpr, CE, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (c.mkLt (c.mkLit 0) CE)
      pure <| c.m.applyLemma `scaled_infeasible_close #[sumExpr, CE, sumProof, hC, identProof]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

end LP.Tactic.LP.Internal
