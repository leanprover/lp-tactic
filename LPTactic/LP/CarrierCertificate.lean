/-
Carrier-parametrized certificate normalizer for the `lp` tactic — the unified engine
shared by the `Int` (native-literal) and field/`ℝ` (`ofRat`) carriers. Written ONCE against
a `CarrierMethods` record (named per Lean core precedent: `Simp.Methods`/`Grind.Methods`),
which bundles the per-carrier-class varying pieces: cached operator Exprs, the coefficient
renderer, leaf-arithmetic proofs, the scalar recognizer / literal bridge, and a fixed-arity
lemma applier (namespace + universe levels + instance-prefix baked in).

The structural walk (`normalizeR`/`proveMerge`/`proveSmul`/`proveNeg`/`render`/spine/
`buildWeightedSum`) is identical across carriers and lives here. The thin per-carrier ASSEMBLY
(clearing/closers/dispatch) stays explicit in the carrier modules (Codex: keep dispatch
explicit, share only the skeleton). NO tactic calls on the hot path; uses `quickScalarLit?`
(never the O(N²) recursive `parseScalar?`) — the lesson banked from the Int prototype.
-/
module
public meta import LPTactic.LP.Certificate

public meta section

open Lean Meta

namespace LP.Tactic.LP.Internal

/-- The per-carrier strategy bundle parametrizing the shared normalizer. Built once per `lp`
invocation (carrier `α` is fixed), so its closures cache the synthesized instances. -/
structure CarrierMethods where
  /-- the carrier type `α` -/
  α : Expr
  /-- pre-applied carrier operators `@HAdd.hAdd α α α _` etc. (de-typeclassed hot path) -/
  addFn : Expr
  mulFn : Expr
  subFn : Expr
  negFn : Expr
  /-- render a rational coefficient as its carrier literal (`Int.ofNat`/`ofRat`/…) -/
  mkLit : Rat → Expr
  /-- leaf proof `mkLit a + mkLit b = mkLit (a+b)` (pure; `Eq.refl` for `Int`, `ofRat_add` for fields) -/
  litAddPf : Rat → Rat → Expr
  /-- leaf proof `mkLit a * mkLit b = mkLit (a*b)` -/
  litMulPf : Rat → Rat → Expr
  /-- leaf proof `-(mkLit a) = mkLit (-a)` -/
  litNegPf : Rat → Expr
  /-- recognize a carrier scalar Expr's rational value (carrier peel + `quickScalarLit?`) -/
  scalarLit? : Expr → MetaM (Option Rat)
  /-- proof `e = mkLit r` for a user scalar Expr `e` of value `r` (`Eq.refl` for `Int`, bridge for fields) -/
  proveLitEq : Expr → Rat → MetaM Expr
  /-- apply a normalizer fixed-arity lemma by base name (namespace/levels/instance-prefix baked in) -/
  applyLemma : Name → Array Expr → Expr
  /-- `Eq.trans` for the carrier, no `isDefEq` middle-term unification -/
  mkEqTrans : Expr → Expr → Expr → Expr → Expr → Expr
  /-- Atomization table: maps each LP variable key back to its `Expr` (a real `fvar`
  for ordinary atoms, or the stored opaque-atom `Expr` for a virtual fvar). Injected by
  the atomic path; empty for the binder frontends. -/
  atoms : AtomTable := {}

namespace CarrierMethods

@[inline] def mkAdd (m : CarrierMethods) (a b : Expr) : Expr := mkApp2 m.addFn a b
@[inline] def mkMul (m : CarrierMethods) (a b : Expr) : Expr := mkApp2 m.mulFn a b
@[inline] def mkSub (m : CarrierMethods) (a b : Expr) : Expr := mkApp2 m.subFn a b
@[inline] def mkNeg (m : CarrierMethods) (a : Expr) : Expr := mkApp m.negFn a

/-- Render a sorted `LinExpr` to `c₀*x₀ + (… + const)`. -/
def render (m : CarrierMethods) (L : LinExpr) : Expr := Id.run do
  let mut acc := m.mkLit L.const
  for i in [0:L.coeffs.size] do
    let idx := L.coeffs.size - 1 - i
    let (v, coef) := L.coeffs[idx]!
    acc := m.mkAdd (m.mkMul (m.mkLit coef) (m.atoms.keyToExpr v)) acc
  return acc

/-- Normalize an opaque atom subterm `e`: look up the virtual LP variable the parser
assigned it and emit `e = 1*v + 0` via `atom_norm`. Errors cleanly if `e` was not atomized. -/
def normalizeAtom (m : CarrierMethods) (e : Expr) : MetaM (LinExpr × Expr × Expr) := do
  let some a ← canonAtom e
    | throwError "lp: unsupported expression{indentExpr e}"
  let some v := m.atoms.atomToFVar[a]?
    | throwError "lp: atom not registered during parsing{indentExpr e}"
  let L : LinExpr := {coeffs := #[(v, 1)]}
  return (L, m.applyLemma `atom_norm #[e], m.render L)

/-- Precompute heads `cₖ*xₖ`, coefficient Exprs, and shared suffix renderings. -/
def precomputeSpine (m : CarrierMethods) (L : LinExpr) :
    Array Expr × Array Expr × Array Expr := Id.run do
  let n := L.coeffs.size
  let mut heads : Array Expr := Array.mkEmpty n
  let mut qs : Array Expr := Array.mkEmpty n
  for k in [0:n] do
    let (v, coef) := L.coeffs[k]!
    let qE := m.mkLit coef
    qs := qs.push qE
    heads := heads.push (m.mkMul qE (m.atoms.keyToExpr v))
  let mut suffix : Array Expr := Array.mkEmpty (n + 1)
  suffix := suffix.push (m.mkLit L.const)
  for _ in [0:n] do
    let idx := suffix.size
    let cur := suffix[suffix.size - 1]!
    let h := heads[n - idx]!
    suffix := suffix.push (m.mkAdd h cur)
  return (heads, qs, suffix.reverse)

/-- Linear ordered merge `⟦La⟧ + ⟦Lb⟧ = ⟦L⟧`; returns rendered `⟦L⟧` too (no re-render). -/
partial def proveMerge (m : CarrierMethods) (vars : Array FVarId) (La Lb : LinExpr) :
    MetaM (LinExpr × Expr × Expr) := do
  let (headA, qA, suffA) := m.precomputeSpine La
  let (headB, qB, suffB) := m.precomputeSpine Lb
  go headA qA suffA headB qB suffB 0 0
where
  go (headA qA suffA headB qB suffB : Array Expr) (i j : Nat) :
      MetaM (LinExpr × Expr × Expr) := do
    let aDone := i ≥ La.coeffs.size
    let bDone := j ≥ Lb.coeffs.size
    if aDone && bDone then
      let mVal := La.const + Lb.const
      return ({const := mVal}, m.litAddPf La.const Lb.const, m.mkLit mVal)
    if aDone then
      let (vB, cB) := Lb.coeffs[j]!
      let h := headB[j]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB i (j+1)
      let aE := suffA[i]!; let tbE := suffB[j+1]!
      let resE := m.mkAdd h resPrev
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs },
        m.applyLemma `take_right #[aE, h, tbE, resPrev, pRest], resE)
    if bDone then
      let (vA, cA) := La.coeffs[i]!
      let h := headA[i]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB (i+1) j
      let taE := suffA[i+1]!; let bE := suffB[j]!
      let resE := m.mkAdd h resPrev
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs },
        m.applyLemma `take_left #[h, taE, bE, resPrev, pRest], resE)
    let (vA, cA) := La.coeffs[i]!
    let (vB, cB) := Lb.coeffs[j]!
    let iA := varIdx vars vA
    let iB := varIdx vars vB
    if iA > iB then
      let h := headA[i]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB (i+1) j
      let taE := suffA[i+1]!; let bE := suffB[j]!
      let resE := m.mkAdd h resPrev
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs },
        m.applyLemma `take_left #[h, taE, bE, resPrev, pRest], resE)
    else if iA < iB then
      let h := headB[j]!
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB i (j+1)
      let aE := suffA[i]!; let tbE := suffB[j+1]!
      let resE := m.mkAdd h resPrev
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs },
        m.applyLemma `take_right #[aE, h, tbE, resPrev, pRest], resE)
    else
      let mVal := cA + cB
      let mE := m.mkLit mVal
      let hm := m.litAddPf cA cB
      let xE := m.atoms.keyToExpr vA
      let (restL, pRest, resPrev) ← go headA qA suffA headB qB suffB (i+1) (j+1)
      let taE := suffA[i+1]!; let tbE := suffB[j+1]!
      let cAE := qA[i]!; let cBE := qB[j]!
      if mVal == 0 then
        -- `hm : cAE + cBE = mkLit 0`; each carrier's `combine_zero` accepts this shape
        -- (`Int`: `mkLit 0 ≡ (0:Int)` by defeq; fields: stated with `= ofRat 0`).
        return (restL,
          m.applyLemma `combine_zero #[xE, taE, tbE, resPrev, cAE, cBE, pRest, hm], resPrev)
      else
        let resE := m.mkAdd (m.mkMul mE xE) resPrev
        return ({ restL with coeffs := #[(vA, mVal)] ++ restL.coeffs },
          m.applyLemma `combine #[xE, taE, tbE, resPrev, cAE, cBE, mE, pRest, hm], resE)

/-- Scale a sorted `LinExpr` by `k`: `k * ⟦La⟧ = ⟦L⟧`. -/
partial def proveSmul (m : CarrierMethods) (kE : Expr) (kVal : Rat) (La : LinExpr) :
    MetaM (LinExpr × Expr × Expr) := do
  let (_, qA, suffA) := m.precomputeSpine La
  go qA suffA 0
where
  go (qA suffA : Array Expr) (i : Nat) : MetaM (LinExpr × Expr × Expr) := do
    if i ≥ La.coeffs.size then
      let mVal := kVal * La.const
      return ({const := mVal}, m.litMulPf kVal La.const, m.mkLit mVal)
    let (v, coef) := La.coeffs[i]!
    let mVal := kVal * coef
    let mE := m.mkLit mVal
    let hm := m.litMulPf kVal coef
    let xE := m.atoms.keyToExpr v
    let (restL, pRest, resPrev) ← go qA suffA (i+1)
    let cE := qA[i]!; let restE := suffA[i+1]!
    let pf := m.applyLemma `smul_cons #[kE, xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal == 0 then
      return (restL, pf, resPrev)
    else
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf,
        m.mkAdd (m.mkMul mE xE) resPrev)

/-- Negate a sorted `LinExpr`: `-⟦La⟧ = ⟦L⟧`. -/
partial def proveNeg (m : CarrierMethods) (La : LinExpr) : MetaM (LinExpr × Expr × Expr) := do
  let (_, qA, suffA) := m.precomputeSpine La
  go qA suffA 0
where
  go (qA suffA : Array Expr) (i : Nat) : MetaM (LinExpr × Expr × Expr) := do
    if i ≥ La.coeffs.size then
      let mVal := -La.const
      return ({const := mVal}, m.litNegPf La.const, m.mkLit mVal)
    let (v, coef) := La.coeffs[i]!
    let mVal := -coef
    let mE := m.mkLit mVal
    let hm := m.litNegPf coef
    let xE := m.atoms.keyToExpr v
    let (restL, pRest, resPrev) ← go qA suffA (i+1)
    let cE := qA[i]!; let restE := suffA[i+1]!
    let pf := m.applyLemma `neg_cons #[xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal == 0 then
      return (restL, pf, resPrev)
    else
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf,
        m.mkAdd (m.mkMul mE xE) resPrev)

/-- Structural normalizer: `(L, pf : e = ⟦L⟧, ⟦L⟧)`. -/
partial def normalizeR (m : CarrierMethods) (vars : Array FVarId) (e : Expr) :
    MetaM (LinExpr × Expr × Expr) := do
  if let some r ← m.scalarLit? e then
    return ({const := r}, ← m.proveLitEq e r, m.mkLit r)
  match e with
  | .fvar id =>
      let L : LinExpr := {coeffs := #[(id, 1)]}
      return (L, m.applyLemma `atom_norm #[e], m.render L)
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          let aE := args[4]!; let bE := args[5]!
          let (La, pa, rA) ← m.normalizeR vars aE
          let (Lb, pb, rB) ← m.normalizeR vars bE
          let step1 := m.applyLemma `add_congr_eq #[aE, rA, bE, rB, pa, pb]
          let (L, pm, rL) ← m.proveMerge vars La Lb
          return (L, m.mkEqTrans e (m.mkAdd rA rB) rL step1 pm, rL)
      | .const ``HSub.hSub _ =>
          let aE := args[4]!; let bE := args[5]!
          let (La, pa, rA) ← m.normalizeR vars aE
          let (Lb, pb, rB) ← m.normalizeR vars bE
          let (Lnb, pn, rLnb) ← m.proveNeg Lb
          let (L, pm, rL) ← m.proveMerge vars La Lnb
          let negBExpr := m.mkNeg bE
          let negRB := m.mkNeg rB
          let midSub := m.mkAdd aE negBExpr
          let midAdd := m.mkAdd rA rLnb
          let step1 := m.applyLemma `sub_to_add_neg #[aE, bE]
          let stepNeg := m.applyLemma `neg_congr_eq #[bE, rB, pb]
          let stepNegFull := m.mkEqTrans negBExpr negRB rLnb stepNeg pn
          let step2 := m.applyLemma `add_congr_eq #[aE, rA, negBExpr, rLnb, pa, stepNegFull]
          let chained1 := m.mkEqTrans e midSub midAdd step1 step2
          return (L, m.mkEqTrans e midAdd rL chained1 pm, rL)
      | .const ``Neg.neg _ =>
          let aE := args[2]!
          if aE.isFVar then
            let L : LinExpr := {coeffs := #[(aE.fvarId!, -1)]}
            return (L, m.applyLemma `neg_atom_norm #[aE], m.render L)
          let (La, pa, rA) ← m.normalizeR vars aE
          let (L, pn, rL) ← m.proveNeg La
          let step1 := m.applyLemma `neg_congr_eq #[aE, rA, pa]
          return (L, m.mkEqTrans e (m.mkNeg rA) rL step1 pn, rL)
      | .const ``HMul.hMul _ =>
          let lhsE := args[4]!; let rhsE := args[5]!
          if let some kVal ← m.scalarLit? lhsE then
            if kVal != 0 && rhsE.isFVar then
              let L : LinExpr := {coeffs := #[(rhsE.fvarId!, kVal)]}
              let coefE := m.mkLit kVal
              let hKEq ← m.proveLitEq lhsE kVal
              let step1 := m.applyLemma `mul_congr_eq_l #[lhsE, coefE, rhsE, hKEq]
              let rL := m.render L
              let step2 := m.applyLemma `mul_atom_norm #[coefE, rhsE]
              return (L, m.mkEqTrans e (m.mkMul coefE rhsE) rL step1 step2, rL)
            let coefE := m.mkLit kVal
            let hKEq ← m.proveLitEq lhsE kVal
            let (Lr, pr, rLr) ← m.normalizeR vars rhsE
            let (L, ps, rL) ← m.proveSmul coefE kVal Lr
            let step1 := m.applyLemma `mul_congr_eq_l #[lhsE, coefE, rhsE, hKEq]
            let stepR := m.applyLemma `mul_congr_eq_r #[coefE, rhsE, rLr, pr]
            let mid1 := m.mkMul coefE rhsE
            let mid2 := m.mkMul coefE rLr
            return (L, m.mkEqTrans e mid1 rL step1 (m.mkEqTrans mid1 mid2 rL stepR ps), rL)
          else if let some kVal ← m.scalarLit? rhsE then
            let coefE := m.mkLit kVal
            let hKEq ← m.proveLitEq rhsE kVal
            let (Lr, pr, rLr) ← m.normalizeR vars lhsE
            let (L, ps, rL) ← m.proveSmul coefE kVal Lr
            let stepRc := m.applyLemma `mul_congr_eq_r #[lhsE, rhsE, coefE, hKEq]
            let mulComm ← mkAppM ``Lean.Grind.CommSemiring.mul_comm #[lhsE, coefE]
            let stepR := m.applyLemma `mul_congr_eq_r #[coefE, lhsE, rLr, pr]
            let m1 := m.mkMul lhsE coefE
            let m2 := m.mkMul coefE lhsE
            let m3 := m.mkMul coefE rLr
            return (L, m.mkEqTrans e m1 rL stepRc
              (m.mkEqTrans m1 m2 rL mulComm (m.mkEqTrans m2 m3 rL stepR ps)), rL)
          else
            m.normalizeAtom e
      | .const ``HDiv.hDiv _ =>
          let dividend := args[4]!; let divisor := args[5]!
          -- `e / c = c⁻¹ * e` (true even at `c = 0`); recurse through the scalar-mul
          -- path, which recognises the closed inverse `c⁻¹` as the scalar `1/c`.
          if let some cVal ← m.scalarLit? divisor then
            if cVal == 0 then
              throwError "lp: division by the zero constant{indentExpr e}"
            let invE ← mkAppM ``Inv.inv #[divisor]
            let mulE := m.mkMul invE dividend
            let (L, pInner, rL) ← m.normalizeR vars mulE
            let pDiv := m.applyLemma `div_eq_inv_mul #[dividend, divisor]
            return (L, m.mkEqTrans e mulE rL pDiv pInner, rL)
          m.normalizeAtom e
      | _ => m.normalizeAtom e

/-- Normalize `lhsId` and check it cancels to the constant `cVal` (as a `Rat`). -/
def proveCertificateIdentity (m : CarrierMethods) (vars : Array FVarId) (lhsId : Expr)
    (cVal : Rat) : MetaM Expr := do
  let (L, pfNorm, _) ← m.normalizeR vars lhsId
  unless L.const == cVal do
    throwError "lp: normalized constant {L.const} ≠ residual {cVal}"
  unless L.coeffs.isEmpty do
    throwError "lp: {L.coeffs.size} surviving atom(s) after normalization"
  return pfNorm

end CarrierMethods

end LP.Tactic.LP.Internal
