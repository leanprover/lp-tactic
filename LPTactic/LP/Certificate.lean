module
public import LPTactic.LP.Problem

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-! ## Tactic-side proof assembly: the `Rat` carrier.

This file holds the `Rat`-specific strategy for the unified certificate engine
(`CarrierCertificate.lean`): coefficients render as kernel-reducible `Q.toRat`
literals, numeral-leaf proofs go through the `ratlit_*` mini-`norm_num` with
`Eq.refl` side conditions, and the assembly closes with the unscaled
`direct_*_close` lemmas (rational multipliers, no integer clearing). The structural
normalizer itself is the shared `CarrierMethods.normalizeR`. -/

def ratList (xs : Array Rat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map (toString ·)) ++ "]"

/-! ## Cached `Rat`-arithmetic operator templates.

The proof-term construction renders `Rat` operators O(N²) times per certificate.
Pre-built fully-applied instance Exprs avoid repeated typeclass inference for
`HAdd`/`HMul`/`HSub`/`Neg` in this hot path; they are constant Exprs with no
metavariables and are used via raw `mkApp2`/`mkApp`. -/

/-- `@HAdd.hAdd Rat Rat Rat instHAdd_Rat_Rat_Rat` — partially-applied,
takes the two `Rat` arguments. -/
def addRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHAdd [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instAdd)
  mkApp4 (mkConst ``HAdd.hAdd [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@HMul.hMul Rat Rat Rat _` partially applied. -/
def mulRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHMul [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instMul)
  mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@HSub.hSub Rat Rat Rat _` partially applied. -/
def subRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHSub [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instSub)
  mkApp4 (mkConst ``HSub.hSub [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- `@Neg.neg Rat Rat.instNeg` partially applied. -/
def negRatFn : Expr :=
  mkApp2 (mkConst ``Neg.neg [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instNeg)

/-- The standing proof `Nat.one_ne_zero : (1 : Nat) ≠ 0`, used as the
denominator-nonzero proof for every integer-denominator `Q` payload. -/
def den1NeZeroProof : Expr := mkConst ``Nat.one_ne_zero

/-- Emit a `Q.mk num den den_ne` Expr for the `Rat` value `r`. For the
overwhelmingly common `r.den = 1` case (integer coefficients) we use the
cached `Nat.one_ne_zero` proof; otherwise `Nat.succ_ne_zero (den - 1)`,
which typechecks against `den ≠ 0` by kernel literal reduction (`Rat`
guarantees `den ≠ 0`). Pure, so the engine's `mkLit` can call it. -/
def mkQLit (r : Rat) : Expr :=
  let numE : Expr := match r.num with
    | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkNatLit k)
    | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkNatLit k)
  let denE : Expr := mkNatLit r.den
  let denNeProof :=
    if r.den == 1 then den1NeZeroProof
    else mkApp (mkConst ``Nat.succ_ne_zero) (mkNatLit (r.den - 1))
  mkApp3 (mkConst ``LP.Tactic.Q.mk) numE denE denNeProof

/-- Build a `Rat` literal Expr.  We emit a `Q.toRat`-normalized form so
that the explicit-proof-term discharger can apply `Q.toRat_add`/
`toRat_mul`/`toRat_neg` without bridging through `Rat.div`-form
literals. -/
def mkRatLit (r : Rat) : Expr :=
  mkApp (mkConst ``LP.Tactic.Q.toRat) (mkQLit r)

/-- Compute the numerical residual `c = (rhs - lhs) + Σ λᵢ * eᵢ`
expressed as a `LinExpr`. The caller verifies that the variable
coefficients all vanish; what remains is the closed `Rat` constant
that gets fed to `decide` for the sign check and to
`proveCertificateIdentity` for the algebraic identity proof. -/
def computeResidual (objLin : LinExpr) (rowLins : Array LinExpr)
    (mults : Array Rat) : LinExpr := Id.run do
  -- Fused accumulation: one `FVarId`-keyed map over all nonzero multipliers,
  -- instead of a `LinExpr.add` fold that rescans the accumulated coefficients
  -- per row (`O(m · n²)` on dense problems). Coefficient order in the result is
  -- irrelevant: callers only check closedness and read the constant.
  let mut const := objLin.const
  let mut acc : Std.HashMap FVarId Rat := .emptyWithCapacity (2 * objLin.coeffs.size)
  for (v, c) in objLin.coeffs do
    acc := acc.insert v (acc.getD v 0 + c)
  for h : i in [0:rowLins.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      const := const + lam * rowLins[i].const
      for (v, c) in rowLins[i].coeffs do
        acc := acc.insert v (acc.getD v 0 + lam * c)
  let mut coeffs : Array (FVarId × Rat) := Array.mkEmpty acc.size
  for (v, c) in acc do
    if c != 0 then coeffs := coeffs.push (v, c)
  return { const, coeffs }

def isLinExprClosed (e : LinExpr) : Bool :=
  e.coeffs.all (fun (_, c) => c == 0)

/-- Position of `v` in the invocation's fixed variable order, looked up in the
`mkVarIdx` map built once per invocation (the old `vars.idxOf?` rescanned the
array inside every merge comparison). The caller guarantees membership; on
lookup failure we return `vidx.size` so the result is still a valid total
order (the unknown atom sorts last). -/
def varIdx (vidx : VarIdx) (v : FVarId) : Nat :=
  vidx.getD v vidx.size

/-- Weighted-sum entries `(λ, term, leProof, strictProof?)` for the nonzero
multipliers, in iteration order. A strict row contributes its `term < 0`
proof when `wantStrict` (strict goals / infeasibility), so a positive
multiplier on it can upgrade the Farkas sum from `≤ 0` to `< 0`. Shared by
the `Rat`, ring (`Int`/`Dyadic`), and field assemblies. -/
def collectEntries (rows : Array Row) (mults : Array Rat) (wantStrict : Bool) :
    MetaM (Array (Rat × Expr × Expr × Option Expr)) := do
  let mut entries : Array (Rat × Expr × Expr × Option Expr) := #[]
  for h : i in [0:rows.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      let sp? ← if wantStrict && rows[i].strict then pure (some (← rows[i].strictProof))
                else pure none
      entries := entries.push (lam, ← rows[i].term, ← rows[i].proof, sp?)
  return entries

/-! ### Cached side-condition templates for the numeral leaves.

The `ratlit_{add,mul,neg}` leaf proofs are emitted O(N²) times per certificate.
Each leaf needs the same side-condition shape, such as
`(Q.add qa qb).num * (qm.den : Int) = …`. We compute that template just
once per process, keyed in an `IO.Ref`, and instantiate `qa`/`qb`/`qm`
per leaf. -/

initialize ratlitAddDomainRef : IO.Ref (Option Expr) ← IO.mkRef none
initialize ratlitMulDomainRef : IO.Ref (Option Expr) ← IO.mkRef none
initialize ratlitNegDomainRef : IO.Ref (Option Expr) ← IO.mkRef none

/-- Walk past `n` `Pi` binders and return the body. -/
def stripForalls (n : Nat) (e : Expr) : Expr :=
  match n with
  | 0 => e
  | n + 1 => stripForalls n e.bindingBody!

/-- Compute / fetch the cached side-condition template of `ratlit_add`,
i.e. the type of its 4th explicit argument with the first three
arguments left as bvars `#2, #1, #0` (referring to `qa, qb, qm`). -/
def getRatlitAddDomain : MetaM Expr := do
  if let some t ← ratlitAddDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_add)
  -- typ : ∀ qa qb qm, hType → conclusion
  let body3 := stripForalls 3 typ
  let dom := body3.bindingDomain!
  ratlitAddDomainRef.set (some dom)
  return dom

def getRatlitMulDomain : MetaM Expr := do
  if let some t ← ratlitMulDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_mul)
  let dom := (stripForalls 3 typ).bindingDomain!
  ratlitMulDomainRef.set (some dom)
  return dom

def getRatlitNegDomain : MetaM Expr := do
  if let some t ← ratlitNegDomainRef.get then return t
  let typ ← inferType (mkConst ``ratlit_neg)
  let dom := (stripForalls 2 typ).bindingDomain!
  ratlitNegDomainRef.set (some dom)
  return dom

/-- Build an `Eq.refl`-shaped proof of a closed `Int` literal equality.
The two sides are kernel-reducible to the same numeric value (this is
what makes the leaf valid in the first place), so `Eq.refl LHS` typechecks
where `LHS = RHS` is expected — moving the literal arithmetic work from
the tactic-side `mkDecideProof` into a single kernel reduction. -/
def mkEqReflProof (hType : Expr) : Expr :=
  -- hType has shape `@Eq Int LHS RHS`; extract LHS and emit `Eq.refl LHS`.
  let lhs := hType.appFn!.appArg!
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Int) lhs

end LP.Tactic.LP.Internal
