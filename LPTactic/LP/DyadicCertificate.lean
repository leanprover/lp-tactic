/-
`Dyadic` carrier instance for the unified certificate engine: native kernel-reducible
literals via `Dyadic.ofInt`/`ofIntWithPrec` (integer and power-of-two coefficients; never
division — dyadics have no `/`), with the cleared residual checked to be dyadic. The whole
assembly is the shared ordered-ring one in `RingCertificate.lean`; only the literal
renderer and scalar recognizer live here.
-/
module
public meta import LPTactic.LP.RingCertificate
public import LPTactic.LP.DyadicGeneric

public meta section

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

/-- The `Dyadic` `RingCtx`: integer multipliers, dyadic (power-of-two denominator)
residual. -/
def mkDCtx : MetaM RingCtx :=
  mkRingCtx ``Dyadic `LP.Tactic.LP.Internal.DyadicC "dyadic" mkDyadicNum dyadicScalarLit?
    (fun cV => do
      unless (pow2Log? cV.den).isSome do throwError "lp(dyadic): residual {cV} not dyadic")

end LP.Tactic.LP.Internal.DyadicC
