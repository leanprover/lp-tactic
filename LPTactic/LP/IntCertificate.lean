/-
`Int` carrier instance for the unified certificate engine: native `Int.ofNat`/`negSucc`
literals (defeq to user `OfNat`/`Neg` literals, so leaves close by bare `Eq.refl`) plus
an integrality check on the cleared residual. The whole assembly (multiplier clearing,
weighted sum, scaled/unscaled closers) is the shared ordered-ring one in
`RingCertificate.lean`; only the literal renderer and scalar recognizer live here.
-/
module
public meta import LPTactic.LP.RingCertificate
public import LPTactic.LP.IntGeneric

public meta section

open Lean Meta

namespace LP.Tactic.LP.Internal.IntC

/-- Render an `Int` value as a native literal (`Int.ofNat k` / `Int.negSucc k`), defeq to a
user `(k : Int)` `OfNat`/`Neg` literal. -/
def mkIntNum (n : Int) : Expr :=
  match n with
  | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkRawNatLit k)
  | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkRawNatLit k)

/-- Recognize an `Int` scalar value: native `Int.ofNat`/`Int.negSucc` (the engine's own
rendered literals) plus user `OfNat`/`Neg`/`HMul`/`HDiv` via `quickScalarLit?`. Uses
`quickScalarLit?` (O(1) reject of `HAdd`/`HSub`), NEVER the O(N²) recursive `parseScalar?`. -/
partial def intScalarLit? (e : Expr) : MetaM (Option Rat) := do
  if e.isAppOfArity ``Int.ofNat 1 then
    return (← parseNatLit? e.appArg!).map (fun k => ((Int.ofNat k : Int) : Rat))
  if e.isAppOfArity ``Int.negSucc 1 then
    return (← parseNatLit? e.appArg!).map (fun k => ((Int.negSucc k : Int) : Rat))
  quickScalarLit? e

/-- The `Int` `RingCtx`: integer multipliers only (the residual must clear to an
integer; a fractional one means the certificate is not expressible over `Int`). -/
def mkICtx : MetaM RingCtx :=
  mkRingCtx ``Int `LP.Tactic.LP.Internal.IntC "int" (fun r => mkIntNum r.num) intScalarLit?
    (fun cV => do
      unless cV.den == 1 do throwError "lp(int): cleared residual {cV} not integral")

end LP.Tactic.LP.Internal.IntC
