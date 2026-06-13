module
public meta import LPTactic.LP.Types
public import LPTactic.LP.FieldGeneric
public import LPTactic.LP.IntGeneric
public import LPTactic.LP.DyadicGeneric
public import LPTactic.LP.NatGeneric

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

def fvarLetValue? (id : FVarId) : MetaM (Option Expr) := do
  let decl ← id.getDecl
  match decl with
  | .cdecl .. => return none
  | .ldecl (value := value) .. => return some value

/-- Read a `Nat` literal Expr — either `Expr.lit (.natVal n)` or
`OfNat.ofNat n` for a `Nat`-typed `OfNat`. -/
def parseNatLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  match e with
  | .lit (.natVal n) => return some n
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
        match args[1]! with
        | .lit (.natVal n) => return some n
        | _ => return none
      else
        return none

/-- Read an `Int` literal Expr in `Int.ofNat n` / `Int.negSucc n` form. -/
def parseIntLit? (e : Expr) : MetaM (Option Int) := do
  let e ← whnfR e
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Int.ofNat && args.size == 1 then
    return (← parseNatLit? args[0]!).map (Int.ofNat ·)
  else if fn.isConstOf ``Int.negSucc && args.size == 1 then
    return (← parseNatLit? args[0]!).map (Int.negSucc ·)
  else
    return none

/-- Try to recognize `e` as `Q.toRat ⟨n, d, _⟩` for closed `Int`/`Nat`
literals `n`, `d`. Inspected BEFORE `whnfR` so the `@[inline]` `Q.toRat`
isn't unfolded out of the parse. -/
def tryQToRat? (e : Expr) : MetaM (Option Rat) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``LP.Tactic.Q.toRat && args.size == 1 do
    return none
  let q ← whnfR args[0]!
  let qFn := q.getAppFn
  let qArgs := q.getAppArgs
  unless qFn.isConstOf ``LP.Tactic.Q.mk && qArgs.size == 3 do
    return none
  let some n ← parseIntLit? qArgs[0]! | return none
  let some d ← parseNatLit? qArgs[1]! | return none
  if h : d = 0 then return none
  else return some (Rat.normalize n d h)

/-- Scalar recognizer for the `lp` explicit-proof-term discharger.
Recognises `Q.toRat ⟨…⟩`, `@OfNat.ofNat Rat n _`, `let`-bound scalars,
and `Neg`/`HMul`/`HDiv` *of scalars* — but deliberately does **not**
descend into `HAdd`/`HSub` operands. The full `parseScalar?` recurses
through `+`/`-` trees to fold compound closed scalars like `2 - 1`;
calling that at every syntax node of a dense row was an O(N²) blow-up
in tactic-side work. Skipping `HAdd`/`HSub` keeps every call bounded by
the maximal *scalar-only* subtree: a row body (`HAdd` head) is rejected
in O(1), and a coefficient like `1/3` or `c` is still recognized. A
genuinely compound `(2+3) * x` is not short-circuited here, but
`normalize` still handles it via its structural `HAdd` path.

`allowDiv` mirrors `ScalarCaps`: on `Int`/`Nat` (`allowDiv := false`) a `/`/`⁻¹` is
floor/integer division, NOT a rational scalar — so a closed `5 / 2` is NOT the scalar
`2.5`. The parser atomizes those, and the normalizer (whose `scalarLit?` is this) must
agree, or the two models diverge (a `Int.ofNat 5` rendered for an atomized `5 / 2`). -/
partial def quickScalarLit? (e : Expr) (allowDiv : Bool := true) : MetaM (Option Rat) := do
  if let some v ← tryQToRat? e then return some v
  -- Match `parseScalar?`'s reducible `whnf` so a reducibly-wrapped scalar (a `@[reducible]`
  -- abbrev, a cast, …) is recognized identically by the parser and the certificate normalizer.
  -- Cheap: a row body (`HAdd`/`HSub` head, not reducible) stays put and is rejected in O(1).
  let e ← withReducible <| whnfR e
  -- Re-test for a `Q.toRat` literal exposed by the unfolding (as `parseScalar?` does).
  if let some v ← tryQToRat? e then return some v
  match e with
  | .fvar id =>
      match ← fvarLetValue? id with
      | some value => quickScalarLit? value allowDiv
      | none => return none
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
      match args[1]! with
      | .lit (.natVal n) => return some (OfNat.ofNat n)
      | _ => return none
    if fn.isConstOf ``Neg.neg && args.size == 3 then
      return (← quickScalarLit? args[2]! allowDiv).map (fun x => -x)
    if fn.isConstOf ``HMul.hMul && args.size == 6 then
      match ← quickScalarLit? args[4]! allowDiv, ← quickScalarLit? args[5]! allowDiv with
      | some a, some b => return some (a * b)
      | _, _ => return none
    if allowDiv && fn.isConstOf ``HDiv.hDiv && args.size == 6 then
      match ← quickScalarLit? args[4]! allowDiv, ← quickScalarLit? args[5]! allowDiv with
      | some _, some 0 => return none
      | some a, some b => return some (a / b)
      | _, _ => return none
    if allowDiv && fn.isConstOf ``Inv.inv && args.size == 3 then
      match ← quickScalarLit? args[2]! allowDiv with
      | some 0 => return none
      | some a => return some (1 / a)
      | none => return none
    return none

/-- Which exact-arithmetic operations the carrier supports in linear expressions.
The `lp` parser interprets `+`/`-`/`*`/`/` with exact field semantics; for carriers
where an operation is NOT exact it must be rejected, not silently mis-modelled into a
wrong LP. `Nat` subtraction is truncating (`Nat.sub`); `Int`/`Nat` division is
integer/floor division. (`Nat` has no `Neg` instance and `Dyadic` no `Div` instance,
so those never reach the parser.) -/
structure ScalarCaps where
  carrier  : Expr
  allowSub : Bool
  allowDiv : Bool

/-- Capabilities for a carrier: subtraction is exact except on `Nat`; division is exact
only on a field (`Rat`/`ℝ`) — never on `Int`/`Nat`. -/
def scalarCapsFor (carrier : Expr) : MetaM ScalarCaps := do
  let isNat ← isDefEq carrier (mkConst ``Nat)
  let isInt ← isDefEq carrier (mkConst ``Int)
  return { carrier, allowSub := !isNat, allowDiv := !(isNat || isInt) }

/-- Recognise an expression as a reducibly-closed scalar of value `Rat`, with a
  pre-`whnfR` check for `Q.toRat ⟨…⟩` literals so the explicit-proof-term
  discharger's `mkRatLit` outputs are recognized as scalars. Rejects (throws on) any
  occurrence of an operation the carrier does not support exactly (`caps`), so a
  truncating `Nat.sub` or an `Int`/`Nat` `/` never silently produces a wrong LP. -/
partial def parseScalar? (caps : ScalarCaps) (e : Expr) : MetaM (Option Rat) := do
  if let some v ← tryQToRat? e then
    return some v
  let e ← withReducible <| whnfR e
  if let some v ← tryQToRat? e then
    return some v
  match e with
  | .fvar id =>
      match ← fvarLetValue? id with
      | some value => parseScalar? caps value
      | none => return none
  | .lit (.natVal n) =>
      -- Raw `Nat` literal (e.g. `mkNatNum`'s output, or a `Nat`-carrier numeral).
      return some (n : Rat)
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``OfNat.ofNat _ =>
          if args.size == 3 then
            match args[1]! with
            | .lit (.natVal n) => return some (OfNat.ofNat n)
            | _ => return none
      -- Native computable-carrier literal forms (the `mkIntNum`/`mkDyadicNum`
      -- frontend-numeral and certificate-leaf renderings), so spliced witnesses
      -- and recomputed bounds round-trip through the parser.
      | .const ``Int.ofNat _ =>
          if args.size == 1 then return (← parseScalar? caps args[0]!)
      | .const ``Int.negSucc _ =>
          if args.size == 1 then
            return (← parseScalar? caps args[0]!).map (fun n => -(n + 1))
      | .const ``Dyadic.ofInt _ =>
          if args.size == 1 then return (← parseScalar? caps args[0]!)
      | .const ``Dyadic.ofIntWithPrec _ =>
          if args.size == 2 then
            match ← parseScalar? caps args[0]!, ← parseScalar? caps args[1]! with
            | some num, some k => return some (num / ((2 : Rat) ^ k.num.toNat))
            | _, _ => return none
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseScalar? caps args[2]!).map (fun x => -x)
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            match ← parseScalar? caps args[4]!, ← parseScalar? caps args[5]! with
            | some a, some b => return some (a + b)
            | _, _ => return none
      | .const ``HSub.hSub _ =>
          -- Truncating `Nat.sub` is not a `Rat` subtraction: return `none` here so
          -- `parseInto` atomizes the whole `a - b` (the rejection-with-`cutsat`-hint now
          -- fires only where atomization is off, e.g. the binder frontends).
          if caps.allowSub && args.size == 6 then
            match ← parseScalar? caps args[4]!, ← parseScalar? caps args[5]! with
            | some a, some b => return some (a - b)
            | _, _ => return none
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            match ← parseScalar? caps args[4]!, ← parseScalar? caps args[5]! with
            | some a, some b => return some (a * b)
            | _, _ => return none
      | .const ``HDiv.hDiv _ =>
          -- `Int`/`Nat` `/` is integer/floor division, not the rational quotient: return
          -- `none` so `parseInto` atomizes the whole quotient (rejection-with-hint fires
          -- only where atomization is off).
          if caps.allowDiv && args.size == 6 then
            match ← parseScalar? caps args[4]!, ← parseScalar? caps args[5]! with
            | some _, some 0 => return none
            | some a, some b => return some (a / b)
            | _, _ => return none
      | .const ``Inv.inv _ =>
          -- A closed scalar inverse `c⁻¹` (e.g. `2⁻¹` = ½) over a field carrier.
          if caps.allowDiv && args.size == 3 then
            match ← parseScalar? caps args[2]! with
            | some 0 => return none
            | some a => return some (1 / a)
            | none => return none
      | _ => return none
      return none

/-- Turn a carrier-typed opaque subterm into a *virtual* LP variable: a fresh `FVarId`
recorded in the atom table and deduplicated by canonical `Expr`, so identical atoms share
a variable. Returns `none` when atomization is off, the term is not of the carrier type, or
it fails `canonAtom` hygiene. The virtual fvar only ever keys `LinExpr`; the proof term uses
the stored `Expr` (never `Expr.fvar` of a virtual). -/
def atomVar (e : Expr) : ParseM (Option FVarId) := do
  unless (← get).allowAtoms do return none
  unless ← isDefEq (← inferType e) (← get).carrier do return none
  let some a ← canonAtom (← get).carrier e | return none
  if let some fv ← findDefEqAtom (← get).atomToFVar a then return some fv
  let fv ← mkFreshFVarId
  modify fun s => { s with
    atomToFVar := s.atomToFVar.insert a fv
    fvarToAtom := s.fvarToAtom.insert fv a }
  addVar fv
  return some fv

/-- `FVarId`-keyed accumulator threaded through `parseInto`. Coefficients accumulate
in a hash map (O(1) per term) instead of merging intermediate `LinExpr`s, which
rescanned the accumulated coefficient array per incoming term — an O(N²) pattern on
dense rows. `order` records first occurrences so `toLinExpr` is deterministic and
matches the old left-to-right coefficient order. -/
structure LinAcc where
  const : Rat := 0
  coeffs : Std.HashMap FVarId Rat := {}
  order : Array FVarId := #[]

def LinAcc.addCoeff (acc : LinAcc) (v : FVarId) (k : Rat) : LinAcc :=
  match acc.coeffs[v]? with
  | some c => { acc with coeffs := acc.coeffs.insert v (c + k) }
  | none => { acc with coeffs := acc.coeffs.insert v k, order := acc.order.push v }

/-- Densify in first-occurrence order, dropping coefficients that cancelled to zero
(matching the old `addCoeff` merge semantics). -/
def LinAcc.toLinExpr (acc : LinAcc) : LinExpr := Id.run do
  let mut coeffs : Array (FVarId × Rat) := Array.mkEmpty acc.order.size
  for v in acc.order do
    let c := acc.coeffs.getD v 0
    if c != 0 then coeffs := coeffs.push (v, c)
  return { const := acc.const, coeffs }

/-- At a parse dead-end, atomize the (original, pre-`whnf`) term if atomization is on
— contributing `k * atom` to the accumulator — else fail with `msg`. -/
def atomIntoOrThrow (acc : LinAcc) (k : Rat) (e : Expr) (msg : MessageData) :
    ParseM LinAcc := do
  if let some fv ← atomVar e then
    return acc.addCoeff fv k
  throwError msg

/-- The `cutsat`/`omega` hint for a truncating `Nat`-subtraction subterm. Thrown by the
binder frontends (atomization off); on the atomic path the subterm atomizes instead and
the hint is re-surfaced by `solveAtomic` only if the residual LP fails to close. -/
def subTruncMsg (carrier : Expr) : MessageData :=
  m!"lp: subtraction over `{carrier}` is truncating (`Nat.sub`) {
    ""}and is not supported by `lp`; use `cutsat` (or `omega`) for goals {
    ""}involving `Nat` subtraction"

/-- The `cutsat`/`omega` hint for an `Int`/`Nat` floor-division (or `%`) subterm. -/
def divTruncMsg (carrier : Expr) : MessageData :=
  m!"lp: division/`%` over `{carrier}` is integer/truncating division {
    ""}and is not supported by `lp`; use `cutsat` (or `omega`) for goals {
    ""}involving `Int`/`Nat` division"

/-- Atomize a subterm whose head operation the carrier does NOT model exactly
(truncating `Nat`-subtraction, `Int`/`Nat` floor-`/`/`%`). Records that a truncating
atom was introduced so a failed solve can re-surface the `cutsat` hint, then atomizes
`e` (or, where atomization is off / the atom is unhygienic, throws `msg` now). -/
def atomTruncatingInto (acc : LinAcc) (k : Rat) (e : Expr) (msg : MessageData) :
    ParseM LinAcc := do
  modify fun s => { s with truncatingAtoms := true }
  atomIntoOrThrow acc k e msg

/-- Accumulating affine parser: add `k * e` into `acc` in a single pass over the
syntax tree. The scalar multiplier `k` threads through `-`/`neg`/scalar-`*`/`/ c`
nodes, so no intermediate per-subtree `LinExpr`s are built or merged. -/
partial def parseInto (caps : ScalarCaps) (acc : LinAcc) (k : Rat) (e : Expr) :
    ParseM LinAcc := do
  let eOrig := e
  if let some v ← parseScalar? caps e then
    return { acc with const := acc.const + k * v }
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? caps e then
    return { acc with const := acc.const + k * v }
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? caps value then
          return { acc with const := acc.const + k * v }
      let ty ← inferType e
      unless ← isDefEq ty (← get).carrier do
        throwError "lp: expected a {(← get).carrier} expression, found{indentExpr e}"
      addVar id
      return acc.addCoeff id k
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            return ← parseInto caps (← parseInto caps acc k args[4]!) k args[5]!
      | .const ``HSub.hSub _ =>
          -- Truncating `Nat`-subtraction cannot be descended into as exact subtraction;
          -- atomize the whole `a - b` opaquely. Ring carriers (`Int`/`Dyadic`/field)
          -- subtract exactly and descend.
          if args.size == 6 then
            unless caps.allowSub do
              return ← atomTruncatingInto acc k eOrig (subTruncMsg caps.carrier)
            return ← parseInto caps (← parseInto caps acc k args[4]!) (-k) args[5]!
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return ← parseInto caps acc (-k) args[2]!
      | .const ``OfNat.ofNat _ =>
          if let some v ← parseScalar? caps e then
            return { acc with const := acc.const + k * v }
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            -- A zero scalar still parses the other side (type checks, registers its
            -- variables) and contributes zero coefficients, as the old `.smul 0` did.
            if let some c ← parseScalar? caps lhs then
              return ← parseInto caps acc (k * c) rhs
            if let some c ← parseScalar? caps rhs then
              return ← parseInto caps acc (k * c) lhs
            -- Neither side is a (compound) closed scalar: ring-normalize the product —
            -- distribute through the additive structure of either factor and reassociate
            -- left-nested products (`p * (n + 1) ↝ p*n + p`), then reparse the result so the
            -- linear part becomes visible. A genuine product-of-atoms (nothing distributes)
            -- still atomizes opaquely, exactly as before. The certificate normalizer mirrors
            -- this via the same `distributeMul?`, so the atom columns agree.
            if let some (dist, _, _) ← distributeMul? caps.allowSub e lhs rhs then
              return ← parseInto caps acc k dist
            return ← atomIntoOrThrow acc k eOrig "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed scalar"
      | .const ``HDiv.hDiv _ =>
          -- `Int`/`Nat` `/` is floor division — even `x / 2` is NOT the affine `(1/2)•x`,
          -- so atomize the whole quotient opaquely. On a field/`Rat` carrier, `e / c` with
          -- `c` a reducibly-closed nonzero scalar IS the affine `(1/c) • e` (e.g. `x / 2`),
          -- kept linear; division by a non-constant (`2 / x`, `x / y`) atomizes.
          if args.size == 6 then
            unless caps.allowDiv do
              return ← atomTruncatingInto acc k eOrig (divTruncMsg caps.carrier)
            if let some c ← parseScalar? caps args[5]! then
              if c == 0 then
                throwError "lp: division by the zero constant"
              return ← parseInto caps acc (k / c) args[4]!
          return ← atomIntoOrThrow acc k eOrig "lp: division is outside the supported affine grammar"
      | .const ``HMod.hMod _ =>
          -- `Int`/`Nat` `%` is truncating/modular; atomize the whole `a % b` opaquely
          -- (with the `cutsat` hint on a failed solve). Other carriers' `%` (rare) falls
          -- through to the generic atomizer below.
          if args.size == 6 && !caps.allowDiv then
            return ← atomTruncatingInto acc k eOrig (divTruncMsg caps.carrier)
      | _ => pure ()
      -- Cast normalization (`push_cast`): a cast of `ℕ`/`ℤ` arithmetic pushes inward so the
      -- linear structure (and any match against the goal's separately-cast columns) becomes
      -- visible; the pushed form reparses. An opaque cast leaf (`↑(#A)`) still atomizes. The
      -- normalizer mirrors this via the same `pushCast?`, so the atom columns agree.
      if let some (pushed, _) ← pushCast? e then
        return ← parseInto caps acc k pushed
      let carrier := (← get).carrier
      atomIntoOrThrow acc k eOrig m!"lp: unsupported {carrier} expression{indentExpr e}"

def parseExpr (e : Expr) : ParseM LinExpr := do
  let caps ← scalarCapsFor (← get).carrier
  return (← parseInto caps {} 1 e).toLinExpr

/-- Is `e` a term of the goal's carrier type? Checked against the `carrier`
in `ParseState` (set from the goal), so hypotheses over a different type are
skipped rather than mis-parsed. -/
def isCarrierExpr (e : Expr) : ParseM Bool := do
  isDefEq (← inferType e) (← get).carrier

/-- Does `α` admit a certificate engine? The computable core carriers (`Rat`, `Int`,
`Dyadic`, `Nat`) are short-circuited (native instances, no synth); any other type is
accepted iff it carries the ordered-`Field` bundle (`ℝ` etc.). Used by the `∃`/`∀`/
`maximize` frontends to dispatch on any supported carrier, not just `Rat`. (`isDefEq`,
not `isConstOf`, so reducible aliases of the core carriers are still recognized.)

The field branch demands `IsCharP α 0`, not just `Lean.Grind.Field α`. The certificate
engine renders rational coefficients via the `Field.NormNum.ofRat` lemmas (`add_eq`,
`mul_eq`, `ofRat_add`, …), which carry `[IsCharP α 0]` — numeral faithfulness is false in
positive characteristic (e.g. `1/2 + 1/2 = 1` fails in `ℤ/2ℤ`). An ordered Grind field
supplies `IsCharP α 0` for free (core's `OrderedRing → IsCharP` instance), so `ℝ` and any
abstract ordered field still dispatch here. A bare or non-ordered field — `ℂ`, a
`NormedField`, the fraction field of a valuation ring — does not, and must fall through
cleanly: without this gate such a carrier dispatches to the field engine and then leaks a
raw `failed to synthesize Lean.Grind.IsCharP α 0` from certificate assembly (Issue 59). -/
def isCarrierType (α : Expr) : MetaM Bool := do
  for c in [``Rat, ``Int, ``Dyadic, ``Nat] do
    if ← isDefEq α (mkConst c) then return true
  unless (← synthInstance? (← mkAppM ``Lean.Grind.Field #[α])).isSome do return false
  return (← synthInstance? (← mkAppM ``Lean.Grind.IsCharP #[α, toExpr (0 : Nat)])).isSome

def parseAtomicRat (rel : Rel) (lhs rhs : Expr) :
    ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  unless (← isCarrierExpr lhs) && (← isCarrierExpr rhs) do
    return none
  return some (rel, lhs, rhs, ← parseExpr lhs, ← parseExpr rhs)

def parseAtomic? (type : Expr) : ParseM (Option (Rel × Expr × Expr × LinExpr × LinExpr)) := do
  let e := type
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const ``LE.le _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[2]! args[3]!
  | .const ``GE.ge _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[3]! args[2]!
  | .const ``LT.lt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[2]! args[3]!
  | .const ``GT.gt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[3]! args[2]!
  | .const ``Eq _ =>
      if args.size == 3 then
        return ← parseAtomicRat .eq args[1]! args[2]!
  | _ => pure ()
  return none

/-- If `type` is a negated proposition `¬ P` — written as `Not P`, `P → False`, or
`Ne a b` (returning the underlying `a = b`) — return `P`, else `none`. Used to recognise
negated comparison hypotheses (linarith's `removeNegations`): `¬ (a ≤ b)`, `¬ (a < b)`,
`a ≠ b`. -/
def notInner? (type : Expr) : MetaM (Option Expr) := do
  match type.getAppFn with
  | .const ``Not _ =>
      let args := type.getAppArgs
      return if args.size == 1 then some args[0]! else none
  | .const ``Ne _ =>
      let args := type.getAppArgs
      if args.size == 3 then return some (← mkAppM ``Eq #[args[1]!, args[2]!]) else return none
  | _ =>
      if type.isArrow && type.bindingBody!.isConstOf ``False then
        return some type.bindingDomain!
      else
        return none

def isAnd? (type : Expr) : Option (Expr × Expr) :=
  let fn := type.getAppFn
  let args := type.getAppArgs
  match fn with
  | .const ``And _ =>
      if args.size == 2 then some (args[0]!, args[1]!) else none
  | _ => none

/-- Pick the carrier-native row-closure lemma name (`Int`/`Dyadic` use their own native
lemmas; `Field.*` requires a `Field` instance the computable rings lack). -/
def carrierSubNonposName (intName dyadicName fieldName : Name) : ParseM Name := do
  let carrier := (← get).carrier
  if ← isDefEq carrier (mkConst ``Int) then return intName
  if ← isDefEq carrier (mkConst ``Dyadic) then return dyadicName
  return fieldName

/-- The discrete integer carriers (`ℤ`, `ℕ`), on which a strict `a < b` is equivalent to
the `+1`-slack non-strict `a + 1 ≤ b`. `Dyadic` and the field carriers are dense, so they
keep the strict ℚ-row. Returns `some true` for `ℤ`, `some false` for `ℕ`, `none` otherwise. -/
def intCarrierIsInt? : ParseM (Option Bool) := do
  let carrier := (← get).carrier
  if ← isDefEq carrier (mkConst ``Int) then return some true
  if ← isDefEq carrier (mkConst ``Nat) then return some false
  return none

/-- Build `(e + 1)` over the goal's carrier (`@HAdd.hAdd α α α _ e 1`), the strengthened
side of an integer strict fact. -/
def addOne (e : Expr) : ParseM Expr := do
  let one ← mkAppOptM ``OfNat.ofNat #[some (← get).carrier, some (mkRawNatLit 1), none]
  mkAppM ``HAdd.hAdd #[e, one]

/-- Recognise `type` as a `ℕ` comparison `a ≤ b` / `a < b` / `a = b` (descending through
`≥`/`>` by flipping), returning `(rel, a, b)` with `a b : ℕ`. Used by the `zify` lift to
spot a `ℕ` hypothesis sitting under a ring-carrier goal. -/
def natComparison? (type : Expr) : MetaM (Option (Rel × Expr × Expr)) := do
  let nat := mkConst ``Nat
  let args := type.getAppArgs
  match type.getAppFn with
  | .const ``LE.le _ => if args.size == 4 && (← isDefEq args[0]! nat) then return some (.le, args[2]!, args[3]!)
  | .const ``GE.ge _ => if args.size == 4 && (← isDefEq args[0]! nat) then return some (.le, args[3]!, args[2]!)
  | .const ``LT.lt _ => if args.size == 4 && (← isDefEq args[0]! nat) then return some (.lt, args[2]!, args[3]!)
  | .const ``GT.gt _ => if args.size == 4 && (← isDefEq args[0]! nat) then return some (.lt, args[3]!, args[2]!)
  | .const ``Eq _ => if args.size == 3 && (← isDefEq args[0]! nat) then return some (.eq, args[1]!, args[2]!)
  | _ => pure ()
  return none

/-- `zify` for a `ℕ` hypothesis under a ring-carrier goal: lift `a ≤ b` / `a < b` / `a = b`
over `ℕ` to the goal carrier `R` via the monotone cast (`linarith`'s `zify`/`push_cast`
preprocessing), returning a proof of `↑a (rel) ↑b : R` so the hypothesis constrains the
goal's `↑(·)` columns. Returns `none` when the goal carrier is `ℕ` itself (no lift) or the
hypothesis is not a `ℕ` comparison; throws (caught upstream by `collectHyps`' fail-open
wrapper, or here by the local `try`) when `R` lacks the ordered-ring cast structure, so a
carrier without the monotone cast simply drops the hypothesis rather than failing the call. -/
def zifyNatHyp? (proof type : Expr) : ParseM (Option Expr) := do
  let R := (← get).carrier
  -- A `ℕ`-carrier goal keeps `ℕ` hypotheses on the fast path; only lift into a different
  -- (ring) carrier.
  if ← isDefEq R (mkConst ``Nat) then return none
  let some (rel, a, b) ← natComparison? type | return none
  try
    let lifted ← match rel with
      | .le => mkAppOptM ``Lean.Grind.OrderedRing.natCast_le_natCast_of_le
                 (#[some R] ++ Array.replicate 6 none ++ #[some a, some b, some proof])
      | .lt => mkAppOptM ``Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt
                 (#[some R] ++ Array.replicate 6 none ++ #[some a, some b, some proof])
      | .eq =>
          -- `↑(·)` is a function, so cast congruence lifts the equality: `↑a = ↑b`.
          let castFn ← mkAppOptM ``Nat.cast #[some R, none]
          mkAppM ``congrArg #[castFn, proof]
    return some lifted
  catch _ => return none

partial def collectHypProof (origin : Name) (proof : Expr) :
    ParseM (Array Row) := do
  let type ← inferType proof
  if (isAnd? type).isSome then
    let left ← mkAppM ``And.left #[proof]
    let right ← mkAppM ``And.right #[proof]
    return (← collectHypProof origin left) ++ (← collectHypProof origin right)
  -- Negated comparison (linarith's `removeNegations`): contribute the flipped row,
  -- wrapping the hypothesis with the core `Grind.Order.lt_of_not_le`/`le_of_not_lt`
  -- conversions and feeding the positive comparison back through the existing machinery
  -- (so the carrier dispatch, strict tagging, and `Nat` no-subtraction path are all reused).
  -- `¬ (a ≤ b)` ⟶ `b < a` (strict),
  -- `¬ (a < b)` ⟶ `b ≤ a`; `¬ (a ≥ b)`/`¬ (a > b)` flip the same way. `a ≠ b` is a
  -- disequality with no single linear row, so it contributes nothing (as a bare `≠` does).
  if let some inner ← notInner? type then
    match inner.getAppFn with
    | .const ``LE.le _ | .const ``GE.ge _ =>
        return ← collectHypProof origin (← mkAppM ``Lean.Grind.Order.lt_of_not_le #[proof])
    | .const ``LT.lt _ | .const ``GT.gt _ =>
        return ← collectHypProof origin (← mkAppM ``Lean.Grind.Order.le_of_not_lt #[proof])
    | _ => return #[]
  match ← parseAtomic? type with
  | none =>
      -- `zify`: a `ℕ` comparison under a ring-carrier goal lifts via the monotone cast so
      -- it constrains the goal's `↑(·)` columns (`linarith`'s `zify`/`push_cast`). The
      -- lifted `↑a (rel) ↑b` is over the goal carrier, so it parses on the normal path.
      if let some lifted ← zifyNatHyp? proof type then
        return ← collectHypProof origin lifted
      return #[]
  | some (.lt, lhsExpr, rhsExpr, lhs, rhs) =>
      match ← intCarrierIsInt? with
      | some isInt =>
          -- Integer strengthening (`ℤ`/`ℕ`): a strict `a < b` is the `+1`-slack non-strict
          -- `a + 1 ≤ b`, the preprocessing step `linarith` applies and `lp` was missing. We
          -- emit a NON-strict row whose `term`/`expr` carry the `+1` (so a chain of `k`
          -- strict facts keeps all `k` units of slack), discharged by `add_one_le_of_lt`.
          -- Sound within ℚ-Farkas: it changes the rows, not the certificate theory.
          let lhsPlus ← addOne lhsExpr
          let row := let r := lhs.sub rhs; { r with const := r.const + 1 }
          let leProof ←
            if isInt then mkAppM ``IntC.add_one_le_of_lt #[proof]
            else mkAppM ``NatC.add_one_le_of_lt #[proof]
          -- `ℤ` uses the ring assembly (`term`/`proof`: the strengthened `(a+1) - b ≤ 0`);
          -- `ℕ` uses the no-subtraction assembly (`lhsExpr`/`rhsExpr`/`leProof`: `a + 1 ≤ b`).
          -- The ring fields stay dead on the `ℕ` path; we make them throwing thunks (as
          -- `natNonnegRows` does) so a dispatch mistake fails loudly rather than building a
          -- bogus `IntC.*` application over a `ℕ` proof.
          if isInt then
            return #[{
              term := mkAppM ``HSub.hSub #[lhsPlus, rhsExpr],
              expr := row,
              proof := mkAppM ``IntC.sub_nonpos_of_le #[leProof],
              lhsExpr := lhsPlus, rhsExpr := rhsExpr, leProof := pure leProof }]
          else
            return #[{
              term := throwError "lp: ℕ strengthened strict row has no ring term (forced on non-ℕ path)"
              expr := row,
              proof := throwError "lp: ℕ strengthened strict row has no ring proof (forced on non-ℕ path)"
              lhsExpr := lhsPlus, rhsExpr := rhsExpr, leProof := pure leProof }]
      | none =>
          -- Dense carriers (`Dyadic`/field/`Rat`): `a < b` does NOT imply `a + 1 ≤ b`, so we
          -- keep BOTH the relaxed `a - b ≤ 0` (`proof`) AND the strict `a - b < 0`
          -- (`strictProof`), tagging the row `strict`. A positive multiplier on a strict row
          -- then upgrades the Farkas sum from `≤ 0` to `< 0`, proving strict goals / strict
          -- contradictions the relaxed combination cannot.
          let row := lhs.sub rhs
          let ltName ← carrierSubNonposName ``IntC.sub_nonpos_of_lt ``DyadicC.sub_nonpos_of_lt
            ``Field.sub_nonpos_of_lt
          let negName ← carrierSubNonposName ``IntC.sub_neg_of_lt ``DyadicC.sub_neg_of_lt
            ``Field.sub_neg_of_lt
          return #[{
            term := mkAppM ``HSub.hSub #[lhsExpr, rhsExpr],
            expr := row,
            proof := mkAppM ltName #[proof],
            lhsExpr := lhsExpr, rhsExpr := rhsExpr,
            leProof := mkAppM ``Nat.le_of_lt #[proof],
            strict := true, strictProof := mkAppM negName #[proof] }]
  | some (.le, lhsExpr, rhsExpr, lhs, rhs) =>
      let row := lhs.sub rhs
      -- Row closure: `Int` needs native `IntC.*` lemmas (`Field.*` requires a `Field`
      -- instance `Int` lacks); fields/`Rat`-as-field use `Field.*`.
      let leName ← carrierSubNonposName ``IntC.sub_nonpos_of_le ``DyadicC.sub_nonpos_of_le
        ``Field.sub_nonpos_of_le
      return #[{
        term := mkAppM ``HSub.hSub #[lhsExpr, rhsExpr],
        expr := row,
        proof := mkAppM leName #[proof],
        lhsExpr := lhsExpr, rhsExpr := rhsExpr, leProof := pure proof }]
  | some (.eq, lhsExpr, rhsExpr, lhs, rhs) =>
      let d := lhs.sub rhs
      let eqName ← carrierSubNonposName ``IntC.sub_nonpos_of_eq ``DyadicC.sub_nonpos_of_eq
        ``Field.sub_nonpos_of_eq
      -- Both directions of the equality, each also exposed as an `≤` row for the
      -- `Nat` (no-subtraction) assembly: `lhs ≤ rhs` and `rhs ≤ lhs` via `le_of_eq`.
      -- (`leProof` is forced only by the `Nat` path; ring carriers use `term`/`proof`.)
      return #[
        {
          term := mkAppM ``HSub.hSub #[lhsExpr, rhsExpr],
          expr := d,
          proof := mkAppM eqName #[proof],
          lhsExpr := lhsExpr, rhsExpr := rhsExpr,
          leProof := mkAppM ``Nat.le_of_eq #[proof] },
        {
          term := mkAppM ``HSub.hSub #[rhsExpr, lhsExpr],
          expr := d.neg,
          proof := do mkAppM eqName #[← mkEqSymm proof],
          lhsExpr := rhsExpr, rhsExpr := lhsExpr,
          leProof := do mkAppM ``Nat.le_of_eq #[← mkEqSymm proof] }]

def collectHyps : ParseM (Array Row) := do
  let mut rows := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then
        -- Fail-open: a hypothesis whose shape lies OUTSIDE the supported fragment
        -- (truncating `Nat` subtraction, `Int`/`Nat` floor division, division by a
        -- non-constant, …) makes its per-hypothesis parse THROW. Per the documented
        -- contract, hypotheses outside the fragment are silently ignored — never fatal.
        -- So catch the parse error and drop the offending hypothesis, restoring the
        -- parse state first so its partial variable/atom registrations don't leak into
        -- the LP. Throws are reserved for the goal side (parsed by its own caller).
        let saved ← get
        try
          rows := rows ++ (← collectHypProof decl.userName decl.toExpr)
        catch _ =>
          set saved
  return rows

end LP.Tactic.LP.Internal
