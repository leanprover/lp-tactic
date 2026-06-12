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
`normalize` still handles it via its structural `HAdd` path. -/
partial def quickScalarLit? (e : Expr) : MetaM (Option Rat) := do
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
      | some value => quickScalarLit? value
      | none => return none
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
      match args[1]! with
      | .lit (.natVal n) => return some (OfNat.ofNat n)
      | _ => return none
    if fn.isConstOf ``Neg.neg && args.size == 3 then
      return (← quickScalarLit? args[2]!).map (fun x => -x)
    if fn.isConstOf ``HMul.hMul && args.size == 6 then
      match ← quickScalarLit? args[4]!, ← quickScalarLit? args[5]! with
      | some a, some b => return some (a * b)
      | _, _ => return none
    if fn.isConstOf ``HDiv.hDiv && args.size == 6 then
      match ← quickScalarLit? args[4]!, ← quickScalarLit? args[5]! with
      | some _, some 0 => return none
      | some a, some b => return some (a / b)
      | _, _ => return none
    if fn.isConstOf ``Inv.inv && args.size == 3 then
      match ← quickScalarLit? args[2]! with
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
          -- Truncating `Nat.sub` cannot be modelled by the LP; reject outright.
          unless caps.allowSub do
            throwError "lp: subtraction over `{caps.carrier}` is truncating (`Nat.sub`) {
              ""}and is not supported by `lp`; use `cutsat` (or `omega`) for goals {
              ""}involving `Nat` subtraction"
          if args.size == 6 then
            match ← parseScalar? caps args[4]!, ← parseScalar? caps args[5]! with
            | some a, some b => return some (a - b)
            | _, _ => return none
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            match ← parseScalar? caps args[4]!, ← parseScalar? caps args[5]! with
            | some a, some b => return some (a * b)
            | _, _ => return none
      | .const ``HDiv.hDiv _ =>
          -- `Int`/`Nat` `/` is integer/floor division, not the rational quotient.
          unless caps.allowDiv do
            throwError "lp: division over `{caps.carrier}` is integer/truncating division {
              ""}and is not supported by `lp`; use `cutsat` (or `omega`) for goals {
              ""}involving `Int`/`Nat` division"
          if args.size == 6 then
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
  let some a ← canonAtom e | return none
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
          -- `parseScalar?` above already rejects `Nat` subtraction; ring carriers
          -- (`Int`/`Dyadic`/field) reach here and subtract exactly.
          if args.size == 6 then
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
            return ← atomIntoOrThrow acc k eOrig "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed scalar"
      | .const ``HDiv.hDiv _ =>
          -- `e / c` with `c` a reducibly-closed nonzero scalar is the affine `(1/c) • e`
          -- (e.g. `x / 2`), kept linear rather than atomized. `Int`/`Nat` `/` is integer
          -- division, rejected by `parseScalar?` above. Division by a non-constant
          -- (`2 / x`, `x / y`) stays unsupported here (atomized once that lands).
          if args.size == 6 then
            if let some c ← parseScalar? caps args[5]! then
              if c == 0 then
                throwError "lp: division by the zero constant"
              return ← parseInto caps acc (k / c) args[4]!
          return ← atomIntoOrThrow acc k eOrig "lp: division is outside the supported affine grammar"
      | _ => pure ()
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
not `isConstOf`, so reducible aliases of the core carriers are still recognized.) -/
def isCarrierType (α : Expr) : MetaM Bool := do
  for c in [``Rat, ``Int, ``Dyadic, ``Nat] do
    if ← isDefEq α (mkConst c) then return true
  return (← synthInstance? (← mkAppM ``Lean.Grind.Field #[α])).isSome

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

partial def collectHypProof (origin : Name) (proof : Expr) :
    ParseM (Array Row) := do
  let type ← inferType proof
  if (isAnd? type).isSome then
    let left ← mkAppM ``And.left #[proof]
    let right ← mkAppM ``And.right #[proof]
    return (← collectHypProof origin left) ++ (← collectHypProof origin right)
  match ← parseAtomic? type with
  | none => return #[]
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
        rows := rows ++ (← collectHypProof decl.userName decl.toExpr)
  return rows

end LP.Tactic.LP.Internal
