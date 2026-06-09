module
public meta import LPTactic.LP.Types
public import LPTactic.LP.FieldGeneric
public import LPTactic.LP.IntGeneric
public import LPTactic.LP.DyadicGeneric

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

partial def parseExpr (e : Expr) : ParseM LinExpr := do
  let caps ← scalarCapsFor (← get).carrier
  if let some v ← parseScalar? caps e then
    return { const := v }
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? caps e then
    return { const := v }
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? caps value then
          return { const := v }
      let ty ← inferType e
      unless ← isDefEq ty (← get).carrier do
        throwError "lp: expected a {(← get).carrier} expression, found{indentExpr e}"
      addVar id
      return { coeffs := #[(id, 1)] }
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).add (← parseExpr args[5]!)
      | .const ``HSub.hSub _ =>
          -- `parseScalar?` above already rejects `Nat` subtraction; ring carriers
          -- (`Int`/`Dyadic`/field) reach here and subtract exactly.
          if args.size == 6 then
            return (← parseExpr args[4]!).sub (← parseExpr args[5]!)
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseExpr args[2]!).neg
      | .const ``OfNat.ofNat _ =>
          if let some v ← parseScalar? caps e then
            return { const := v }
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            if let some c ← parseScalar? caps lhs then
              return (← parseExpr rhs).smul c
            if let some c ← parseScalar? caps rhs then
              return (← parseExpr lhs).smul c
            throwError "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed scalar"
      | .const ``HDiv.hDiv _ =>
          -- `e / c` with `c` a reducibly-closed nonzero scalar is the affine `(1/c) • e`
          -- (e.g. `x / 2`), kept linear rather than atomized. `Int`/`Nat` `/` is integer
          -- division, rejected by `parseScalar?` above. Division by a non-constant
          -- (`2 / x`, `x / y`) stays unsupported here (atomized once that lands).
          if args.size == 6 then
            if let some c ← parseScalar? caps args[5]! then
              if c == 0 then
                throwError "lp: division by the zero constant"
              return (← parseExpr args[4]!).smul (1 / c)
          throwError "lp: division is outside the supported affine grammar"
      | _ => pure ()
      throwError "lp: unsupported {(← get).carrier} expression{indentExpr e}"

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
      -- Cheap strict relaxation: use a strict hypothesis `a < b` as the weaker
      -- `a - b ≤ 0` (sound). This lets lp *use* strict hypotheses wherever
      -- non-strictness suffices. It does NOT recover the strictness itself
      -- (e.g. `a < b, b ≤ a ⊢ False`) and cannot prove strict *goals*; that needs
      -- a strict-aware Farkas certificate (tracked upstream). The `leProof`
      -- (`Nat.le_of_lt`) is only forced by the `Nat` no-subtraction assembly.
      let row := lhs.sub rhs
      let ltName ← carrierSubNonposName ``IntC.sub_nonpos_of_lt ``DyadicC.sub_nonpos_of_lt
        ``Field.sub_nonpos_of_lt
      return #[{
        term := mkAppM ``HSub.hSub #[lhsExpr, rhsExpr],
        expr := row,
        proof := mkAppM ltName #[proof],
        lhsExpr := lhsExpr, rhsExpr := rhsExpr,
        leProof := mkAppM ``Nat.le_of_lt #[proof] }]
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
