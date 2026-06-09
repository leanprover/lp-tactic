module
public meta import LPTactic.Dispatch
public meta import LPTactic.LP.BackendOption
public meta import LPTactic.LP.Certificate
public meta import LPTactic.LP.FieldCertificate
public meta import LPTactic.LP.IntCertificate
public meta import LPTactic.LP.DyadicCertificate
public meta import LPTactic.LP.NatCertificate

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-! ## Per-goal driver.

Given a parsed atomic `Rat` goal `lhs op rhs` and the collected `≤`/`=`
hypotheses-as-rows, build the LP, run SoPlex, and assemble the direct
certificate proof. -/

/-- Assemble the optimal-branch certificate proof from the numerical
multipliers and the parsed rows. Shared between the SoPlex-driven path
and the trivial closed-goal short-circuit (where multipliers are all
zero and `c = objLin.const`). -/
def assembleLeProof (rows : Array Row) (strict : Bool)
    (objLin : LinExpr) (mults : Array Rat) (vars : Array FVarId)
    (lhs rhs : Expr) (atoms : AtomTable := {}) : TacticM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual objLin rowLins mults
  unless isLinExprClosed residual do
    throwError "lp: dual certificate did not algebraically cancel the goal{
      ""} (residual still depends on variables); refusing to build a proof"
  let c := residual.const
  let rhsMinusLhs ← mkRatSub rhs lhs
  -- For a strict goal, include each strict row's `term < 0` proof so a positive multiplier
  -- on it upgrades the sum to `< 0` (proving the strict goal even when the residual `c = 0`).
  let mut entries : Array (Rat × Expr × Expr × Option Expr) := #[]
  for h : i in [0:rows.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      let row := rows[i]
      let sp? ← if strict && row.strict then pure (some (← row.strictProof)) else pure none
      entries := entries.push (lam, ← row.term, ← row.proof, sp?)
  let (sumExpr, sumProof, sumStrict) ← buildWeightedSumAndProof entries
  -- Residual sign required: a strict goal needs `0 < c`, UNLESS a strict row made the sum
  -- strict (`sumStrict`), in which case `0 ≤ c` suffices.
  if strict then
    if sumStrict then
      unless decide (0 ≤ c) do
        throwError "lp: goal is not entailed; numerical residual is {c}, not ≥ 0"
    else
      unless decide (0 < c) do
        throwError "lp: goal is not entailed; numerical residual is {c}, not > 0 {
          ""}(no strict hypothesis available to upgrade it)"
  else
    unless decide (0 ≤ c) do
      throwError "lp: goal is not entailed; numerical residual is {c}, not ≥ 0"
  let cExpr ← mkRatLit c
  let lhsId ← mkRatAdd rhsMinusLhs sumExpr
  -- Explicit-proof-term discharge of `lhsId = c`.
  let identProof ← proveCertificateIdentity vars lhsId c atoms
  -- Build the final closer by explicit-argument application instead of
  -- `mkAppM`. The four implicits (`lhs`, `rhs`, `s`, `c`) are already in
  -- hand here, so making `mkAppM` rediscover them by `isDefEq` over the
  -- deeply nested `sumProof`/`identProof` types can blow the elaborator's
  -- `maxRecDepth` on large LPs.
  if strict then
    if sumStrict then
      let hC ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), cExpr])
      return mkAppN (mkConst ``direct_lt_close_strict)
        #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
      return mkAppN (mkConst ``direct_lt_close)
        #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]
  else
    let hC ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), cExpr])
    return mkAppN (mkConst ``direct_le_close)
      #[lhs, rhs, sumExpr, cExpr, sumProof, hC, identProof]

/-- `Rat` fast-path Farkas closer (infeasible branch), via the original `Q`-literal
discharger (`buildWeightedSumAndProof`/`mkRatLit`/`direct_infeasible_close`). Mirrors
`Field.assembleInfeasibleProof` but produces the byte-for-byte shipped `Rat` proof term,
avoiding the generic `ofRat` literal bridge. -/
def assembleInfeasibleProofRat (rows : Array Row) (strict : Bool)
    (mults : Array Rat) (vars : Array FVarId) (lhs rhs : Expr)
    (atoms : AtomTable := {}) : TacticM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do
    throwError "lp: SoPlex reported infeasible but the Farkas certificate did not{
      ""} algebraically cancel"
  let c := residual.const
  -- Include each strict row's `term < 0`, so a strict hypothesis with a positive multiplier
  -- makes the Farkas sum strict (`< 0`) and certifies infeasibility even at residual `c = 0`
  -- (e.g. `a < b, b ≤ a ⊢ False`), which the relaxed (`≤`) combination cannot.
  let mut entries : Array (Rat × Expr × Expr × Option Expr) := #[]
  for h : i in [0:rows.size] do
    let lam := mults[i]!
    if lam ≠ 0 then
      let row := rows[i]
      let sp? ← if row.strict then pure (some (← row.strictProof)) else pure none
      entries := entries.push (lam, ← row.term, ← row.proof, sp?)
  let (sumExpr, sumProof, sumStrict) ← buildWeightedSumAndProof entries
  -- `c > 0` always certifies infeasibility; a strict sum (`s < 0`) does so already at `0 ≤ c`.
  if sumStrict then
    unless decide (0 ≤ c) do
      throwError "lp: SoPlex reported infeasible but Farkas residual {c} is not ≥ 0"
  else
    unless decide (0 < c) do
      throwError "lp: SoPlex reported infeasible but Farkas residual {c} is not > 0"
  let cExpr ← mkRatLit c
  let identProof ← proveCertificateIdentity vars sumExpr c atoms
  let hFalse ←
    if sumStrict then
      let hC ← mkDecideProof (← mkAppM ``LE.le #[(← mkRatLit 0), cExpr])
      pure <| mkAppN (mkConst ``direct_infeasible_close_strict)
        #[sumExpr, cExpr, sumProof, hC, identProof]
    else
      let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
      pure <| mkAppN (mkConst ``direct_infeasible_close)
        #[sumExpr, cExpr, sumProof, hC, identProof]
  let goalType ←
    if strict then mkAppM ``LT.lt #[lhs, rhs] else mkAppM ``LE.le #[lhs, rhs]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

/-- For the `Nat` carrier, build a `0 ≤ x` row for each LP variable. lp's columns are free
(unbounded below), but every `Nat` value is `≥ 0`; linarith gets this from its ℕ→ℤ
preprocessing. We instead add an explicit row per variable, discharged by `Nat.zero_le` (so the
ring `term`/`proof` are never forced — the `Nat` assembly only reads `leProof`). Atoms count
too: an opaque `Nat` subterm (e.g. truncated `a - b`) is also `≥ 0`. -/
def natNonnegRows (vars : Array FVarId) (atoms : AtomTable) : MetaM (Array Row) :=
  vars.mapM fun v => do
    let xE := atoms.keyToExpr v
    let leProof ← mkAppM ``Nat.zero_le #[xE]
    -- The `0` exactly as it appears in `leProof`'s type, so the `Nat` assembly's weighted
    -- `Σ kᵢ·lhsᵢ ≤ Σ kᵢ·rhsᵢ` stays syntactically consistent.
    let zeroE := ((← inferType leProof).getAppArgs)[2]!
    pure {
      term := throwError "lp: Nat nonneg row has no ring term (forced on non-Nat path)"
      proof := throwError "lp: Nat nonneg row has no ring proof (forced on non-Nat path)"
      expr := { coeffs := #[(v, -1)] }
      lhsExpr := zeroE, rhsExpr := xE, leProof := pure leProof }

/-- For a ring carrier (`ℝ`/`ℤ`/`Rat`/`Dyadic`), an opaque atom that is a `Nat`-cast `↑n`
is `≥ 0`. linarith gets this from its ℕ→ℤ cast preprocessing; lp's columns are free, so we
add an explicit `0 ≤ ↑n` row per such atom — otherwise a goal bounded only by `↑n ≥ 0` is
spuriously unbounded. `mkNonneg R n` builds the carrier's `0 ≤ (↑n : R)` proof (e.g.
`Int.natCast_nonneg`, `OrderedRing.natCast_nonneg`); `subNonposName` is the carrier's
`a ≤ b → a - b ≤ 0` lemma (`IntC`/`DyadicC`/`Field`). -/
def castNonnegRows (vars : Array FVarId) (atoms : AtomTable)
    (subNonposName : Name) (mkNonneg : Expr → MetaM Expr) : MetaM (Array Row) := do
  let mut out : Array Row := #[]
  for v in vars do
    let e := atoms.keyToExpr v
    -- Match `↑n` for `n : ℕ`: `@Nat.cast R _ n` (or its `NatCast.natCast` unfolding).
    if e.isAppOfArity ``Nat.cast 3 || e.isAppOfArity ``NatCast.natCast 3 then
      -- Best-effort: if the carrier's nonneg lemma / instance can't be built for this atom,
      -- skip it (no row) rather than failing the whole goal — soundness is unaffected.
      try
        let leProof ← mkNonneg e
        -- The `0 ≤ ↑n` from `mkNonneg`; take its exact `0` and `↑n` so the row, the
        -- `subNonposName` application, and the certificate identity all agree syntactically.
        let leArgs := (← inferType leProof).getAppArgs
        let zeroE := leArgs[2]!
        let castE := leArgs[3]!
        let term ← mkAppM ``HSub.hSub #[zeroE, castE]
        let proof ← mkAppM subNonposName #[leProof]
        out := out.push {
          term := pure term, proof := pure proof,
          expr := { coeffs := #[(v, -1)] },
          lhsExpr := zeroE, rhsExpr := castE }
      catch _ => pure ()
  return out

def proveEntailed (rows : Array Row) (strict : Bool)
    (vars : Array FVarId) (lhs rhs : Expr) (atoms : AtomTable := {}) : TacticM Expr := do
  -- Objective: `rhs - lhs` as a `LinExpr`. Parse against the goal's carrier
  -- (not the default `Rat`) so non-`Rat` atoms like `(x : ℝ)` are accepted.
  -- Reuse the hypothesis parse's atom table so a goal atom (`‖x‖`, `π`, …) maps to
  -- the *same* virtual LP variable the hypotheses used, keeping the certificate consistent.
  let carrier ← inferType lhs
  let (objLin, _) ←
    (do
      let lhsLin ← parseExpr lhs
      let rhsLin ← parseExpr rhs
      pure (rhsLin.sub lhsLin)).run
        { vars := vars, carrier, allowAtoms := true
          atomToFVar := atoms.atomToFVar, fvarToAtom := atoms.fvarToAtom }
  -- Short-circuit when the goal is purely a closed `Rat` comparison: no
  -- rows are needed, no SoPlex call is needed, and the empty-sum direct
  -- certificate is enough. The wider `isLinExprClosed objLin` case is
  -- only safe when the residual constant has the right sign — otherwise
  -- the rows may be inconsistent and the proper certificate routes
  -- through SoPlex's infeasibility branch (vacuous-guard case from the
  -- x-independent inner-`∀` path).
  let canShortcut : Bool :=
    vars.size = 0 ||
    (isLinExprClosed objLin &&
     (if strict then decide (0 < objLin.const) else decide (0 ≤ objLin.const)))
  -- Fast-path for `α = Rat`: route through the original `Q`-literal discharger,
  -- which produces the byte-for-byte shipped proof term and pays no
  -- `userLit = ofRat r` literal-bridge cost (the field engine's ~20% overhead).
  -- `isDefEq` (not a syntactic check) so `Rat` aliases / reducible defs hit it too.
  -- Only synthesize the field `CCtx` for genuine non-`Rat` carriers (e.g. `ℝ`).
  -- Computable-carrier fast paths render coefficients as NATIVE kernel-reducible
  -- literals (defeq to user literals, no `ofRat` bridge): `Rat` via the original
  -- `Q`-discharger, `Int` via the integer-cleared native-`Int.mul` discharger.
  -- Only genuine non-computable carriers (e.g. `ℝ`) take the field `CCtx`.
  let isRat ← isDefEq carrier ratType
  let isInt ← isDefEq carrier (mkConst ``Int)
  let isDyadic ← isDefEq carrier (mkConst ``Dyadic)
  let isNat ← isDefEq carrier (mkConst ``Nat)
  let cctx? : Option Field.CCtx ←
    if isRat || isInt || isDyadic || isNat then pure none
    else pure (some (← Field.mkCCtx carrier))
  let ictx? : Option IntC.ICtx ←
    if isInt then pure (some (← IntC.mkICtx)) else pure none
  let dctx? : Option DyadicC.DCtx ←
    if isDyadic then pure (some (← DyadicC.mkDCtx)) else pure none
  let nctx? : Option NatC.NCtx ←
    if isNat then pure (some (← NatC.mkNCtx)) else pure none
  -- ℕ nonnegativity: add a `0 ≤ x` row per variable for the `Nat` carrier (lp's columns are
  -- free, but ℕ values are `≥ 0`), so goals like `0 ≤ n` or `n ≤ n + m` aren't spuriously
  -- reported unbounded. For ring carriers, the analogous `0 ≤ ↑n` rows for `Nat`-cast atoms.
  let rows ←
    if isNat then pure (rows ++ (← natNonnegRows vars atoms))
    else if isRat then pure rows  -- the Rat fast-path normalizer doesn't yet thread cast
                                  -- atoms through the certificate identity; ℝ uses the CCtx path.
    else
      let subNonposName :=
        if isInt then ``IntC.sub_nonpos_of_le
        else if isDyadic then ``DyadicC.sub_nonpos_of_le
        else ``Field.sub_nonpos_of_le
      -- Build `0 ≤ (↑n : R)` for a cast atom `e = @Nat.cast R _ n`. `Int` has a core
      -- `Int.natCast_nonneg`; other ordered-ring carriers (`ℝ`, `Rat`, …) use the `Grind`
      -- `OrderedRing.natCast_nonneg` — we pin only `R` and unify the result against `e`,
      -- so the (variable) instance arity and the atom's own `NatCast` instance both match.
      let mkNonneg (e : Expr) : MetaM Expr := do
        let args := e.getAppArgs
        let R := args[0]!; let n := args[2]!
        if isInt then
          return ← mkAppM ``Int.natCast_nonneg #[n]
        -- Fully apply `natCast_nonneg` (carrier `R`, its instances inferred, cast `n`), then
        -- confirm by defeq that it proves `0 ≤ e` for the atom's own `NatCast` instance. We
        -- build the expected type so we never inspect a partially-applied (`∀`) proof term.
        let zeroR ← mkAppOptM ``OfNat.ofNat #[some R, some (mkNatLit 0), none]
        let want ← mkAppM ``LE.le #[zeroR, e]
        let proof ← mkAppOptM ``Lean.Grind.OrderedRing.natCast_nonneg
          (#[some R] ++ Array.replicate 6 none ++ #[some n])
        unless ← isDefEq (← inferType proof) want do
          throwError "lp: cast-nonneg lemma did not match the atom"
        -- Pin the type to `0 ≤ e` (the atom's own cast instance), so the caller reads back
        -- the atom verbatim and the certificate identity stays consistent.
        mkExpectedTypeHint (← instantiateMVars proof) want
      pure (rows ++ (← castNonnegRows vars atoms subNonposName mkNonneg))
  let assembleOptimal (mults : Array Rat) : TacticM Expr :=
    match nctx?, ictx?, dctx?, cctx? with
    | some nc, _, _, _ => nc.assembleLeProof rows strict objLin mults vars lhs rhs
    | _, some ic, _, _ => ic.assembleLeProof rows strict objLin mults vars lhs rhs atoms
    | _, _, some dc, _ => dc.assembleLeProof rows strict objLin mults vars lhs rhs atoms
    | _, _, _, none    => assembleLeProof rows strict objLin mults vars lhs rhs atoms
    | _, _, _, some c  => c.assembleLeProof rows strict objLin mults vars lhs rhs atoms
  if canShortcut then
    let mults := Array.replicate rows.size (0 : Rat)
    return ← assembleOptimal mults
  -- Numerical row data is only needed once we know a solver call is
  -- required; the closed-goal path above proves the goal with the empty
  -- weighted sum.
  let rowDense := rows.map (·.expr.toDense vars)
  let rowConsts := rows.map (·.expr.const)
  let objCoeffs := objLin.toDense vars
  let objConst := objLin.const
  -- Build the LP.
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs objConst vars.size hSize
  let opts : Options := { ({} : Options) with sense := .minimize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => throwError "lp: invalid generated problem: {repr e}"
    | .ok p => pure p
  let sol ←
    match ← LP.dispatchSolveExact opts normalized (← getBackendOverride) with
    | .error e => throwError "lp: solveExact failed: {repr e}"
    | .ok sol => pure sol
  -- Handle the unbounded case up front: there is no dual to consume.
  match sol.status with
  | .unbounded =>
      let baseRepr := sol.certificate.primal |>.map (ratList ·.toArray) |>.getD "?"
      let rayRepr := sol.certificate.ray |>.map (ratList ·.toArray) |>.getD "?"
      throwError "lp: objective is unbounded above; base={baseRepr}, ray={rayRepr}"
  | _ => pure ()
  let some d := sol.certificate.dual
    | throwError "lp: SoPlex returned no dual certificate"
  let mults := d.rowUpper.toArray
  -- Verify multipliers are nonneg.
  unless mults.all (fun lam => 0 ≤ lam) do
    throwError "lp: SoPlex returned a negative upper-bound multiplier; refusing to build a proof"
  -- Branch on the SoPlex outcome.
  let rowLins := rows.map (·.expr)
  match sol.status with
  | .optimal =>
      try
        assembleOptimal mults
      catch e =>
        -- Strict goal whose LP dual didn't put a positive multiplier on a strict row, so the
        -- residual upgrade couldn't fire. `lhs < rhs` is exactly the strict-infeasibility of
        -- `{rows, rhs ≤ lhs}`: re-solve with the strict-margin probe on the augmented system
        -- (the negation `rhs - lhs ≤ 0` is the objective row `objLin`), then normalize the dual
        -- so that negation row's multiplier is 1 and retry the (re-validated) assembly.
        if strict && rows.any (·.strict) then
          let rowDense' := rowDense.push objCoeffs
          let rowConsts' := rowConsts.push objConst
          let strictFlags' := (rows.map (·.strict)).push false
          have hSize' : rowDense'.size = rowConsts'.size := by
            simp [rowDense', rowConsts', hSize]
          let pS := buildStrictProblem rowDense' rowConsts' strictFlags' vars.size hSize'
          let optsS : Options := { ({} : Options) with sense := .maximize, presolve := false }
          let some normS := (validate pS).toOption | throw e
          let some solS := (← LP.dispatchSolveExact optsS normS (← getBackendOverride)).toOption
            | throw e
          match solS.status, solS.certificate.dual with
          | .optimal, some dS =>
              let multsAll := dS.rowUpper.toArray
              let lamNeg := multsAll[rows.size]!
              unless 0 < lamNeg do throw e
              -- Scale-invariant: divide by the negation row's multiplier to pin it at 1.
              let newMults := (multsAll.extract 0 rows.size).map (· / lamNeg)
              unless newMults.all (0 ≤ ·) do throw e
              assembleOptimal newMults
          | _, _ => throw e
        else throw e
  | .infeasible =>
      let goalType ←
        if strict then mkAppM ``LT.lt #[lhs, rhs] else mkAppM ``LE.le #[lhs, rhs]
      match nctx?, ictx?, dctx?, cctx? with
      | some nc, _, _, _ => nc.assembleInfeasibleProof rows mults vars goalType
      | _, some ic, _, _ => ic.assembleInfeasibleProof rows mults vars goalType atoms
      | _, _, some dc, _ => dc.assembleInfeasibleProof rows mults vars goalType atoms
      | _, _, _, none    => assembleInfeasibleProofRat rows strict mults vars lhs rhs atoms
      | _, _, _, some c  => c.assembleInfeasibleProof rows mults vars goalType atoms
  | s =>
      throwError "lp: solver outcome was unchecked: {repr s}"
/-- The carrier type `α` of an atomic comparison goal `lhs op rhs` — the first
explicit type argument of `LE`/`LT`/`GE`/`GT`/`Eq`. -/
def relCarrier? (type : Expr) : Option Expr :=
  let args := type.getAppArgs
  match type.getAppFn with
  | .const ``LE.le _ | .const ``GE.ge _
  | .const ``LT.lt _ | .const ``GT.gt _ =>
      if args.size == 4 then some args[0]! else none
  | .const ``Eq _ =>
      if args.size == 3 then some args[0]! else none
  | _ => none

def solveAtomic (g : MVarId) : TacticM Unit := do
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    -- Detect the goal's carrier `α` and parse hypotheses against it (those over
    -- a different type are skipped). Defaults to `Rat` when the head is not a
    -- recognized comparison (parsing then fails with the usual error).
    let carrier := (relCarrier? target).getD ratType
    let ((parsed?, rows), st) ← (do
      let p ← parseAtomic? target
      let hs ← collectHyps
      pure (p, hs)).run { carrier, allowAtoms := true }
    -- Atom table shared by the goal re-parse and the certificate normalizer.
    let atoms : AtomTable := { fvarToAtom := st.fvarToAtom, atomToFVar := st.atomToFVar }
    let some (rel, lhsExpr, rhsExpr, _, _) := parsed?
      | throwError "lp: goal is not an atomic comparison over {carrier}"
    match rel with
    | .le =>
        let proof ← proveEntailed rows false st.vars lhsExpr rhsExpr atoms
        g.assign proof
    | .lt =>
        let proof ← proveEntailed rows true st.vars lhsExpr rhsExpr atoms
        g.assign proof
    | .eq =>
        let h₁ ← proveEntailed rows false st.vars lhsExpr rhsExpr atoms
        let h₂ ← proveEntailed rows false st.vars rhsExpr lhsExpr atoms
        -- Carrier-native antisymmetry: `Field.le_antisymm` still *requires* a `Field`
        -- instance (its `omit` only drops it from the proof, not the signature), so `Int`
        -- must use `IntC.le_antisymm`. No `Field.*` lemma touches the `Int` path.
        let proof ←
          if ← isDefEq carrier (mkConst ``Int) then
            mkAppM ``IntC.le_antisymm #[h₁, h₂]
          else if ← isDefEq carrier (mkConst ``Dyadic) then
            mkAppM ``DyadicC.le_antisymm #[h₁, h₂]
          else if ← isDefEq carrier (mkConst ``Nat) then
            mkAppM ``NatC.le_antisymm #[h₁, h₂]
          else
            mkAppM ``Field.le_antisymm #[h₁, h₂]
        g.assign proof

end LP.Tactic.LP.Internal
