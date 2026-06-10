module
public meta import LPTactic.Dispatch
public meta import LPTactic.LP.BackendOption
public meta import LPTactic.LP.RatCertificate
public meta import LPTactic.LP.FieldCertificate
public meta import LPTactic.LP.IntCertificate
public meta import LPTactic.LP.DyadicCertificate
public meta import LPTactic.LP.NatCertificate

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-! ## Carrier dispatch.

The single place the supported carriers are enumerated. The atomic discharger
(`proveEntailed`), the `=`-goal antisymmetry split, and the `∃`/`maximize`
frontends all consume the same `CarrierOps` record, so adding a carrier means
extending `mkCarrierOps` once. -/

inductive CarrierKind where
  | rat | int | dyadic | nat | field
  deriving BEq, Repr

/-- Detect the goal's carrier kind by `isDefEq` (not a syntactic check), so aliases /
reducible defs hit the fast paths too; only genuinely different carriers (e.g. `ℝ`)
land on the field path. -/
def detectCarrierKind (carrier : Expr) : MetaM CarrierKind := do
  if ← isDefEq carrier ratType then return .rat
  if ← isDefEq carrier (mkConst ``Int) then return .int
  if ← isDefEq carrier (mkConst ``Dyadic) then return .dyadic
  if ← isDefEq carrier (mkConst ``Nat) then return .nat
  return .field

/-- The per-invocation carrier strategy: certificate assembly for both LP branches,
antisymmetry for the `=`-goal split, and the frontend witness-numeral renderer. -/
structure CarrierOps where
  carrier : Expr
  kind : CarrierKind
  /-- Optimal-branch certificate (`rows strict objLin mults vars lhs rhs atoms`). -/
  assembleLe : Array Row → Bool → LinExpr → Array Rat → Array FVarId → Expr → Expr →
    AtomTable → MetaM Expr
  /-- Infeasible-branch (Farkas) certificate; proves `goalType` via `False.elim`
  (`rows mults vars goalType atoms`). -/
  assembleInfeasible : Array Row → Array Rat → Array FVarId → Expr → AtomTable → MetaM Expr
  /-- `lhs ≤ rhs → rhs ≤ lhs → lhs = rhs`, carrier-native. -/
  leAntisymm : Expr → Expr → MetaM Expr
  /-- Render a primal/bound `Rat` value as a carrier literal for the `∃`/`maximize`
  frontends; throws if `v` is not representable in the carrier (non-integer for
  `Int`/`Nat`, negative for `Nat`, non-dyadic for `Dyadic`). That case is genuine
  integer/lattice programming (a fractional vertex/optimum has no carrier witness),
  which is `omega`/`cutsat`'s job, not `lp`'s ℚ-Farkas. -/
  mkNumeral : Rat → MetaM Expr

/-- Build the `CarrierOps` for `carrier`. Computable carriers take fast paths that
render coefficients as native kernel-reducible literals (defeq to user literals, no
`userLit = ofRat r` bridge): `Rat` via the `Q`-literal discharger, `Int`/`Dyadic` via
the integer-cleared native-mul discharger, `Nat` via the no-subtraction semiring
assembly. Only genuine non-computable carriers (e.g. `ℝ`) synthesize the field `CCtx`. -/
def mkCarrierOps (carrier : Expr) : MetaM CarrierOps := do
  match ← detectCarrierKind carrier with
  | .rat =>
    let rc ← mkRatCtx
    return {
      carrier, kind := .rat
      assembleLe := fun rows strict objLin mults vars lhs rhs atoms =>
        rc.assembleLeProof rows strict objLin mults vars lhs rhs atoms
      assembleInfeasible := fun rows mults vars goalType atoms =>
        rc.assembleInfeasibleProof rows mults vars goalType atoms
      -- `Field.le_antisymm` still *requires* a `Field` instance (its `omit` only drops
      -- it from the proof, not the signature); `Rat` has one, so this is fine here.
      leAntisymm := fun h₁ h₂ => mkAppM ``Field.le_antisymm #[h₁, h₂]
      -- Witness numerals use the structural `OfNat`/`Neg`/`HDiv` shapes (recognized by
      -- the parser), built from the field context on demand.
      mkNumeral := fun v => do (← Field.mkCCtx carrier).mkRatNumeral v }
  | .int =>
    let ic ← IntC.mkICtx
    return {
      carrier, kind := .int
      assembleLe := fun rows strict objLin mults vars lhs rhs atoms =>
        ic.assembleLeProof rows strict objLin mults vars lhs rhs atoms
      assembleInfeasible := fun rows mults vars goalType atoms =>
        ic.assembleInfeasibleProof rows mults vars goalType atoms
      leAntisymm := fun h₁ h₂ => mkAppM ``IntC.le_antisymm #[h₁, h₂]
      mkNumeral := fun v => do
        unless v.den == 1 do
          throwError "lp: `∃`/`maximize` over `Int` needs an integer value, but the {
            ""}LP gave {v}; integrality is `omega`/`cutsat`'s job, not `lp`'s ℚ-Farkas"
        pure (IntC.mkIntNum v.num) }
  | .dyadic =>
    let dc ← DyadicC.mkDCtx
    return {
      carrier, kind := .dyadic
      assembleLe := fun rows strict objLin mults vars lhs rhs atoms =>
        dc.assembleLeProof rows strict objLin mults vars lhs rhs atoms
      assembleInfeasible := fun rows mults vars goalType atoms =>
        dc.assembleInfeasibleProof rows mults vars goalType atoms
      leAntisymm := fun h₁ h₂ => mkAppM ``DyadicC.le_antisymm #[h₁, h₂]
      mkNumeral := fun v => do
        unless (DyadicC.pow2Log? v.den).isSome do
          throwError "lp: `∃`/`maximize` over `Dyadic` needs a dyadic value (denominator {
            ""}a power of two), but the LP gave {v}"
        pure (DyadicC.mkDyadicNum v) }
  | .nat =>
    let nc ← NatC.mkNCtx
    return {
      carrier, kind := .nat
      assembleLe := fun rows strict objLin mults vars lhs rhs _atoms =>
        nc.assembleLeProof rows strict objLin mults vars lhs rhs
      assembleInfeasible := fun rows mults vars goalType _atoms =>
        nc.assembleInfeasibleProof rows mults vars goalType
      leAntisymm := fun h₁ h₂ => mkAppM ``NatC.le_antisymm #[h₁, h₂]
      mkNumeral := fun v => do
        unless v.den == 1 && v.num ≥ 0 do
          throwError "lp: `∃`/`maximize` over `Nat` needs a nonneg integer value, but the {
            ""}LP gave {v}; integrality is `omega`/`cutsat`'s job, not `lp`'s ℚ-Farkas"
        pure (NatC.mkNatNum v) }
  | .field =>
    let cc ← Field.mkCCtx carrier
    return {
      carrier, kind := .field
      assembleLe := fun rows strict objLin mults vars lhs rhs atoms =>
        cc.assembleLeProof rows strict objLin mults vars lhs rhs atoms
      assembleInfeasible := fun rows mults vars goalType atoms =>
        cc.assembleInfeasibleProof rows mults vars goalType atoms
      leAntisymm := fun h₁ h₂ => mkAppM ``Field.le_antisymm #[h₁, h₂]
      mkNumeral := cc.mkRatNumeral }

/-! ## Per-goal driver.

Given a parsed atomic comparison goal `lhs op rhs` and the collected `≤`/`=`
hypotheses-as-rows, build the LP, run SoPlex, and assemble the direct
certificate proof. -/

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

/-- Direction-independent setup shared by both directions of an `=` goal: the goal
sides parsed once, the carrier ops synthesized once, and the rows augmented once
with the carrier's nonnegativity facts. An `=` goal proves both `≤` directions from
one `EntailEnv` instead of redoing this work per direction. -/
structure EntailEnv where
  rows : Array Row
  vars : Array FVarId
  atoms : AtomTable
  lhs : Expr
  rhs : Expr
  lhsLin : LinExpr
  rhsLin : LinExpr
  ops : CarrierOps

def mkEntailEnv (rows : Array Row) (vars : Array FVarId) (lhs rhs : Expr)
    (atoms : AtomTable := {}) : TacticM EntailEnv := do
  -- Parse the goal sides against the goal's carrier (not the default `Rat`) so
  -- non-`Rat` atoms like `(x : ℝ)` are accepted.
  -- Reuse the hypothesis parse's atom table so a goal atom (`‖x‖`, `π`, …) maps to
  -- the *same* virtual LP variable the hypotheses used, keeping the certificate consistent.
  -- The updated parse state is discarded: callers must already have registered the goal
  -- sides' variables and atoms in `vars`/`atoms` (as `solveAtomic` does by parsing the
  -- target before collecting hypotheses), so this reparse discovers nothing new.
  let carrier ← inferType lhs
  let ((lhsLin, rhsLin), _) ←
    (do pure ((← parseExpr lhs), (← parseExpr rhs))).run
        { vars := vars, carrier, allowAtoms := true
          atomToFVar := atoms.atomToFVar, fvarToAtom := atoms.fvarToAtom }
  let ops ← mkCarrierOps carrier
  -- ℕ nonnegativity: add a `0 ≤ x` row per variable for the `Nat` carrier (lp's columns are
  -- free, but ℕ values are `≥ 0`), so goals like `0 ≤ n` or `n ≤ n + m` aren't spuriously
  -- reported unbounded. For ring carriers, the analogous `0 ≤ ↑n` rows for `Nat`-cast atoms.
  let rows ←
    if ops.kind == .nat then pure (rows ++ (← natNonnegRows vars atoms))
    else if ops.kind == .rat then
      pure rows  -- cast-atom nonneg rows are not yet enabled on the Rat fast path;
                 -- ℝ uses the field path below.
    else
      let subNonposName :=
        match ops.kind with
        | .int => ``IntC.sub_nonpos_of_le
        | .dyadic => ``DyadicC.sub_nonpos_of_le
        | _ => ``Field.sub_nonpos_of_le
      -- Build `0 ≤ (↑n : R)` for a cast atom `e = @Nat.cast R _ n`. `Int` has a core
      -- `Int.natCast_nonneg`; other ordered-ring carriers (`ℝ`, `Rat`, …) use the `Grind`
      -- `OrderedRing.natCast_nonneg` — we pin only `R` and unify the result against `e`,
      -- so the (variable) instance arity and the atom's own `NatCast` instance both match.
      let mkNonneg (e : Expr) : MetaM Expr := do
        let args := e.getAppArgs
        let R := args[0]!; let n := args[2]!
        if ops.kind == .int then
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
  return { rows, vars, atoms, lhs, rhs, lhsLin, rhsLin, ops }

/-- Prove the entailed comparison from a prebuilt `EntailEnv`: `lhs ≤ rhs` (or
`lhs < rhs` when `strict`), or the swapped direction `rhs ≤ lhs` when `swap` —
the objective is the corresponding difference of the pre-parsed goal sides. -/
def proveEntailedCore (env : EntailEnv) (strict : Bool) (swap : Bool := false) :
    TacticM Expr := do
  let rows := env.rows
  let vars := env.vars
  let atoms := env.atoms
  let (lhs, rhs) := if swap then (env.rhs, env.lhs) else (env.lhs, env.rhs)
  -- Objective: `rhs - lhs` as a `LinExpr`.
  let objLin := if swap then env.lhsLin.sub env.rhsLin else env.rhsLin.sub env.lhsLin
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
  let assembleOptimal (mults : Array Rat) : TacticM Expr :=
    env.ops.assembleLe rows strict objLin mults vars lhs rhs atoms
  if canShortcut then
    let mults := Array.replicate rows.size (0 : Rat)
    return ← assembleOptimal mults
  -- Numerical row data is only needed once we know a solver call is
  -- required; the closed-goal path above proves the goal with the empty
  -- weighted sum.
  let vidx := mkVarIdx vars
  let rowDense := rows.map (·.expr.toDense vidx)
  let rowConsts := rows.map (·.expr.const)
  let objCoeffs := objLin.toDense vidx
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
      env.ops.assembleInfeasible rows mults vars goalType atoms
  | s =>
      throwError "lp: solver outcome was unchecked: {repr s}"

def proveEntailed (rows : Array Row) (strict : Bool)
    (vars : Array FVarId) (lhs rhs : Expr) (atoms : AtomTable := {}) : TacticM Expr := do
  proveEntailedCore (← mkEntailEnv rows vars lhs rhs atoms) strict

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
        -- Both `≤` directions share one `EntailEnv` (goal parse, carrier ops,
        -- nonneg-row augmentation); only the LP solve and assembly run per direction.
        let env ← mkEntailEnv rows st.vars lhsExpr rhsExpr atoms
        let h₁ ← proveEntailedCore env false
        let h₂ ← proveEntailedCore env false (swap := true)
        -- Carrier-native antisymmetry (e.g. `Field.le_antisymm` still *requires* a
        -- `Field` instance `Int` lacks, so the dispatch matters).
        let proof ← env.ops.leAntisymm h₁ h₂
        g.assign proof

end LP.Tactic.LP.Internal
