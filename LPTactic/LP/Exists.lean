module
public meta import LPTactic.Dispatch
public meta import LPTactic.LP.Atomic
public meta import LPTactic.LP.BackendOption
public meta import LPTactic.LP.Forall

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-! ## Existential goals (`∃ x₁ … xₙ : Rat, B`).

Closes goals of the form `∃ x₁ … xₙ : Rat, B` where `B` is a flat
conjunction of atomic non-strict (in)equality constraints over the
existential binders and reducibly-closed numeric constants only.

The algorithm:

1. Strip nested `∃ x : Rat, …` binders into a single block (entered via
   one `lambdaBoundedTelescope` per binder so the body is canonicalized
   in the same environment the atomic-goal extractor sees).
2. Parse the body as a flat conjunction of atomic Rat (in)equalities;
   reject strict constraints, nested quantifiers, or non-atomic shapes.
3. Verify the **closed-body invariant over the canonicalized atoms**:
   every free `Rat` local appearing in any extracted `LinExpr` must be
   an existential binder. Locals that hide behind reducible
   abbreviations, `let`-bindings, projections, or coercions are
   canonicalized by `parseExpr`'s `withReducible <| whnfR` before the
   check, so the check sees the post-canonicalization atoms.
4. Build a witness LP: `max 0 subject to A x ≤ b` (objective `c = 0`).
   Any feasible point is optimal at value `0`.
5. Run SoPlex via `solveExact` and branch:
   - `.optimal x*` → splice the primal as `Rat` literals into an
     `Exists.intro` chain; recurse on the now-closed residual body.
   - `.infeasible` → fall back to an inconsistency probe on the outer
     hypotheses alone. If that certifies `H` inconsistent, close by
     `absurd`. Otherwise surface a "body infeasible, context
     consistent" error.
   - anything else → surface the underlying solver status.
6. The residual after splicing is a closed `And`/`Eq`/`LE` conjunction
   in `Rat`; `solveGoal` discharges each conjunct via the closed-goal
   atomic short-circuit (no SoPlex call, empty weighted sum).

Soundness comes from Lean reconstructing each primal value as a `Rat`
literal and rebuilding the residual proof — solver row activities and
objective values are not trusted. -/

/-- Is `e` of the form `∃ x : α, …` for a supported carrier `α`? Used as the
existential-goal dispatch predicate. -/
def isExistsRat? (e : Expr) : MetaM Bool := do
  let e ← whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``Exists && args.size == 2 do return false
  isCarrierType (← whnf args[0]!)

/-- Peel an outer chain of `∃ x : Rat, …` binders into a single block.
Calls `k` with the array of binder fvars and the body (with binders
substituted as fvars). The fvars are only valid inside `k`. -/
partial def peelExistsRat (target : Expr) (acc : Array FVarId)
    (k : Array FVarId → Expr → MetaM α) : MetaM α := do
  -- `whnf` may unfold `LE.le` for `Rat` into `Rat.blt _ _ = false`, so
  -- preserve the original `target` to pass into `k`; only the `whnf`
  -- form is consulted to decide whether the head is `Exists`.
  let targetW ← whnf target
  let fn := targetW.getAppFn
  let args := targetW.getAppArgs
  if fn.isConstOf ``Exists && args.size == 2 then
    let αbinder ← whnf args[0]!
    -- First binder fixes the carrier; subsequent binders must match it (a
    -- different-typed inner `∃` stops the peel and lands in the body `k`).
    let accept ←
      if acc.size > 0 then
        isDefEq αbinder (← inferType (Expr.fvar acc[0]!))
      else
        isCarrierType αbinder
    if accept then
      let pred := args[1]!
      return ← Meta.lambdaBoundedTelescope pred 1 fun xs body => do
        peelExistsRat body (acc.push xs[0]!.fvarId!) k
  k acc target

/-- Collect atomic non-strict Rat (in)equalities from an existential
body, descending only through `And`. Throws on strict inequalities,
nested quantifiers, or any non-atomic shape. -/
partial def collectExistsAtoms (body : Expr) :
    ParseM (Array (Rel × LinExpr × LinExpr)) := do
  -- Detect `And` on a `whnfR`-reduced form (matching the atomic-goal
  -- top-level `And` dispatch in `solveGoal`). The non-reduced `body`
  -- is what we pass to `parseAtomic?`: reducible whnf can unfold
  -- `LE.le` into `Rat.blt _ _ = false`, which `parseAtomic?` wouldn't
  -- recognize.
  let bodyW ← whnfR body
  if let some (left, right) := isAnd? bodyW then
    return (← collectExistsAtoms left) ++ (← collectExistsAtoms right)
  match ← parseAtomic? body with
  | none =>
      throwError
        "lp: existential body must be a flat conjunction of atomic non-strict {
          ""}Rat (in)equality constraints; got{indentExpr body}"
  | some (.lt, _, _, _, _) =>
      throwError "lp: strict inequalities are not supported in existential bodies"
  | some (rel, _, _, lhs, rhs) =>
      return #[(rel, lhs, rhs)]

/-- Closed-body invariant check, post-canonicalization.

For each extracted `LinExpr`, every free `Rat` local in `.coeffs` must
be an existential binder. Outer parameters (or `let`-bindings that
canonicalise to non-binder fvars) are rejected here with a precise
message identifying the offending local. -/
def checkClosedBody (atoms : Array (Rel × LinExpr × LinExpr))
    (binders : Array FVarId) : MetaM Unit := do
  let isBinder (v : FVarId) : Bool := binders.any (· == v)
  let checkLin (L : LinExpr) : MetaM Unit := do
    for (v, _) in L.coeffs do
      unless isBinder v do
        let decl ← v.getDecl
        throwError "lp(∃): existential body references non-binder `Rat` local `{
          decl.userName}` after canonicalization; the closed-existential path {
          ""}requires every linear expression in the body to depend only on the {
          ""}existential binders."
  for (_, lhs, rhs) in atoms do
    checkLin lhs
    checkLin rhs

/-! ### Carrier-generic frontend context (`∃`/`maximize`).

The `∃`/`maximize` frontends need exactly two carrier-specific operations beyond the
(already carrier-aware) atomic discharger `proveEntailed`: rendering a primal/bound
value as a carrier literal, and turning an inconsistent hypothesis set into a proof of
the surrounding goal. `FrontendCtx` bundles both, dispatched once per invocation.

For the non-field carriers (`Int`/`Dyadic`/`Nat`) the primal/bound from the ℚ LP must
LAND in the carrier — an integer for `Int`, a nonneg integer for `Nat`, a dyadic for
`Dyadic`. When it does not, `mkNumeral` throws: that case is genuine integer/lattice
programming (a fractional vertex/optimum has no carrier witness), which is `omega`/
`cutsat`'s job, not `lp`'s ℚ-Farkas. The contradiction path has no such restriction —
Farkas inconsistency of ℚ-affine hypotheses is carrier-independent. -/
structure FrontendCtx where
  carrier : Expr
  /-- Render a primal/bound `Rat` value as a `carrier` literal; throws if `v` is not
  representable in `carrier` (non-integer for `Int`/`Nat`, negative for `Nat`,
  non-dyadic for `Dyadic`). -/
  mkNumeral : Rat → MetaM Expr
  /-- Prove `goalType` from inconsistent `rows` weighted by nonneg Farkas `mults`
  (zero objective), via `False.elim`. -/
  mkContradiction : Array Row → Array Rat → Array FVarId → Expr → MetaM Expr

/-- The `Rat` Farkas-contradiction path (`Q`-literal discharger), kept off the `ofRat`
field bridge so `∃`/`maximize` over `Rat` does not regress. -/
def ratHypsContradiction (rows : Array Row) (mults : Array Rat) (vars : Array FVarId)
    (goalType : Expr) : MetaM Expr := do
  let rowLins := rows.map (·.expr)
  let residual := computeResidual {} rowLins mults
  unless isLinExprClosed residual do throwError "lp: Farkas certificate did not cancel"
  let cval := residual.const
  let mut entries : Array (Rat × Expr × Expr) := #[]
  for h : i in [0:rows.size] do
    let lam := mults[i]!
    if lam ≠ 0 then entries := entries.push (lam, ← rows[i].term, ← rows[i].proof)
  let (sumExpr, sumProof) ← buildWeightedSumAndProof entries
  let identProof ← proveCertificateIdentity vars sumExpr cval
  let cExpr ← mkRatLit cval
  let hC ← mkDecideProof (← mkAppM ``LT.lt #[(← mkRatLit 0), cExpr])
  let hFalse := mkAppN (mkConst ``direct_infeasible_close)
    #[sumExpr, cExpr, sumProof, hC, identProof]
  mkAppOptM ``False.elim #[some goalType, some hFalse]

/-- Build the per-invocation `FrontendCtx`, dispatched on the carrier (mirrors the
`Atomic.proveEntailed` 5-way split). -/
def mkFrontendCtx (carrier : Expr) : MetaM FrontendCtx := do
  if ← isDefEq carrier (mkConst ``Int) then
    let ic ← IntC.mkICtx
    return {
      carrier := carrier
      mkNumeral := fun v => do
        unless v.den == 1 do
          throwError "lp: `∃`/`maximize` over `Int` needs an integer value, but the {
            ""}LP gave {v}; integrality is `omega`/`cutsat`'s job, not `lp`'s ℚ-Farkas"
        pure (IntC.mkIntNum v.num)
      mkContradiction := fun rows mults vars gt => ic.assembleInfeasibleProof rows mults vars gt }
  else if ← isDefEq carrier (mkConst ``Dyadic) then
    let dc ← DyadicC.mkDCtx
    return {
      carrier := carrier
      mkNumeral := fun v => do
        unless (DyadicC.pow2Log? v.den).isSome do
          throwError "lp: `∃`/`maximize` over `Dyadic` needs a dyadic value (denominator {
            ""}a power of two), but the LP gave {v}"
        pure (DyadicC.mkDyadicNum v)
      mkContradiction := fun rows mults vars gt => dc.assembleInfeasibleProof rows mults vars gt }
  else if ← isDefEq carrier (mkConst ``Nat) then
    let nc ← NatC.mkNCtx
    return {
      carrier := carrier
      mkNumeral := fun v => do
        unless v.den == 1 && v.num ≥ 0 do
          throwError "lp: `∃`/`maximize` over `Nat` needs a nonneg integer value, but the {
            ""}LP gave {v}; integrality is `omega`/`cutsat`'s job, not `lp`'s ℚ-Farkas"
        pure (NatC.mkNatNum v)
      mkContradiction := fun rows mults vars gt => nc.assembleInfeasibleProof rows mults vars gt }
  else
    let cc ← Field.mkCCtx carrier
    let isRat ← isDefEq carrier ratType
    return {
      carrier := carrier
      mkNumeral := cc.mkRatNumeral
      mkContradiction := fun rows mults vars gt =>
        if isRat then ratHypsContradiction rows mults vars gt
        else cc.assembleInfeasibleProof rows mults vars gt }

/-- Try to certify that the outer hypotheses `rows` (over `vars`) are inconsistent,
producing a proof of `goalType` (via `False.elim`) on success, or `none` if the probe
doesn't fire (no rows, unchecked status, or the LP says feasible).

This is the existential-path inconsistency-probe fallback: a fixed constant-zero
objective (`max 0 subject to H`) so we probe only the consistency of `H`; the carrier's
`mkContradiction` builds the `goalType` proof from the Farkas dual. -/
def tryHypsInconsistent (fctx : FrontendCtx) (rows : Array Row) (vars : Array FVarId)
    (goalType : Expr) : MetaM (Option Expr) := do
  if rows.size = 0 then return none
  -- Zero-variable special case: every row is a closed `c ≤ 0` fact. A row with
  -- `const > 0` is *itself* `False`; certify it with multiplier 1 on that row.
  -- (SoPlex aborts on 0-column problems, so we never call it here.)
  if vars.size = 0 then
    for h : i in [0:rows.size] do
      if isLinExprClosed rows[i].expr && decide (0 < rows[i].expr.const) then
        let mults := (Array.replicate rows.size (0 : Rat)).set! i 1
        return some (← fctx.mkContradiction rows mults vars goalType)
    return none
  let rowDense := rows.map (·.expr.toDense vars)
  let rowConsts := rows.map (·.expr.const)
  let objCoeffs := Array.replicate vars.size (0 : Rat)
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs 0 vars.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error _ => return none
    | .ok p => pure p
  let sol ←
    match ← LP.dispatchSolveExact opts normalized (← getBackendOverride) with
    | .error _ => return none
    | .ok sol => pure sol
  match sol.status with
  | .infeasible =>
      let some d := sol.certificate.dual | return none
      let mults := d.rowUpper.toArray
      unless mults.all (fun lam => 0 ≤ lam) do return none
      let residual := computeResidual {} (rows.map (·.expr)) mults
      unless isLinExprClosed residual do return none
      unless decide (0 < residual.const) do return none
      return some (← fctx.mkContradiction rows mults vars goalType)
  | _ => return none

/-- Apply `Exists.intro` with the given witness to `g`, returning the
metavariable for the body proof obligation. The witness must be a
`Rat` expression. -/
def introExistsRat (g : MVarId) (witness : Expr) : MetaM MVarId := do
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let tyW ← whnf ty
    let fn := tyW.getAppFn
    let args := tyW.getAppArgs
    unless fn.isConstOf ``Exists && args.size == 2 do
      throwError "lp(introExistsRat): expected `∃ x : Rat, _`, got{indentExpr ty}"
    let level := match fn with
      | .const _ (u :: _) => u
      | _ => Level.succ Level.zero
    let αE := args[0]!
    let predE := args[1]!
    -- Only beta-reduce the predicate applied to the witness; do not
    -- `whnf` further (it may unfold `LE.le` into `Rat.blt _ _ = false`
    -- and block the residual proof's atomic-comparison dispatch).
    let bodyTy := (mkApp predE witness).headBeta
    let newMVar ← mkFreshExprSyntheticOpaqueMVar bodyTy (tag := `lp_exists_body)
    let proof := mkApp4 (mkConst ``Exists.intro [level]) αE predE witness newMVar
    g.assign proof
    return newMVar.mvarId!
partial def collectExistsBody (xBinders : Array FVarId) (body : Expr) :
    ParseM (Array (Rel × LinExpr × LinExpr) × Array LinExpr × Array BendersUniversal) := do
  let bodyW ← whnfR body
  if let some (left, right) := isAnd? bodyW then
    let (al, ul, bl) ← collectExistsBody xBinders left
    let (ar, ur, br) ← collectExistsBody xBinders right
    return (al ++ ar, ul ++ ur, bl ++ br)
  if ← isForallRat? body then
    match ← classifyUniversal xBinders (← get).carrier body with
    | .independentGuards residuals => return (#[], residuals, #[])
    | .dependentGuards universals => return (#[], #[], universals)
  match ← parseAtomic? body with
  | none =>
      throwError "lp: existential body must be a flat conjunction of atomic {
        ""}non-strict Rat (in)equality constraints or `∀ y : Rat, G → atomic` {
        ""}subformulas; got{indentExpr body}"
  | some (.lt, _, _, _, _) =>
      throwError "lp: strict inequalities are not supported in existential bodies"
  | some (rel, _, _, lhs, rhs) =>
      return (#[(rel, lhs, rhs)], #[], #[])

/-- Existential-goal driver. Pre: `g`'s goal type is `∃ x : Rat, …`. -/
partial def solveExistential (solveGoal : MVarId → TacticM Unit)
    (g : MVarId) : TacticM Unit := do
  -- The carrier `α` comes from the existential binder; build its certificate
  -- context once (witnesses + the inconsistency-probe Farkas proof use it).
  let (carrier, fctx) ← g.withContext do
    let t ← whnf (← instantiateMVars (← g.getType))
    let args := t.getAppArgs
    unless t.getAppFn.isConstOf ``Exists && args.size == 2 do
      throwError "lp(∃): expected an existential goal, got{indentExpr (← g.getType)}"
    let carrier ← whnf args[0]!
    pure (carrier, ← mkFrontendCtx carrier)
  -- Collect outer hypotheses (visible before entering the binders); used
  -- only by the inconsistency-probe fallback on `.infeasible`.
  let (hypRows, hypState) ← g.withContext do
    (collectHyps).run { carrier }
  -- Enter the existential telescope, parse the body, solve the witness
  -- LP, and pop the primal back out as an `Array Rat` (closed values
  -- remain valid outside the telescope).
  let result : Except (Option String) (Array Rat) ← g.withContext do
    let target ← instantiateMVars (← g.getType)
    peelExistsRat target #[] fun binders body => do
      if binders.size = 0 then
        throwError "lp(∃): expected at least one `∃ x : Rat, _` binder"
      -- Parse the body. The walker classifies each inner `∀ y : Rat, _`
      -- as x-independent (residual rows on the witness LP) or
      -- x-dependent (Benders subproblems), returning the atoms,
      -- residual rows, and Benders subproblems in one pass.
      let ((atoms, univResiduals, bendersUnivs), _) ←
        (collectExistsBody binders body).run { vars := binders, carrier }
      checkClosedBody atoms binders
      -- Encode each atomic constraint as `lhs - rhs ≤ 0` (an `=` atom
      -- expands to a `≤ 0` row in each direction), then append the
      -- inner-`∀` residual rows (each already in `≤ 0` form).
      let mut lpRows : Array LinExpr := #[]
      for (rel, lhs, rhs) in atoms do
        let d := lhs.sub rhs
        match rel with
        | .le => lpRows := lpRows.push d
        | .eq =>
            lpRows := lpRows.push d
            lpRows := lpRows.push d.neg
        | .lt =>
            throwError "lp(∃): strict inequalities are not supported"
      lpRows := lpRows ++ univResiduals
      if bendersUnivs.isEmpty then
        -- No x-dependent guards: a single witness LP solves the whole
        -- problem.
        solveWitnessLP lpRows binders
      else
        -- x-dependent guards present: iterative Benders search. The
        -- accepted candidate is validated post-splice by the
        -- x-independent sup-LP machinery (each original
        -- `∀ y, G(x*, y) → atomic(x*, y)` becomes y-only after
        -- substitution and falls through that path).
        runBendersLoop binders lpRows bendersUnivs
  match result with
  | .ok primal =>
      -- Splice the primal as carrier numerals into an `Exists.intro` chain.
      let mut curG := g
      for v in primal do
        let wExpr ← fctx.mkNumeral v
        curG ← introExistsRat curG wExpr
      -- Residual: closed `And`/`Eq`/`LE` conjunction in `Rat`. Discharge
      -- via the closed-goal atomic short-circuit.
      solveGoal curG
  | .error none =>
      -- Witness LP infeasible: probe whether outer hyps are inconsistent.
      match ← tryHypsInconsistent fctx hypRows hypState.vars (← g.getType) with
      | some proof =>
          g.assign proof
      | none =>
          throwError "lp(∃): existential body is infeasible and the {
            ""}tactic could not certify that the outer hypotheses are {
            ""}inconsistent. The goal may still be provable by other means."
  | .error (some msg) =>
      throwError "lp(∃): {msg}"

end LP.Tactic.LP.Internal
