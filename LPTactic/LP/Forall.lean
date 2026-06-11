module
public meta import LPTactic.Dispatch
public meta import LPTactic.LP.BackendOption
public meta import LPTactic.LP.Certificate

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-- Solve a witness LP for the existential binders. Each row carries a `strict`
flag: a `true` row `coeffsᵀ x + const ≤ 0` must be satisfied *strictly*
(`< 0`) by the returned witness.

When no row is strict the LP has a constant-zero objective — any feasible
point is optimal. When some row is strict, we maximize a bounded slack `s`
(`s ≤ 1`) tightening each strict row to `coeffsᵀ x + s ≤ -const`
(`buildStrictProblem`); a certified optimum with `s > 0` gives a witness
that satisfies every strict row strictly (`coeffsᵀ x + const ≤ -s < 0`),
while non-strict rows stay at `≤ 0`. An optimum with `s ≤ 0` means no
strictly-feasible point exists, reported as infeasible.

On success returns the primal `Array Rat` of size `binders.size` (the margin
column, when present, is dropped). On infeasibility returns `Except.error
none`; on any non-`.optimal`, non-`.infeasible` outcome returns
`Except.error (some msg)`.

Pre: every `lpRows` entry is in `≤ 0` form (`coeffsᵀ x + const ≤ 0`). -/
def solveWitnessLP (lpRows : Array (LinExpr × Bool)) (binders : Array FVarId) :
    MetaM (Except (Option String) (Array Rat)) := do
  if lpRows.size = 0 then
    -- No constraints: any witness works; pick `0` for each binder.
    return .ok (Array.replicate binders.size (0 : Rat))
  let bIdx := mkVarIdx binders
  let rowDense := lpRows.map (·.1.toDense bIdx)
  let rowConsts := lpRows.map (·.1.const)
  let strictFlags := lpRows.map (·.2)
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  if strictFlags.any (·) then
    -- Strict rows present: maximize the slack `s` and accept iff its certified
    -- value is positive (so each strict row holds strictly at the witness).
    let pS := buildStrictProblem rowDense rowConsts strictFlags binders.size hSize
    let normalized ←
      match validate pS with
      | .error e => return .error (some s!"invalid generated problem: {repr e}")
      | .ok p => pure p
    let sol ←
      match ← LP.dispatchSolveExact opts normalized (← getBackendOverride) with
      | .error e => return .error (some s!"solveExact failed: {repr e}")
      | .ok sol => pure sol
    match sol.status with
    | .optimal =>
        let some pr := sol.certificate.primal
          | return .error (some "SoPlex reported optimal but returned no primal certificate")
        let primal := pr.toArray
        -- The margin LP has `binders.size + 1` columns (the witness columns
        -- `0 .. binders.size-1` plus the margin column `binders.size`); guard the
        -- shape so a malformed primal is a clean error, not a panic.
        unless primal.size == binders.size + 1 do
          return .error (some s!"strict witness LP returned {primal.size} primal entries, expected {binders.size + 1}")
        -- Recompute the margin from the primal (we do not trust the solver's
        -- objective) and accept only if it is positive, so each strict row holds
        -- strictly at the witness.
        let margin := primal[binders.size]!
        unless decide (0 < margin) do return .error none
        return .ok (primal.extract 0 binders.size)
    | .infeasible => return .error none
    | .unbounded =>
        -- Cannot arise: the margin column is bounded above by `1`. Treat as a
        -- solver/verifier invariant violation.
        return .error (some "SoPlex reported `unbounded` for the bounded-margin witness LP; treating as an unchecked invariant violation")
    | s => return .error (some s!"solver outcome was unchecked: {repr s}")
  else
    let objCoeffs := Array.replicate binders.size (0 : Rat)
    let p := buildProblem rowDense rowConsts objCoeffs 0 binders.size hSize
    let normalized ←
      match validate p with
      | .error e => return .error (some s!"invalid generated problem: {repr e}")
      | .ok p => pure p
    let sol ←
      match ← LP.dispatchSolveExact opts normalized (← getBackendOverride) with
      | .error e => return .error (some s!"solveExact failed: {repr e}")
      | .ok sol => pure sol
    match sol.status with
    | .optimal =>
        let some pr := sol.certificate.primal
          | return .error (some "SoPlex reported optimal but returned no primal certificate")
        return .ok pr.toArray
    | .infeasible => return .error none
    | .unbounded =>
        -- Cannot arise for a constant-zero objective. Treat as a
        -- solver/verifier invariant violation.
        return .error (some "SoPlex reported `unbounded` for a constant-zero objective; treating as an unchecked invariant violation")
    | s => return .error (some s!"solver outcome was unchecked: {repr s}")
/-! ## Inner-`∀` elimination over x-independent guards.

Extends the existential body grammar with subformulas of shape
`∀ y₁ … yₘ : Rat, G₁ → … → Gₖ → atomic(x, y)` where the universal
guards `Gᵢ` and the atomic body's `y`-dependent part form an LP region
independent of the existential-bound `x`. Each such universal is
eliminated by a sup-LP that bounds `β(y)` over the guard region; the
resulting `α(x) + γ + M ≤ 0` constraint joins the witness LP.

After the witness is spliced, each residual `∀ y, G → atomic(witness, y)`
falls back to the atomic-goal path via `solveGoal`'s
`intros`+`solveAtomic` recursion: `G`-hypotheses are picked up by
`collectHyps`, and the same Farkas multipliers that proved
sup-boundedness reconstruct the bound on `β(y)`. The vacuous-guard
case (`Verified.infeasible` on the sup-LP) adds no constraint to the
witness LP; the atomic-goal infeasibility branch derives `False` from
the `G`-hypotheses post-splicing and closes the atomic via
`False.elim`.

Limitations:
- No outer-parameter promotion: outer Rat locals are rejected in both
  the universal body's `α(x)` and the guards. The two failure modes
  ("Outer parameter in body" vs "Outer parameter in guard") get
  separate diagnostics.
- Strict universal guards and strict universal bodies are supported on
  the x-independent path: a strict guard relaxes to its closure for the
  sup-LP (sound, since the actual region is smaller), and a strict body
  marks its residual row `strict` so the witness LP places `x*` strictly
  inside. Each residual `∀ y, G(x*, y) → atomic(x*, y)` is re-proved
  post-splice by the top-level strict-aware Farkas machinery, so
  soundness never rests on the witness LP's strict reasoning. This is a
  conservative sufficient condition for witness selection, not a decision
  procedure: a strict body whose sup over the *closed* region is attained
  only on a strict guard face can be rejected even though a witness
  exists. On the Benders (x-dependent guard) path strict guards and
  strict bodies are still rejected (the cut machinery is non-strict).
- Bilinear `x * y` terms in the universal body are rejected by the
  extractor (one side of `*` must be a reducibly-closed Rat scalar). -/

/-- Is `e` of the form `∀ y : Rat, _` with the binder actually used in the
body? `Rat → P` (non-dependent function type) is *not* recognized as a
universal — the inner-`∀` path only fires on quantifiers, not implications. -/
def isForallRat? (e : Expr) : MetaM Bool := do
  match ← whnf e with
  | .forallE _ ty body _ =>
      let tyW ← whnf ty
      return (← isCarrierType tyW) && body.hasLooseBVars
  | _ => return false

/-- Outcome of the sup-LP for one body direction of an x-independent
inner universal. -/
inductive SupResult
  | /-- Optimal: `M` is the Lean-recomputed value of `β` at the spliced
       primal; the witness LP receives `α(x) + γ + M ≤ 0`. -/
    bounded (M : Rat)
  | /-- Verified vacuity: the guard LP is infeasible; the universal is
       vacuously true and contributes no witness-LP constraint. The
       post-splice atomic obligation falls through to the atomic-goal
       path, which discharges it from the (infeasible) guard hypotheses
       via `False.elim`. -/
    vacuous

/-- Build and solve `max β(y) s.t. (guardsLe each ≤ 0)`.

- `.bounded M` on optimal: `M := β.evalAt` recomputed from the
  solver-returned primal (we do not trust the solver's objective).
- `.vacuous` on infeasible: the guard region is empty.
- Throws on `unbounded` or any unchecked status (with diagnostic). -/
def runSupLP (yBinders : Array FVarId) (guardsLe : Array LinExpr)
    (β : LinExpr) : MetaM SupResult := do
  if guardsLe.size = 0 then
    -- No guards: feasible region is all of `R^|y|`. If `β` is constant
    -- in `y`, the sup is just that constant; otherwise the sup is `+∞`.
    if β.coeffs.size = 0 then
      return .bounded β.const
    throwError "lp(∀): universal has no guards but `β(y)` is non-constant; {
      ""}sup is unbounded above. Universal constraint impossible under the stated guard."
  -- Guards present: must run the LP to detect vacuity even when `β` is
  -- constant in `y`. A constant-`β` universal with infeasible guards is
  -- still vacuously true, and dropping the residual row is necessary:
  -- otherwise the strengthened witness LP would carry a fake row
  -- `α(x) + γ + β.const ≤ 0` that may rule out an otherwise good witness.
  let yIdx := mkVarIdx yBinders
  let rowDense := guardsLe.map (·.toDense yIdx)
  let rowConsts := guardsLe.map (·.const)
  let objCoeffs := β.toDense yIdx
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs 0 yBinders.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => throwError "lp(∀): invalid sup-LP: {repr e}"
    | .ok p => pure p
  let sol ←
    match ← LP.dispatchSolveExact opts normalized (← getBackendOverride) with
    | .error e => throwError "lp(∀): solveExact failed on sup-LP: {repr e}"
    | .ok sol => pure sol
  match sol.status with
  | .optimal =>
      let some pr := sol.certificate.primal
        | throwError "lp(∀): sup-LP reported optimal without a primal certificate"
      let M := β.evalAt yIdx pr.toArray
      return .bounded M
  | .infeasible =>
      return .vacuous
  | .unbounded =>
      throwError "lp(∀): sup-LP is unbounded above; universal constraint impossible {
        ""}under the stated guard"
  | s =>
      throwError "lp(∀): sup-LP outcome was unchecked: {repr s}"

/-- Parse a universal guard expression into `≤ 0` directions over
`xBinders ∪ yBinders` (1 row for `≤`, 2 for `=`), paired with whether the
guard was strict (`<`). No validation against xBinder occurrence; the
caller decides whether x-dependence is acceptable (the x-independent path
accepts strict guards and routes to a sup-LP; the Benders path rejects
strict guards). A strict guard relaxes to its closure (`≤`) here: the
sup-LP only needs the closed region (using a larger region for a sup
bound is sound), and the actual strict guard is recovered by the
post-splice atomic re-proof. Unparseable shapes are rejected at this
layer. -/
def parseGuardLinExprs (xBinders yBinders : Array FVarId) (carrier : Expr) (g : Expr) :
    MetaM (Array LinExpr × Bool) := do
  let parsed ← (parseAtomic? g).run' { vars := xBinders ++ yBinders, carrier }
  match parsed with
  | none =>
      throwError "lp(∀): universal guard must be an atomic Rat {
        ""}(in)equality{indentExpr g}"
  | some (.lt, _, _, lhs, rhs) =>
      -- Strict guard: relax to its closure for the LP region; report strictness.
      return (#[lhs.sub rhs], true)
  | some (.le, _, _, lhs, rhs) =>
      return (#[lhs.sub rhs], false)
  | some (.eq, _, _, lhs, rhs) =>
      let d := lhs.sub rhs
      return (#[d, d.neg], false)

/-! ## Inner-`∀` with x-dependent guards via Benders.

Extends the inner-`∀` path to subformulas whose guards may mention the
surrounding existential variables, via an iterative constraint-generation
(Benders) search for a witness `x*`. The cuts are search-direction
guidance only — they do **not** appear in the final proof. Once Benders
accepts a candidate `x*`, the witness is spliced via `Exists.intro`,
after which each original `∀ y, G(x*, y) → atomic(x*, y)` becomes y-only
(since `x*` is a concrete `Rat` literal); the x-independent sup-LP
machinery discharges each universal directly at `x*`, and the
closed-goal atomic short-circuit handles the residual atoms.

Policy (no completeness commitment):
- `Verified.unbounded` from any subproblem → tactic fails with a precise
  message. Generating sound ray cuts on `x` requires a Farkas projection
  over the guard polyhedron and is not currently implemented.
- Outer `Rat` parameters in either body or guard → rejected at the
  numeric-witness restriction (rejected before any Benders work).
- Strict guards / strict bodies → rejected.
- Extreme dual extraction is not enforced; SoPlex's returned dual is
  used directly, with duplicate-cut detection plus a max-iterations
  safety net guarding against cycling on adversarial bases. -/

/-- One body direction of an x-dependent universal subformula, captured
in the parametric form

```
∀ y, A · y ≤ b + B · x  →  p · y ≤ q · x + r
```

with each guard row stored as a (`guardY`, `guardX`) pair of `LinExpr`s
whose sum is the original guard's `≤ 0` direction. The subproblem at a
concrete `x*` is `max bodyY(y) s.t. (guardY(y) + guardX.evalAt(x*) ≤ 0)`,
and the body is satisfied at `x*` iff `M + bodyX.evalAt(x*) ≤ 0`. -/
structure BendersUniversal where
  yBinders : Array FVarId
  guardY : Array LinExpr
  guardX : Array LinExpr
  bodyY : LinExpr
  bodyX : LinExpr
  /-- The original `∀`-expression, retained only for diagnostics. -/
  source : Expr := default

/-- Outcome of a Benders subproblem solve at a concrete candidate `x*`. -/
inductive BendersSubResult
  | /-- Subproblem is feasible with finite optimum `M` and dual `λ`.
       `λ.size` equals the row count of the parametric LP. -/
    bounded (M : Rat) (lam : Array Rat)
  | /-- Verified-infeasible guards at `x*`: the universal is vacuously
       true at this candidate, no cut. -/
    infeasibleGuard
  | /-- Subproblem unbounded: fail fast (the corresponding ray cut on
       `x` is non-linear and is not currently produced). -/
    unboundedFail (msg : String)
  | /-- `Verified.unchecked` from SoPlex: fail. -/
    uncheckedFail (msg : String)

/-- Solve the parametric subproblem at a concrete `xStar`: maximize
`bodyY(y)` subject to `guardY[i](y) + guardX[i].evalAt(xStar) ≤ 0`.
Returns `bounded M λ`, `infeasibleGuard`, `unboundedFail`, or
`uncheckedFail`. Dispatches on `Verified.{optimal,infeasible,unbounded,
unchecked}` exactly as the x-independent sup-LP does. -/
def runBendersSubproblem (u : BendersUniversal)
    (xBinders : Array FVarId) (xStar : Array Rat) : MetaM BendersSubResult := do
  -- Build the y-only rows: each `guardY[i]` with constant
  -- `guardX[i].evalAt(xStar)`. A constant-`bodyY` subproblem with no
  -- y-only rows has its optimum equal to `bodyY.const` (treated as
  -- bounded), and a constant-`bodyY` subproblem with no constraints can
  -- still arrive via constant guards — let SoPlex handle it normally.
  let nRows := u.guardY.size
  let xIdx := mkVarIdx xBinders
  let mut rowLins : Array LinExpr := Array.mkEmpty nRows
  for h : i in [0:nRows] do
    let gy := u.guardY[i]
    let gx := u.guardX[i]!
    let c := gx.evalAt xIdx xStar
    rowLins := rowLins.push { const := gy.const + c, coeffs := gy.coeffs }
  if u.yBinders.isEmpty then
    -- Degenerate: no y-variables. `bodyY` is then constant and the
    -- subproblem is feasibility-of-guards only. Check guard feasibility
    -- numerically (all rows must satisfy `const ≤ 0`).
    let allOk := rowLins.all (fun L => decide (L.const ≤ 0))
    if !allOk then return .infeasibleGuard
    return .bounded u.bodyY.const (Array.replicate nRows 0)
  if rowLins.isEmpty then
    -- No guards: feasible region is `R^|y|`. Bounded iff `bodyY` is
    -- constant in y.
    if u.bodyY.coeffs.size = 0 then
      return .bounded u.bodyY.const #[]
    return .unboundedFail
      "lp (Benders): subproblem has no guards but `p · y` is non-constant; sup is +∞."
  let yIdx := mkVarIdx u.yBinders
  let rowDense := rowLins.map (·.toDense yIdx)
  let rowConsts := rowLins.map (·.const)
  let objCoeffs := u.bodyY.toDense yIdx
  have hSize : rowDense.size = rowConsts.size := by
    simp [rowDense, rowConsts]
  let p := buildProblem rowDense rowConsts objCoeffs 0 u.yBinders.size hSize
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  let normalized ←
    match validate p with
    | .error e => return .uncheckedFail s!"invalid Benders subproblem LP: {repr e}"
    | .ok p => pure p
  let sol ←
    match ← LP.dispatchSolveExact opts normalized (← getBackendOverride) with
    | .error e => return .uncheckedFail s!"solveExact failed on Benders subproblem: {repr e}"
    | .ok sol => pure sol
  match sol.status with
  | .optimal =>
      let some pr := sol.certificate.primal
        | return .uncheckedFail "Benders subproblem reported optimal without a primal certificate"
      let some d := sol.certificate.dual
        | return .uncheckedFail "Benders subproblem reported optimal without a dual certificate"
      -- Recompute objective at primal; do not trust SoPlex's number.
      let M := u.bodyY.evalAt yIdx pr.toArray
      let lam := d.rowUpper.toArray
      -- Sanity: nonnegativity of multipliers (a maximize LP's row-upper
      -- duals must be ≥ 0; reject otherwise).
      unless lam.all (fun l => 0 ≤ l) do
        return .uncheckedFail "Benders subproblem dual has a negative multiplier"
      return .bounded M lam
  | .infeasible =>
      return .infeasibleGuard
  | .unbounded =>
      return .unboundedFail
        ("lp (Benders): cannot produce a linear cut from an unbounded subproblem; " ++
         "the goal may still be true but requires symbolic-QE machinery " ++
         "that is not currently implemented.")
  | s =>
      return .uncheckedFail s!"Benders subproblem outcome was unchecked: {repr s}"

/-- Compute the Benders optimal-point cut from a subproblem with dual
multipliers `λ`. In the parametric form `∀ y, A·y ≤ b + B·x → p·y ≤ q·x + r`,
the standard cut is `(λᵀ B − q) · x ≤ r − λᵀ b`. In our `≤ 0`
representation this is `cut := bodyX - Σᵢ λᵢ · guardX[i] ≤ 0`. -/
def computeBendersCut (u : BendersUniversal) (lam : Array Rat) : LinExpr := Id.run do
  let mut acc : LinExpr := u.bodyX
  for h : i in [0:u.guardX.size] do
    let l := lam[i]!
    if l ≠ 0 then
      acc := acc.sub (u.guardX[i].smul l)
  return acc

/-- Outcome of canonicalising a candidate Benders cut. -/
inductive CutCanon
  | /-- Cut canonicalises to `0 ≤ 0` or `0 ≤ c` with `c ≥ 0` — drop it. -/
    tautology
  | /-- Cut canonicalises to `0 ≤ c` with `c < 0` — search cannot
       continue from this candidate without first finding an inconsistency. -/
    contradiction
  | /-- Cut is non-degenerate; carries the canonical form (for duplicate
       detection) plus the proof-shaped `LinExpr` to splice into the master. -/
    normal (key : Array (FVarId × Int) × Int) (cut : LinExpr)

def fvarLt (a b : FVarId) : Bool :=
  match a.name.quickCmp b.name with
  | .lt => true
  | _ => false

/-- Canonicalise a Benders cut into a form suitable for tautology /
contradiction detection and duplicate hashing. The cut is fixed in
`coeffs · x + const ≤ 0` orientation; canonicalization clears
denominators, divides by the *positive* gcd, drops zero coeffs, and
sorts coeffs by FVarId. Do **not** sign-flip after this step — the
orientation is intrinsic to the cut. -/
def canonicaliseCut (cut : LinExpr) : CutCanon := Id.run do
  -- Step 1: drop zero coeffs and sort. (`addCoeff` should already have
  -- merged duplicates, but we re-sort here.)
  let nz := cut.coeffs.filter (fun (_, c) => c ≠ 0)
  let sorted := nz.qsort (fun (a, _) (b, _) => fvarLt a b)
  if sorted.isEmpty then
    -- Pure-constant `const ≤ 0` form.
    if cut.const ≤ 0 then return .tautology
    else return .contradiction
  -- Step 2: clear denominators by multiplying by LCM of all denominators
  -- (including const's).
  let lcmDen : Nat := denLcm ((sorted.map (fun (_, c) => c)).push cut.const)
  let lcmInt : Int := Int.ofNat lcmDen
  let scaleRat (r : Rat) : Int := r.num * (lcmInt / Int.ofNat r.den)
  let intCoeffs : Array (FVarId × Int) := sorted.map (fun (v, c) => (v, scaleRat c))
  let intConst : Int := scaleRat cut.const
  -- Step 3: divide by positive gcd of |intCoeffs| and |intConst|.
  let mut g : Nat := intConst.natAbs
  for (_, c) in intCoeffs do
    g := Nat.gcd g c.natAbs
  if g = 0 then
    -- All zero (shouldn't happen given sorted.isEmpty short-circuit).
    return .tautology
  let gInt : Int := Int.ofNat g
  let finalCoeffs : Array (FVarId × Int) := intCoeffs.map (fun (v, c) => (v, c / gInt))
  let finalConst : Int := intConst / gInt
  -- Step 4: emit normal form with the proof-shaped `LinExpr` rebuilt
  -- (over the sorted FVarIds; integer coefficients reinterpreted as
  -- `Rat`s).
  let normCoeffs : Array (FVarId × Rat) :=
    finalCoeffs.map (fun (v, c) => (v, Rat.ofInt c))
  let normLin : LinExpr := { const := Rat.ofInt finalConst, coeffs := normCoeffs }
  return .normal (finalCoeffs, finalConst) normLin

/-- A canonical-form key plus the candidate-rejection log. Tracks the
duplicate-detection state across a Benders run. -/
structure BendersState where
  /-- Canonical keys of cuts already in the master. Append-only. -/
  cutKeys : Array (Array (FVarId × Int) × Int) := #[]
  /-- Master constraints: the `x`-independent body atoms plus all
      accepted cuts, each in `≤ 0` form over `xBinders`, paired with a
      `strict` flag. Generated Benders cuts are always non-strict; a
      `strict` master row comes only from the existential's own strict
      atoms, carried in via `initialMaster`. -/
  masterRows : Array (LinExpr × Bool) := #[]
  /-- Candidates already proposed by the master LP (deduplicated by
      vector equality). If the master proposes the same candidate twice
      the search is stuck. -/
  triedCandidates : Array (Array Rat) := #[]
  iter : Nat := 0
  deriving Inhabited

def keyEq (a b : Array (FVarId × Int) × Int) : Bool :=
  a.snd == b.snd &&
  a.fst.size == b.fst.size &&
  (Array.zip a.fst b.fst).all (fun ((v1, c1), (v2, c2)) => v1 == v2 && c1 == c2)

def arrayRatEq (a b : Array Rat) : Bool :=
  a.size == b.size && (Array.zip a b).all (fun (x, y) => x == y)

/-- Configurable upper bound on Benders iterations. With cut
canonicalization and duplicate suppression, finite termination *should*
hold under nondegenerate dual extraction, but adversarial degeneracy
without extreme-dual selection can cycle; the bound is a safety net. -/
def bendersMaxIter : Nat := 64

/-- Run the Benders cutting-plane search. Returns either a Rat-valued
witness `x*` (each universal verified-satisfied at `x*`) or an error
message. The user-facing proof is built afterwards by the caller via
`introExistsRat` + post-splice validation through the x-independent
sup-LP machinery. -/
partial def runBendersLoop (xBinders : Array FVarId)
    (initialMaster : Array (LinExpr × Bool)) (universals : Array BendersUniversal) :
    MetaM (Except (Option String) (Array Rat)) := do
  let mut state : BendersState :=
    { masterRows := initialMaster, cutKeys := #[], triedCandidates := #[], iter := 0 }
  let xIdx := mkVarIdx xBinders
  while state.iter < bendersMaxIter do
    state := { state with iter := state.iter + 1 }
    -- Solve the master LP.
    let candResult ← solveWitnessLP state.masterRows xBinders
    let xStar ←
      match candResult with
      | .error none =>
          -- Master infeasible. Two ways this happens:
          -- (a) initial master was infeasible (caller falls back to
          --     inconsistency probe);
          -- (b) accumulated cuts made the master infeasible. v1 cannot
          --     distinguish a real infeasibility-of-the-existential
          --     from "search exhausted because cuts over-excluded";
          --     return the same `.error none` so the caller probes
          --     hypotheses (correct fallback semantics).
          return .error none
      | .error (some msg) => return .error (some msg)
      | .ok xStar => pure xStar
    -- Candidate repeat detection.
    if state.triedCandidates.any (arrayRatEq xStar) then
      return .error (some "lp (Benders): made no progress — the same candidate was proposed twice.")
    state := { state with triedCandidates := state.triedCandidates.push xStar }
    -- Subproblem sweep. We accept the candidate iff every universal is
    -- satisfied at `x*`; otherwise we accumulate the *first* violating
    -- cut and restart. Accumulating all violations at once is also
    -- valid but can over-constrain the master; one at a time is the
    -- textbook Benders loop.
    let mut anyViolation := false
    for u in universals do
      match ← runBendersSubproblem u xBinders xStar with
      | .infeasibleGuard =>
          continue
      | .unboundedFail msg => return .error (some msg)
      | .uncheckedFail msg => return .error (some msg)
      | .bounded M lam =>
          let bodyAtX := u.bodyX.evalAt xIdx xStar
          if M + bodyAtX ≤ 0 then continue
          -- Violation: derive cut.
          let cut := computeBendersCut u lam
          match canonicaliseCut cut with
          | .tautology =>
              -- At a violating candidate, an optimal dual must satisfy
              --   cut.evalAt(x*) = M + bodyX.evalAt(x*) > 0,
              -- so a tautological cut here means the dual returned by
              -- SoPlex failed an invariant (stationarity / nonnegativity)
              -- or we computed the cut with the wrong sign. Surface it
              -- distinctly from a routine "weak cut" outcome.
              return .error (some
                ("lp (Benders): derived a tautological cut at a violating " ++
                 "candidate. The dual certificate from SoPlex appears not to be " ++
                 "optimal — this is an invariant violation, not a routine " ++
                 "non-extreme-dual outcome."))
          | .contradiction =>
              -- Cut-augmented master would be inconsistent. Caller
              -- falls back to inconsistency probe on H.
              return .error none
          | .normal key cutLin =>
              if state.cutKeys.any (keyEq key) then
                -- The previous identical cut is already in the master,
                -- so `x*` should not have been master-feasible. Hitting
                -- this branch implies the master LP returned a vertex
                -- the cut set already excludes — again an invariant
                -- violation rather than non-extreme-dual fallout.
                return .error (some
                  ("lp (Benders): duplicate cut produced for a candidate " ++
                   "the existing cut should already exclude — invariant violation."))
              state := { state with
                cutKeys := state.cutKeys.push key
                -- Benders cuts are always non-strict (`≤ 0`); strict universal
                -- bodies are rejected before reaching this path. Strict rows in
                -- the master come only from the existential's own strict atoms,
                -- carried in `initialMaster`.
                masterRows := state.masterRows.push (cutLin, false) }
              anyViolation := true
              break
    if !anyViolation then
      -- All universals satisfied at `x*`; accept candidate.
      return .ok xStar
  return .error (some
    s!"lp (Benders): hit the max-iterations safety net ({bendersMaxIter}); search exhausted.")

/-- Classification of an inner-`∀` subformula based on whether any
guard mentions an existential binder. -/
inductive UniversalDispatch
  | /-- All guards are x-independent → residual `≤ 0` rows on `xBinders`
       that join the witness LP directly, each paired with a `strict`
       flag (a strict universal body yields a strict residual row). -/
    independentGuards (residuals : Array (LinExpr × Bool))
  | /-- At least one guard mentions an existential binder → Benders
       subproblems (one per body direction). -/
    dependentGuards (universals : Array BendersUniversal)

/-- Classify one universal subformula, building the data needed for
either the x-independent path or the Benders path. The numeric-witness
restriction is enforced here (before any Benders work): outer Rat
parameters in either the body or any guard cause a precise rejection. -/
def classifyUniversal (xBinders : Array FVarId) (carrier : Expr) (forallExpr : Expr) :
    MetaM UniversalDispatch := do
  let forallExpr ← whnf forallExpr
  Meta.forallTelescopeReducing forallExpr fun args bodyAtom => do
    -- Partition `args` into yBinders (Rat-typed) and guard hypotheses (Prop).
    let mut yBinders : Array FVarId := #[]
    let mut guardExprs : Array Expr := #[]
    let mut seenGuard : Bool := false
    for arg in args do
      let argId := arg.fvarId!
      let decl ← argId.getDecl
      let ty ← whnf decl.type
      if ← isDefEq ty carrier then
        if seenGuard then
          throwError "lp(∀): universal `Rat` binders must precede guards{
            indentExpr forallExpr}"
        yBinders := yBinders.push argId
      else
        seenGuard := true
        guardExprs := guardExprs.push arg
    if yBinders.isEmpty then
      throwError "lp(∀): expected at least one `∀ y : Rat, _` binder{
        indentExpr forallExpr}"
    -- Parse guards as `Array LinExpr` (no x/y validation yet), tracking whether
    -- any guard was strict (`<`).
    let mut allGuardDirs : Array LinExpr := #[]
    let mut anyStrictGuard := false
    for hExpr in guardExprs do
      let gType ← inferType hExpr
      let (dirs, strict) ← parseGuardLinExprs xBinders yBinders carrier gType
      allGuardDirs := allGuardDirs ++ dirs
      anyStrictGuard := anyStrictGuard || strict
    -- Validate guard scope: each coefficient must be in `xBinders ∪ yBinders`.
    -- Outer Rat parameters in any guard are rejected (numeric-witness restriction).
    let mut anyXInGuard := false
    for L in allGuardDirs do
      let (_, _, outside) := L.partitionXY xBinders yBinders
      if outside.size > 0 then
        let nameStrs ← outside.toList.mapM fun v => do
          return s!"`{(← v.getDecl).userName}`"
        throwError "lp(∀): outer Rat local(s) {String.intercalate ", " nameStrs} {
          ""}appear in a universal guard{indentExpr forallExpr}; parametric {
          ""}witnesses are not supported"
      for (v, _) in L.coeffs do
        if xBinders.any (· == v) then anyXInGuard := true
    -- Parse body atomic.
    let parsedBody ← (parseAtomic? bodyAtom).run' { vars := xBinders ++ yBinders, carrier }
    let some (rel, _, _, lhsLin, rhsLin) := parsedBody
      | throwError "lp(∀): universal body must be an atomic Rat {
          ""}(in)equality{indentExpr bodyAtom}"
    -- A strict (`<`) body is supported on the x-independent path: its residual
    -- row is marked strict so the witness LP places `x*` strictly inside. On the
    -- Benders (x-dependent guard) path strict bodies and strict guards are
    -- rejected below — the cut machinery is non-strict there.
    let bodyStrict := rel = .lt
    let d := lhsLin.sub rhsLin
    let bodyDirs : Array LinExpr :=
      match rel with
      | .le => #[d]
      | .lt => #[d]
      | .eq => #[d, d.neg]
    -- Validate body coeffs: only in `xBinders ∪ yBinders`. The
    -- numeric-witness restriction is enforced here too.
    for L in bodyDirs do
      let (_, _, outside) := L.partitionXY xBinders yBinders
      if outside.size > 0 then
        let nameStrs ← outside.toList.mapM fun v => do
          return s!"`{(← v.getDecl).userName}`"
        throwError "lp(∀): outer Rat local(s) {String.intercalate ", " nameStrs} {
          ""}appear in the universal body{indentExpr bodyAtom}; parametric {
          ""}witnesses are not supported"
    if !anyXInGuard then
      -- x-independent guards: solve a sup-LP per body direction and
      -- contribute residual `≤ 0` rows on `xBinders` to the witness LP.
      let mut residuals : Array (LinExpr × Bool) := #[]
      for bodyDir in bodyDirs do
        let (β, α, _) := bodyDir.partitionXY xBinders yBinders
        match ← runSupLP yBinders allGuardDirs β with
        | .bounded M =>
            residuals := residuals.push ({ const := α.const + M, coeffs := α.coeffs }, bodyStrict)
        | .vacuous => pure ()
      return .independentGuards residuals
    -- At least one guard mentions an x-binder → Benders path. Strictness is not
    -- supported here: the constraint-generation cuts are derived in non-strict
    -- (`≤ 0`) form, and a strict guard / body would need a strict-aware cut and
    -- duplicate-key scheme this path does not implement. Reject with a targeted
    -- message (the x-independent path and the existential's own atoms keep full
    -- strict support).
    if anyStrictGuard then
      throwError "lp(∀): a strict (`<`) guard in a universal routed to the {
        ""}Benders (x-dependent guard) path is not supported; the Benders path {
        ""}uses non-strict cuts{indentExpr forallExpr}"
    if bodyStrict then
      throwError "lp(∀): a strict (`<`) universal body under an x-dependent {
        ""}guard (Benders path) is not supported{indentExpr forallExpr}"
    -- Build one BendersUniversal per body direction. Each direction shares the
    -- same guard data; only the body splits differ for an `=` body.
    let mut guardY : Array LinExpr := #[]
    let mut guardX : Array LinExpr := #[]
    for L in allGuardDirs do
      let (β, α, _) := L.partitionXY xBinders yBinders
      -- `α` is the x-part with const = L.const; `β` is y-only, const 0.
      guardY := guardY.push β
      guardX := guardX.push α
    let mut bendUniversals : Array BendersUniversal := #[]
    for bodyDir in bodyDirs do
      let (β, α, _) := bodyDir.partitionXY xBinders yBinders
      bendUniversals := bendUniversals.push
        { yBinders := yBinders
          guardY := guardY
          guardX := guardX
          bodyY := β
          bodyX := α
          source := forallExpr }
    return .dependentGuards bendUniversals


end LP.Tactic.LP.Internal
