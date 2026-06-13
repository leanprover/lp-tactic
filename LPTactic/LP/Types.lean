module
public meta import Lean
public import Init.Data.Vector.Lemmas
public import LPTactic.Basic
public import LPTactic.Q
meta import LPTactic.LP.CarrierLemmas

public meta section

open Lean Meta Elab Tactic
open LP LP.Verify
open LP.Tactic (Q)

namespace LP.Tactic.LP.Internal

/-! # Direct certificate backend for the `lp` tactic.

SoPlex is used as an untrusted oracle to find Farkas / dual multipliers.
The proof term is a compact arithmetic certificate over the original
hypotheses and goal: a weighted sum of hypothesis-side `≤ 0` facts plus
a closed `Rat` algebraic identity, discharged by an explicit-proof-term
construction (`proveCertificateIdentity`). No `Problem` / `denseMatrix` /
`AffCert` data reductions reach the kernel. -/

/-! ## Small `Rat` helpers and closing lemmas -/

/-- LCM of the denominators of `rs` (`1` for the empty array). Shared by
the carrier clearing steps (`Int`/`Nat`/`Dyadic` `clearMultipliers`) and
the Benders cut canonicalizer, which all scale rationals by this value
to clear denominators. -/
def denLcm (rs : Array Rat) : Nat :=
  rs.foldl (fun acc r => Nat.lcm acc r.den) 1

theorem rat_le_of_sub_nonpos {a b : Rat} (h : a - b ≤ 0) : a ≤ b := by
  have hAdd := (Rat.add_le_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_le {a b : Rat} (h : a ≤ b) : a - b ≤ 0 := by
  have hAdd := (Rat.add_le_add_right (a := a) (b := b) (c := -b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_sub_nonpos_of_eq {a b : Rat} (h : a = b) : a - b ≤ 0 := by
  subst h
  simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel]

/-- Rewrite `e / c` as the scalar multiple `c⁻¹ * e` so the normalizer can reuse the
scalar-multiplication path. Holds unconditionally (at `c = 0` both sides are `0`).
Args explicit to match `applyLemma`. -/
theorem div_eq_inv_mul (a b : Rat) : a / b = b⁻¹ * a := by grind

/-- Divisor congruence: rewrite a compound closed divisor to its literal before the
`div_eq_inv_mul` step. Args explicit to match `applyLemma`. -/
theorem div_congr_eq_r (a b B : Rat) (e : b = B) : a / b = a / B := by subst e; rfl

theorem rat_lt_of_sub_neg {a b : Rat} (h : a - b < 0) : a < b := by
  have hAdd := (Rat.add_lt_add_right (a := a - b) (b := 0) (c := b)).mpr h
  simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add]
    using hAdd

theorem rat_le_of_nonneg_sub {a b : Rat} (h : 0 ≤ b - a) : a ≤ b :=
  LP.Verify.RatAux.sub_nonneg.mp h

theorem rat_lt_of_pos_sub {a b : Rat} (h : 0 < b - a) : a < b := by
  have hle : a ≤ b := rat_le_of_nonneg_sub (Rat.le_of_lt h)
  exact Rat.lt_of_le_of_ne hle (by
    intro hEq
    subst hEq
    simp [Rat.sub_eq_add_neg, Rat.add_neg_cancel] at h)

/-- A nonnegative scalar of a nonpositive value is nonpositive. Implicit-arg order
`{a k}` matches the shared `buildWeightedSumDecide` lemma applier. -/
theorem smul_nonpos {a k : Rat} (ha : a ≤ 0) (hk : 0 ≤ k) : k * a ≤ 0 := by
  have h := Rat.mul_le_mul_of_nonneg_left ha hk
  simpa [Rat.mul_zero] using h

/-- Sum of two nonpositive `Rat`s is nonpositive. -/
theorem add_nonpos {a b : Rat} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 := by
  have h := LP.Verify.RatAux.add_le_add ha hb
  simpa [Rat.zero_add] using h

/-- A strictly positive scalar of a strictly negative value is strictly negative.
Used to carry strictness through the weighted Farkas sum from a strict (`<`) row. -/
theorem smul_neg {a k : Rat} (ha : a < 0) (hk : 0 < k) : k * a < 0 :=
  (Rat.mul_neg_iff_of_pos_left hk).mpr ha

/-- A strictly negative head plus a nonpositive tail is strictly negative. -/
theorem add_neg_nonpos {a b : Rat} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 := by grind

/-- A nonpositive head plus a strictly negative tail is strictly negative. -/
theorem add_nonpos_neg {a b : Rat} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 := by grind

theorem le_of_lt {a b : Rat} (h : a < b) : a ≤ b := Rat.le_of_lt h

theorem zero_self_le : (0 : Rat) ≤ 0 := Rat.le_refl

/-- Final closer for non-strict goals.

Given a nonpositive sum `s ≤ 0`, a nonnegative residual `c`, and the
algebraic identity `(rhs - lhs) + s = c`, we get `lhs ≤ rhs`. The
identity is a pure `Rat` polynomial fact in the user expressions and is
discharged by the explicit-proof-term construction at tactic time. -/
theorem direct_le_close {lhs rhs s c : Rat}
    (hSum : s ≤ 0) (hC : 0 ≤ c) (hIdent : rhs - lhs + s = c) :
    lhs ≤ rhs := by
  apply rat_le_of_nonneg_sub
  -- (rhs - lhs) = c - s ; both 0 ≤ c and -s ≥ 0
  have hStep : c - s = rhs - lhs := by
    have h := hIdent
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
           Rat.add_neg_cancel, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add, Rat.neg_neg]
  rw [← hStep]
  exact LP.Verify.RatAux.sub_nonneg.mpr (Rat.le_trans hSum hC)

/-- Final closer for strict goals: same shape as `direct_le_close`, but the
residual must be strictly positive. -/
theorem direct_lt_close {lhs rhs s c : Rat}
    (hSum : s ≤ 0) (hC : 0 < c) (hIdent : rhs - lhs + s = c) :
    lhs < rhs := by
  apply rat_lt_of_pos_sub
  have hStep : c - s = rhs - lhs := by
    have h := hIdent
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
           Rat.add_neg_cancel, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add, Rat.neg_neg]
  rw [← hStep]
  -- 0 < c - s, with hC : 0 < c, hSum : s ≤ 0, so s < c (via le_lt transitivity).
  have hsc : s < c := Rat.lt_of_le_of_ne (Rat.le_trans hSum (Rat.le_of_lt hC)) (by
    intro hEq
    subst hEq
    exact (Rat.not_le.mpr hC) hSum)
  exact (Rat.lt_iff_sub_pos s c).mp hsc

/-- Strict-row closer for strict goals: when a strict (`<`) row carries a positive
multiplier the weighted sum is *strictly* negative (`s < 0`), so a merely nonnegative
residual `0 ≤ c` already yields `lhs < rhs` (no `0 < c` needed). -/
theorem direct_lt_close_strict {lhs rhs s c : Rat}
    (hSum : s < 0) (hC : 0 ≤ c) (hIdent : rhs - lhs + s = c) :
    lhs < rhs := by
  apply rat_lt_of_pos_sub
  have hStep : c - s = rhs - lhs := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
           Rat.add_neg_cancel, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add, Rat.neg_neg]
  rw [← hStep]
  -- 0 < c - s: `s < 0 ≤ c`, so `s < c`.
  exact (Rat.lt_iff_sub_pos s c).mp (by grind)

/-- Final closer for infeasibility: `s ≤ 0` and `s = c` with `0 < c` is
`False`. Used when SoPlex reports an infeasible LP and supplies a Farkas
certificate. -/
theorem direct_infeasible_close {s c : Rat}
    (hSum : s ≤ 0) (hC : 0 < c) (hIdent : s = c) : False := by
  rw [hIdent] at hSum
  exact Rat.not_le.mpr hC hSum

/-- Strict-row infeasibility closer: a strictly negative sum `s < 0` that the identity
equates to a nonnegative residual `0 ≤ c` is a contradiction (`s = c ≥ 0` but `s < 0`). -/
theorem direct_infeasible_close_strict {s c : Rat}
    (hSum : s < 0) (hC : 0 ≤ c) (hIdent : s = c) : False := by
  rw [hIdent] at hSum
  exact Rat.not_le.mpr hSum hC

/-! ## Explicit-proof-term discharger lemmas

These lemmas are the fixed-arity building blocks for the `normalizeR` /
`proveMerge` proof-term construction (`CarrierCertificate.lean`) that discharges
the closed `Rat` algebraic identities on both the optimal and infeasible branches
of the `lp` tactic. Each lemma is applied by the metaprogram with `mkAppN` and
explicit arguments; the
kernel only structurally typechecks the resulting term, never reducing a
recursive function over the certificate. Numeral side conditions on `Q`
denominators reduce via GMP `Int` arithmetic — the only kernel *reduction*
in the produced proof.

`⟦L⟧` for a sorted `LinExpr` `{const := r, coeffs := [(x₀,c₀), …]}` is
rendered right-nested with the constant innermost:
`c₀ * x₀ + (c₁ * x₁ + (… + (cₙ₋₁ * xₙ₋₁ + r) …))`. -/

declare_lp_normalizer_ring_lemmas Rat

/-! ### Mini-`norm_num` for `Q`-shaped `Rat` numeral leaves.

Each leaf proves a closed `Rat` arithmetic fact between three `Q.toRat`
literals. The side condition is a closed `Int` equality discharged by
`mkDecideProof` — the kernel reduces it via GMP `Int` multiply + `decEq`.
This is the only kernel reduction in the produced certificate proof. -/

theorem ratlit_add (qa qb qm : Q)
    (h : (Q.add qa qb).num * (qm.den : Int)
         = qm.num * ((Q.add qa qb).den : Int)) :
    qa.toRat + qb.toRat = qm.toRat := by
  rw [← Q.toRat_add]; exact Q.toRat_eq_of_cross h

theorem ratlit_mul (qa qb qm : Q)
    (h : (Q.mul qa qb).num * (qm.den : Int)
         = qm.num * ((Q.mul qa qb).den : Int)) :
    qa.toRat * qb.toRat = qm.toRat := by
  rw [← Q.toRat_mul]; exact Q.toRat_eq_of_cross h

theorem ratlit_neg (qa qm : Q)
    (h : (Q.neg qa).num * (qm.den : Int)
         = qm.num * ((Q.neg qa).den : Int)) :
    -qa.toRat = qm.toRat := by
  rw [← Q.toRat_neg]; exact Q.toRat_eq_of_cross h

/-! ## Parsing affine `Rat` expressions and `≤`/`=` hypotheses.

The parsing layer keeps proof-facing row data separate from the dense
LP matrix representation. Each parsed row carries:

* `term : Expr` — the source-side Lean expression `lhsᵢ - rhsᵢ`;
* `proof : Expr` of type `term ≤ 0`;
* `linexpr : LinExpr` — numerical coefficients on the parsed variables,
  used to build the LP problem fed to SoPlex and to compute the
  numerical residual after the dual comes back.

The proof-facing artefacts are thunks: most parsed rows receive a zero
dual multiplier, so their Lean-side term and proof are never demanded by
the certificate.
-/

inductive Rel where
  | le
  | lt
  | eq
  deriving Repr, DecidableEq

structure LinExpr where
  const : Rat := 0
  coeffs : Array (FVarId × Rat) := #[]
  deriving Inhabited

structure Row where
  /-- `lhsᵢ - rhsᵢ` (ring carriers; uses subtraction — never forced on the `Nat` path). -/
  term : MetaM Expr
  expr : LinExpr
  /-- proof of `term ≤ 0` (ring carriers). -/
  proof : MetaM Expr
  /-- the original `lhsᵢ`/`rhsᵢ` exprs and `leProof : lhsᵢ ≤ rhsᵢ` — the no-subtraction form
  the `Nat` carrier uses (a weighted `Σkᵢ·lhsᵢ ≤ Σkᵢ·rhsᵢ`). Lazy `default`s so ring carriers
  pay nothing. -/
  lhsExpr : Expr := default
  rhsExpr : Expr := default
  leProof : MetaM Expr := throwError "lp: row has no ≤-proof (non-Nat carrier)"
  /-- `true` for rows that came from a strict (`<`) hypothesis. Such a row carries the
  strict `strictProof : term < 0` in addition to the relaxed `proof : term ≤ 0`, so a
  positive multiplier on it can upgrade the Farkas sum from `≤ 0` to `< 0` — proving
  strict goals / strict contradictions the relaxed (`≤`) combination cannot. -/
  strict : Bool := false
  /-- proof of `term < 0` (ring carriers), only present (and only forced) for strict rows. -/
  strictProof : MetaM Expr := throwError "lp: row has no <-proof (non-strict row)"

def ratType : Expr := mkConst ``Rat

structure ParseState where
  vars : Array FVarId := #[]
  /-- The carrier type `α` of the goal being parsed. Atoms and scalars are
  checked against this; hypotheses over a different type are skipped. Defaults
  to `Rat` so existing `Rat`-only entry points need no change. -/
  carrier : Expr := ratType
  /-- Atomization (the atomic path only). When `true`, an unrecognized carrier-typed
  subterm (`π`, `↑n`, `‖x‖`, `f x`, `x*y`, …) becomes an opaque LP variable instead of a
  parse error. The `∃`/`∀`/`maximize` frontends leave this `false` so their binder
  variables stay genuine fvars. -/
  allowAtoms : Bool := false
  /-- Atom table: each opaque atom is given a fresh *virtual* `FVarId` (never a real local;
  it only keys `LinExpr` and is mapped back to its `Expr` for the proof term). Deduplicated
  by canonical atom `Expr` so identical atoms share a variable. -/
  atomToFVar : Std.HashMap Expr FVarId := {}
  fvarToAtom : Std.HashMap FVarId Expr := {}
  /-- Set when the parser atomized a subterm whose head operation the carrier does NOT
  model exactly — truncating `Nat`-subtraction or `Int`/`Nat` floor-division/`%`. The
  atom carries no arithmetic, so a goal that genuinely needs truncation semantics will
  fail to solve; `solveAtomic` reads this to re-surface the `cutsat`/`omega` hint at the
  point of failure (instead of the parser rejecting the call outright). -/
  truncatingAtoms : Bool := false
  deriving Inhabited

/-- The atom-table half the certificate normalizer needs: virtual-fvar → atom `Expr`
(to reconstruct proof-term subterms) and atom `Expr` → virtual-fvar (to re-key on reparse). -/
structure AtomTable where
  fvarToAtom : Std.HashMap FVarId Expr := {}
  atomToFVar : Std.HashMap Expr FVarId := {}
  deriving Inhabited

/-- Reconstruct the `Expr` an LP variable stands for: the stored atom for a virtual
fvar, else the real local `Expr.fvar`. -/
def AtomTable.keyToExpr (t : AtomTable) (v : FVarId) : Expr :=
  t.fvarToAtom.getD v (Expr.fvar v)

/-! ### Commutative-product atom canonicalization

Opaque non-affine subterms are atomized and keyed by their `Expr`. Ring-equal but not
defeq forms — `f x * y` vs `y * f x` — would otherwise get *separate* LP columns, so the
hypothesis row never constrains the goal column and the refutation LP is unbounded.

We canonicalize a product atom by flattening its carrier-`*` chain and sorting the
resulting factors by `Expr.lt` (a total order). Both commuted forms then share one
canonical key, hence one column. The reordering is sound under the carrier's
`CommSemiring` (every carrier the normalizer runs on synthesizes one — the certificate
already uses `Lean.Grind.CommSemiring.mul_comm`), and the certificate proves
`original = canonical` from `mul_assoc`/`mul_comm` (`mulCanon?` below). Only
top-level carrier products are reordered (factors stay opaque); `^` and products buried
inside a factor are left as-is. -/

/-- Extract the partially-applied carrier multiplication head `@HMul.hMul α α α inst`
from a *homogeneous* product `e = a * b` over `carrier` (all three `HMul` type arguments
defeq `carrier`), or `none` otherwise. Reusing `e`'s own head keeps the `HMul` instance
identical to the source term; the homogeneity check rejects heterogeneous `•`-style muls. -/
def carrierMulHead? (carrier : Expr) (e : Expr) : MetaM (Option Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  unless fn.isConstOf ``HMul.hMul && args.size == 6 do return none
  unless (← isDefEq args[0]! carrier) && (← isDefEq args[1]! carrier)
      && (← isDefEq args[2]! carrier) do return none
  return some e.appFn!.appFn!

/-- View `e` as `mulHead a b` (a product with *exactly* this head, hence the same `HMul`
instance), returning its two operands. A child product built with a different instance is
not matched, so it stays an opaque factor rather than being flattened with the wrong head. -/
def asMulHeadApp? (mulHead e : Expr) : Option (Expr × Expr) :=
  if e.isApp && e.appFn!.isApp && e.appFn!.appFn!.equal mulHead then
    some (e.appFn!.appArg!, e.appArg!)
  else none

/-- Build the right-nested product `f₀ * (f₁ * (… * fₙ₋₁))` from a nonempty factor
array, using `mulHead` (the carrier's `HMul` head). -/
def buildRightNested (mulHead : Expr) (fs : Array Expr) : Expr := Id.run do
  let mut acc := fs[fs.size - 1]!
  for i in [1:fs.size] do
    acc := mkApp2 mulHead fs[fs.size - 1 - i]! acc
  return acc

/-- Flatten a product into its factor list, recursively splitting `*` nodes that share
`mulHead` and preserving left-to-right order. Subterms that are not `mulHead` products
(including products under a different instance) are leaves. -/
partial def flattenMul (mulHead : Expr) (e : Expr) (out : Array Expr) : Array Expr :=
  match asMulHeadApp? mulHead e with
  | none => out.push e
  | some (a, b) => flattenMul mulHead b (flattenMul mulHead a out)

/-- Insert `x` into the sorted (by `Expr.lt`) nonempty factor array `s`. Mirrors the
branching of `proveInsert` so the key path and the proof path agree on the result. -/
partial def insertSorted (x : Expr) (s : Array Expr) : Array Expr :=
  if Expr.lt s[0]! x then
    if s.size == 1 then #[s[0]!, x]
    else #[s[0]!] ++ insertSorted x (s.extract 1 s.size)
  else #[x] ++ s

/-- Insertion-sort a nonempty factor array by `Expr.lt`. -/
partial def sortFactors (fs : Array Expr) : Array Expr :=
  if fs.size ≤ 1 then fs
  else insertSorted fs[0]! (sortFactors (fs.extract 1 fs.size))

/-- `a * (b * c) = b * (a * c)` over the carrier, from `mul_comm` + `mul_assoc`. -/
def mkMulLeftComm (mulHead a b c : Expr) : MetaM Expr := do
  let e1 ← mkEqSymm (← mkAppM ``Lean.Grind.Semiring.mul_assoc #[a, b, c])
  let comm ← mkAppM ``Lean.Grind.CommSemiring.mul_comm #[a, b]
  let e2 ← mkCongrFun (← mkCongrArg mulHead comm) c
  let e3 ← mkAppM ``Lean.Grind.Semiring.mul_assoc #[b, a, c]
  mkEqTrans e1 (← mkEqTrans e2 e3)

/-- Prove `RN(fa) * RN(fb) = RN(fa ++ fb)` by re-associating, where `RN` is
`buildRightNested mulHead`. Both arrays nonempty. -/
partial def proveAppendRN (mulHead : Expr) (fa fb : Array Expr) : MetaM Expr := do
  if fa.size == 1 then
    return ← mkEqRefl (mkApp2 mulHead fa[0]! (buildRightNested mulHead fb))
  let x := fa[0]!
  let rest := fa.extract 1 fa.size
  let assoc ← mkAppM ``Lean.Grind.Semiring.mul_assoc
    #[x, buildRightNested mulHead rest, buildRightNested mulHead fb]
  let congr ← mkCongrArg (mkApp mulHead x) (← proveAppendRN mulHead rest fb)
  mkEqTrans assoc congr

/-- Reassociate a carrier product `e` to right-nested form over its flattened factors,
returning `(flatFactors, pf : e = RN flatFactors)`. -/
partial def proveReassoc (mulHead : Expr) (e : Expr) :
    MetaM (Array Expr × Expr) := do
  match asMulHeadApp? mulHead e with
  | none => return (#[e], ← mkEqRefl e)
  | some (a, b) =>
      let (fa, pa) ← proveReassoc mulHead a
      let (fb, pb) ← proveReassoc mulHead b
      let congrAB ← mkCongr (← mkCongrArg mulHead pa) pb
      let app ← proveAppendRN mulHead fa fb
      return (fa ++ fb, ← mkEqTrans congrAB app)

/-- Insert `x` into the sorted nonempty product `s` (= `RN s`), returning
`(s', pf : x * RN(s) = RN(s'))`. Mirrors `insertSorted`. -/
partial def proveInsert (mulHead : Expr) (x : Expr) (s : Array Expr) :
    MetaM (Array Expr × Expr) := do
  let s0 := s[0]!
  if Expr.lt s0 x then
    if s.size == 1 then
      return (#[s0, x], ← mkAppM ``Lean.Grind.CommSemiring.mul_comm #[x, s0])
    let rest := s.extract 1 s.size
    let lcomm ← mkMulLeftComm mulHead x s0 (buildRightNested mulHead rest)
    let (ins, pIns) ← proveInsert mulHead x rest
    let congr ← mkCongrArg (mkApp mulHead s0) pIns
    return (#[s0] ++ ins, ← mkEqTrans lcomm congr)
  else
    return (#[x] ++ s, ← mkEqRefl (mkApp2 mulHead x (buildRightNested mulHead s)))

/-- Sort a nonempty flattened factor array, returning `(sorted, pf : RN(flat) = RN(sorted))`.
Insertion sort, mirroring `sortFactors`. -/
partial def proveSort (mulHead : Expr) (flat : Array Expr) :
    MetaM (Array Expr × Expr) := do
  if flat.size == 1 then
    return (flat, ← mkEqRefl flat[0]!)
  let x := flat[0]!
  let (sortedRest, pRest) ← proveSort mulHead (flat.extract 1 flat.size)
  let congr ← mkCongrArg (mkApp mulHead x) pRest
  let (sorted, pIns) ← proveInsert mulHead x sortedRest
  return (sorted, ← mkEqTrans congr pIns)

/-- The canonical sorted-factor key for a carrier product `e`, or `none` when `e` is not a
carrier product, has a single factor, or is already canonical. Pure (no proof), used to
key the atom table; the proof-producing `mulCanon?` returns the same canonical `Expr`. -/
def mulCanonKey? (carrier : Expr) (e : Expr) : MetaM (Option Expr) := do
  let some mulHead ← carrierMulHead? carrier e | return none
  let flat := flattenMul mulHead e #[]
  if flat.size < 2 then return none
  let canon := buildRightNested mulHead (sortFactors flat)
  if canon.equal e then return none else return some canon

/-- Canonicalize a carrier product by flattening and sorting its factors, returning the
canonical product and a proof `e = canon`. `none` when `e` is not a reorderable product or
is already canonical. The returned `canon` equals `mulCanonKey?`'s key. -/
def mulCanon? (carrier : Expr) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some mulHead ← carrierMulHead? carrier e | return none
  let flat := flattenMul mulHead e #[]
  if flat.size < 2 then return none
  let canon := buildRightNested mulHead (sortFactors flat)
  if canon.equal e then return none
  -- Only build the reordering proof once we know reordering is needed.
  let (flat', pReassoc) ← proveReassoc mulHead e
  let (sorted, pSort) ← proveSort mulHead flat'
  -- The proof path must rebuild *exactly* the key path's canonical form, or the parser
  -- and certificate would key the atom on different columns. Guard the invariant.
  unless (buildRightNested mulHead sorted).equal canon do
    throwError "lp: internal canonicalization mismatch{indentExpr e}"
  return some (canon, ← mkEqTrans pReassoc pSort)

/-- Canonicalize an atom `Expr` into a stable LP-variable key: strip metadata and
instantiate assigned mvars; reject terms with unassigned/level mvars or loose bvars
(unstable or out of context); and canonicalize commuted carrier products
(`mulCanonKey?`) so ring-equal products share one key. Used identically by the parser and
the certificate normalizer so their atom keys agree. -/
def canonAtom (carrier : Expr) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e.consumeMData
  if e.hasExprMVar || e.hasLevelMVar || e.hasLooseBVars then return none
  return some ((← mulCanonKey? carrier e).getD e)

/-- Match `e` (already `whnfR`-reduced) as a binary application of `head` (a heterogeneous
`HAdd`/`HSub`/`HMul` operator constant, all 6 explicit+instance args), returning its two
operands. -/
private def asBinop? (head : Name) (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if e.getAppFn.isConstOf head && args.size == 6 then some (args[4]!, args[5]!) else none

/-! ### Product ring-normalization (distributivity / reassociation)

`lp` atomizes a product of two non-scalar factors opaquely, hiding any linear structure
(`p * (n + 1)` becomes one atom rather than `p*n + p`). `linarith` runs a ring pass first;
`distributeMul?` is `lp`'s: it pushes a `*` through the additive structure of either
operand and reassociates left-nested products so scalars surface, leaving genuine
products-of-atoms (e.g. `p*n`) as the only opaque monomials — which the existing atomizer
canonicalizes (`mulCanonKey?`) so commuted forms share a column. -/

/-- Decide how to ring-normalize a product `lhs * rhs` whose two factors are BOTH
non-scalar (the caller has already tried the scalar-`*` paths). Returns the distributed /
reassociated expression together with the normalizer lemma's base name and explicit
arguments proving `lhs * rhs = result`, or `none` when neither factor is additive and
`lhs` is not itself a product — a genuine product-of-atoms monomial, atomized as before.

Shared verbatim by the parser (`parseInto`, which uses only the result `Expr`) and the
certificate normalizer (`normalizeR`, which also applies the named lemma via `applyLemma`),
so the two walks distribute identically and agree on every atom column. Determinism is what
makes the lockstep hold: both call this with the same `lhs`/`rhs` and get the same result.

The result `Expr` reuses `e`'s own `HMul` head for every rebuilt product (so atom keys
stay consistent with the source term) and synthesizes the `+`/`-`/`neg` heads via `mkAppM`
(defeq to the monomorphic lemma's operators, which is all the certificate `Eq.trans`
needs). `allowSub` mirrors `ScalarCaps`: on a carrier without exact subtraction/negation
(`Nat`) the `-`/`neg` cases never fire (`Nat` has no `Neg`, so they never appear). -/
def distributeMul? (allowSub : Bool) (e lhs rhs : Expr) :
    MetaM (Option (Expr × Name × Array Expr)) := do
  let mulHead := e.appFn!.appFn!
  let mkMul (a b : Expr) : Expr := mkApp2 mulHead a b
  let lhs ← withReducible <| whnfR lhs
  let rhs ← withReducible <| whnfR rhs
  -- Distribute over `lhs`'s additive structure: `(a ± b) * c`, `(-a) * c`.
  if let some (a, b) := asBinop? ``HAdd.hAdd lhs then
    return some (← mkAppM ``HAdd.hAdd #[mkMul a rhs, mkMul b rhs], `add_mul, #[a, b, rhs])
  if allowSub then
    if let some (a, b) := asBinop? ``HSub.hSub lhs then
      return some (← mkAppM ``HSub.hSub #[mkMul a rhs, mkMul b rhs], `sub_mul, #[a, b, rhs])
    if lhs.isAppOfArity ``Neg.neg 3 then
      let a := lhs.appArg!
      return some (← mkAppM ``Neg.neg #[mkMul a rhs], `neg_mul, #[a, rhs])
  -- `lhs` is a (non-scalar) product: reassociate `(a * b) * c = a * (b * c)` so a scalar
  -- buried at the head of a left-nested product surfaces for the scalar-`*` path.
  if let some (a, b) := asBinop? ``HMul.hMul lhs then
    return some (mkMul a (mkMul b rhs), `mul_reassoc, #[a, b, rhs])
  -- `lhs` is atomic; distribute over `rhs`'s additive structure: `a * (b ± c)`, `a * (-c)`.
  if let some (b, c) := asBinop? ``HAdd.hAdd rhs then
    return some (← mkAppM ``HAdd.hAdd #[mkMul lhs b, mkMul lhs c], `mul_add, #[lhs, b, c])
  if allowSub then
    if let some (b, c) := asBinop? ``HSub.hSub rhs then
      return some (← mkAppM ``HSub.hSub #[mkMul lhs b, mkMul lhs c], `mul_sub, #[lhs, b, c])
    if rhs.isAppOfArity ``Neg.neg 3 then
      let c := rhs.appArg!
      return some (← mkAppM ``Neg.neg #[mkMul lhs c], `mul_neg, #[lhs, c])
  return none

/-- Look up the LP variable for a canonical atom `a`: first the exact (syntactic) key, then,
on a miss, an `isDefEq` scan over the registered atoms. The scan lets atoms that are equal up
to definitional unfolding (`↑n` via different cast paths, `π` behind different reducible
wrappers, a subterm reconstructed after a `rw`) share one variable, so the hypotheses and the
goal stay on the same column. Merging only ever unifies *defeq* atoms, so it is sound: the
certificate identity check remains the authority. -/
def findDefEqAtom (m : Std.HashMap Expr FVarId) (a : Expr) : MetaM (Option FVarId) := do
  if let some fv := m[a]? then return some fv
  for (a', fv) in m do
    if ← isDefEq a a' then return some fv
  return none

abbrev ParseM := StateT ParseState MetaM

def addVar (fvarId : FVarId) : ParseM Unit := do
  let s ← get
  if s.vars.any (· == fvarId) then
    return ()
  set { s with vars := s.vars.push fvarId }

/-- The `FVarId → position` index of an invocation's fixed variable order. Built once
per `lp` invocation (`mkVarIdx`); the certificate merge and the dense matrix build do
O(1) lookups instead of rescanning the `vars` array per coefficient. -/
abbrev VarIdx := Std.HashMap FVarId Nat

def mkVarIdx (vars : Array FVarId) : VarIdx := Id.run do
  let mut m : VarIdx := .emptyWithCapacity vars.size
  for h : i in [0:vars.size] do
    m := m.insert vars[i] i
  return m

/-- Merge two coefficient lists: `a`'s entries keep their positions (updated in
place), `b`'s new variables append in `b`-order, and entries that cancel to zero
are dropped. A small `b` merges by direct scan (in-place `set!`/`push`, no
rebuild); a large `b` goes through one map-indexed pass — `O(|a| + |b|)` instead
of the per-coefficient rescan `O(|a| · |b|)`. -/
def LinExpr.add (a b : LinExpr) : LinExpr := Id.run do
  let const := a.const + b.const
  if b.coeffs.isEmpty then return { a with const }
  if a.coeffs.isEmpty then
    -- Match the merge paths (and the old fold), which drop zero coefficients from `b`.
    return { const, coeffs := if b.coeffs.any (·.2 == 0) then b.coeffs.filter (·.2 != 0) else b.coeffs }
  let mut out := a.coeffs
  let mut cancelled := false
  if b.coeffs.size ≤ 4 then
    for (v, c) in b.coeffs do
      if c != 0 then
        match out.findIdx? (·.1 == v) with
        | some i =>
            let c' := out[i]!.2 + c
            out := out.set! i (v, c')
            if c' == 0 then cancelled := true
        | none =>
            out := out.push (v, c)
  else
    let mut idx : Std.HashMap FVarId Nat := .emptyWithCapacity a.coeffs.size
    for h : i in [0:a.coeffs.size] do
      idx := idx.insert a.coeffs[i].1 i
    for (v, c) in b.coeffs do
      if c != 0 then
        match idx[v]? with
        | some i =>
            let c' := out[i]!.2 + c
            out := out.set! i (v, c')
            if c' == 0 then cancelled := true
        | none =>
            idx := idx.insert v out.size
            out := out.push (v, c)
  return { const, coeffs := if cancelled then out.filter (·.2 != 0) else out }

def LinExpr.neg (a : LinExpr) : LinExpr :=
  { const := -a.const, coeffs := a.coeffs.map fun (v, c) => (v, -c) }

def LinExpr.sub (a b : LinExpr) : LinExpr :=
  a.add b.neg

def LinExpr.smul (c : Rat) (a : LinExpr) : LinExpr :=
  if c = 0 then {}
  else { const := c * a.const, coeffs := a.coeffs.map fun (v, k) => (v, c * k) }

/-- Convert a `LinExpr` to a dense coefficient `Array Rat` over a fixed
variable ordering, given as its `mkVarIdx` index map. Unknown variables are
skipped (treated as zero coefficient, which only happens in degenerate
parses). -/
def LinExpr.toDense (e : LinExpr) (vidx : VarIdx) :
    Array Rat := Id.run do
  let mut out := Array.replicate vidx.size (0 : Rat)
  for (v, c) in e.coeffs do
    if let some i := vidx[v]? then
      out := out.set! i (out[i]! + c)
  return out

/-- Evaluate a `LinExpr` at a concrete `Rat` assignment `xs`, indexed by the
fixed variable ordering's `mkVarIdx` map. Variables in `e.coeffs` not present
in the order are silently ignored (degenerate-parse coeffs are treated as
zero). -/
def LinExpr.evalAt (e : LinExpr) (vidx : VarIdx) (xs : Array Rat) :
    Rat := Id.run do
  let mut acc := e.const
  for (v, c) in e.coeffs do
    if let some i := vidx[v]? then
      acc := acc + c * xs[i]!
  return acc

/-- Partition a `LinExpr`'s coefficients by variable scope, used by the
inner-`∀` paths to split `(φ − ψ)(x, y) = α(x) + β(y) + γ` after parsing
the body as a single linear expression. Returns `(β, α, outside)` where:
- `β` holds the coeffs over `ys` (with `const := 0`),
- `α` holds the coeffs over `xs` together with the constant `γ := e.const`,
- `outside` lists any FVarIds in `e.coeffs` that belong to neither scope
  (these trigger the syntactic-rejection / outer-parameter checks).

Algebraically: `e = α.const + Σ (v,c) ∈ α.coeffs c·v + Σ (v,c) ∈ β.coeffs c·v
+ (outside contributions)`. -/
def LinExpr.partitionXY (e : LinExpr) (xs ys : Array FVarId) :
    LinExpr × LinExpr × Array FVarId := Id.run do
  let mut αCoeffs : Array (FVarId × Rat) := #[]
  let mut βCoeffs : Array (FVarId × Rat) := #[]
  let mut outside : Array FVarId := #[]
  for (v, c) in e.coeffs do
    if xs.any (· == v) then αCoeffs := αCoeffs.push (v, c)
    else if ys.any (· == v) then βCoeffs := βCoeffs.push (v, c)
    else outside := outside.push v
  let α : LinExpr := { const := e.const, coeffs := αCoeffs }
  let β : LinExpr := { coeffs := βCoeffs }
  (β, α, outside)

end LP.Tactic.LP.Internal
