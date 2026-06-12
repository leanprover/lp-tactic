/-
  Tests for issue #43: a proof-embedded `Fin` literal defeated the atom lookup
  ("atom not registered during parsing").

  The parser (`parseInto`) reduces every subterm with `whnfR` (reducible
  transparency) before deciding to descend or atomize, but the certificate
  normalizer (`normalizeR`) matched the *raw* structure with no reduction. The
  two walks then diverged on a reducibly-reducing head: the cast of an
  anonymous-constructor `Fin` literal, `↑⟨b + 1, h⟩` (a `Fin.val` projection of
  `Fin.mk`), reduces to `b + 1` for the parser — which registers the atom `b` —
  but stayed an opaque projection for the normalizer, which atomized a term the
  parser never registered and then threw "atom not registered during parsing".

  The fix mirrors the parser's per-node `whnfR` in `normalizeR`: reduce first,
  recurse on the reduced form, and transport the equality proof back to the
  original term by defeq (the reduction is reducible, hence definitional). The
  same `↑⟨e, h⟩`-after-reduction shape is common in simplicial/combinatorial
  Mathlib code; the reported site is
  `Mathlib/AlgebraicTopology/DoldKan/Degeneracies.lean`.

  These cases close from the goal alone (zero hypothesis rows), so they exercise
  the parse/normalize agreement through `proveCertificateIdentity` without a
  registered LP backend.
-/

import LPTactic

namespace LPTacticTest.Issue43

/-! ## The reported shape: `Fin.val` of an anonymous-constructor literal. -/

example (n b : Nat) (h : b + 1 < n) : (⟨b + 1, h⟩ : Fin n).val ≤ b + 1 := by lp
example (n b : Nat) (h : b + 1 < n) : b ≤ (⟨b + 1, h⟩ : Fin n).val := by lp
example (n b : Nat) (h : b + 1 < n) :
    (⟨b + 1, h⟩ : Fin n).val ≤ (⟨b + 1, h⟩ : Fin n).val + 1 := by lp
example (n b : Nat) (h : b + 1 < n) : (⟨b + 1, h⟩ : Fin n).val + 2 ≤ b + 3 := by lp

/-! ## Strict variant. -/

example (n b : Nat) (h : b + 1 < n) : (⟨b + 1, h⟩ : Fin n).val < b + 2 := by lp

/-! ## Two distinct `Fin`-literal atoms share their reduced columns. -/

example (n b c : Nat) (hb : b + 1 < n) (hc : c + 1 < n) :
    (⟨b + 1, hb⟩ : Fin n).val + (⟨c + 1, hc⟩ : Fin n).val ≤ b + c + 3 := by lp

/-! ## An irreducible `Fin.succ` head stays atomized — consistently on both walks. -/

example (n b : Nat) (h : b < n) :
    (Fin.succ (⟨b, h⟩ : Fin n)).val ≤ (Fin.succ (⟨b, h⟩ : Fin n)).val := by lp

end LPTacticTest.Issue43
