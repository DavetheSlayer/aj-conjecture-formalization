import Mathlib
import AJHandoff.PairDefs
import AJConjecture.SkeinUFormClasp
import AJConjecture.SkeinLongKnot
import AJConjecture.SkeinHalfTwist

/-!
# The four families of twisted Whitehead doubles: shared parameters and interfaces

Source: *Whitehead doubles and the failure of the square-free AJ conjecture*, revision 5
(handoff of 18 November 2026), Theorem 1.1. The satellites are `W_{ε,ℓ}(T_η)`: clasp sign `ε`,
signed twist `ℓ ∈ ℤ`, companion `T(r, s)` (`η = true`) or its mirror `T(r, -s)` (`η = false`),
for coprime `2 ≤ r < s`.

* `twIndex η r s ℓ` is the effective index `a = ± r s - ℓ` of the negative-clasp satellite.
* `halfTwistZ c k` is the signed power `Σ_c^k` of the cabled half twist, and `claspSOp c σ` the
  clasp built from two half twists of sign `σ` (`claspSOp c true = claspOp c`, the clasp of the
  untwisted family `pairWhiteheadKnot`).
* `IsBandClasp K C k σ`: the long-knot operator of `K` is that of the band-and-clasp diagram over
  the companion `C`, with `k` signed half twists of the band and clasp sign `σ`. The untwisted
  family satisfies `IsBandClasp (pairWhiteheadKnot r s h) (torusPairKnot r s h) (-2 (r-1) s) true`
  (`longKnotOp_pairWhiteheadKnot`).
* `mirrorWord`, `BraidKnot.mirror`: the mirror image of a closed braid (every crossing reversed).
* `invWord`, `BraidKnot.inv`: the closure of the inverse braid (the letters in the opposite order,
  every crossing reversed): the mirror image with the opposite orientation. The families over the
  mirror companion are defined with it, because the knot group of the inverse braid is the knot
  group of the braid with the inverse longitude.
-/

noncomputable section

namespace AJConjecture

/-- The effective index `a = η r s - ℓ` (`η = true`: right-handed companion, `a = r s - ℓ`;
`η = false`: mirror companion, `a = - r s - ℓ`). -/
def twIndex (η : Bool) (r s : ℕ) (ℓ : ℤ) : ℤ :=
  (if η then ((r * s : ℕ) : ℤ) else -((r * s : ℕ) : ℤ)) - ℓ

/-- The signed power `Σ_c^k` of the cabled half twist of two bundles of `c` strands:
`halfTwist c true ^ k` for `k ≥ 0` and `halfTwist c false ^ (-k)` for `k < 0`. -/
def halfTwistZ (c : ℕ) (k : ℤ) : SkMat (2 * c) (2 * c) :=
  if 0 ≤ k then halfTwist c true ^ k.toNat else halfTwist c false ^ (-k).toNat

/-- The clasp of two bundles of `c` strands built from two cabled half twists of sign `σ`
(a thick cup on the right, the full twist `Σ_c^{±2}` on the two middle bundles, a thick cap on
the left). `claspSOp c true` is `claspOp c`. -/
def claspSOp (c : ℕ) (σ : Bool) : SkMat (2 * c) (2 * c) :=
  skPlace (2 * c) (4 * c) (2 * c) (cupThick c) *
    skPlace (4 * c) (4 * c) c (halfTwist c σ * halfTwist c σ) *
      skPlace (4 * c) (2 * c) 0 (capThick c)

theorem claspSOp_true (c : ℕ) : claspSOp c true = claspOp c := rfl

/-- The clasp of sign `σ` as a Morse word on two strands (`claspSWord true = claspWord`). -/
def claspSWord (σ : Bool) : MorseWord :=
  [(.cup, 2), (.cross σ, 1), (.cross σ, 1), (.cap, 0)]

theorem claspSWord_true : claspSWord true = claspWord := rfl

/-- The band-and-clasp long-knot identity: at every thickness `c`, the long-knot operator of `K`
is the partial trace over the second bundle of the long-knot operator of the companion `C` at
thickness `2c`, followed by `k` signed half twists of the band and the clasp of sign `σ`. -/
def IsBandClasp (K C : BraidKnot) (k : ℤ) (σ : Bool) : Prop :=
  ∀ c : ℕ, longKnotOp K c =
    ptrTail c (2 * c) (longKnotOp C (2 * c) * (halfTwistZ c k * claspSOp c σ))

/-- The mirror image of a braid word: every crossing is reversed. -/
def mirrorWord (w : BraidWord) : BraidWord := w.map fun g ↦ (g.1, !g.2)

theorem isOnStrands_mirrorWord {m : ℕ} {w : BraidWord} (h : IsOnStrands m w) :
    IsOnStrands m (mirrorWord w) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  exact h g' hg'

theorem strandPerm_mirrorWord (m : ℕ) (w : BraidWord) :
    strandPerm m (mirrorWord w) = strandPerm m w := by
  simp [strandPerm, mirrorWord, List.map_map, Function.comp_def]

theorem writhe_mirrorWord (w : BraidWord) : writhe (mirrorWord w) = -writhe w := by
  induction w with
  | nil => simp [mirrorWord, writhe]
  | cons g w ih =>
    simp only [mirrorWord, writhe, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [ih]
    cases g.2 <;> simp <;> ring

/-- The mirror image of a closed braid. -/
def BraidKnot.mirror (K : BraidKnot) : BraidKnot where
  strands := K.strands
  word := mirrorWord K.word
  strands_pos := K.strands_pos
  isOnStrands := isOnStrands_mirrorWord K.isOnStrands
  connected := by
    rw [strandPerm_mirrorWord]
    exact K.connected

/-- The inverse of a braid word: the letters in the opposite order, every crossing reversed. -/
def invWord (w : BraidWord) : BraidWord := (mirrorWord w).reverse

theorem isOnStrands_invWord {m : ℕ} {w : BraidWord} (h : IsOnStrands m w) :
    IsOnStrands m (invWord w) := fun g hg ↦
  isOnStrands_mirrorWord h g (List.mem_reverse.1 hg)

/-- A strand transposition is an involution. -/
theorem strandSwap_mul_self (m i : ℕ) : strandSwap m i * strandSwap m i = 1 := by
  unfold strandSwap
  split_ifs
  · exact Equiv.swap_mul_self _ _
  · exact one_mul 1

theorem strandPerm_invWord (m : ℕ) (w : BraidWord) :
    strandPerm m (invWord w) = (strandPerm m w)⁻¹ := by
  induction w with
  | nil => simp [invWord, mirrorWord, strandPerm]
  | cons g w ih =>
    have hcons : strandPerm m (invWord (g :: w)) = strandPerm m (invWord w) * strandSwap m g.1 := by
      simp [invWord, mirrorWord, strandPerm, List.map_append, List.prod_append]
    have hw : strandPerm m (g :: w) = strandSwap m g.1 * strandPerm m w := by
      simp [strandPerm]
    rw [hcons, ih, hw, mul_inv_rev]
    congr 1
    exact (eq_inv_of_mul_eq_one_left (strandSwap_mul_self m g.1))

theorem writhe_invWord (w : BraidWord) : writhe (invWord w) = -writhe w := by
  have h : writhe (invWord w) = writhe (mirrorWord w) := by
    simp only [invWord, writhe, List.map_reverse, List.sum_reverse]
  rw [h, writhe_mirrorWord]

/-- The closure of the inverse word of a knot has one component. -/
theorem connected_invWord (K : BraidKnot) (i j : Fin K.strands) :
    ∃ k : ℕ, (strandPerm K.strands (invWord K.word) ^ k) i = j := by
  obtain ⟨k, hk⟩ := K.connected j i
  refine ⟨k, ?_⟩
  rw [strandPerm_invWord, inv_pow, Equiv.Perm.inv_eq_iff_eq, hk]

/-- The closure of the inverse braid: the mirror image of the closed braid, with the opposite
orientation. -/
def BraidKnot.inv (K : BraidKnot) : BraidKnot where
  strands := K.strands
  word := invWord K.word
  strands_pos := K.strands_pos
  isOnStrands := isOnStrands_invWord K.isOnStrands
  connected := connected_invWord K

end AJConjecture
