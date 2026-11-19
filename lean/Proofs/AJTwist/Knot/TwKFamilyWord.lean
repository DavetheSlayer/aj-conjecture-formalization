import Mathlib
import AJTwist.Knot.TwKKnot

/-!
# The four families as data: numbers of strands and braid words

`twFamilyKnot r s h σ η ℓ` carries the proofs that its braid word closes up to a knot. Its data
are named here, so that statements about the four families can be made about every closed braid
with these data (the solution file of the release does this):

* `twFamilyStrands r s η ℓ`: the number of strands;
* `twFamilyWord r s σ η ℓ`: the braid word. Over the companion `T(r, s)` (`η = true`) it is
  `twWhiteheadWord r s ℓ σ`; over the mirror companion `T(r, -s)` (`η = false`) it is the inverse
  `invWord` of the word `twWhiteheadWord r s (-ℓ) (!σ)` of the satellite with the opposite clasp
  and the opposite twist over `T(r, s)` (the mirror identity
  `(W_{ε,ℓ}(T_η))^* = W_{-ε,-ℓ}(T_{-η})` of the paper, used as the definition).

A closed braid with these data is `twFamilyKnot r s h σ η ℓ` (`eq_twFamilyKnot_of_word`), because
the remaining fields of a `BraidKnot` are proofs.
-/

namespace AJConjecture

/-- The number of strands of `twFamilyKnot r s h σ η ℓ`. -/
def twFamilyStrands (r s : ℕ) (η : Bool) (ℓ : ℤ) : ℕ :=
  if η then twStrands r s ℓ else twStrands r s (-ℓ)

/-- The braid word of `twFamilyKnot r s h σ η ℓ` (`σ = true`: negative clasp; `η = true`:
companion `T(r, s)`, `η = false`: companion `T(r, -s)`). -/
def twFamilyWord (r s : ℕ) (σ η : Bool) (ℓ : ℤ) : BraidWord :=
  if η then twWhiteheadWord r s ℓ σ else invWord (twWhiteheadWord r s (-ℓ) (!σ))

theorem strands_twFamilyKnot (r s : ℕ) (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    (twFamilyKnot r s h σ η ℓ).strands = twFamilyStrands r s η ℓ := by
  cases η <;> rfl

theorem word_twFamilyKnot (r s : ℕ) (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    (twFamilyKnot r s h σ η ℓ).word = twFamilyWord r s σ η ℓ := by
  cases η <;> rfl

/-- A closed braid with the number of strands and the word of `twFamilyKnot r s h σ η ℓ` is that
knot. -/
theorem eq_twFamilyKnot_of_word {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ)
    {K : BraidKnot} (hs : K.strands = twFamilyStrands r s η ℓ)
    (hw : K.word = twFamilyWord r s σ η ℓ) : K = twFamilyKnot r s h σ η ℓ := by
  rw [← strands_twFamilyKnot r s h σ η ℓ] at hs
  rw [← word_twFamilyKnot r s h σ η ℓ] at hw
  generalize twFamilyKnot r s h σ η ℓ = K' at hs hw
  cases K
  cases K'
  dsimp only at hs hw
  subst hs hw
  rfl

/-- Without twist, with the negative clasp and over `T(r, s)` the data are those of Theorem T. -/
theorem twFamilyWord_untwisted {r s : ℕ} (h : IsTorusPair r s) :
    twFamilyStrands r s true 0 = pairStrands r s ∧
      twFamilyWord r s true true 0 = pairWhiteheadWord r s := by
  have hK := twWhiteheadKnot_zero_true h
  exact ⟨congrArg BraidKnot.strands hK, congrArg BraidKnot.word hK⟩

end AJConjecture
