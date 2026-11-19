import Mathlib
import AJPaper.Filling.PpAGenericTwP
import AJPaper.Filling.PpASubOne
import AJPaper.Filling.PpATwistBound
import AJPaper.Filling.PpATwistTuple

/-!
# The A-polynomial of the twist knots (PpA, Section 7.6, claim 1)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`): "The containing equation for the
filling and the abelian line therefore give `A_(Z_(-k)) ≐ (L - 1) 𝒫_k` (`k ∈ ℤ`)."

For the closed braids `ppaTwistKnot ℓ` (`Z_ℓ = W_(-,ℓ)(U)`, `AJPaper.Filling.PpATwistKnot`):

* `ppa_aPolynomial_twistKnot`: every A-polynomial of `Z_ℓ` is associated to `(L - 1) 𝒫_(-ℓ)` in
  `R = ℚ(M)[L, L⁻¹]`;
* `ppa_aPolynomial_pureClosure`: the same in the paper's indexing, `A_(Z_(-k)) ≐ (L - 1) 𝒫_k`.

(An A-polynomial exists: `ppa_exists_aPolynomial_twistKnot`.) At `k = 0` this is the unknot,
`A ≐ L - 1`; `k = 1` is the figure-eight knot with `𝒫_1 = B_1`, `k = -1` a trefoil with
`𝒫_(-1) = C_1 = L + M⁶`.

Route: `associated_of_dvd_dvd` (the comparison ring is a domain). One direction is
`ppa_aPolynomial_twistKnot_dvd`. The other: for `ℓ = 0`, `ppa_toComparison_sub_one_dvd`
(`twP_zero`); for `ℓ ≠ 0`, `ppa_twP_dvd_of_generic` with `ppa_mem_eigenvalueSet_twistKnot`, then
`ppa_sub_one_mul_dvd` with `ppa_prime_toComparison_twP`, `ppa_not_sub_one_dvd_twP`.

What stays interpretation: that the closed braid `ppaTwistKnot ℓ` is the twist knot `Z_ℓ` (knot
type checked by Alexander polynomial and coloured Jones values, see `PpATwistKnot`), and that
`IsAPolynomialOf (eigenvalueSet K)` is the horizontal part of the paper's `A_K` (Lemma 7.1).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Section 7.6: the A-polynomial of the twist knot `Z_ℓ` is `(L - 1) 𝒫_(-ℓ)` up to a unit of
`ℚ(M)[L, L⁻¹]`. -/
theorem ppa_aPolynomial_twistKnot (ℓ : ℤ) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (ppaTwistKnot ℓ)) A) :
    Associated (toComparison A) (toComparison ((X - 1) * twP (-ℓ))) := by
  refine associated_of_dvd_dvd (ppa_aPolynomial_twistKnot_dvd ℓ hA) ?_
  by_cases hℓ : ℓ = 0
  · subst hℓ
    rw [neg_zero, twP_zero, mul_one]
    exact ppa_toComparison_sub_one_dvd _ hA
  · have hk : -ℓ ≠ 0 := neg_ne_zero.2 hℓ
    exact ppa_sub_one_mul_dvd _ hA (ppa_prime_toComparison_twP _ hk)
      (ppa_not_sub_one_dvd_twP _ hk)
      (ppa_twP_dvd_of_generic hA (-ℓ) hk fun _ _ hM hM4 hQ hP ↦
        ppa_mem_eigenvalueSet_twistKnot ℓ hM hM4 hQ hP)

/-- Section 7.6 in the indexing of the paper: `A_(Z_(-k)) ≐ (L - 1) 𝒫_k` for every `k ∈ ℤ`. -/
theorem ppa_aPolynomial_pureClosure (k : ℤ) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (ppaTwistKnot (-k))) A) :
    Associated (toComparison A) (toComparison ((X - 1) * twP k)) := by
  have h := ppa_aPolynomial_twistKnot (-k) hA
  rwa [neg_neg] at h

end AJConjecture
