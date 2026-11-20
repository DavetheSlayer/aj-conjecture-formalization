import Mathlib
import AJTwist.Knot.TwKKnot
import AJTwist.Knot.TwKMirrorGroup
import AJPaper.Filling.PpAGenericTwP
import AJPaper.Filling.PpAGenericRev
import AJPaper.Filling.PpASubOne
import AJPaper.Filling.PpAPoints

/-!
# The companion-abelian filling factor of the four families (PpA, Section 7.6, claim 2)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`), last paragraph: "For a
negative-clasp satellite with disk twist `ℓ` … `(L - 1) 𝒫_(-ℓ) ∣ A_S`. This extension concerns
the companion-abelian filling."

For the marked satellites `twFamilyKnot r s h σ η ℓ = W_(ε,ℓ)(T_η)` of the library
(`σ = true`: negative clasp; `η = true`: companion `T(r, s)`, `η = false`: its mirror) and
every A-polynomial `A` of the eigenvalue set, in `R = ℚ(M)[L, L⁻¹]`:

* `ppa_fillingFactor_dvd_neg` (negative clasp, both companions, every `ℓ`):
  `(L - 1) 𝒫_(-ℓ) ∣ A`. This is the paper's statement.
* `ppa_fillingFactor_dvd_pos` (positive clasp, both companions, every `ℓ`): the reverse in `L`
  of `(L - 1) 𝒫_ℓ` divides `A`: the statement for the mirror knot `W_(-,-ℓ)(T_(-η))` with `L`
  inverted, in the form of the library's bound `(twBound ℓ (-a)).reverse`
  (`twClassClauses_twFamilyKnot_pos`).

For `ℓ = 0` both say `L - 1 ∣ A` (`twP_zero`).

Route. `ℓ = 0`: `ppa_toComparison_sub_one_dvd` (`twP_zero`, `mul_one`; the reverse of `L - 1` is
`1 - L`, or `ppa_toComparison_reverse_sub_one_mul`). `ℓ ≠ 0`: the four rows are
`twFamilyKnot_true`, `twFamilyKnot_false`:

| clasp | `η` | knot `K` (`W = twWhiteheadKnot r s h`) | points of `eigenvalueSet K` |
|---|---|---|---|
| `-` | `+` | `W ℓ true` | zeros `(M, L)` of `𝒫_(-ℓ)` |
| `-` | `-` | `(W (-ℓ) false).inv` | zeros `(M, L)` of `𝒫_(-ℓ)` |
| `+` | `+` | `W ℓ false` | `(M, L⁻¹)` for the zeros `(M, L)` of `𝒫_ℓ` |
| `+` | `-` | `(W (-ℓ) true).inv` | `(M, L⁻¹)` for the zeros `(M, L)` of `𝒫_ℓ` |

by `ppa_mem_eigenvalueSet_neg h ℓ`, `ppa_mem_eigenvalueSet_pos h (-ℓ)`,
`ppa_mem_eigenvalueSet_pos h ℓ`, `ppa_mem_eigenvalueSet_neg h (-ℓ)` respectively, with
`eigenvalueSet_inv` for the two inverse braids.

(`eigenvalueSet_inv K : eigenvalueSet K.inv = (fun p ↦ (p.1, p.2⁻¹)) '' eigenvalueSet K`;
`inv_inv`, `neg_neg`.) Then `ppa_twP_dvd_of_generic` resp. `ppa_twP_reverse_dvd_of_generic`
give the factor `𝒫_(-ℓ)` resp. `(𝒫_ℓ).reverse`, and `ppa_sub_one_mul_dvd` with
`ppa_prime_toComparison_twP`, `ppa_not_sub_one_dvd_twP` (resp. the `_reverse` versions and
`ppa_toComparison_reverse_sub_one_mul`) the product with `L - 1`.

Nothing here is conditional. What stays interpretation, as everywhere in the library, is that
`IsAPolynomialOf (eigenvalueSet K)` is the horizontal part of the paper's `A_S` (Lemma 7.1).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The generic zeros of `𝒫_(-ℓ)` are eigenvalue points of `W_(-,ℓ)(T_η)`, both companions. -/
private theorem mem_eigenvalueSet_family_neg_ppaFilling {r s : ℕ} (h : IsTorusPair r s)
    (η : Bool) (ℓ : ℤ) {M L : ℂ} (hM : M ≠ 0) (hM4 : M ^ 4 ≠ 1) (hQ : M ^ 2 + L ≠ 0)
    (hP : evalPoint (mapC (twP (-ℓ))) (M, L) = 0) :
    (M, L) ∈ eigenvalueSet (twFamilyKnot r s h true η ℓ) := by
  cases η with
  | true =>
    rw [twFamilyKnot_true]
    exact ppa_mem_eigenvalueSet_neg h ℓ hM hM4 hQ hP
  | false =>
    rw [twFamilyKnot_false, eigenvalueSet_inv]
    exact ⟨(M, L⁻¹), ppa_mem_eigenvalueSet_pos h (-ℓ) hM hM4 hQ hP, by simp only [inv_inv]⟩

/-- The images under `L ↦ L⁻¹` of the generic zeros of `𝒫_ℓ` are eigenvalue points of
`W_(+,ℓ)(T_η)`, both companions. -/
private theorem mem_eigenvalueSet_family_pos_ppaFilling {r s : ℕ} (h : IsTorusPair r s)
    (η : Bool) (ℓ : ℤ) {M L : ℂ} (hM : M ≠ 0) (hM4 : M ^ 4 ≠ 1) (hQ : M ^ 2 + L ≠ 0)
    (hP : evalPoint (mapC (twP ℓ)) (M, L) = 0) :
    (M, L⁻¹) ∈ eigenvalueSet (twFamilyKnot r s h false η ℓ) := by
  cases η with
  | true =>
    rw [twFamilyKnot_true]
    exact ppa_mem_eigenvalueSet_pos h ℓ hM hM4 hQ hP
  | false =>
    rw [twFamilyKnot_false, eigenvalueSet_inv]
    refine ⟨(M, L), ppa_mem_eigenvalueSet_neg h (-ℓ) hM hM4 hQ ?_, rfl⟩
    rw [neg_neg]
    exact hP

/-- Section 7.6, negative clasp: `(L - 1) 𝒫_(-ℓ)` divides every A-polynomial of `W_(-,ℓ)(T_η)`
in `ℚ(M)[L, L⁻¹]`. -/
theorem ppa_fillingFactor_dvd_neg {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    {A : ℤ[X][X]} (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h true η ℓ)) A) :
    toComparison ((X - 1) * twP (-ℓ)) ∣ toComparison A := by
  by_cases hℓ : ℓ = 0
  · rw [hℓ, neg_zero, twP_zero, mul_one]
    exact ppa_toComparison_sub_one_dvd _ hA
  · have hℓ' : -ℓ ≠ 0 := neg_ne_zero.2 hℓ
    exact ppa_sub_one_mul_dvd _ hA (ppa_prime_toComparison_twP (-ℓ) hℓ')
      (ppa_not_sub_one_dvd_twP (-ℓ) hℓ')
      (ppa_twP_dvd_of_generic hA (-ℓ) hℓ' fun _ _ hM hM4 hQ hP ↦
        mem_eigenvalueSet_family_neg_ppaFilling h η ℓ hM hM4 hQ hP)

/-- Section 7.6, positive clasp: the reverse in `L` of `(L - 1) 𝒫_ℓ` divides every
A-polynomial of `W_(+,ℓ)(T_η)` in `ℚ(M)[L, L⁻¹]`. -/
theorem ppa_fillingFactor_dvd_pos {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    {A : ℤ[X][X]} (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h false η ℓ)) A) :
    toComparison ((X - 1) * twP ℓ).reverse ∣ toComparison A := by
  refine (ppa_toComparison_reverse_sub_one_mul (twP ℓ)).dvd.trans ?_
  by_cases hℓ : ℓ = 0
  · have h1 : (1 : ℤ[X][X]).reverse = 1 := by rw [← C_1, reverse_C]
    rw [hℓ, twP_zero, h1, mul_one]
    exact ppa_toComparison_sub_one_dvd _ hA
  · exact ppa_sub_one_mul_dvd _ hA (ppa_prime_toComparison_twP_reverse ℓ hℓ)
      (ppa_not_sub_one_dvd_twP_reverse ℓ hℓ)
      (ppa_twP_reverse_dvd_of_generic hA ℓ hℓ fun _ _ hM hM4 hQ hP ↦
        mem_eigenvalueSet_family_pos_ppaFilling h η ℓ hM hM4 hQ hP)

end AJConjecture
