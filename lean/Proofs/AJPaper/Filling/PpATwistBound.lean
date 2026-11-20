import Mathlib
import AJConjecture.APolynomialUnique
import AJFamily.Classical.APolynomialOfStable
import AJHandoff.TorusKnot.PairKPeriGeneric
import AJTwist.Classical.TwCClauses
import AJTwist.Classical.TwCSatelliteBound
import AJPaper.Filling.PpATwistForward

/-!
# The containing equation of the twist knots (PpA, Section 7.6, claim 1: the bound)

Source: arXiv:2611.24826v1, Section 7.2 (`classical.tex`): "all generic actual outer values lie
on the following containing equation", for the pure filling: `A_(Z_ℓ) ∣ (L - 1) 𝒫_(-ℓ)`.

* `ppa_evalPoint_twistKnot`: every point of the eigenvalue set of `ppaTwistKnot ℓ` is a zero of
  `(L - 1) 𝒫_(-ℓ)` (every point, not only the generic ones);
* `ppa_exists_aPolynomial_twistKnot`: an A-polynomial exists;
* `ppa_aPolynomial_twistKnot_dvd`: every A-polynomial divides `(L - 1) 𝒫_(-ℓ)` in
  `R = ℚ(M)[L, L⁻¹]`.

Route. For a representation `ρ`, the tuple `F t = ρ (x_t)` is fixed by the run
(`braidRun_fst_of_hom`), `ρ (meridian) = edgeMer F 0` (`edgeMer_zero`) and `ρ (longitude)` is
the orbit loop and commutes with it (`map_longitude_eq_orbitLoop` with the block list
`ppaTwistBlocks ℓ`, `ppaTwistBlocks_valid`). So `ppa_twistPattern_of_fixed` gives
`IsWhPattern a (c ^ ℓ) c l` in `SL₂(ℂ)`, and `evalPoint_twP_of_whPattern (-ℓ) a (c ^ ℓ) c l 1`
(`t = 1 * c ^ (-(-ℓ))`) the first statement. The other two follow as in
`twClassClauses_of_bound` (`AJTwist.Classical.TwCClauses`): `exists_isAPolynomialOf_of_isAutStable`
with `eigenvalueSet_isAutStable`, the descent of divisibility from `ℂ` to `R`, and
`isAPolynomialOf_toComparison_associated`; the bound is not zero (`twBound_ne_zero (-ℓ) 0`,
`twBound`, `twP_zero`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Every boundary eigenvalue pair of the twist knot `Z_ℓ` is a zero of `(L - 1) 𝒫_(-ℓ)`. -/
theorem ppa_evalPoint_twistKnot (ℓ : ℤ) {p : ℂ × ℂ} (hp : p ∈ eigenvalueSet (ppaTwistKnot ℓ)) :
    evalPoint (mapC ((X - 1) * twP (-ℓ))) p = 0 := by
  obtain ⟨ρ, hm, hl, hM, hL⟩ := hp
  obtain ⟨p1, p2⟩ := p
  simp only at hM hL
  subst hM hL
  have hF : runTop (3 + twExtra ℓ) (ppaTwistBlocks ℓ)
      (fun t : Fin (3 + twExtra ℓ) ↦ ρ (PresentedGroup.of t)) =
        fun t : Fin (3 + twExtra ℓ) ↦ ρ (PresentedGroup.of t) :=
    braidRun_fst_of_hom (ppaTwistKnot ℓ) ρ
  obtain ⟨hlon, hc⟩ := map_longitude_eq_orbitLoop (ppaTwistKnot ℓ) (ppaTwistBlocks ℓ) rfl
    (ppaTwistBlocks_valid ℓ) ρ
  have hmer : ρ (meridian (ppaTwistKnot ℓ)) =
      edgeMer (fun t : Fin (3 + twExtra ℓ) ↦ ρ (PresentedGroup.of t)) 0 :=
    (edgeMer_zero (fun t : Fin (3 + twExtra ℓ) ↦ ρ (PresentedGroup.of t))
      (ppaTwistKnot ℓ).strands_pos).symm
  have hpat := ppa_twistPattern_of_fixed ℓ _ hF (hmer ▸ hc)
  rw [← hmer] at hpat
  exact evalPoint_twP_of_whPattern (-ℓ) _ _ _ _ 1 (fun x ↦ by rw [one_mul, mul_one])
    (hlon ▸ hpat) (by rw [one_mul, neg_neg]) hm hl

/-- The classical clauses of the twist knot `Z_ℓ` for the bound `(L - 1) 𝒫_(-ℓ)` (with the
trivial obstruction polynomial `1`). -/
private theorem twClassClauses_ppaTwistBound (ℓ : ℤ) :
    TwClassClauses (ppaTwistKnot ℓ) 1 ((X - 1) * twP (-ℓ)) := by
  have hne : (X - 1 : ℤ[X][X]) * twP (-ℓ) ≠ 0 := by
    have h := twBound_ne_zero (-ℓ) 0
    rwa [twBound, twP_zero, mul_one] at h
  refine twClassClauses_of_bound hne (fun p hp ↦ ppa_evalPoint_twistKnot ℓ hp) ?_
  rw [map_one]
  exact isCoprime_one_left

/-- The twist knot `Z_ℓ` has an A-polynomial. -/
theorem ppa_exists_aPolynomial_twistKnot (ℓ : ℤ) :
    ∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet (ppaTwistKnot ℓ)) A :=
  (twClassClauses_ppaTwistBound ℓ).1

/-- Every A-polynomial of the twist knot `Z_ℓ` divides `(L - 1) 𝒫_(-ℓ)` in `ℚ(M)[L, L⁻¹]`. -/
theorem ppa_aPolynomial_twistKnot_dvd (ℓ : ℤ) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (ppaTwistKnot ℓ)) A) :
    toComparison A ∣ toComparison ((X - 1) * twP (-ℓ)) :=
  ((twClassClauses_ppaTwistBound ℓ).2 A hA).1

end AJConjecture
