import Mathlib
import AJPaper.Filling.PpAPolyFacts
import AJPaper.Filling.PpAGenericDvd

/-!
# Generic points of `𝒫_k = 0` and the factor `𝒫_k` of the A-polynomial (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`): "The realizations are dense in that
curve."

The representations of Section 7.6 exist at the zeros `(M, L)` of `𝒫_k` with `M ≠ 0`,
`M⁴ ≠ 1`, `L ≠ -M²` (`AJPaper.Filling.PpAPattern`).

`ppa_twP_dvd_of_generic`: if these zeros of `𝒫_k` (`k ≠ 0`) lie in `S`, then `𝒫_k ∣ A` in
`R = ℚ(M)[L, L⁻¹]` for every A-polynomial `A` of `S`.

Route: `ppa_toComparison_dvd_of_generic` with `P = 𝒫_k` and
`Bad = ppaBad = M (M⁴ - 1) (L + M²)`. Primality and the constant coefficient are in
`AJPaper.Filling.PpAPolyFacts`. An irreducible `g` of positive `L`-degree dividing `mapC ppaBad`
is associated to `L + M²` (it does not divide the factor in `ℂ[M]`, by degree), as in the
private `rev_not_dvd_revBad` of `AJHandoff.TorusKnot.PairKReverse`; if it also divided `𝒫_k`,
then `𝒫_k` would vanish at `(2, -4)`, against `ppa_evalPoint_twP_ne_zero`. A zero of `𝒫_k`
where `ppaBad` does not vanish satisfies the three conditions (`evalPoint_mapC_ppaBad`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The polynomial `M (M⁴ - 1) (L + M²)` cutting out the points excluded in Section 7.6. -/
def ppaBad : ℤ[X][X] := C (X * (X ^ 4 - 1)) * (X + C (X ^ 2))

theorem evalPoint_mapC_ppaBad (M L : ℂ) :
    evalPoint (mapC ppaBad) (M, L) = M * (M ^ 4 - 1) * (L + M ^ 2) := by
  simp [ppaBad, mapC, evalPoint, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_pow]

/-- Evaluation at a point is multiplicative. -/
private theorem evalPoint_mul_ppaGenericTwP (P Q : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (P * Q) p = evalPoint P p * evalPoint Q p := by
  simp [evalPoint, Polynomial.eval₂_mul]

/-- The image of `ppaBad` over `ℂ`. -/
private theorem mapC_ppaBad_ppaGenericTwP :
    mapC ppaBad = C (X * (X ^ 4 - 1)) * (X + C (X ^ 2)) := by
  simp [ppaBad, mapC]

/-- An irreducible polynomial of positive `L`-degree dividing `M (M⁴ - 1) (L + M²)` is divisible
by `L + M²`. -/
private theorem add_sq_dvd_of_dvd_ppaBad_ppaGenericTwP {g : ℂ[X][X]} (hg : Irreducible g)
    (hdeg : 0 < g.natDegree) (hd : g ∣ mapC ppaBad) : (X + C (X ^ 2) : ℂ[X][X]) ∣ g := by
  rw [mapC_ppaBad_ppaGenericTwP] at hd
  have hq : (X * (X ^ 4 - 1) : ℂ[X]) ≠ 0 := by
    refine mul_ne_zero X_ne_zero fun h0 ↦ ?_
    have := congrArg (Polynomial.eval 2) h0
    norm_num at this
  rcases hg.prime.dvd_or_dvd hd with h1 | h1
  · have := Polynomial.natDegree_le_of_dvd h1 (C_ne_zero.2 hq)
    rw [natDegree_C] at this
    omega
  · obtain ⟨k, hk⟩ := h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact X_add_C_ne_zero _ hk
    have hd1 : (X + C (X ^ 2) : ℂ[X][X]).natDegree = 1 := natDegree_X_add_C _
    rw [hk, natDegree_mul hg.ne_zero hk0] at hd1
    have hkd : k.natDegree = 0 := by omega
    have hlc : g.leadingCoeff * k.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hk]
      exact (monic_X_add_C _).leadingCoeff
    have hku : IsUnit k := by
      rw [eq_C_of_natDegree_eq_zero hkd]
      refine isUnit_C.2 (IsUnit.of_mul_eq_one_right g.leadingCoeff ?_)
      have hc0 : k.leadingCoeff = k.coeff 0 := by rw [leadingCoeff, hkd]
      rw [← hc0, hlc]
    rw [hk]
    exact (Associated.symm ⟨hku.unit, rfl⟩).dvd

/-- If the generic zeros of `𝒫_k` lie in `S`, then `𝒫_k` divides every A-polynomial of `S` in
the comparison ring. -/
theorem ppa_twP_dvd_of_generic {S : Set (ℂ × ℂ)} {A : ℤ[X][X]} (hA : IsAPolynomialOf S A)
    (k : ℤ) (hk : k ≠ 0)
    (hgen : ∀ M L : ℂ, M ≠ 0 → M ^ 4 ≠ 1 → M ^ 2 + L ≠ 0 →
      evalPoint (mapC (twP k)) (M, L) = 0 → (M, L) ∈ S) :
    toComparison (twP k) ∣ toComparison A := by
  refine ppa_toComparison_dvd_of_generic (Bad := ppaBad) hA (ppa_prime_toComparison_twP k hk)
    (ppa_coeff_zero_twP_ne_zero k) (fun g hg hdeg hdvd hd ↦ ?_) fun p hp hB ↦ ?_
  · obtain ⟨u, hu⟩ := (add_sq_dvd_of_dvd_ppaBad_ppaGenericTwP hg hdeg hd).trans hdvd
    apply ppa_evalPoint_twP_ne_zero k
    rw [hu, evalPoint_mul_ppaGenericTwP]
    simp [evalPoint, Polynomial.eval₂_pow]
    norm_num
  · obtain ⟨M, L⟩ := p
    rw [evalPoint_mapC_ppaBad] at hB
    have hM : M ≠ 0 := fun h0 ↦ hB (by rw [h0]; ring)
    have hM4 : M ^ 4 ≠ 1 := fun h0 ↦ hB (by rw [h0]; ring)
    have hQ : M ^ 2 + L ≠ 0 := fun h0 ↦ hB (by rw [add_comm L, h0]; ring)
    exact hgen M L hM hM4 hQ hp

end AJConjecture
