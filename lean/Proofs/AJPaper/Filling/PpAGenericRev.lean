import Mathlib
import AJPaper.Filling.PpAGenericDvd
import AJPaper.Filling.PpASubOne

/-!
# Generic points and the reversed factor `(𝒫_k).reverse` of the A-polynomial (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`) and Section 8.2 (`conclusion.tex`,
"Transport under the satellite mirror"): for the positive clasp and for the mirror images the
longitude eigenvalue is inverted.

`ppa_twP_reverse_dvd_of_generic`: if the images `(M, L⁻¹)` of the zeros `(M, L)` of `𝒫_k`
(`k ≠ 0`) with `M ≠ 0`, `M⁴ ≠ 1`, `L ≠ -M²` lie in `S`, then the reverse of `𝒫_k` in `L` divides
every A-polynomial of `S` in `R = ℚ(M)[L, L⁻¹]`.

Route: `ppa_toComparison_dvd_of_generic` with `P = (𝒫_k).reverse` and
`Bad = ppaBadRev = M (M⁴ - 1) L (M² L + 1)`. `P` is prime in `R`
(`ppa_prime_toComparison_twP_reverse`); its constant coefficient is the leading coefficient of
`𝒫_k` (`Polynomial.coeff_zero_reverse`), not zero because `𝒫_k ≠ 0`. An irreducible `g` of
positive `L`-degree dividing `mapC ppaBadRev` is associated to `L` or to `M² L + 1`; in the
first case `P` would have constant coefficient `0`, in the second it would vanish at
`(2, -1/4)`, i.e. `𝒫_k(2, -4) = 0` (`evalPoint_mapC_reverse_eq_zero_iff`), against
`ppa_evalPoint_twP_ne_zero`. A zero `(M, L')` of `P` where `ppaBadRev` does not vanish has
`L' ≠ 0`, so `(M, L'⁻¹)` is a zero of `𝒫_k` (`evalPoint_mapC_reverse_eq_zero_iff`) with
`M² + L'⁻¹ ≠ 0` (as `M² L' + 1 ≠ 0`), and `(M, (L'⁻¹)⁻¹) = (M, L')` lies in `S`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The polynomial `M (M⁴ - 1) L (M² L + 1)`: the excluded points after `L ↦ L⁻¹`. -/
def ppaBadRev : ℤ[X][X] := C (X * (X ^ 4 - 1)) * (X * (C (X ^ 2) * X + 1))

theorem evalPoint_mapC_ppaBadRev (M L : ℂ) :
    evalPoint (mapC ppaBadRev) (M, L) = M * (M ^ 4 - 1) * (L * (M ^ 2 * L + 1)) := by
  simp [ppaBadRev, mapC, evalPoint, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_pow]

/-- Evaluation at a point is multiplicative. -/
private theorem evalPoint_mul_ppaGenericRev (P Q : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (P * Q) p = evalPoint P p * evalPoint Q p := by
  simp [evalPoint, Polynomial.eval₂_mul]

/-- The image of `ppaBadRev` over `ℂ`. -/
private theorem mapC_ppaBadRev_ppaGenericRev :
    mapC ppaBadRev = C (X * (X ^ 4 - 1)) * (X * (C (X ^ 2) * X + 1)) := by
  simp [ppaBadRev, mapC]

/-- An irreducible polynomial of positive `L`-degree dividing `M² L + 1` is divisible by it. -/
private theorem linear_dvd_of_dvd_ppaGenericRev {g : ℂ[X][X]} (hg : Irreducible g)
    (hdeg : 0 < g.natDegree) (h1 : g ∣ (C (X ^ 2) * X + 1 : ℂ[X][X])) :
    (C (X ^ 2) * X + 1 : ℂ[X][X]) ∣ g := by
  obtain ⟨k, hk⟩ := h1
  have h00 : g.coeff 0 * k.coeff 0 = 1 := by
    rw [← mul_coeff_zero, ← hk]
    simp
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h00
  have hd1 : (C (X ^ 2) * X + 1 : ℂ[X][X]).natDegree ≤ 1 := by compute_degree
  rw [hk, natDegree_mul hg.ne_zero hk0] at hd1
  have hkd : k.natDegree = 0 := by omega
  have hku : IsUnit k := by
    rw [eq_C_of_natDegree_eq_zero hkd]
    exact isUnit_C.2 (IsUnit.of_mul_eq_one_right (g.coeff 0) h00)
  rw [hk]
  exact (Associated.symm ⟨hku.unit, rfl⟩).dvd

/-- No irreducible factor of positive `L`-degree of the reverse of `𝒫_k` divides
`M (M⁴ - 1) L (M² L + 1)`. -/
private theorem not_dvd_ppaBadRev_ppaGenericRev (k : ℤ) {g : ℂ[X][X]} (hg : Irreducible g)
    (hdeg : 0 < g.natDegree) (hdvd : g ∣ mapC (twP k).reverse) : ¬ g ∣ mapC ppaBadRev := by
  intro hd
  rw [mapC_ppaBadRev_ppaGenericRev] at hd
  have hq : (X * (X ^ 4 - 1) : ℂ[X]) ≠ 0 := by
    refine mul_ne_zero X_ne_zero fun h0 ↦ ?_
    have := congrArg (Polynomial.eval 2) h0
    norm_num at this
  rcases hg.prime.dvd_or_dvd hd with h1 | h1
  · have := Polynomial.natDegree_le_of_dvd h1 (C_ne_zero.2 hq)
    rw [natDegree_C] at this
    omega
  rcases hg.prime.dvd_or_dvd h1 with h2 | h2
  · have hX : (X : ℂ[X][X]) ∣ mapC (twP k).reverse :=
      (hg.dvd_symm Polynomial.irreducible_X h2).trans hdvd
    rw [Polynomial.X_dvd_iff, mapC, coeff_map, coeff_zero_reverse] at hX
    have hlc : (twP k).leadingCoeff = 0 :=
      Polynomial.map_injective _ (Int.cast_injective (α := ℂ)) (by simpa using hX)
    rw [leadingCoeff_eq_zero] at hlc
    exact ppa_coeff_zero_twP_ne_zero k (by rw [hlc, coeff_zero])
  · obtain ⟨u, hu⟩ := (linear_dvd_of_dvd_ppaGenericRev hg hdeg h2).trans hdvd
    have hz : evalPoint (mapC (twP k).reverse) (2, (-4 : ℂ)⁻¹) = 0 := by
      rw [hu, evalPoint_mul_ppaGenericRev]
      simp [evalPoint, Polynomial.eval₂_pow]
      norm_num
    exact ppa_evalPoint_twP_ne_zero k
      ((evalPoint_mapC_reverse_eq_zero_iff (twP k) 2 (-4) (by norm_num)).1 hz)

/-- If the images under `L ↦ L⁻¹` of the generic zeros of `𝒫_k` lie in `S`, then the reverse of
`𝒫_k` divides every A-polynomial of `S` in the comparison ring. -/
theorem ppa_twP_reverse_dvd_of_generic {S : Set (ℂ × ℂ)} {A : ℤ[X][X]}
    (hA : IsAPolynomialOf S A) (k : ℤ) (hk : k ≠ 0)
    (hgen : ∀ M L : ℂ, M ≠ 0 → M ^ 4 ≠ 1 → M ^ 2 + L ≠ 0 →
      evalPoint (mapC (twP k)) (M, L) = 0 → (M, L⁻¹) ∈ S) :
    toComparison (twP k).reverse ∣ toComparison A := by
  have hP0 : (twP k).reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse, Ne, leadingCoeff_eq_zero]
    intro h0
    exact ppa_coeff_zero_twP_ne_zero k (by rw [h0, coeff_zero])
  refine ppa_toComparison_dvd_of_generic (Bad := ppaBadRev) hA
    (ppa_prime_toComparison_twP_reverse k hk) hP0
    (fun g hg hdeg hdvd ↦ not_dvd_ppaBadRev_ppaGenericRev k hg hdeg hdvd) fun p hp hB ↦ ?_
  obtain ⟨M, L⟩ := p
  rw [evalPoint_mapC_ppaBadRev] at hB
  have hM : M ≠ 0 := fun h0 ↦ hB (by rw [h0]; ring)
  have hM4 : M ^ 4 ≠ 1 := fun h0 ↦ hB (by rw [h0]; ring)
  have hL : L ≠ 0 := fun h0 ↦ hB (by rw [h0]; ring)
  have hQ : M ^ 2 + L⁻¹ ≠ 0 := fun h0 ↦ hB <| by
    have h1 : M ^ 2 * L + 1 = (M ^ 2 + L⁻¹) * L := by field_simp
    rw [h1, h0]
    ring
  have hz : evalPoint (mapC (twP k)) (M, L⁻¹) = 0 := by
    rw [← evalPoint_mapC_reverse_eq_zero_iff (twP k) M L⁻¹ (inv_ne_zero hL), inv_inv]
    exact hp
  have hmem := hgen M L⁻¹ hM hM4 hQ hz
  rwa [inv_inv] at hmem

end AJConjecture
