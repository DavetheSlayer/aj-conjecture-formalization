import Mathlib
import AJConjecture.APolynomial
import AJTwist.Classical.TwCSatelliteDefs
import AJTwist.Classical.TwCTwistBoundInt

/-!
# The classical bound for twisted Whitehead satellites (Unit C1)

Source: revision 5, Section 7 (`classical.tex`, "The two companion fillings" and
eq. (classicalcontainment)): restricted to the companion group a representation is abelian on
it (longitude trivial) or sends the central element to `±I`; with the twisted gluing this
forces a signed filling `μ_A λ_A^k` of the pattern with `k ∈ {-ℓ, a}`, and a filling of index
`k` gives `𝒫_k = 0`.

* `evalPoint_twP_of_whPattern`: in `SL₂(ℂ)`, pattern relations whose axis meridian is
  `t = z c^(-n)` with `z` central and `c` the axis longitude give `(L - 1) 𝒫_n = 0` at the
  eigenvalue pair. Route: `a₁ := t⁻¹ a t = c^n a c^(-n)` (the central factor cancels), so
  `a₁ c^n = c^n a`, `c = compMer a a₁`, and the longitude word is that of `twist_bound_int`.
* `evalPoint_twBound_of_twWhSatellite` (negative clasp): for a companion with
  `CompanionDichotomyZ C n₀`, every point of `eigenvalueSet K` is a zero of
  `twBound (-ℓ) (n₀ - ℓ) = (L - 1) 𝒫_(-ℓ) 𝒫_(n₀-ℓ)`: in the abelian case `t = c^ℓ` (index `-ℓ`),
  in the central case `t = z c^(ℓ - n₀)` (index `n₀ - ℓ`). For `T(r, s)`, `n₀ = r s` and the
  second index is `a = twIndex true r s ℓ`. The bound holds at every point of the eigenvalue
  set: no meridian factor is needed.
* `evalPoint_twBound_of_twWhSatelliteP` (positive clasp): every point `(M, L)` of
  `eigenvalueSet K` has `(M, L⁻¹)` on `twBound ℓ (ℓ - n₀)`: the same lemma for `t⁻¹` and the
  inverse longitude (indices `ℓ` and `ℓ - n₀`).

Numerical evidence (`SCR/C/py/w4_twk_bound.py`, `v4_reps.py`): `SL₂(ℂ)` representations of the
groups of closed braids of the twisted doubles of `T(2, 3)` (TwK's `twBlocks 2 3 ℓ σ` and a
second braid family for the same knots), `ℓ ∈ {-2, -1, 0, 1, 2}`, found by least squares; at
every nonabelian solution `𝒫_(6-ℓ)(M, L)` (negative clasp) resp. `𝒫_(ℓ-6)(M, L⁻¹)` (positive
clasp) vanishes to `10⁻⁹` and the polynomials of the other sign conventions do not.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value of the bound through the first filling factor. -/
private theorem evalPoint_twBound_left_twCSatelliteBound (k₁ k₂ : ℤ) (q : ℂ × ℂ) :
    evalPoint (mapC (twBound k₁ k₂)) q =
      evalPoint (mapC ((X - 1) * twP k₁)) q * evalPoint (mapC (twP k₂)) q := by
  simp only [evalPoint, mapC, twBound, Polynomial.map_mul, eval₂_mul]

/-- The value of the bound through the second filling factor. -/
private theorem evalPoint_twBound_right_twCSatelliteBound (k₁ k₂ : ℤ) (q : ℂ × ℂ) :
    evalPoint (mapC (twBound k₁ k₂)) q =
      evalPoint (mapC ((X - 1) * twP k₂)) q * evalPoint (mapC (twP k₁)) q := by
  simp only [evalPoint, mapC, twBound, Polynomial.map_mul, eval₂_mul]
  ring

/-- The inverse of an upper triangular element of `SL₂(ℂ)` is upper triangular with the inverse
first diagonal entry. -/
private theorem inv_entries_twCSatelliteBound (Y : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h : Y.1 1 0 = 0) : (Y⁻¹).1 1 0 = 0 ∧ (Y⁻¹).1 0 0 = (Y.1 0 0)⁻¹ := by
  have hdet := Y.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  have h11 : Y.1 1 1 = (Y.1 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  constructor
  · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h]
  · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h11]

/-- Pattern relations in `SL₂(ℂ)` with axis meridian `t = z c^(-n)`, `z` central: the
eigenvalue pair is a zero of `(L - 1) 𝒫_n`. -/
theorem evalPoint_twP_of_whPattern (n : ℤ) (a t c l z : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hz : ∀ x, z * x = x * z) (hp : IsWhPattern a t c l) (ht : t = z * c ^ (-n))
    (ha : a.1 1 0 = 0) (hl : l.1 1 0 = 0) :
    evalPoint (mapC ((X - 1) * twP n)) (a.1 0 0, l.1 0 0) = 0 := by
  obtain ⟨hc, hlw⟩ := hp
  have hz1 : ∀ x, z⁻¹ * x * z = x := fun x ↦ by rw [mul_assoc, ← hz, inv_mul_cancel_left]
  have hz2 : ∀ x, z * x * z⁻¹ = x := fun x ↦ by rw [hz, mul_inv_cancel_right]
  have e1 : t⁻¹ * a * t = c ^ n * a * (c ^ n)⁻¹ := by
    have h : t⁻¹ * a * t = c ^ n * (z⁻¹ * a * z) * (c ^ n)⁻¹ := by
      rw [ht, zpow_neg]
      group
    rw [h, hz1]
  have e2 : t * a⁻¹ * t⁻¹ = (c ^ n)⁻¹ * a⁻¹ * c ^ n := by
    have h : t * a⁻¹ * t⁻¹ = z * ((c ^ n)⁻¹ * a⁻¹ * c ^ n) * z⁻¹ := by
      rw [ht, zpow_neg]
      group
    rw [h, hz2]
  have hrel : t⁻¹ * a * t * c ^ n = c ^ n * a := by rw [e1, inv_mul_cancel_right]
  have hl2 : l = a ^ 2 * (c ^ n)⁻¹ * a⁻¹ * c ^ n * a * (t⁻¹ * a * t)⁻¹ * a⁻¹ := by
    have h : a ^ 2 * (c ^ n)⁻¹ * a⁻¹ * c ^ n = a ^ 2 * ((c ^ n)⁻¹ * a⁻¹ * c ^ n) := by
      simp only [mul_assoc]
    rw [hlw, h, ← e2]
    simp only [mul_assoc]
  rw [hc] at hrel hl2
  rw [hl2] at hl ⊢
  exact twist_bound_int n a _ ha hrel hl

/-- Unit C1, negative clasp: the eigenvalue set of an `ℓ`-twisted negative-clasp Whitehead
satellite over a companion with the dichotomy of exponent `n₀` lies in the zero set of
`(L - 1) 𝒫_(-ℓ) 𝒫_(n₀-ℓ)`. -/
theorem evalPoint_twBound_of_twWhSatellite {C K : BraidKnot} {n₀ ℓ : ℤ}
    (hC : CompanionDichotomyZ C n₀) (hK : IsTwWhSatellite C K ℓ) {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet K) : evalPoint (mapC (twBound (-ℓ) (n₀ - ℓ))) p = 0 := by
  obtain ⟨ρ, hm, hl, hM, hL⟩ := hp
  obtain ⟨φ, hpat⟩ := hK
  obtain ⟨p1, p2⟩ := p
  simp only at hM hL
  subst hM hL
  have hpat' := hpat.map ρ
  rw [map_mul, map_mul, map_zpow, map_zpow] at hpat'
  rcases hC (ρ.comp φ) with h1 | ⟨z, hz, h2⟩
  · rw [MonoidHom.comp_apply] at h1
    rw [evalPoint_twBound_left_twCSatelliteBound,
      evalPoint_twP_of_whPattern (-ℓ) _ _ _ _ 1 (fun x ↦ by rw [one_mul, mul_one]) hpat'
        (by rw [h1, neg_neg]) hm hl, zero_mul]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h2
    rw [evalPoint_twBound_right_twCSatelliteBound,
      evalPoint_twP_of_whPattern (n₀ - ℓ) _ _ _ _ z hz hpat'
        (by rw [h2, mul_assoc, ← zpow_add, neg_sub, neg_add_eq_sub]) hm hl, zero_mul]

/-- Unit C1, positive clasp: for an `ℓ`-twisted positive-clasp Whitehead satellite over a
companion with the dichotomy of exponent `n₀`, every point `(M, L)` of the eigenvalue set has
`(M, L⁻¹)` in the zero set of `(L - 1) 𝒫_ℓ 𝒫_(ℓ-n₀)`. -/
theorem evalPoint_twBound_of_twWhSatelliteP {C K : BraidKnot} {n₀ ℓ : ℤ}
    (hC : CompanionDichotomyZ C n₀) (hK : IsTwWhSatelliteP C K ℓ) {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet K) : evalPoint (mapC (twBound ℓ (ℓ - n₀))) (p.1, p.2⁻¹) = 0 := by
  obtain ⟨ρ, hm, hl, hM, hL⟩ := hp
  obtain ⟨φ, hpat⟩ := hK
  obtain ⟨p1, p2⟩ := p
  simp only at hM hL
  subst hM hL
  have hpat' := hpat.map ρ
  rw [map_inv, map_inv, map_mul, map_mul, map_zpow, map_zpow] at hpat'
  obtain ⟨hl10, hl00⟩ := inv_entries_twCSatelliteBound _ hl
  rw [← hl00]
  rcases hC (ρ.comp φ) with h1 | ⟨z, hz, h2⟩
  · rw [MonoidHom.comp_apply] at h1
    rw [evalPoint_twBound_left_twCSatelliteBound,
      evalPoint_twP_of_whPattern ℓ _ _ _ _ 1 (fun x ↦ by rw [one_mul, mul_one]) hpat'
        (by rw [h1, one_mul, one_mul, zpow_neg]) hm hl10, zero_mul]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h2
    have hz' : ∀ x, z⁻¹ * x = x * z⁻¹ := fun x ↦ by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hz, mul_inv_cancel_right]
    rw [evalPoint_twBound_right_twCSatelliteBound,
      evalPoint_twP_of_whPattern (ℓ - n₀) _ _ _ _ z⁻¹ hz' hpat'
        (by rw [h2, mul_assoc, ← zpow_add, mul_inv_rev, ← hz', ← zpow_neg, neg_add_eq_sub])
        hm hl10, zero_mul]

end AJConjecture
