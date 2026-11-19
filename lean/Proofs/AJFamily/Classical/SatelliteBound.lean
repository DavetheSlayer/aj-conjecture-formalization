import Mathlib
import AJFamily.Classical.SatelliteData
import AJFamily.Classical.TorusCompanionSL2
import AJFamily.Classical.TwistBoundGen

/-!
# The bound on the eigenvalue set

If `a, a₁, d, l ∈ SL₂(ℂ)` satisfy the satellite relations, with `a` and `l` upper triangular,
then `(L - 1) B_m`, `m = 2(2k+1)`, vanishes at their diagonal entries `(a₀₀, l₀₀)`. Either
`c = d`, and then `l = 1`; or `(cd)^(2k+1) = -1` is central, and the relations reduce to the
twist relation `a₁ c^m = c^m a` handled by `twist_bound_gen`. Hence the bound vanishes on the
eigenvalue set of any knot with `SatellitePeripheral`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Conjugating by `(w * z)⁻¹` with `z` central is conjugating by `w⁻¹`. -/
private theorem satellite_inv_conj_central {G : Type*} [Group G] (z w g : G)
    (hz : ∀ x : G, z * x = x * z) : (w * z)⁻¹ * g * (w * z) = w⁻¹ * g * w := by
  calc (w * z)⁻¹ * g * (w * z) = z⁻¹ * (w⁻¹ * g * w * z) := by group
    _ = z⁻¹ * (z * (w⁻¹ * g * w)) := by rw [hz]
    _ = w⁻¹ * g * w := by group

/-- Conjugating by `w * z` with `z` central is conjugating by `w`. -/
private theorem satellite_conj_central {G : Type*} [Group G] (z w g : G)
    (hz : ∀ x : G, z * x = x * z) : w * z * g * (w * z)⁻¹ = w * g * w⁻¹ := by
  calc w * z * g * (w * z)⁻¹ = w * (z * (g * z⁻¹)) * w⁻¹ := by group
    _ = w * (g * z⁻¹ * z) * w⁻¹ := by rw [hz]
    _ = w * g * w⁻¹ := by group

/-- The gluing relation with a central correction gives the general twist-knot relation. -/
private theorem satellite_rel_of_central {G : Type*} [Group G] (m : ℕ) (z c a a₁ : G)
    (hz : ∀ x : G, z * x = x * z)
    (h : a₁ = (c ^ (-(m : ℤ)) * z)⁻¹ * a * (c ^ (-(m : ℤ)) * z)) :
    a₁ * c ^ m = c ^ m * a := by
  rw [h, satellite_inv_conj_central z _ a hz]
  group

/-- The longitude word with a central correction is the general twist-knot longitude word. -/
private theorem satellite_long_of_central {G : Type*} [Group G] (m : ℕ) (z c a a₁ : G)
    (hz : ∀ x : G, z * x = x * z) :
    a ^ 2 * (c ^ (-(m : ℤ)) * z) * a⁻¹ * (c ^ (-(m : ℤ)) * z)⁻¹ * a * a₁⁻¹ * a⁻¹ =
      a ^ 2 * (c ^ m)⁻¹ * a⁻¹ * c ^ m * a * a₁⁻¹ * a⁻¹ := by
  calc a ^ 2 * (c ^ (-(m : ℤ)) * z) * a⁻¹ * (c ^ (-(m : ℤ)) * z)⁻¹ * a * a₁⁻¹ * a⁻¹
      = a ^ 2 * (c ^ (-(m : ℤ)) * z * a⁻¹ * (c ^ (-(m : ℤ)) * z)⁻¹) * a * a₁⁻¹ * a⁻¹ := by
        group
    _ = a ^ 2 * (c ^ (-(m : ℤ)) * a⁻¹ * (c ^ (-(m : ℤ)))⁻¹) * a * a₁⁻¹ * a⁻¹ := by
      rw [satellite_conj_central z _ a⁻¹ hz]
    _ = a ^ 2 * (c ^ m)⁻¹ * a⁻¹ * c ^ m * a * a₁⁻¹ * a⁻¹ := by group

/-- An element of `SL₂(ℂ)` whose matrix is `-1` is central. -/
private theorem satellite_central_of_coe_eq_neg_one (z : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hz : (z : Matrix (Fin 2) (Fin 2) ℂ) = -1) (x : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    z * x = x * z := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, hz, neg_one_mul, mul_neg_one]

/-- The family bound vanishes at any point with `L = 1`. -/
private theorem famBound_eval_L_one (m : ℕ) (M : ℂ) :
    evalPoint (mapC (famBound m)) (M, 1) = 0 := by
  simp only [evalPoint, mapC, famBound, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one, sub_self,
    zero_mul]

/-- The companion longitude is trivial when the two companion generators agree. -/
private theorem compLong_self {G : Type*} [Group G] (k : ℕ) (c : G) : compLong k c c = 1 := by
  rw [compLong, ← sq, ← pow_mul, famDegree, zpow_neg, zpow_natCast, inv_mul_cancel]

theorem famBound_of_satelliteData (k : ℕ) (a a₁ d l : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h : IsSatelliteData k a a₁ d l) (ha : a.1 1 0 = 0) (hl : l.1 1 0 = 0) :
    evalPoint (mapC (famBound (famDegree k))) (a.1 0 0, l.1 0 0) = 0 := by
  obtain ⟨hrel, hglue, hlong⟩ := h
  obtain ⟨c, hc⟩ : ∃ c, c = compMer a a₁ := ⟨_, rfl⟩
  rw [← hc] at hrel hglue hlong
  rcases torus_rel_eq_or_center_eq_neg_one k c d hrel with hcd | hneg
  · subst hcd
    rw [compLong_self] at hglue hlong
    have ha₁ : a₁ = a := by rw [hglue]; group
    have hl1 : l = 1 := by rw [hlong, ha₁]; group
    rw [hl1]
    exact famBound_eval_L_one _ _
  · have hz := satellite_central_of_coe_eq_neg_one _ hneg
    have hrel' := satellite_rel_of_central (famDegree k) _ c a a₁ hz hglue
    rw [compLong, satellite_long_of_central (famDegree k) _ c a a₁ hz] at hlong
    subst hlong
    rw [hc, compMer] at hrel' hl ⊢
    exact twist_bound_gen (famDegree k) a a₁ ha hrel' hl

theorem evalPoint_famBound_of_mem_eigenvalueSet {K : BraidKnot} {k : ℕ}
    (hK : SatellitePeripheral K k) {p : ℂ × ℂ} (hp : p ∈ eigenvalueSet K) :
    evalPoint (mapC (famBound (famDegree k))) p = 0 := by
  obtain ⟨ρ, hm, hl, hM, hL⟩ := hp
  obtain ⟨a₁, d, h⟩ := hK
  have h' := famBound_of_satelliteData k _ _ _ _ (h.map ρ) hm hl
  rw [hM, hL] at h'
  exact h'

end AJConjecture
