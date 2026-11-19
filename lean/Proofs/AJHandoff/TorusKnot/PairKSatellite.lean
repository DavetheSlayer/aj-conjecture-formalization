import Mathlib
import AJConjecture.APolynomial
import AJFamily.Classical.SatelliteData
import AJFamily.Classical.TwistBoundGen

/-!
# Whitehead satellites over an arbitrary companion, and the classical bound

`IsWhSatellite C K` says that the knot group of `K` carries the peripheral structure of the
untwisted negative-clasp Whitehead double of the companion `C`: a homomorphism `φ` from the
knot group of `C` and a meridian `μ₁` of the second clasp arc such that `φ` sends the companion
meridian to `compMer μ μ₁ = μ μ₁⁻¹ μ⁻¹ μ₁`, `μ₁` is `μ` transported once along the image `Λ` of
the companion longitude, and the longitude of `K` is the pattern word
`μ² Λ μ⁻¹ Λ⁻¹ μ μ₁⁻¹ μ⁻¹`. These are the relations of `IsSatelliteData` (`r = 2`) with the
companion group no longer presented by two generators.

`CompanionDichotomy C m` says that every representation of the companion group into `SL₂(ℂ)`
sends the longitude either to `1` or to a central element times the `(-m)`-th power of the
meridian. For `T(r, s)` it holds with `m = rs` (`AJHandoff.TorusKnot.PairKTorusDichotomy`),
covering both central signs `ε = ±1` and reducible nonabelian representations.

`evalPoint_famBound_of_whSatellite`: if `C` has the dichotomy with exponent `m` and `K` is a
Whitehead satellite of `C`, every point of the eigenvalue set of `K` is a zero of
`(L - 1) B_m = famBound m`. Route: as `famBound_of_satelliteData`; in the first case `μ₁ = μ`
and the longitude is `1`; in the second the central factor cancels from the gluing and
longitude words, which become the twist relation `μ₁ c^m = c^m μ` of `twist_bound_gen`.
-/

namespace AJConjecture

/-- The peripheral structure of the untwisted negative-clasp Whitehead double of `C` in the knot
group of `K`. -/
def IsWhSatellite (C K : BraidKnot) : Prop :=
  ∃ (φ : KnotGroup C →* KnotGroup K) (μ₁ : KnotGroup K),
    φ (meridian C) = compMer (meridian K) μ₁ ∧
    μ₁ = (φ (longitude C))⁻¹ * meridian K * φ (longitude C) ∧
    longitude K = meridian K ^ 2 * φ (longitude C) * (meridian K)⁻¹ * (φ (longitude C))⁻¹ *
      meridian K * μ₁⁻¹ * (meridian K)⁻¹

/-- Every `SL₂(ℂ)` representation of the companion group sends the longitude to `1` or to a
central element times the `(-m)`-th power of the meridian. -/
def CompanionDichotomy (C : BraidKnot) (m : ℕ) : Prop :=
  ∀ ρ : KnotGroup C →* Matrix.SpecialLinearGroup (Fin 2) ℂ,
    ρ (longitude C) = 1 ∨
      ∃ z : Matrix.SpecialLinearGroup (Fin 2) ℂ, (∀ x, z * x = x * z) ∧
        ρ (longitude C) = z * ρ (meridian C) ^ (-(m : ℤ))

/-- Conjugating by `(z * w)⁻¹` with `z` central is conjugating by `w⁻¹`. -/
private theorem whSat_inv_conj_central {G : Type*} [Group G] (z w g : G)
    (hz : ∀ x : G, z * x = x * z) : (z * w)⁻¹ * g * (z * w) = w⁻¹ * g * w := by
  calc (z * w)⁻¹ * g * (z * w) = w⁻¹ * (z⁻¹ * (g * z)) * w := by group
    _ = w⁻¹ * (z⁻¹ * (z * g)) * w := by rw [hz]
    _ = w⁻¹ * g * w := by group

/-- Conjugating by `z * w` with `z` central is conjugating by `w`. -/
private theorem whSat_conj_central {G : Type*} [Group G] (z w g : G)
    (hz : ∀ x : G, z * x = x * z) : z * w * g * (z * w)⁻¹ = w * g * w⁻¹ := by
  calc z * w * g * (z * w)⁻¹ = z * (w * g * w⁻¹) * z⁻¹ := by group
    _ = w * g * w⁻¹ * z * z⁻¹ := by rw [hz]
    _ = w * g * w⁻¹ := by group

/-- The family bound vanishes at any point with `L = 1`. -/
private theorem whSat_famBound_eval_L_one (m : ℕ) (M : ℂ) :
    evalPoint (mapC (famBound m)) (M, 1) = 0 := by
  simp only [evalPoint, mapC, famBound, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_one, sub_self, zero_mul]

/-- T-CLASS (bound), for an arbitrary companion: the eigenvalue set of a Whitehead satellite
lies in the zero set of `(L - 1) B_m`. -/
theorem evalPoint_famBound_of_whSatellite {C K : BraidKnot} {m : ℕ}
    (hC : CompanionDichotomy C m) (hK : IsWhSatellite C K) {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet K) : evalPoint (mapC (famBound m)) p = 0 := by
  obtain ⟨ρ, hm, hl, hM, hL⟩ := hp
  obtain ⟨φ, μ₁, hmer, hglue, hlong⟩ := hK
  obtain ⟨p1, p2⟩ := p
  simp only at hM hL
  subst hM hL
  have hmer' := congrArg ρ hmer
  have hglue' := congrArg ρ hglue
  have hlong' := congrArg ρ hlong
  simp only [compMer, map_mul, map_inv, map_pow] at hmer' hglue' hlong'
  rw [hlong'] at hl ⊢
  set a := ρ (meridian K)
  set a₁ := ρ μ₁
  rcases hC (ρ.comp φ) with h1 | ⟨z, hz, h2⟩
  · rw [MonoidHom.comp_apply] at h1
    rw [h1] at hglue' hlong' ⊢
    have ha₁ : a₁ = a := by rw [hglue']; group
    rw [ha₁]
    have : a ^ 2 * 1 * a⁻¹ * 1⁻¹ * a * a⁻¹ * a⁻¹ = 1 := by group
    rw [this]
    exact whSat_famBound_eval_L_one _ _
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hmer'] at h2
    rw [h2] at hglue' ⊢
    rw [h2] at hl
    have hrel : a₁ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m = (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a := by
      set c := a * a₁⁻¹ * a⁻¹ * a₁
      rw [hglue', whSat_inv_conj_central z _ a hz]
      group
    have hw : a ^ 2 * (z * (a * a₁⁻¹ * a⁻¹ * a₁) ^ (-(m : ℤ))) * a⁻¹ *
        (z * (a * a₁⁻¹ * a⁻¹ * a₁) ^ (-(m : ℤ)))⁻¹ * a * a₁⁻¹ * a⁻¹ =
        a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
          a₁⁻¹ * a⁻¹ := by
      calc _ = a ^ 2 * (z * (a * a₁⁻¹ * a⁻¹ * a₁) ^ (-(m : ℤ)) * a⁻¹ *
            (z * (a * a₁⁻¹ * a⁻¹ * a₁) ^ (-(m : ℤ)))⁻¹) * a * a₁⁻¹ * a⁻¹ := by group
        _ = a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ (-(m : ℤ)) * a⁻¹ *
            ((a * a₁⁻¹ * a⁻¹ * a₁) ^ (-(m : ℤ)))⁻¹) * a * a₁⁻¹ * a⁻¹ := by
          rw [whSat_conj_central z _ a⁻¹ hz]
        _ = _ := by group
    rw [hw] at hl ⊢
    exact twist_bound_gen m a a₁ hm hrel hl

end AJConjecture
