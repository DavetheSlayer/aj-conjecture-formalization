import Mathlib
import AJConjecture.QAlgComplexShiftScale
import AJConjecture.QAlgNodeJetBasic
import AJConjecture.QAlgNodeLocalRing

/-!
# The shift is an automorphism of the local ring of a point `(-1, m₀)`

The shift `M ↦ t² M` preserves the value at `(-1, m₀)` (`complexSpec_complexShift`), so the
ideal of the point is its own preimage and the shift induces a local homomorphism of
`Localization.AtPrime (nodeIdeal m₀)` (`Localization.localRingHom`). It is injective (the shift
is injective on the domain `ℂ[t][M]`) and surjective: a fraction `a / s` is the image of
`g_a t^(2 deg s) / (g_s t^(2 deg a))` with `g_a`, `g_s` from
`exists_complexShift_eq_C_X_pow_mul` (`g_s` does not vanish at the point because
`g_s(-1, m₀) = s(-1, m₀)`).
-/

open Polynomial

namespace AJConjecture

/-- Membership in the ideal of the point `(-1, m₀)`. -/
theorem mem_nodeIdeal_iff (m₀ : ℂ) (a : ℂ[X][X]) :
    a ∈ nodeIdeal m₀ ↔ (complexSpec a).eval m₀ = 0 := by
  rw [nodeIdeal, RingHom.mem_ker]
  rfl

/-- The ideal of the point `(-1, m₀)` is its own preimage under the shift. -/
private theorem nodeIdeal_eq_comap_complexShift (m₀ : ℂ) :
    nodeIdeal m₀ = (nodeIdeal m₀).comap complexShift := by
  ext a
  rw [Ideal.mem_comap, mem_nodeIdeal_iff, mem_nodeIdeal_iff,
    complexSpec_complexShift]

/-- The shift is injective. -/
private theorem complexShift_injective_shiftEquiv : Function.Injective complexShift := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hcomp : c.comp (C (X ^ 2) * X : ℂ[X][X]) = 0 := hc
  rcases Polynomial.comp_eq_zero_iff.mp hcomp with h | ⟨-, h⟩
  · exact h
  · exfalso
    have h1 := congrArg (fun q : ℂ[X][X] ↦ q.coeff 1) h
    simp only [coeff_C_mul, coeff_X_one, mul_one, coeff_C_succ] at h1
    exact pow_ne_zero 2 X_ne_zero h1

/-- A power of `t` is not in the ideal of the point `(-1, m₀)`. -/
private theorem C_X_pow_notMem_nodeIdeal (m₀ : ℂ) (k : ℕ) :
    (C (X ^ k) : ℂ[X][X]) ∉ nodeIdeal m₀ := by
  rw [mem_nodeIdeal_iff, complexSpec, coe_mapRingHom, map_C, coe_evalRingHom, eval_pow,
    eval_X, eval_C]
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

/-- The shift fixes the polynomials in `t`. -/
private theorem complexShift_C_shiftEquiv (c : ℂ[X]) : complexShift (C c) = C c := by
  have hcomp : complexShift (C c) = (C c : ℂ[X][X]).comp (C (X ^ 2) * X) := rfl
  rw [hcomp, C_comp]

/-- The shift `M ↦ t² M` extends to an automorphism of the local ring of `ℂ[t][M]` at the point
`(-1, m₀)`. -/
theorem exists_ringEquiv_atPrime_nodeIdeal (m₀ : ℂ) :
    ∃ σ : Localization.AtPrime (nodeIdeal m₀) ≃+* Localization.AtPrime (nodeIdeal m₀),
      ∀ a : ℂ[X][X], σ (algebraMap ℂ[X][X] (Localization.AtPrime (nodeIdeal m₀)) a) =
        algebraMap ℂ[X][X] (Localization.AtPrime (nodeIdeal m₀)) (complexShift a) := by
  have hIJ := nodeIdeal_eq_comap_complexShift m₀
  have hinj : Function.Injective
      (Localization.localRingHom (nodeIdeal m₀) (nodeIdeal m₀) complexShift hIJ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (nodeIdeal m₀).primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨m, hm⟩ := hx
    have hm0 : (m : ℂ[X][X]) ≠ 0 := fun h0 ↦ m.2 (h0 ▸ (nodeIdeal m₀).zero_mem)
    have ha : a = 0 := complexShift_injective_shiftEquiv <| by
      rw [map_zero]
      exact (mul_eq_zero.mp hm).resolve_left hm0
    rw [ha, IsLocalization.mk'_zero]
  have hsurj : Function.Surjective
      (Localization.localRingHom (nodeIdeal m₀) (nodeIdeal m₀) complexShift hIJ) := by
    intro y
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (nodeIdeal m₀).primeCompl y
    obtain ⟨ga, hga⟩ := exists_complexShift_eq_C_X_pow_mul a
    obtain ⟨gs, hgs⟩ := exists_complexShift_eq_C_X_pow_mul (s : ℂ[X][X])
    have hshift : complexShift (gs * C (X ^ (2 * a.natDegree))) =
        C (X ^ (2 * (s : ℂ[X][X]).natDegree)) * (s : ℂ[X][X]) * C (X ^ (2 * a.natDegree)) := by
      rw [map_mul, hgs, complexShift_C_shiftEquiv]
    have hmem : gs * C (X ^ (2 * a.natDegree)) ∉ nodeIdeal m₀ := by
      intro hmem
      rw [hIJ, Ideal.mem_comap, hshift] at hmem
      rcases (nodeIdeal_isPrime m₀).mem_or_mem hmem with h1 | h1
      · rcases (nodeIdeal_isPrime m₀).mem_or_mem h1 with h2 | h2
        · exact C_X_pow_notMem_nodeIdeal m₀ _ h2
        · exact s.2 h2
      · exact C_X_pow_notMem_nodeIdeal m₀ _ h1
    refine ⟨IsLocalization.mk' _ (ga * C (X ^ (2 * (s : ℂ[X][X]).natDegree)))
      (⟨_, hmem⟩ : (nodeIdeal m₀).primeCompl), ?_⟩
    rw [Localization.localRingHom_mk']
    apply IsLocalization.mk'_eq_of_eq
    simp only [map_mul, hga, hgs, complexShift_C_shiftEquiv]
    ring
  have hbij : Function.Bijective
      (Localization.localRingHom (nodeIdeal m₀) (nodeIdeal m₀) complexShift hIJ) := ⟨hinj, hsurj⟩
  exact ⟨RingEquiv.ofBijective _ hbij, fun a ↦ Localization.localRingHom_to_map _ _ _ hIJ a⟩

end AJConjecture
