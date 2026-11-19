import Mathlib
import AJFamily.Quantum.TwistPolyFactorDegree

/-!
# Irreducibility of the twist polynomial

For `m ≥ 2`, `B_m` is irreducible in `ℂ(M)[L]`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

theorem irreducible_twistPoly_ratFunc (m : ℕ) (hm : 2 ≤ m) :
    Irreducible ((twistPoly m).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) := by
  set φ := (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)) with hφ
  have hinj : Function.Injective φ :=
    (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
      (Polynomial.map_injective _ (Int.cast_injective (α := ℂ)))
  set P := (twistPoly m).map φ with hP
  have hdeg : P.natDegree = 2 * m := by
    rw [hP, Polynomial.natDegree_map_eq_of_injective hinj, natDegree_twistPoly]
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hPunit : ¬ IsUnit P := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg, hgP⟩ := WfDvdMonoid.exists_irreducible_factor hPunit hP0
  have hle := two_mul_le_natDegree_of_dvd_twistPoly m hm hg hgP
  obtain ⟨h, hgh⟩ := hgP
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgh
    exact hP0 hgh
  have hdegs : P.natDegree = g.natDegree + h.natDegree := by
    rw [hgh, Polynomial.natDegree_mul hg.ne_zero hh0]
  have hh : h.natDegree = 0 := by omega
  have hhu : IsUnit h := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hh]
    refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
    intro hc
    apply hh0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hh, hc, map_zero]
  rw [hgh]
  exact (irreducible_mul_isUnit hhu).mpr hg

end AJConjecture
