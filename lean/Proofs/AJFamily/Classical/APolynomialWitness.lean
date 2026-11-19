import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.ExtraFactorIrreducible
import AJFamily.Classical.APolynomialOfStable
import AJFamily.Classical.FamilyPoint
import AJFamily.Classical.SatelliteBound

/-!
# An A-polynomial not divisible by the extra factor

For a braid knot with the satellite peripheral structure over `T(2, 2k+1)`, some A-polynomial of
its eigenvalue set is not divisible by `extraFactor` in the comparison ring: otherwise the bound
`(L - 1) B_m`, which vanishes on the eigenvalue set, would vanish on the whole zero set of the
irreducible `extraFactor`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem exists_aPolynomial_not_extraFactor_dvd {K : BraidKnot} {k : ℕ}
    (hK : SatellitePeripheral K k) :
    ∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A ∧
      ¬ toComparison extraFactor ∣ toComparison A := by
  have hm : 0 < famDegree k := by unfold famDegree; omega
  obtain ⟨A, hA, -⟩ := exists_isAPolynomialOf_of_isAutStable (famBound_ne_zero hm)
    (fun p hp ↦ evalPoint_famBound_of_mem_eigenvalueSet hK hp) (eigenvalueSet_isAutStable K)
  refine ⟨A, hA, fun hdvd ↦ ?_⟩
  have h1 : extraFactor ∣ A := extraFactor_dvd_of_toComparison_dvd hdvd
  have h2 : extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) ∣
      A.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) := Polynomial.map_dvd _ h1
  have h3 := (hA.2 _ irreducible_extraFactor_map).mp h2
  obtain ⟨p, hp0, hpne⟩ := exists_extraFactor_zero_not_famBound_zero hm
  exact hpne (h3 p hp0 _ fun s hs ↦ evalPoint_famBound_of_mem_eigenvalueSet hK hs)

end AJConjecture
