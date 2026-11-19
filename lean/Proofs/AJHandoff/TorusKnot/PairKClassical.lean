import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.ExtraFactorIrreducible
import AJFamily.Classical.APolynomialOfStable
import AJFamily.Classical.FamilyPoint
import AJHandoff.TorusKnot.PairKPeripheral
import AJHandoff.TorusKnot.PairKTorusDichotomy

/-!
# The classical side of Theorem T

For every admissible pair, with `m = rs`:

* `evalPoint_famBound_pair`: every point of the eigenvalue set of `Wh⁻₀(T(r, s))` is a zero of
  `(L - 1) B_m` (T-CLASS, bound);
* `exists_aPolynomial_pair`: an A-polynomial with integer coefficients exists, divides
  `(L - 1) B_m` over `ℂ`, and is not divisible by `E` in `ℚ(M)[L, L⁻¹]` (T-AEX, first half;
  Galois descent `exists_isAPolynomialOf_of_isAutStable` is general);
* `exists_extraFactor_zero_not_famBound_pair`: a zero of `E` off the curve `(L - 1) B_m = 0`,
  for both parities of `m` (`exists_extraFactor_zero_not_famBound_zero` is general in `m`).
-/

open Polynomial

namespace AJConjecture

/-- T-CLASS (bound): the eigenvalue set of `Wh⁻₀(T(r, s))` lies in the zero set of
`(L - 1) B_(rs)`. -/
theorem evalPoint_famBound_pair {r s : ℕ} (h : IsTorusPair r s) {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet (pairWhiteheadKnot r s h)) :
    evalPoint (mapC (famBound (r * s))) p = 0 :=
  evalPoint_famBound_of_whSatellite (companionDichotomy_torusPairKnot h)
    (isWhSatellite_pairWhiteheadKnot h) hp

/-- `rs > 0` for an admissible pair. -/
theorem pair_mul_pos {r s : ℕ} (h : IsTorusPair r s) : 0 < r * s := by
  obtain ⟨hr, hrs, -⟩ := h
  exact Nat.mul_pos (by omega) (by omega)

/-- A zero of `E` at which `(L - 1) B_(rs)` does not vanish. -/
theorem exists_extraFactor_zero_not_famBound_pair {r s : ℕ} (h : IsTorusPair r s) :
    ∃ p : ℂ × ℂ, evalPoint (mapC extraFactor) p = 0 ∧
      evalPoint (mapC (famBound (r * s))) p ≠ 0 :=
  exists_extraFactor_zero_not_famBound_zero (pair_mul_pos h)

/-- T-AEX (first half): an integral A-polynomial of `Wh⁻₀(T(r, s))` exists; it divides
`(L - 1) B_(rs)` over `ℂ` and is not divisible by `E` in the comparison ring. -/
theorem exists_aPolynomial_pair {r s : ℕ} (h : IsTorusPair r s) :
    ∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A ∧
      mapC A ∣ mapC (famBound (r * s)) ∧ ¬ toComparison extraFactor ∣ toComparison A := by
  obtain ⟨A, hA, hdvd⟩ := exists_isAPolynomialOf_of_isAutStable
    (famBound_ne_zero (pair_mul_pos h)) (fun p hp ↦ evalPoint_famBound_pair h hp)
    (eigenvalueSet_isAutStable _)
  refine ⟨A, hA, hdvd, fun hE ↦ ?_⟩
  have h1 : extraFactor ∣ A := extraFactor_dvd_of_toComparison_dvd hE
  have h2 : extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) ∣
      A.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) := Polynomial.map_dvd _ h1
  have h3 := (hA.2 _ irreducible_extraFactor_map).mp h2
  obtain ⟨p, hp0, hpne⟩ := exists_extraFactor_zero_not_famBound_pair h
  exact hpne (h3 p hp0 _ fun q hq ↦ evalPoint_famBound_pair h hq)

end AJConjecture
