import Mathlib
import AJConjecture.WitnessPolynomials

/-!
# The extra factor is absolutely irreducible

`E = L² - (M⁴ - 4M² + 1) L + M⁴` is irreducible in `ℂ[M][L]`: a factorisation `(L - a)(L - b)`
would need `a b = M⁴` and `a + b = M⁴ - 4M² + 1`, but divisors of `M⁴` are monomials.
-/

open Polynomial

namespace AJConjecture

/-- The extra factor over `ℂ`, written out. -/
private theorem extraFactor_map_complex_eq :
    extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) := by
  simp [extraFactor]

/-- No monomial `C c * X ^ i` has a complementary monomial summing to `M⁴ - 4M² + 1`. -/
private theorem monomial_add_ne_extraFactor_trace (c : ℂ) (hc : c ≠ 0) (i : ℕ) (hi : i ≤ 4) :
    (C c * (C c * X ^ i) + X ^ (4 - i) : ℂ[X]) ≠ C c * (X ^ 4 - 4 * X ^ 2 + 1) := by
  intro h
  have h2 := congrArg (fun p : ℂ[X] ↦ p.coeff 2) h
  have h0 := congrArg (fun p : ℂ[X] ↦ p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one, coeff_ofNat_mul] at h0 h2
  clear h
  interval_cases i <;> simp_all

/-- The extra factor has no root in `ℂ[M]`. -/
private theorem extraFactor_quadratic_ne_zero (a : ℂ[X]) :
    a ^ 2 - (X ^ 4 - 4 * X ^ 2 + 1) * a + X ^ 4 ≠ 0 := by
  intro h
  have hab : a * ((X ^ 4 - 4 * X ^ 2 + 1) - a) = X ^ 4 := by linear_combination -h
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X _).mp (Dvd.intro _ hab)
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  obtain rfl : a = C c * X ^ i := by rw [← hu, ← hcu, mul_comm]
  have hXi : (X ^ i : ℂ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hsplit : (X ^ 4 : ℂ[X]) = X ^ i * X ^ (4 - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have hb : C c * ((X ^ 4 - 4 * X ^ 2 + 1) - C c * X ^ i) = X ^ (4 - i) := by
    apply mul_left_cancel₀ hXi
    rw [← hsplit]
    linear_combination hab
  apply monomial_add_ne_extraFactor_trace c hc0 i hi
  rw [← hb]
  ring

/-- The extra factor `E` is irreducible over `ℂ`. -/
theorem irreducible_extraFactor_map :
    Irreducible (extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
  rw [extraFactor_map_complex_eq]
  have hdeg : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) : ℂ[X][X]).natDegree = 2 := by
    compute_degree!
  have hmonic : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) : ℂ[X][X]).Monic := by
    monicity!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha ↦ extraFactor_quadratic_ne_zero a ?_
  have hroot := (mem_roots hmonic.ne_zero).mp ha
  simpa [IsRoot.def] using hroot

end AJConjecture
