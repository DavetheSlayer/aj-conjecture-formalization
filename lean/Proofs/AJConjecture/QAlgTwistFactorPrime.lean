import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# The twist factor and `L - 1` are prime in the comparison ring

`B` is irreducible in `ℤ[M][L]`, hence primitive, hence irreducible over `ℚ(M)` by Gauss's
lemma; its constant coefficient `M^24` is nonzero, so it stays prime in `ℚ(M)[L, L⁻¹]`. The same
holds for `L - 1`.
-/

open Polynomial

namespace AJConjecture

/-- Over a field, divisibility by a polynomial with nonzero constant coefficient descends from
the Laurent polynomial ring. -/
theorem dvd_of_toLaurent_dvd {K : Type*} [Field K] {p q : K[X]}
    (hp : p.coeff 0 ≠ 0) (h : toLaurent p ∣ toLaurent q) : p ∣ q := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨n, r', hr'⟩ := LaurentPolynomial.exists_T_pow r
  have hmul : q * X ^ n = p * r' := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hr, hr', mul_assoc]
  have hunit : IsCoprime (C (p.coeff 0)) (X : K[X]) :=
    ⟨C (p.coeff 0)⁻¹, 0, by rw [zero_mul, add_zero, ← C_mul, inv_mul_cancel₀ hp, C_1]⟩
  have hcop : IsCoprime p (X : K[X]) := by
    have hadd := hunit.add_mul_left_left (divX p)
    rwa [add_comm, mul_comm, divX_mul_X_add] at hadd
  exact (hcop.pow_right (n := n)).dvd_of_dvd_mul_right (Dvd.intro r' hmul.symm)

/-- Over a field, a prime polynomial with nonzero constant coefficient stays prime in the
Laurent polynomial ring. -/
theorem prime_toLaurent_of_prime {K : Type*} [Field K] {p : K[X]}
    (hp : Prime p) (h0 : p.coeff 0 ≠ 0) : Prime (toLaurent p) := by
  refine ⟨(map_ne_zero_iff _ Polynomial.toLaurent_injective).mpr hp.ne_zero, fun hu ↦ ?_,
    fun a b hab ↦ ?_⟩
  · refine hp.not_isUnit (isUnit_of_dvd_one (dvd_of_toLaurent_dvd h0 ?_))
    rw [map_one]
    exact hu.dvd
  · obtain ⟨m, a', ha⟩ := LaurentPolynomial.exists_T_pow a
    obtain ⟨n, b', hb⟩ := LaurentPolynomial.exists_T_pow b
    have hdvd : toLaurent p ∣ toLaurent (a' * b') := by
      rw [map_mul, ha, hb, mul_mul_mul_comm]
      exact hab.mul_right _
    rcases hp.dvd_or_dvd (dvd_of_toLaurent_dvd h0 hdvd) with h | h
    · left
      rw [← (LaurentPolynomial.isUnit_T (m : ℤ)).dvd_mul_right, ← ha]
      exact map_dvd _ h
    · right
      rw [← (LaurentPolynomial.isUnit_T (n : ℤ)).dvd_mul_right, ← hb]
      exact map_dvd _ h

/-- `L - 1` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
theorem prime_toComparison_X_sub_one : Prime (toComparison (X - 1)) := by
  have hmap : (Polynomial.mapRingHom
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))))
      (X - 1) = X - C 1 := by
    simp
  have hprime : Prime (toLaurent (X - C (1 : RatFunc ℚ))) :=
    prime_toLaurent_of_prime (irreducible_X_sub_C 1).prime (by simp)
  rw [← hmap] at hprime
  exact hprime

end AJConjecture
