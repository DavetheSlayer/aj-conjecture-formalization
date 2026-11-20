import Mathlib
import AJConjecture.APolynomial
import AJFamily.Quantum.TwistPolyPrime
import AJTwist.Factor.TwFOnePrime
import AJTwist.Factor.TwFNegPrime
import AJTwist.Classical.TwCPolys

/-!
# The filling polynomials `𝒫_k` in the comparison ring (PpA, Section 7.6)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`, "The companion-abelian filling
factor"): "By Section 5, `𝒫_k` is reduced, distinct from `L - 1`, and defines a horizontal
curve in the generic chart."

The facts about `𝒫_k = twP k` (`k ≠ 0`) used to pass from generic points to divisibility, for
all signs of `k` at once:

* `ppa_prime_toComparison_twP`: `𝒫_k` is prime in `R = ℚ(M)[L, L⁻¹]`
  (`prime_toComparison_twistPoly` for `k ≥ 2`, `prime_toComparison_twistPoly_one`,
  `prime_toComparison_twistPolyNeg` for `k < 0`);
* `ppa_not_sub_one_dvd_twP`: `L - 1` does not divide `𝒫_k` in `R`
  (`not_toComparison_dvd_twistPoly_one`, `not_toComparison_dvd_twistPolyNeg`; for `k ≥ 2` by
  `eval_one_eq_zero_of_toComparison_X_sub_one_dvd` and `𝒫_k(1, 1) = 4^k`, an induction on the
  recurrence of `twistPoly`);
* `ppa_coeff_zero_twP_ne_zero`: the constant coefficient in `L` is not zero
  (`coeff_zero_twistPoly`, `coeff_zero_twistPolyNeg`);
* `ppa_evalPoint_twP_ne_zero`: `𝒫_k(2, -4) ≠ 0`, so no factor of `𝒫_k` is the line
  `L = -M²` (`B_m(M, -M²) = (M² (M⁴ - 1)²)^m` as in the private `rev_famB_ne_zero` of
  `AJHandoff.TorusKnot.PairKReverse`; `eval_neg_twistPolyNeg`);
* `ppa_natDegree_twP_pos`: positive degree in `L` (`natDegree_twistPoly`,
  `natDegree_twistPolyNeg`).

The same facts for the reverse in `L` are in `AJPaper.Filling.PpASubOne`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A nonzero integer is a positive natural number or the negative of one. -/
private theorem exists_natCast_or_neg_polyFacts (k : ℤ) (hk : k ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ (k = (m : ℤ) ∨ k = -(m : ℤ)) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact ⟨m, by omega, Or.inl rfl⟩
  · exact ⟨m, by omega, Or.inr rfl⟩

/-- The value of an integer polynomial at a point `(M, r(M))` of the graph of `r ∈ ℤ[M]`. -/
private theorem evalPoint_mapC_graph_polyFacts (P : ℤ[X][X]) (r : ℤ[X]) (M : ℂ) :
    evalPoint (mapC P) (M, (r.map (Int.castRingHom ℂ)).eval M) =
      ((P.eval r).map (Int.castRingHom ℂ)).eval M := by
  have h := Polynomial.hom_eval₂ P (RingHom.id ℤ[X])
    ((Polynomial.evalRingHom M).comp (Polynomial.mapRingHom (Int.castRingHom ℂ))) r
  rw [RingHom.comp_id] at h
  rw [evalPoint, mapC, Polynomial.eval₂_map]
  exact h.symm

/-- `𝒫_k` is prime in the comparison ring `ℚ(M)[L, L⁻¹]` for `k ≠ 0`. -/
theorem ppa_prime_toComparison_twP (k : ℤ) (hk : k ≠ 0) : Prime (toComparison (twP k)) := by
  obtain ⟨m, hm, rfl | rfl⟩ := exists_natCast_or_neg_polyFacts k hk
  · rw [twP_natCast]
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · obtain rfl : m = 1 := by omega
      exact prime_toComparison_twistPoly_one
    · exact prime_toComparison_twistPoly m h2
  · rw [twP_neg_natCast m hm]
    exact prime_toComparison_twistPolyNeg m hm

/-- `L - 1` does not divide `𝒫_k` in the comparison ring for `k ≠ 0`. -/
theorem ppa_not_sub_one_dvd_twP (k : ℤ) (hk : k ≠ 0) :
    ¬ toComparison (X - 1) ∣ toComparison (twP k) := by
  obtain ⟨m, hm, rfl | rfl⟩ := exists_natCast_or_neg_polyFacts k hk
  · rw [twP_natCast]
    intro h
    have h0 := eval_one_eq_zero_of_toComparison_X_sub_one_dvd h
    rw [eval_one_twistPoly hm] at h0
    have h1 := congrArg (Polynomial.eval 1) h0
    simp only [eval_neg, eval_mul, eval_pow, eval_add, eval_sub, eval_X, eval_C, eval_one,
      eval_zero, one_pow, mul_one, one_mul] at h1
    have h2 : ((1 : ℤ) + 1) ^ (2 * m) ≠ 0 := pow_ne_zero _ (by norm_num)
    apply h2
    linear_combination h1
  · rw [twP_neg_natCast m hm]
    exact (not_toComparison_dvd_twistPolyNeg m hm).1

/-- The constant coefficient of `𝒫_k` in `L` is not zero. -/
theorem ppa_coeff_zero_twP_ne_zero (k : ℤ) : (twP k).coeff 0 ≠ 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [twP_zero]
  obtain ⟨m, hm, rfl | rfl⟩ := exists_natCast_or_neg_polyFacts k hk
  · rw [twP_natCast, coeff_zero_twistPoly]
    exact pow_ne_zero _ X_ne_zero
  · rw [twP_neg_natCast m hm, coeff_zero_twistPolyNeg m hm]
    exact pow_ne_zero _ X_ne_zero

/-- `𝒫_k` does not vanish at `(M, L) = (2, -4)`, a point of the line `L = -M²`. -/
theorem ppa_evalPoint_twP_ne_zero (k : ℤ) : evalPoint (mapC (twP k)) (2, -4) ≠ 0 := by
  have hpt : ((-(X ^ 2) : ℤ[X]).map (Int.castRingHom ℂ)).eval 2 = -4 := by
    simp only [Polynomial.map_neg, Polynomial.map_pow, map_X, eval_neg, eval_pow, eval_X]
    norm_num
  rw [← hpt, evalPoint_mapC_graph_polyFacts]
  by_cases hk : k = 0
  · subst hk
    simp [twP_zero]
  obtain ⟨m, hm, rfl | rfl⟩ := exists_natCast_or_neg_polyFacts k hk
  · rw [twP_natCast, eval_neg_twistPoly]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
      map_X, eval_mul, eval_pow, eval_sub, eval_X, eval_one]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  · rw [twP_neg_natCast m hm, eval_neg_twistPolyNeg m hm]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
      map_X, eval_mul, eval_pow, eval_sub, eval_X, eval_one]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

/-- `𝒫_k` has positive degree in `L` for `k ≠ 0`. -/
theorem ppa_natDegree_twP_pos (k : ℤ) (hk : k ≠ 0) : 0 < (twP k).natDegree := by
  obtain ⟨m, hm, rfl | rfl⟩ := exists_natCast_or_neg_polyFacts k hk
  · rw [twP_natCast, natDegree_twistPoly]
    omega
  · rw [twP_neg_natCast m hm, natDegree_twistPolyNeg m hm]
    omega

end AJConjecture
