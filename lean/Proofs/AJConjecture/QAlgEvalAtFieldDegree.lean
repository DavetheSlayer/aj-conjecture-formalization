import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# The degree in `t` of a coefficient at large colours

For a nonzero `c = ∑_e c_e(t) M^e`, the degree in `t` of `c(t, t^(2n)) = ∑_e c_e(t) t^(2ne)` is
`deg c_d + 2nd` for all large `n`, where `d` is the degree of `c` in `M`: the top term dominates.
-/

open Polynomial

namespace AJConjecture

/-- At a natural colour, the value of a coefficient is the image of a polynomial in `t`. -/
private theorem evalAtField_natCast_eq_algebraMap (m : ℕ) (c : Coeff) :
    evalAtField (m : ℤ) c = algebraMap ℚ[X] (RatFunc ℚ)
      ((c.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).eval (X ^ (2 * m))) := by
  have hφ : (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) =
      Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [RatFunc.algebraMap_X]
  rw [eval_map, Polynomial.hom_eval₂, hφ, map_pow, RatFunc.algebraMap_X]
  simp only [evalAtField, coe_eval₂RingHom]
  congr 1

/-- The degree in `t` of `P(t, t ^ k)` when `k` exceeds the degrees in `t` of the lower
coefficients of `P`: the top term dominates. -/
private theorem natDegree_eval_X_pow_of_coeff_natDegree_lt {P : ℚ[X][X]} (hP : P ≠ 0) {k : ℕ}
    (hk : ∀ e < P.natDegree, (P.coeff e).natDegree < k) :
    P.eval (X ^ k) ≠ 0 ∧
      (P.eval (X ^ k)).natDegree = P.leadingCoeff.natDegree + k * P.natDegree := by
  have hlead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have htop : (P.leadingCoeff * (X ^ k) ^ P.natDegree).natDegree =
      P.leadingCoeff.natDegree + k * P.natDegree := by
    rw [← pow_mul, natDegree_mul_X_pow _ hlead]
  have htop0 : P.leadingCoeff * (X ^ k) ^ P.natDegree ≠ 0 :=
    mul_ne_zero hlead (pow_ne_zero _ (pow_ne_zero _ X_ne_zero))
  have hbot : ⊥ < (P.leadingCoeff * (X ^ k) ^ P.natDegree).degree :=
    bot_lt_iff_ne_bot.mpr (degree_eq_bot.not.mpr htop0)
  have hlow : (∑ e ∈ Finset.range P.natDegree, P.coeff e * (X ^ k) ^ e).degree <
      (P.leadingCoeff * (X ^ k) ^ P.natDegree).degree := by
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff hbot).mpr fun e he ↦ ?_)
    by_cases h0 : P.coeff e = 0
    · rw [h0, zero_mul, degree_zero]
      exact hbot
    · apply degree_lt_degree
      rw [htop, ← pow_mul, natDegree_mul_X_pow _ h0]
      have he' : e < P.natDegree := Finset.mem_range.mp he
      have h1 : (P.coeff e).natDegree < k := hk e he'
      have h2 : k * (e + 1) ≤ k * P.natDegree := Nat.mul_le_mul_left k he'
      rw [Nat.mul_succ] at h2
      omega
  have hdeg : (P.eval (X ^ k)).degree = (P.leadingCoeff * (X ^ k) ^ P.natDegree).degree := by
    rw [eval_eq_sum_range, Finset.sum_range_succ]
    exact degree_add_eq_right_of_degree_lt hlow
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [h, degree_zero] at hdeg
    exact hbot.ne hdeg
  · rw [← htop]
    exact natDegree_eq_of_degree_eq hdeg

/-- The degree in `t` of a nonzero coefficient evaluated at the colour `n` is an affine function
of `n` for all large `n`. -/
theorem exists_intDegree_evalAtField_eq {c : Coeff} (hc : c ≠ 0) :
    ∃ a b n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
      evalAtField n c ≠ 0 ∧ (evalAtField n c).intDegree = a * n + b := by
  have hP : c.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Polynomial.map_injective _ Int.cast_injective)).mpr hc
  set P : ℚ[X][X] := c.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) with hPdef
  refine ⟨2 * P.natDegree, P.leadingCoeff.natDegree,
    ((Finset.range P.natDegree).sup fun e ↦ (P.coeff e).natDegree : ℕ) + 1, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (by positivity) hn)
  have hk : ∀ e < P.natDegree, (P.coeff e).natDegree < 2 * m := by
    intro e he
    have hle : (P.coeff e).natDegree ≤
        (Finset.range P.natDegree).sup fun e ↦ (P.coeff e).natDegree :=
      Finset.le_sup (f := fun e ↦ (P.coeff e).natDegree) (Finset.mem_range.mpr he)
    omega
  obtain ⟨hne, hdeg⟩ := natDegree_eval_X_pow_of_coeff_natDegree_lt hP hk
  rw [evalAtField_natCast_eq_algebraMap, ← hPdef]
  refine ⟨(map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hne, ?_⟩
  rw [RatFunc.intDegree_polynomial, hdeg]
  push_cast
  ring

end AJConjecture
