import Mathlib
import AJPaper.Zheng.PpZP41Reduce
import AJPaper.Zheng.PpZP41TestSum
import AJPaper.Zheng.PpZP41TestEval
import AJPaper.Zheng.PpZP41Sum

/-!
# Zheng's Proposition 4.1 for `(p, q) = (a, 2)` (Unit PpZ, node `PpZ_Prop41`)

Source: H. Zheng, arXiv:math/0508138v4, Proposition 4.1: `A⁺_{a,2}(N, 1) ≠ 0` for every integer
`N`, for odd `a ≥ 3`. (For `a = 1` the sum is `0`: the hypothesis `3 ≤ a` is necessary.)

Route. Suppose `geoZhengA a N 1 = 0`. Choose `u` with `8u ≡ 1 (mod a)` (`a` odd:
`Int.exists_mul_emod_eq_one_of_coprime` / `Int.gcd_eq_gcd_ab`); `u` is coprime to `a`. By
`ppZ_zhengA_eq_conjSum` and nonvanishing of the unit factors (`Complex.exp_ne_zero`, `a ≠ 0`),
`ppZConjSum a N u = 0`. Choose shifts `k ℓ` by `ppZ_exists_nonresidue_shift` (every prime of the
odd number `a` is `≠ 2`; `Classical.choice` over `ℓ`, any value where the hypothesis fails).
Then `ppZ_testSum_eq_zero` with `Φ = ppZTest a N k` (`ppZTest_unitSupported`) and
`ppZTest_apply_exp` (push the weight into the `if`) contradict `ppZ_restricted_sum_ne_zero`.
-/

noncomputable section

namespace AJConjecture

/-- **Zheng, Proposition 4.1** for the companion `T(a, 2)`, `a ≥ 3` odd. -/
theorem zhengProp41_holds (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) : ZhengProp41 a := by
  intro N hA
  have ha1 : 1 ≤ a := by omega
  have hcop8 : IsCoprime (8 : ℤ) (a : ℤ) := by
    have h : Nat.Coprime (2 ^ 3) a := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd)
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr h
  obtain ⟨u, v, huv⟩ := hcop8
  have hu : 8 * u ≡ 1 [ZMOD (a : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨v, by linear_combination -huv⟩
  have hucop : IsCoprime u (a : ℤ) := ⟨8, v, by linear_combination huv⟩
  have hR : ppZConjSum a N u = 0 := by
    have h := ppZ_zhengA_eq_conjSum a hodd N u hu
    rw [hA] at h
    refine (mul_eq_zero.mp h.symm).resolve_left ?_
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero two_ne_zero
      (Nat.cast_ne_zero.mpr (by omega)))) Complex.I_ne_zero) (Complex.exp_ne_zero _))
      (Complex.exp_ne_zero _)
  have hex : ∀ ℓ : ℕ, ∃ k : ℤ, ℓ ∈ a.primeFactors → ¬ (ℓ : ℤ) ∣ N →
      ∀ y : ℤ, ¬ (ℓ : ℤ) ∣ y ^ 2 + N * k := by
    intro ℓ
    by_cases h : ℓ ∈ a.primeFactors ∧ ¬ (ℓ : ℤ) ∣ N
    · have h2 : ℓ ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
          (Nat.dvd_of_mem_primeFactors h.1))
      obtain ⟨k, hk⟩ := ppZ_exists_nonresidue_shift (Nat.prime_of_mem_primeFactors h.1) h2 h.2
      exact ⟨k, fun _ _ ↦ hk⟩
    · exact ⟨0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ h⟩
  choose k hk using hex
  have htest := ppZ_testSum_eq_zero ha1 N hucop hR (ppZTest a N k)
    (ppZTest_unitSupported a ha1 N k)
  refine ppZ_restricted_sum_ne_zero a ha hodd N (Eq.trans ?_ htest)
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [ppZTest_apply_exp a ha1 hodd N k hk m, mul_ite, mul_zero]

end AJConjecture
