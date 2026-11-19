import Mathlib
import AJPaper.Zheng.PpZP41Test
import AJPaper.Zheng.PpZP41Nonres

/-!
# The test function on the exponents `E(m)` (Unit PpZ, node `PpZ_P41TestEval`)

Source: Zheng, (4.21)–(4.22): the set `X = {j : Nj ≡ ∓2 mod α, j ≡ 0 mod β}`.

`ppZTest_apply_exp`: if every shift `k ℓ` (`ℓ ∣ a`, `ℓ ∤ N`) satisfies `ℓ ∤ y² + N k_ℓ` for all `y`,
then for `j = 2m + 1`

  `Φ(E(m)) = ζ_a^{a_c E(m)}` if `β ∣ j` and `α ∣ Nj + 2`, and `Φ(E(m)) = 0` otherwise.

Route. With `E = E(m) = -j(Nj + 4)`:
* `β ∣ E ↔ β ∣ j` (`ppZBeta_dvd_exp_iff`);
* `N E - 4 = -(Nj + 2)²`, so the first indicator of the factor `ℓ` is `[ℓ^e ∣ (Nj+2)²]`;
* `N(E - k_ℓ ℓ^{e-1}) - 4 = -((Nj+2)² + N k_ℓ ℓ^{e-1})`, never divisible by `ℓ^e`
  (`ppZ_not_pow_dvd_sq_add`, `e ≥ 1` on `primeFactors`), so the second indicator is `0`;
* the product of the indicators `[ℓ^e ∣ (Nj+2)²]` over `ℓ ∤ N` is `[α ∣ Nj + 2]`
  (`ppZAlpha_dvd_iff`, `Finset.prod_ite_zero` / `Finset.prod_eq_one`, `Finset.prod_eq_zero`).

Checked numerically: equality holds exactly for 32 values of `a ≤ 1125` (`p41.py`).
-/

noncomputable section

namespace AJConjecture

set_option linter.unusedVariables false in
/-- `Φ(E(m)) = [β ∣ j, α ∣ Nj + 2] · ζ_a^{a_c E(m)}`, `j = 2m + 1`. -/
theorem ppZTest_apply_exp (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) (k : ℕ → ℤ)
    (hk : ∀ ℓ ∈ a.primeFactors, ¬ (ℓ : ℤ) ∣ N → ∀ y : ℤ, ¬ (ℓ : ℤ) ∣ y ^ 2 + N * k ℓ) (m : ℕ) :
    ppZTest a N k (ppZExp N m) =
      if ((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1 ∧
          ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2 then
        ppZRoot a ((ppZPartC a N : ℤ) * ppZExp N m)
      else 0 := by
  have hE1 : N * ppZExp N m - 4 = -(N * (2 * (m : ℤ) + 1) + 2) ^ 2 := by
    rw [ppZExp]
    ring
  have hE2 : ∀ ℓ : ℕ, N * (ppZExp N m - k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) - 4 =
      -((N * (2 * (m : ℤ) + 1) + 2) ^ 2 + N * k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) := by
    intro ℓ
    rw [ppZExp]
    ring
  have hsecond : ∀ ℓ ∈ a.primeFactors, ¬ (ℓ : ℤ) ∣ N → ¬ ((ℓ : ℤ) ^ a.factorization ℓ ∣
      (N * (2 * (m : ℤ) + 1) + 2) ^ 2 + N * k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) := by
    intro ℓ hℓ hℓN
    obtain ⟨hp, hdvd, ha0⟩ := Nat.mem_primeFactors.mp hℓ
    exact ppZ_not_pow_dvd_sq_add hp (hp.factorization_pos_of_dvd ha0 hdvd) (hk ℓ hℓ hℓN) _
  have hprod : ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N),
      ((if (ℓ : ℤ) ^ a.factorization ℓ ∣ N * ppZExp N m - 4 then (1 : ℂ) else 0) -
        (if (ℓ : ℤ) ^ a.factorization ℓ ∣
            N * (ppZExp N m - k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) - 4 then (1 : ℂ) else 0)) =
      if ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2 then 1 else 0 := by
    simp only [hE1, hE2, dvd_neg, ppZAlpha_dvd_iff]
    split_ifs with h
    · refine Finset.prod_eq_one fun ℓ hℓ ↦ ?_
      rw [Finset.mem_filter] at hℓ
      rw [ite_eq_left (h ℓ hℓ.1 hℓ.2), ite_eq_right (hsecond ℓ hℓ.1 hℓ.2), sub_zero]
    · push Not at h
      obtain ⟨ℓ, hℓ, hℓN, hnd⟩ := h
      refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hℓ, hℓN⟩) ?_
      rw [ite_eq_right hnd, ite_eq_right (hsecond ℓ hℓ hℓN), sub_zero]
  rw [ppZTest, hprod]
  simp only [ppZBeta_dvd_exp_iff a hodd]
  by_cases h1 : ((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1
  · by_cases h2 : ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2
    · simp only [h1, h2, and_self, ↓reduceIte, mul_one]
    · simp only [h1, h2, and_false, ↓reduceIte, mul_zero]
  · simp only [h1, false_and, ↓reduceIte, zero_mul]

end AJConjecture
