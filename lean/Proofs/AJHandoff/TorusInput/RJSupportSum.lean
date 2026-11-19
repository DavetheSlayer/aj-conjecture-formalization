import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJHandoff.TorusInput.RJEmbed

/-!
# Sums over the support of the candidate traces (node RA5.iv.2)

For even `b = 2n` and `r ≥ 2`, the map `i ↦ |2ri+1| - 1` is injective on `[-n, n]` with values in
the spectrum, so a sum over the spectrum weighted by `rjCycleValue` is a sum over `i ∈ [-n, n]`
(for any ring endomorphism `φ` of `ℚ(t)`, to be used with `φ = id` and `φ = rjEmbed r`); and on
the support the `r`-th root `ν_N` is the image of `t^(4ri²+4i)/θ_b`.

Route. Unfold `rjCycleValue`, exchange the sums (`Finset.sum_comm`), and use
`Finset.sum_ite_eq` once the injectivity (`|2ri+1| = |2ri'+1|` forces `i = i'` since
`r(i+i') = -1` is impossible for `r ≥ 2`) and the membership (`|2ri+1| - 1 ≤ 2rn = br`, even) are
shown. The second statement: `N(N+2) = (2ri+1)² - 1 = r(4ri²+4i)` and `rjEmbed r X = X^r`
(`RatFunc.map_X`-type lemmas for `RatFunc.mapRingHom`, `Polynomial.expand_X`). Estimate
100–150 lines.
-/

noncomputable section

namespace AJConjecture

/-- The colour `|2ri+1| - 1` of `i ∈ [-n, n]` lies in the spectrum (`b = 2n`, `r ≥ 1`). -/
private theorem rj_natAbs_sub_one_mem_spec (b r : ℕ) (hb : Even b) (hr : 1 ≤ r) (i : ℤ)
    (hi : i ∈ Finset.Icc (-((b / 2 : ℕ) : ℤ)) ((b / 2 : ℕ) : ℤ)) :
    (2 * (r : ℤ) * i + 1).natAbs - 1 ∈ rjSpec b r := by
  obtain ⟨n, rfl⟩ := hb
  rw [Finset.mem_Icc] at hi
  have hn : (n + n) / 2 = n := by omega
  rw [hn] at hi
  have hbr : (n + n) * r = 2 * (n * r) := by ring
  have hbr2 : (n + n) * r / 2 = n * r := by omega
  unfold rjSpec
  rw [Finset.mem_image, hbr2, hbr]
  have hP : ((n * r : ℕ) : ℤ) = (r : ℤ) * n := by push_cast; ring
  have h1 : (r : ℤ) * i ≤ r * n := mul_le_mul_of_nonneg_left hi.2 (by positivity)
  have h2 : -((r : ℤ) * n) ≤ r * i := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hi.1 (by positivity)
  rw [mul_assoc]
  rcases le_or_gt 0 i with h0 | h0
  · have h3 : 0 ≤ (r : ℤ) * i := mul_nonneg (by positivity) h0
    refine ⟨((r : ℤ) * n - r * i).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  · have h3 : (r : ℤ) * i ≤ r * (-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    refine ⟨((r : ℤ) * n + r * i + 1).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega

/-- A sum over the spectrum weighted by the candidate traces is a sum over `[-n, n]`. -/
theorem rj_sum_cycleValue_mul (b r : ℕ) (hb : Even b) (hr : 2 ≤ r)
    (φ : RatFunc ℚ →+* RatFunc ℚ) (g : ℕ → RatFunc ℚ) :
    ∑ N ∈ rjSpec b r, φ (rjCycleValue b r N) * g N =
      ∑ i ∈ Finset.Icc (-((b / 2 : ℕ) : ℤ)) ((b / 2 : ℕ) : ℤ),
        φ (RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) * quantumInt (2 * (r : ℤ) * i + 1) /
            kinkScalar b) * g ((2 * (r : ℤ) * i + 1).natAbs - 1) := by
  simp only [rjCycleValue, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hpos : (2 * (r : ℤ) * i + 1).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, mul_assoc]; omega
  trans ∑ N ∈ rjSpec b r, if (2 * (r : ℤ) * i + 1).natAbs - 1 = N then
      φ (RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) * quantumInt (2 * (r : ℤ) * i + 1) /
        kinkScalar b) * g N else 0
  · refine Finset.sum_congr rfl fun N _ ↦ ?_
    by_cases hN : (2 * (r : ℤ) * i + 1).natAbs = N + 1
    · rw [ite_eq_left hN, ite_eq_left (by omega)]
    · rw [ite_eq_right hN, ite_eq_right (by omega), map_zero, zero_mul]
  · rw [Finset.sum_ite_eq, ite_eq_left (rj_natAbs_sub_one_mem_spec b r hb (by omega) i hi)]

/-- On the support, the `r`-th root `ν_N` is the image of `t^(4ri²+4i)/θ_b`. -/
theorem rj_nu_support (b r : ℕ) (hr : 1 ≤ r) (i : ℤ) :
    rjNu b r ((2 * (r : ℤ) * i + 1).natAbs - 1) =
      rjEmbed r (RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) / kinkScalar b) := by
  rw [rjNu, map_div₀, rjEmbed_zpow_X r hr, ← zpow_natCast]
  congr 2
  have hpos : (2 * (r : ℤ) * i + 1).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, mul_assoc]; omega
  have h1 : (((2 * (r : ℤ) * i + 1).natAbs - 1 : ℕ) : ℤ) =
      ((2 * (r : ℤ) * i + 1).natAbs : ℤ) - 1 := by omega
  have h2 : (((2 * (r : ℤ) * i + 1).natAbs : ℕ) : ℤ) ^ 2 = (2 * (r : ℤ) * i + 1) ^ 2 :=
    Int.natAbs_sq _
  push_cast
  rw [h1]
  linear_combination h2

end AJConjecture
