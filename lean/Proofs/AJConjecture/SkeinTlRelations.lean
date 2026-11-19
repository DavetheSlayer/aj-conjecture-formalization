import Mathlib
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinPlaceComm
import AJConjecture.SkeinTlGenPlace
import AJConjecture.SkeinZigzag

/-!
# The Temperley–Lieb relations

`e_i² = δ e_i`, `e_i e_{i±1} e_i = e_i`, and `e_i e_j = e_j e_i` for `|i - j| ≥ 2`. With
`e_i = capAt * cupAt` they follow from the loop value, the zig-zag identities and the interchange
law; alternatively they are finite matrix identities in dimension `4` and `8` transported by
the placement.
-/

namespace AJConjecture

/-- `e_i² = δ e_i` with `δ = -t² - t⁻²`. -/
theorem tlGenF_mul_self (m i : ℕ) :
    tlGenF m i * tlGenF m i =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • tlGenF m i := by
  by_cases h : i + 2 ≤ m
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    have hi : i ≤ n := by omega
    rw [← capAt_mul_cupAt n i hi, Matrix.mul_assoc, ← Matrix.mul_assoc (cupAt n i),
      cupAt_mul_capAt n i hi, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  · rw [tlGenF_eq_zero m i (by omega), mul_zero, smul_zero]

/-- `e_i e_{i+1} e_i = e_i` when the three factors exist. -/
theorem tlGenF_mul_succ_mul (m i : ℕ) (h : i + 2 < m) :
    tlGenF m i * tlGenF m (i + 1) * tlGenF m i = tlGenF m i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hi : i < n := by omega
  rw [← capAt_mul_cupAt n i (by omega), ← capAt_mul_cupAt n (i + 1) (by omega)]
  calc capAt n i * cupAt n i * (capAt n (i + 1) * cupAt n (i + 1)) * (capAt n i * cupAt n i)
      = capAt n i * (cupAt n i * capAt n (i + 1)) * (cupAt n (i + 1) * capAt n i) *
          cupAt n i := by
        simp only [Matrix.mul_assoc]
    _ = capAt n i * cupAt n i := by
        rw [cupAt_mul_capAt_succ n i hi, cupAt_succ_mul_capAt n i hi, Matrix.mul_one,
          Matrix.mul_one]

/-- `e_{i+1} e_i e_{i+1} = e_{i+1}`. -/
theorem tlGenF_succ_mul_mul (m i : ℕ) :
    tlGenF m (i + 1) * tlGenF m i * tlGenF m (i + 1) = tlGenF m (i + 1) := by
  by_cases h : i + 2 < m
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    have hi : i < n := by omega
    rw [← capAt_mul_cupAt n i (by omega), ← capAt_mul_cupAt n (i + 1) (by omega)]
    calc capAt n (i + 1) * cupAt n (i + 1) * (capAt n i * cupAt n i) *
          (capAt n (i + 1) * cupAt n (i + 1))
        = capAt n (i + 1) * (cupAt n (i + 1) * capAt n i) * (cupAt n i * capAt n (i + 1)) *
            cupAt n (i + 1) := by
          simp only [Matrix.mul_assoc]
      _ = capAt n (i + 1) * cupAt n (i + 1) := by
          rw [cupAt_mul_capAt_succ n i hi, cupAt_succ_mul_capAt n i hi, Matrix.mul_one,
            Matrix.mul_one]
  · rw [tlGenF_eq_zero m (i + 1) (by omega), mul_zero]

/-- Generators on disjoint pairs of factors commute. -/
theorem tlGenF_commute (m i j : ℕ) (h : i + 1 < j) : Commute (tlGenF m i) (tlGenF m j) := by
  by_cases hj : j + 2 ≤ m
  · have key := skPlace_mul_skPlace_comm m m m m i j (tlGenF 2 0) (tlGenF 2 0) (by omega) hj
      rfl rfl rfl
    rw [Nat.add_sub_cancel] at key
    rw [Commute, SemiconjBy, tlGenF_eq_skPlace m i, tlGenF_eq_skPlace m j]
    exact key
  · rw [tlGenF_eq_zero m j (by omega)]
    exact Commute.zero_right _

end AJConjecture
