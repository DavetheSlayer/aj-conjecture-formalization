import Mathlib
import AJPaper.Zheng.PpZNormLocalStep

/-!
# The local expansion of `log S_{n,i}` (Unit PpZ, node `PpZ_NormLocal`)

Source: Zheng, (3.31).

`ppZ_log_normFactor_local`: on the box `|n - N/2| ≤ r`, `|i - N/4| ≤ r`, `1 ≤ r ≤ N/40`,
`|log S_{n,i} - log S₀ - V(n, i)| ≤ 5000 r (r² + N)/N²`.
(With `r = N^δ + 1` the right side is `O(N^{3δ-2})` because `δ > 1/2`.)

Route. Let `F(n, i) = log S_{n,i} - V(n, i)`. By the step lemmas `|F(n+1,i) - F(n,i)|` and
`|F(n,i+1) - F(n,i)|` are `≤ η = 1000(r² + N)/N²` whenever `(n, i)` is in the box. Go from the
centre `(n₀, i₀) = (⌊N/2⌋, ⌊N/4⌋)` (which is in the box: `|n₀ - N/2| ≤ 1/2`, `|i₀ - N/4| ≤ 3/4`)
first in `n` at `i = i₀`, then in `i`: `|F(n,i) - F(n₀,i₀)| ≤ η(|n - n₀| + |i - i₀|) ≤ η(2r + 2)`
(four inductions, or one lemma on monotone lattice paths in a box; when stepping down use the
step lemma at the lower point). Finally `|V(n₀, i₀)| ≤ (π/N)(1/4 + 3/4 + 9/8) ≤ 7/N ≤ 7r(r²+N)/N²`.
Measured: `|…|/N^{3δ-2} ≤ 17` for `r = N^δ`, `N ≤ 30 000` (`l33loc.py`).
-/

noncomputable section

namespace AJConjecture

/-- A sequence with steps `≤ η` on `[a, b)` moves by at most `η (b - a)`. -/
private theorem abs_sub_le_of_steps_up_normLocal {f : ℕ → ℝ} {η : ℝ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → |f (k + 1) - f k| ≤ η) : |f b - f a| ≤ η * ((b : ℝ) - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h1 := ih fun k hk1 hk2 ↦ h k hk1 (by omega)
    have h2 := h m hm (by omega)
    have h3 : |f (m + 1) - f a| ≤ |f (m + 1) - f m| + |f m - f a| := by
      have := abs_add_le (f (m + 1) - f m) (f m - f a)
      rwa [sub_add_sub_cancel] at this
    push_cast
    linarith

/-- A sequence with steps `≤ η` between `a` and `b` moves by at most `η |b - a|`. -/
private theorem abs_sub_le_of_steps_normLocal {f : ℕ → ℝ} {η : ℝ} (a b : ℕ)
    (h : ∀ k, min a b ≤ k → k < max a b → |f (k + 1) - f k| ≤ η) :
    |f b - f a| ≤ η * |(b : ℝ) - a| := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at h
    have hc : (a : ℝ) ≤ b := by exact_mod_cast hab
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b : ℝ) - a)]
    exact abs_sub_le_of_steps_up_normLocal hab h
  · rw [min_eq_right hab, max_eq_left hab] at h
    have hc : (b : ℝ) ≤ a := by exact_mod_cast hab
    rw [abs_sub_comm, abs_sub_comm (b : ℝ), abs_of_nonneg (by linarith : (0 : ℝ) ≤ (a : ℝ) - b)]
    exact abs_sub_le_of_steps_up_normLocal hab h

/-- The potential at the centre `(⌊N/2⌋, ⌊N/4⌋)` is at most `7/N`. -/
private theorem abs_ppZPot_centre_le_normLocal {N : ℕ} (hN : 0 < N) :
    |ppZPot N ((N / 2 : ℕ) : ℝ) ((N / 4 : ℕ) : ℝ)| ≤ 7 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    have : (2 : ℝ) * (N / 2 : ℕ) ≤ N := by exact_mod_cast (by omega : 2 * (N / 2) ≤ N)
    linarith
  have h2 : (N : ℝ) / 2 - 1 / 2 ≤ ((N / 2 : ℕ) : ℝ) := by
    have : (N : ℝ) ≤ 2 * (N / 2 : ℕ) + 1 := by exact_mod_cast (by omega : N ≤ 2 * (N / 2) + 1)
    linarith
  have h3 : ((N / 4 : ℕ) : ℝ) ≤ (N : ℝ) / 4 := by
    have : (4 : ℝ) * (N / 4 : ℕ) ≤ N := by exact_mod_cast (by omega : 4 * (N / 4) ≤ N)
    linarith
  have h4 : (N : ℝ) / 4 - 3 / 4 ≤ ((N / 4 : ℕ) : ℝ) := by
    have : (N : ℝ) ≤ 4 * (N / 4 : ℕ) + 3 := by exact_mod_cast (by omega : N ≤ 4 * (N / 4) + 3)
    linarith
  unfold ppZPot
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < Real.pi / N), div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hNr]
  have hq : |(((N / 2 : ℕ) : ℝ) - N / 2) ^ 2 +
      2 * (((N / 2 : ℕ) : ℝ) - N / 2) * (((N / 4 : ℕ) : ℝ) - N / 4) +
      2 * (((N / 4 : ℕ) : ℝ) - N / 4) ^ 2| ≤ 17 / 8 := by
    rw [abs_le]
    constructor <;> nlinarith
  exact (mul_le_mul Real.pi_lt_d2.le hq (abs_nonneg _) (by norm_num)).trans (by norm_num)

/-- Local expansion: `log S_{n,i} = log S₀ + V(n,i) + O(r(r² + N)/N²)` on the box of radius `r`. -/
theorem ppZ_log_normFactor_local {N n i : ℕ} {r : ℝ} (hr1 : 1 ≤ r) (hr : 40 * r ≤ N)
    (hn : |(n : ℝ) - N / 2| ≤ r) (hi : |(i : ℝ) - N / 4| ≤ r) :
    |Real.log (geoNormFactor N n i) - Real.log (geoNormFactor0 N) - ppZPot N n i| ≤
      5000 * r * (r ^ 2 + N) / (N : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hN
  obtain ⟨hn1, hn2⟩ := abs_le.mp hn
  obtain ⟨hi1, hi2⟩ := abs_le.mp hi
  have h1 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    have : (2 : ℝ) * (N / 2 : ℕ) ≤ N := by exact_mod_cast (by omega : 2 * (N / 2) ≤ N)
    linarith
  have h2 : (N : ℝ) / 2 - 1 / 2 ≤ ((N / 2 : ℕ) : ℝ) := by
    have : (N : ℝ) ≤ 2 * (N / 2 : ℕ) + 1 := by exact_mod_cast (by omega : N ≤ 2 * (N / 2) + 1)
    linarith
  have h3 : ((N / 4 : ℕ) : ℝ) ≤ (N : ℝ) / 4 := by
    have : (4 : ℝ) * (N / 4 : ℕ) ≤ N := by exact_mod_cast (by omega : 4 * (N / 4) ≤ N)
    linarith
  have h4 : (N : ℝ) / 4 - 3 / 4 ≤ ((N / 4 : ℕ) : ℝ) := by
    have : (N : ℝ) ≤ 4 * (N / 4 : ℕ) + 3 := by exact_mod_cast (by omega : N ≤ 4 * (N / 4) + 3)
    linarith
  have hi0 : |((N / 4 : ℕ) : ℝ) - N / 4| ≤ r := by
    rw [abs_le]; constructor <;> linarith
  have hη : 0 ≤ 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2 := by positivity
  -- first in `n` at `i = ⌊N/4⌋`
  have s1 := abs_sub_le_of_steps_normLocal (η := 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2)
    (f := fun k ↦ Real.log (geoNormFactor N k (N / 4)) - ppZPot N k ((N / 4 : ℕ) : ℝ))
    (N / 2) n (by
      intro k hk1 hk2
      have hk1' : (((min (N / 2) n : ℕ)) : ℝ) ≤ k := by exact_mod_cast hk1
      have hk2' : (k : ℝ) + 1 ≤ ((max (N / 2) n : ℕ) : ℝ) := by exact_mod_cast hk2
      rw [Nat.cast_min] at hk1'
      rw [Nat.cast_max] at hk2'
      have hk : |(k : ℝ) - N / 2| ≤ r := by
        rw [abs_le]
        rcases min_le_iff.mp hk1' with h | h <;> rcases le_max_iff.mp hk2' with h' | h' <;>
          constructor <;> linarith
      have := ppZ_log_normFactor_step_left hr1 hr hk hi0
      push_cast
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2])
  -- then in `i`
  have s2 := abs_sub_le_of_steps_normLocal (η := 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2)
    (f := fun k ↦ Real.log (geoNormFactor N n k) - ppZPot N n k)
    (N / 4) i (by
      intro k hk1 hk2
      have hk1' : (((min (N / 4) i : ℕ)) : ℝ) ≤ k := by exact_mod_cast hk1
      have hk2' : (k : ℝ) + 1 ≤ ((max (N / 4) i : ℕ) : ℝ) := by exact_mod_cast hk2
      rw [Nat.cast_min] at hk1'
      rw [Nat.cast_max] at hk2'
      have hk : |(k : ℝ) - N / 4| ≤ r := by
        rw [abs_le]
        rcases min_le_iff.mp hk1' with h | h <;> rcases le_max_iff.mp hk2' with h' | h' <;>
          constructor <;> linarith
      have := ppZ_log_normFactor_step_right hr1 hr hn hk
      push_cast
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2])
  have s3 := abs_ppZPot_centre_le_normLocal hNpos
  have d1 : |(n : ℝ) - ((N / 2 : ℕ) : ℝ)| ≤ 2 * r := by
    rw [abs_le]; constructor <;> linarith
  have d2 : |(i : ℝ) - ((N / 4 : ℕ) : ℝ)| ≤ 2 * r := by
    rw [abs_le]; constructor <;> linarith
  have t1 := (s1.trans (mul_le_mul_of_nonneg_left d1 hη))
  have t2 := (s2.trans (mul_le_mul_of_nonneg_left d2 hη))
  have t3 : 7 / (N : ℝ) ≤ 7 * r * (r ^ 2 + N) / (N : ℝ) ^ 2 := by
    have h5 : (N : ℝ) ≤ r * (r ^ 2 + N) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hr1) hN.le, pow_pos (by linarith : 0 < r) 3]
    rw [div_le_div_iff₀ hN (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h5 hN.le]
  have e1 : 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2 * (2 * r) =
      2000 * (r * (r ^ 2 + N) / (N : ℝ) ^ 2) := by ring
  have e2 : 7 * r * (r ^ 2 + N) / (N : ℝ) ^ 2 = 7 * (r * (r ^ 2 + N) / (N : ℝ) ^ 2) := by ring
  have e3 : 5000 * r * (r ^ 2 + N) / (N : ℝ) ^ 2 =
      5000 * (r * (r ^ 2 + N) / (N : ℝ) ^ 2) := by ring
  have hpos : 0 ≤ r * (r ^ 2 + N) / (N : ℝ) ^ 2 := by positivity
  rw [e1] at t1 t2
  rw [e2] at t3
  rw [e3]
  simp only [geoNormFactor0] at *
  rw [abs_le] at t1 t2 s3 ⊢
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, s3.1, s3.2]

end AJConjecture
