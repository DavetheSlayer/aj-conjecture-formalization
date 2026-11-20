import Mathlib
import AJPaper.Zheng.PpZRidgeBound

/-!
# The global Gaussian bound for `S_{n,i}` (Unit PpZ, node `PpZ_NormGlobal`)

`S_{n,i} ≤ C · exp(-(c/N) d²) · S₀` on the whole triangle `n + i < N`, where
`d = |n - N/2| + |i - N/4|`, with absolute constants `c > 0`, `C`. This is Zheng's Lemma 3.2 in a
form that does not mention `δ`; it also covers the part of the triangle where Zheng's function
`f` is not concave.

Route. Combine `ppZ_normFactor_le_ridge` (decay in `i` at rate `tan(nπ/2N)`) and `ppZ_ridge_le`
(decay of the ridge). Note `|i*(n) - N/4| ≤ |n - N/2|/2 + 1`.
* If `|n - N/2| ≥ d/4`: the ridge bound alone gives `exp(-(c/N) d²/16)`; the factor from the
  `i`-direction is `≤ 1`, because `D = |i - i*(n)|` is a natural number (`D² - D ≥ 0`) and
  `tan(nπ/2N) ≥ 0` for `n < N`.
* If `|n - N/2| < d/4`: then `d ≤ 5N/4` gives `n > 3N/16`, so `tan(nπ/2N) ≥ tan(3π/32) > 3/10`,
  and `D = |i - i*(n)| ≥ |i - N/4| - |n - N/2|/2 - 1 > 5d/8 - 1`; use `D² - D ≥ D²/2 - 1/2`.

Numerically `C = 2`, `c = 0.2` work for all `n + i < N ≤ 520` (`ridge.py`).
-/

noncomputable section

namespace AJConjecture

/-- The ridge value is positive for `n < N`. -/
private theorem ridge_pos_normGlobal {N n : ℕ} (hn : n < N) : 0 < ppZRidge N n := by
  refine ppZ_normFactor_pos ?_
  unfold ppZRidgeIdx
  omega

/-- `|i*(n) - N/4| ≤ |n - N/2|/2 + 1/2`. -/
private theorem ridgeIdx_sub_quarter_normGlobal {N n : ℕ} (hn : n ≤ N) :
    |(ppZRidgeIdx N n : ℝ) - N / 4| ≤ |(n : ℝ) - N / 2| / 2 + 1 / 2 := by
  have hb : 2 * ppZRidgeIdx N n + n ≤ N ∧ N ≤ 2 * ppZRidgeIdx N n + 1 + n := by
    unfold ppZRidgeIdx
    omega
  have h1 : 2 * (ppZRidgeIdx N n : ℝ) + n ≤ N := by exact_mod_cast hb.1
  have h2 : (N : ℝ) ≤ 2 * (ppZRidgeIdx N n : ℝ) + 1 + n := by exact_mod_cast hb.2
  have h3 := le_abs_self ((n : ℝ) - N / 2)
  have h4 := neg_abs_le ((n : ℝ) - N / 2)
  rw [abs_le]
  constructor <;> linarith

/-- `0 ≤ D² - |D|` for a difference `D` of two natural numbers. -/
private theorem natCast_sub_sq_sub_abs_nonneg_normGlobal (i j : ℕ) :
    0 ≤ ((i : ℝ) - j) ^ 2 - |(i : ℝ) - j| := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have h1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  · subst h
    simp
  · have h1 : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    nlinarith

/-- The exponent estimate off the ridge: if the rate `P` is at least `27/(16N)` and
`y ≥ 5d/8 - 1/2`, then `P (y² - y) ≥ (c/N) d² - 2` for `c ≤ 1/5`. -/
private theorem exponent_bound_normGlobal {Nr c P d y : ℝ} (hN : 1 ≤ Nr) (hc5 : c ≤ 1 / 5)
    (hP : 27 / 16 / Nr ≤ P) (hy : 0 ≤ y) (hyy : 0 ≤ y ^ 2 - y) (hd : 5 * d / 8 - 1 / 2 ≤ y)
    (hd0 : 0 ≤ d) : c / Nr * d ^ 2 - 2 ≤ P * (y ^ 2 - y) := by
  have h5 : 25 * d ^ 2 / 192 - 3 / 4 ≤ y ^ 2 - y := by
    nlinarith [sq_nonneg (y - 1), mul_nonneg hd0 hd0]
  have hX : 0 ≤ d ^ 2 / Nr := by positivity
  have hinv : 1 / Nr ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hN
  have hinv0 : 0 ≤ 1 / Nr := by positivity
  have e1 : c / Nr * d ^ 2 = c * (d ^ 2 / Nr) := by ring
  have e2 : 27 / 16 / Nr * (25 * d ^ 2 / 192 - 3 / 4) =
      675 / 3072 * (d ^ 2 / Nr) - 81 / 64 * (1 / Nr) := by ring
  have h6 : 27 / 16 / Nr * (25 * d ^ 2 / 192 - 3 / 4) ≤ 27 / 16 / Nr * (y ^ 2 - y) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h7 : 27 / 16 / Nr * (y ^ 2 - y) ≤ P * (y ^ 2 - y) := mul_le_mul_of_nonneg_right hP hyy
  have h8 : c * (d ^ 2 / Nr) ≤ 1 / 5 * (d ^ 2 / Nr) := mul_le_mul_of_nonneg_right hc5 hX
  rw [e1]
  rw [e2] at h6
  linarith

/-- The rate in the `i`-direction is at least `27/(16N)` when `3N ≤ 16n`. -/
private theorem rate_lower_bound_normGlobal {N n : ℕ} (hN : 1 ≤ N) (hn : n < N)
    (h16 : (3 : ℝ) * N ≤ 16 * n) :
    27 / 16 / (N : ℝ) ≤ 2 * Real.pi / N * Real.tan (n * Real.pi / (2 * N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnr : (n : ℝ) < N := by exact_mod_cast hn
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hq : 3 / 16 ≤ (n : ℝ) / N := by
    rw [le_div_iff₀ hNr]
    linarith
  have harg : (n : ℝ) * Real.pi / (2 * N) = (n : ℝ) / N * (Real.pi / 2) := by ring
  have hq1 : (n : ℝ) / N < 1 := by
    rw [div_lt_one hNr]
    exact hnr
  have htan : (n : ℝ) / N * (Real.pi / 2) ≤ Real.tan (n * Real.pi / (2 * N)) := by
    rw [harg]
    exact Real.le_tan (by positivity) (by nlinarith)
  have h1 : 27 / 16 ≤ 2 * Real.pi * Real.tan (n * Real.pi / (2 * N)) := by
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ Real.pi * Real.pi)]
  have e : 2 * Real.pi / N * Real.tan (n * Real.pi / (2 * N)) =
      2 * Real.pi * Real.tan (n * Real.pi / (2 * N)) / N := by ring
  rw [e]
  exact div_le_div_of_nonneg_right h1 hNr.le

/-- The global bound for one triple `(N, n, i)`, given the ridge bound at `(N, n)`. -/
private theorem gaussian_bound_core_normGlobal {c₁ C₁ c : ℝ} (hc₁ : 0 ≤ c₁)
    (hc16 : c ≤ c₁ / 16) (hc5 : c ≤ 1 / 5) {N n i : ℕ} (hN : 1 ≤ N) (h : n + i < N)
    (hB : ppZRidge N n ≤
      C₁ * Real.exp (-(c₁ / N) * ((n : ℝ) - N / 2) ^ 2) * geoNormFactor0 N) :
    geoNormFactor N n i ≤
      max C₁ 0 * Real.exp 2 *
        Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) *
          geoNormFactor0 N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnN : n < N := by omega
  have hS0 : 0 < geoNormFactor0 N := by
    rw [← ppZ_ridge_center]
    exact ridge_pos_normGlobal (by omega)
  have hT := (ridge_pos_normGlobal hnN).le
  have hA := ppZ_normFactor_le_ridge h
  have hτ : 0 ≤ Real.tan (n * Real.pi / (2 * N)) := by
    have hnr : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
    refine Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by positivity) ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hDD := natCast_sub_sq_sub_abs_nonneg_normGlobal i (ppZRidgeIdx N n)
  have hidx := ridgeIdx_sub_quarter_normGlobal hnN.le
  have hM : 0 ≤ max C₁ 0 := le_max_right _ _
  have hB' : ppZRidge N n ≤
      max C₁ 0 * Real.exp (-(c₁ / N) * ((n : ℝ) - N / 2) ^ 2) * geoNormFactor0 N :=
    hB.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) hS0.le)
  have ha0 := abs_nonneg ((n : ℝ) - N / 2)
  have hb0 := abs_nonneg ((i : ℝ) - N / 4)
  have hP0 : 0 ≤ 2 * Real.pi / N * Real.tan (n * Real.pi / (2 * N)) :=
    mul_nonneg (by positivity) hτ
  have hE1 : Real.exp (-(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
      (((i : ℝ) - ppZRidgeIdx N n) ^ 2 - |(i : ℝ) - ppZRidgeIdx N n|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg hP0 hDD
    linarith
  rcases le_or_gt (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) (4 * |(n : ℝ) - N / 2|) with hd | hd
  · have hexp : Real.exp (-(c₁ / N) * ((n : ℝ) - N / 2) ^ 2) ≤
        Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) := by
      apply Real.exp_le_exp.mpr
      rw [← sq_abs ((n : ℝ) - N / 2)]
      have hd2 : (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 ≤
          16 * |(n : ℝ) - N / 2| ^ 2 := by nlinarith
      have hX : 0 ≤ (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 / N := by positivity
      have h1 : c * ((|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 / N) ≤
          c₁ / 16 * ((|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 / N) :=
        mul_le_mul_of_nonneg_right hc16 hX
      have h2 : c₁ / 16 * ((|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 / N) ≤
          c₁ / 16 * (16 * |(n : ℝ) - N / 2| ^ 2 / N) := by gcongr
      have e1 : -(c₁ / N) * |(n : ℝ) - N / 2| ^ 2 =
          -(c₁ / 16 * (16 * |(n : ℝ) - N / 2| ^ 2 / N)) := by ring
      have e2 : -(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 =
          -(c * ((|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 / N)) := by ring
      rw [e1, e2]
      linarith
    calc geoNormFactor N n i ≤ ppZRidge N n * 1 := hA.trans (mul_le_mul_of_nonneg_left hE1 hT)
      _ = ppZRidge N n := mul_one _
      _ ≤ max C₁ 0 * Real.exp (-(c₁ / N) * ((n : ℝ) - N / 2) ^ 2) * geoNormFactor0 N := hB'
      _ ≤ max C₁ 0 * Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) *
            geoNormFactor0 N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hM) hS0.le
      _ = max C₁ 0 * 1 * Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) *
            geoNormFactor0 N := by ring
      _ ≤ max C₁ 0 * Real.exp 2 *
            Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) *
              geoNormFactor0 N := by
          gcongr
          exact Real.one_le_exp (by norm_num)
  · have hTM : ppZRidge N n ≤ max C₁ 0 * geoNormFactor0 N := by
      refine hB'.trans (mul_le_mul_of_nonneg_right ?_ hS0.le)
      have h1 : Real.exp (-(c₁ / N) * ((n : ℝ) - N / 2) ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c₁ / N * ((n : ℝ) - N / 2) ^ 2 := by positivity
        linarith
      calc max C₁ 0 * Real.exp (-(c₁ / N) * ((n : ℝ) - N / 2) ^ 2) ≤ max C₁ 0 * 1 :=
            mul_le_mul_of_nonneg_left h1 hM
        _ = max C₁ 0 := mul_one _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast (by omega : i ≤ N)
    have hb1 : |(i : ℝ) - N / 4| ≤ 3 * N / 4 := by
      rw [abs_le]
      constructor <;> linarith
    have h16 : (3 : ℝ) * N ≤ 16 * n := by
      have := neg_abs_le ((n : ℝ) - N / 2)
      linarith
    have hP := rate_lower_bound_normGlobal hN hnN h16
    have htri : |(i : ℝ) - N / 4| ≤
        |(i : ℝ) - ppZRidgeIdx N n| + |(ppZRidgeIdx N n : ℝ) - N / 4| := by
      have := abs_add_le ((i : ℝ) - ppZRidgeIdx N n) ((ppZRidgeIdx N n : ℝ) - N / 4)
      rwa [sub_add_sub_cancel] at this
    have key := exponent_bound_normGlobal (c := c)
      (d := |(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) (y := |(i : ℝ) - ppZRidgeIdx N n|)
      hNr hc5 hP (abs_nonneg _) (by rw [sq_abs]; exact hDD) (by linarith) (by positivity)
    rw [sq_abs] at key
    have hE2 : Real.exp (-(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
        (((i : ℝ) - ppZRidgeIdx N n) ^ 2 - |(i : ℝ) - ppZRidgeIdx N n|)) ≤
        Real.exp 2 * Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc geoNormFactor N n i
        ≤ ppZRidge N n * (Real.exp 2 *
            Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2)) :=
          hA.trans (mul_le_mul_of_nonneg_left hE2 hT)
      _ ≤ max C₁ 0 * geoNormFactor0 N * (Real.exp 2 *
            Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2)) :=
          mul_le_mul_of_nonneg_right hTM (by positivity)
      _ = _ := by ring

/-- Global Gaussian bound: `S_{n,i} ≤ C exp(-(c/N)(|n - N/2| + |i - N/4|)²) S₀`. -/
theorem ppZ_normFactor_gaussian_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N n i : ℕ, 1 ≤ N → n + i < N →
      geoNormFactor N n i ≤
        C * Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) *
          geoNormFactor0 N := by
  obtain ⟨c₁, hc₁, C₁, hR⟩ := ppZ_ridge_le
  refine ⟨min (c₁ / 16) (1 / 5), lt_min (by positivity) (by norm_num),
    max C₁ 0 * Real.exp 2, fun N n i hN h ↦ ?_⟩
  exact gaussian_bound_core_normGlobal hc₁.le (min_le_left _ _) (min_le_right _ _) hN h
    (hR N n hN (by omega))

end AJConjecture
