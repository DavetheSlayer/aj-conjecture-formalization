import Mathlib
import AJFamily.VolumeDefs

/-!
# `∫₀¹ arctan(a)/a da = G`

The Taylor expansion `arctan a = ∑_{n<N} (-1)ⁿ a^(2n+1)/(2n+1) + (-1)ᴺ ∫₀ᵃ t^(2N)/(1+t²) dt`
gives `|arctan(a)/a - ∑_{n<N} (-1)ⁿ a^(2n)/(2n+1)| ≤ 1/(2N+1)` uniformly on `(0, 1]`;
integrate termwise (`∫₀¹ a^(2n) = 1/(2n+1)`) and pass to the limit. Note `arctan 0 / 0 = 0` in
Lean; the integrand is continuous on `(0, 1]` and bounded by `1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

open Finset Filter Topology

/-- The geometric identity `1/(1+t²) - ∑_{n<N} (-1)ⁿ t^(2n) = (-1)ᴺ t^(2N)/(1+t²)`. -/
private lemma one_div_one_add_sq_sub_geom_sum (t : ℝ) (N : ℕ) :
    1 / (1 + t ^ 2) - ∑ n ∈ range N, (-1 : ℝ) ^ n * t ^ (2 * n) =
      (-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2) := by
  have h : (1 + t ^ 2) ≠ 0 := by positivity
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ← sub_sub, ih]
    field_simp
    ring

/-- Termwise integration of the truncated geometric series `∑_{n<N} (-1)ⁿ t^(2n)`. -/
private lemma integral_alternating_even_pow_sum (a : ℝ) (N : ℕ) :
    ∫ t in (0 : ℝ)..a, ∑ n ∈ range N, (-1 : ℝ) ^ n * t ^ (2 * n) =
      ∑ n ∈ range N, (-1 : ℝ) ^ n * a ^ (2 * n + 1) / (2 * n + 1) := by
  rw [intervalIntegral.integral_finsetSum
    (fun n _ ↦ Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  ring

/-- Remainder estimate for the Taylor series of `arctan` on `[0, ∞)`. -/
private lemma abs_arctan_sub_taylor_le {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    |Real.arctan a - ∑ n ∈ range N, (-1 : ℝ) ^ n * a ^ (2 * n + 1) / (2 * n + 1)| ≤
      a ^ (2 * N + 1) / (2 * N + 1) := by
  have h1 : ∫ t in (0 : ℝ)..a, 1 / (1 + t ^ 2) = Real.arctan a := by
    rw [integral_one_div_one_add_sq]
    simp
  have h2 : ∫ t in (0 : ℝ)..a, t ^ (2 * N) = a ^ (2 * N + 1) / (2 * N + 1) := by
    rw [integral_pow]
    push_cast
    simp
  have hc : Continuous fun t : ℝ ↦ 1 / (1 + t ^ 2) :=
    continuous_const.div (g := fun t : ℝ ↦ 1 + t ^ 2) (by fun_prop) fun t ↦ by positivity
  rw [← h1, ← integral_alternating_even_pow_sum, ← intervalIntegral.integral_sub
    (hc.intervalIntegrable 0 a)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [one_div_one_add_sq_sub_geom_sum]
  rw [← h2, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le ha (Eventually.of_forall fun t ht ↦ ?_)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hp : 0 < 1 + t ^ 2 := by positivity
  have ht0 : 0 ≤ t ^ (2 * N) := pow_nonneg ht.1.le _
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hp, abs_of_nonneg ht0]
  exact div_le_self ht0 (by nlinarith)

/-- Uniform bound for `arctan a / a` minus its truncated Taylor series on `(0, 1]`. -/
private lemma abs_arctan_div_sub_taylor_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    |Real.arctan a / a - ∑ n ∈ range N, (-1 : ℝ) ^ n * a ^ (2 * n) / (2 * n + 1)| ≤
      1 / (2 * N + 1) := by
  have h := abs_arctan_sub_taylor_le ha.le N
  have e : Real.arctan a / a - ∑ n ∈ range N, (-1 : ℝ) ^ n * a ^ (2 * n) / (2 * n + 1) =
      (Real.arctan a - ∑ n ∈ range N, (-1 : ℝ) ^ n * a ^ (2 * n + 1) / (2 * n + 1)) / a := by
    rw [sub_div, sum_div]
    congr 1
    refine sum_congr rfl fun n _ ↦ ?_
    field_simp
    ring
  rw [e, abs_div, abs_of_pos ha, div_le_iff₀ ha]
  calc _ ≤ a ^ (2 * N + 1) / (2 * N + 1) := h
    _ ≤ a / (2 * N + 1) := by gcongr; exact pow_le_of_le_one ha.le ha1 (by omega)
    _ = 1 / (2 * N + 1) * a := by ring

/-- `a ↦ arctan a / a` is interval integrable on `[0, 1]`. -/
private lemma intervalIntegrable_arctan_div_self :
    IntervalIntegrable (fun a : ℝ ↦ Real.arctan a / a) MeasureTheory.volume 0 1 := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun ?_ ?_
  · exact (Real.continuous_arctan.measurable.div measurable_id).aestronglyMeasurable
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2
      (Eventually.of_forall fun a ha ↦ ?_)
    rw [Set.uIoc_of_le zero_le_one] at ha
    have := abs_arctan_div_sub_taylor_le ha.1 ha.2 0
    simpa [abs_div] using this

/-- `∫₀¹ arctan(a)/a da` is Catalan's constant. -/
theorem integral_arctan_div_self : ∫ a in (0 : ℝ)..1, Real.arctan a / a = catalanConstant := by
  set I := ∫ a in (0 : ℝ)..1, Real.arctan a / a
  have hsum : ∀ N : ℕ, ∫ a in (0 : ℝ)..1,
      ∑ n ∈ range N, (-1 : ℝ) ^ n * a ^ (2 * n) / (2 * n + 1) =
      ∑ n ∈ range N, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
    intro N
    rw [intervalIntegral.integral_finsetSum
      (fun n _ ↦ Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    simp only [one_pow, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, sub_zero]
    field_simp
  have hbound : ∀ N : ℕ,
      |I - ∑ n ∈ range N, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2| ≤ 1 / (2 * N + 1) := by
    intro N
    rw [← hsum, ← intervalIntegral.integral_sub intervalIntegrable_arctan_div_self
      (Continuous.intervalIntegrable (by fun_prop) _ _), ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := 1 / (2 * (N : ℝ) + 1)) (f := fun a : ℝ ↦ Real.arctan a / a -
        ∑ n ∈ range N, (-1 : ℝ) ^ n * a ^ (2 * n) / (2 * n + 1)) fun a ha ↦ by
      rw [Set.uIoc_of_le zero_le_one] at ha
      exact abs_arctan_div_sub_taylor_le ha.1 ha.2 N
    simpa using this
  have h0 : Tendsto (fun N : ℕ ↦ 1 / (2 * (N : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N ↦ by positivity) (fun N ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    gcongr
    linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  have hlim : Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2)
      atTop (𝓝 I) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) h0
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hbound N
  have hg : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hs : Summable (fun n : ℕ ↦ (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) := by
    refine hg.of_norm_bounded fun n ↦ ?_
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    gcongr
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  exact (tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim).symm

end AJConjecture
