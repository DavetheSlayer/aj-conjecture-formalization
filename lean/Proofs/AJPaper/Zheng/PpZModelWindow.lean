import Mathlib
import AJPaper.Zheng.PpZModelTsum
import AJPaper.Zheng.PpZModelTail
import AJPaper.Zheng.PpZFinite

/-!
# The Gaussian model sum over the window (Unit PpZ, node `PpZ_ModelWindow`)

Source: Zheng, (3.30).

`ppZModelWindowSum N δ β` is the sum of the model summand over the window
`|n - N/2| + |i - N/4| < N^δ` (same index set and same `if` as `geoWindowSum`).

* `ppZ_modelWindowSum`: for `1/2 < δ < 2/3`, `N ≥ 65`:
  `‖ppZModelWindowSum N δ β - N (1 - iβ)^{-1/2}‖ ≤ K · N · N^{3δ-2}`.
* `ppZ_modelWindow_abs_le`: `∑_{n<N} ∑_{i<N-n} e^{V(n,i)} ≤ K N`.

Route for the first. For `N ≥ 65` and `δ < 2/3`: `N^δ < N^{2/3} ≤ N/4`, so every lattice point of
the open diamond has `0 ≤ n < N`, `0 ≤ i < N - n`; hence the window sum is the sum of
`ppZModel N β` over `ℤ²` minus the sum over the complement of the diamond (`ppZ_model_summable`,
`Summable.tsum_prod`, `tsum_eq_sum` for the finitely supported part). The full sum is
`N(1 - iβ)^{-1/2} + O(1)` (`ppZ_model_tsum`) and the complement is `≤ K N e^{-(π/10)N^{2δ-1}}`
(`ppZ_model_tail` with `R = N^δ`, `ppZ_model_norm`); conclude with `ppZ_exp_neg_rpow_le`
(node `PpZ_Finite`) and `1 ≤ N^{3δ-1}`. The second statement: `ppZ_model_tail` with `R = 0`,
comparing the finite sum with the `tsum` of a nonnegative summable family.
-/

noncomputable section

namespace AJConjecture

open Classical in
/-- The model sum over the window `|n - N/2| + |i - N/4| < N^δ`. -/
def ppZModelWindowSum (N : ℕ) (δ β : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
    if GeoInWindow N ((N : ℝ) ^ δ) n i then ppZModel N β n i else 0

/-- `N^δ ≤ N/4` for `N ≥ 64`, `δ ≤ 2/3`. -/
private theorem rpow_le_quarter_modelWindow {N : ℕ} (hN : 64 ≤ N) {δ : ℝ} (hδ' : δ ≤ 2 / 3) :
    (N : ℝ) ^ δ ≤ N / 4 := by
  have hN' : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h1 : (N : ℝ) ^ δ ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hδ'
  set t : ℝ := (N : ℝ) ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hN0 _
  have ht3 : t ^ 3 = N := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have ht2 : (N : ℝ) ^ (2 / 3 : ℝ) = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have ht4 : 4 ≤ t := by
    by_contra hlt
    rw [not_le] at hlt
    have : t ^ 3 < 4 ^ 3 := pow_lt_pow_left₀ hlt ht0 (by norm_num)
    linarith
  rw [ht2] at h1
  nlinarith

/-- The square `[0, N)²` inside `ℤ²`. -/
private def squareFinset_modelWindow (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N ×ˢ Finset.range N).map (Nat.castEmbedding.prodMap Nat.castEmbedding)

/-- A lattice point of an open diamond of radius `≤ N/4` lies in the square `[0, N)²`. -/
private theorem mem_squareFinset_modelWindow {N : ℕ} {ρ : ℝ} (hρ : ρ ≤ N / 4) {p : ℤ × ℤ}
    (hp : |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| < ρ) : p ∈ squareFinset_modelWindow N := by
  have h1 : |(p.1 : ℝ) - N / 2| < N / 4 := by linarith [abs_nonneg ((p.2 : ℝ) - N / 4)]
  have h2 : |(p.2 : ℝ) - N / 4| < N / 4 := by linarith [abs_nonneg ((p.1 : ℝ) - N / 2)]
  rw [abs_lt] at h1 h2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have a1 : (0 : ℤ) ≤ p.1 := by
    have : (0 : ℝ) ≤ p.1 := by linarith
    exact_mod_cast this
  have a2 : p.1 < (N : ℤ) := by
    have : (p.1 : ℝ) < N := by linarith
    exact_mod_cast this
  have b1 : (0 : ℤ) ≤ p.2 := by
    have : (0 : ℝ) ≤ p.2 := by linarith
    exact_mod_cast this
  have b2 : p.2 < (N : ℤ) := by
    have : (p.2 : ℝ) < N := by linarith
    exact_mod_cast this
  rw [squareFinset_modelWindow, Finset.mem_map]
  refine ⟨(p.1.toNat, p.2.toNat), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  · ext
    · simp [Int.toNat_of_nonneg a1]
    · simp [Int.toNat_of_nonneg b1]

/-- A sum over the square in `ℤ²` as a double sum over `ℕ`. -/
private theorem sum_squareFinset_modelWindow {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : ℤ × ℤ → M) :
    ∑ p ∈ squareFinset_modelWindow N, f p =
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range N, f ((n : ℤ), (i : ℤ)) := by
  rw [squareFinset_modelWindow, Finset.sum_map, Finset.sum_product]
  rfl

open Classical in
/-- A window sum over the triangle is the sum over `ℤ²` restricted to the open diamond, as
soon as the radius is at most `N/4`. -/
private theorem windowSum_eq_tsum_modelWindow {N : ℕ} {ρ : ℝ} (hρ : ρ ≤ N / 4)
    (F : ℤ → ℤ → ℂ) :
    (∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        if GeoInWindow N ρ n i then F n i else 0) =
      ∑' p : ℤ × ℤ, if |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| < ρ then F p.1 p.2 else 0 := by
  rw [tsum_eq_sum (s := squareFinset_modelWindow N) (fun p hp ↦ ite_eq_right fun h ↦
    hp (mem_squareFinset_modelWindow hρ h)), sum_squareFinset_modelWindow]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Finset.mem_range] at hn
  have hsub : Finset.range (N - n) ⊆ Finset.range N := Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : GeoInWindow N ρ n i
    · rw [ite_eq_left h, ite_eq_left (by simpa [GeoInWindow] using h)]
    · rw [ite_eq_right h, ite_eq_right (by simpa [GeoInWindow] using h)]
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    refine ite_eq_right fun h ↦ ?_
    simp only [Int.cast_natCast] at h
    have h1 := le_abs_self ((n : ℝ) - N / 2)
    have h2 := le_abs_self ((i : ℝ) - N / 4)
    have h3 : (N : ℝ) ≤ n + i := by
      have : N ≤ n + i := by omega
      exact_mod_cast this
    linarith

/-- A nonnegative sum over the triangle is at most the sum over `ℤ²`. -/
private theorem sum_triangle_le_tsum_modelWindow (N : ℕ) {g : ℤ × ℤ → ℝ} (hg : ∀ p, 0 ≤ g p)
    (hs : Summable g) :
    ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n), g ((n : ℤ), (i : ℤ)) ≤ ∑' p, g p := by
  refine le_trans ?_ (hs.sum_le_tsum (squareFinset_modelWindow N) fun p _ ↦ hg p)
  rw [sum_squareFinset_modelWindow]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.sub_le N n))
    fun _ _ _ ↦ hg _

/-- The model over the complement of the diamond of radius `N^δ` is
`≤ K N e^{-(π/10) N^{2δ-1}}`, `K` the constant of `ppZ_model_tail`. -/
private theorem norm_tsum_outside_le_modelWindow {K₁ : ℝ}
    (hK₁ : ∀ (N : ℕ) (R : ℝ), 1 ≤ N → 0 ≤ R →
      ∑' p : ℤ × ℤ, (if R ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
          Real.exp (ppZPot N p.1 p.2) else 0) ≤
        K₁ * N * Real.exp (-(Real.pi / 10) * R ^ 2 / N))
    {N : ℕ} (hN : 1 ≤ N) (β δ : ℝ) :
    ‖∑' p : ℤ × ℤ, (if (N : ℝ) ^ δ ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
        ppZModel N β p.1 p.2 else 0)‖ ≤
      K₁ * N * Real.exp (-(Real.pi / 10) * (N : ℝ) ^ (2 * δ - 1)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := hK₁ N ((N : ℝ) ^ δ) hN (Real.rpow_nonneg hN'.le _)
  have e : -(Real.pi / 10) * ((N : ℝ) ^ δ) ^ 2 / N = -(Real.pi / 10) * (N : ℝ) ^ (2 * δ - 1) := by
    rw [Real.rpow_sub_one hN'.ne', ← Real.rpow_natCast, ← Real.rpow_mul hN'.le,
      show δ * ((2 : ℕ) : ℝ) = 2 * δ by push_cast; ring]
    ring
  rw [e] at h
  have hn : ∀ p : ℤ × ℤ,
      ‖(if (N : ℝ) ^ δ ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
        ppZModel N β p.1 p.2 else 0)‖ =
      (if (N : ℝ) ^ δ ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
        Real.exp (ppZPot N p.1 p.2) else 0) := fun p ↦ by
    split_ifs
    · exact ppZ_model_norm N β p.1 p.2
    · exact norm_zero
  have hs : Summable fun p : ℤ × ℤ ↦
      ‖(if (N : ℝ) ^ δ ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
        ppZModel N β p.1 p.2 else 0)‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_)
      (ppZ_model_summable N hN β)
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  simp only [hn]
  exact h

/-- The model window sum is `N (1 - iβ)^{-1/2} + O(N · N^{3δ-2})`. -/
theorem ppZ_modelWindowSum (β : ℝ) {δ : ℝ} (hδ : 1 / 2 < δ) (hδ' : δ < 2 / 3) :
    ∃ K : ℝ, ∀ N : ℕ, 65 ≤ N →
      ‖ppZModelWindowSum N δ β - (N : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤
        K * (N : ℝ) ^ (3 * δ - 2) * N := by
  obtain ⟨K₀, hK₀⟩ := ppZ_model_tsum β
  obtain ⟨K₁, hK₁⟩ := ppZ_model_tail
  obtain ⟨K₂, hK₂⟩ := ppZ_exp_neg_rpow_le (c := Real.pi / 10) (by positivity) hδ (3 * δ - 2)
  refine ⟨K₀ + |K₁| * K₂, fun N hN ↦ ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hK₀0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ N hN1)
  have hρ := rpow_le_quarter_modelWindow (N := N) (by omega) hδ'.le
  have hsum : Summable fun p : ℤ × ℤ ↦ ppZModel N β p.1 p.2 :=
    (ppZ_model_summable N hN1 β).of_norm
  have hin : Summable fun p : ℤ × ℤ ↦
      if |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| < (N : ℝ) ^ δ then
        ppZModel N β p.1 p.2 else 0 := by
    refine Summable.of_norm_bounded (ppZ_model_summable N hN1 β) fun p ↦ ?_
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  have hout : Summable fun p : ℤ × ℤ ↦
      if (N : ℝ) ^ δ ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
        ppZModel N β p.1 p.2 else 0 := by
    refine Summable.of_norm_bounded (ppZ_model_summable N hN1 β) fun p ↦ ?_
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  have hW : ppZModelWindowSum N δ β =
      (∑' n : ℤ, ∑' i : ℤ, ppZModel N β n i) -
        ∑' p : ℤ × ℤ, (if (N : ℝ) ^ δ ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
          ppZModel N β p.1 p.2 else 0) := by
    rw [ppZModelWindowSum, windowSum_eq_tsum_modelWindow hρ, eq_sub_iff_add_eq,
      ← hin.tsum_add hout, ← hsum.tsum_prod]
    refine tsum_congr fun p ↦ ?_
    by_cases h : |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| < (N : ℝ) ^ δ
    · rw [ite_eq_left h, ite_eq_right (not_le.mpr h), add_zero]
    · rw [ite_eq_right h, ite_eq_left (not_lt.mp h), zero_add]
  have hT := norm_tsum_outside_le_modelWindow hK₁ hN1 β δ
  have hE := hK₂ N hN1
  have hp : 0 < (N : ℝ) ^ (3 * δ - 2) := Real.rpow_pos_of_pos hN' _
  have h1 : 1 ≤ (N : ℝ) ^ (3 * δ - 2) * N := by
    rw [← Real.rpow_add_one hN'.ne']
    exact Real.one_le_rpow hN1' (by linarith)
  rw [hW, sub_right_comm]
  refine (norm_sub_le _ _).trans ?_
  have h2 : K₁ * N * Real.exp (-(Real.pi / 10) * (N : ℝ) ^ (2 * δ - 1)) ≤
      |K₁| * N * (K₂ * (N : ℝ) ^ (3 * δ - 2)) :=
    calc K₁ * N * Real.exp (-(Real.pi / 10) * (N : ℝ) ^ (2 * δ - 1))
        ≤ |K₁| * N * Real.exp (-(Real.pi / 10) * (N : ℝ) ^ (2 * δ - 1)) := by
          gcongr
          exact le_abs_self K₁
      _ ≤ |K₁| * N * (K₂ * (N : ℝ) ^ (3 * δ - 2)) := by
          gcongr
  have h3 : K₀ ≤ K₀ * ((N : ℝ) ^ (3 * δ - 2) * N) := le_mul_of_one_le_right hK₀0 h1
  calc ‖(∑' n : ℤ, ∑' i : ℤ, ppZModel N β n i) - (N : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ))‖ +
        ‖∑' p : ℤ × ℤ, (if (N : ℝ) ^ δ ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
          ppZModel N β p.1 p.2 else 0)‖
      ≤ K₀ * ((N : ℝ) ^ (3 * δ - 2) * N) + |K₁| * N * (K₂ * (N : ℝ) ^ (3 * δ - 2)) :=
        add_le_add ((hK₀ N hN1).trans h3) (hT.trans h2)
    _ = (K₀ + |K₁| * K₂) * (N : ℝ) ^ (3 * δ - 2) * N := by ring

/-- The sum of `e^{V}` over the whole triangle is `O(N)`. -/
theorem ppZ_modelWindow_abs_le :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n), Real.exp (ppZPot N n i) ≤ K * N := by
  obtain ⟨K₁, hK₁⟩ := ppZ_model_tail
  refine ⟨K₁, fun N hN ↦ ?_⟩
  have hs : Summable fun p : ℤ × ℤ ↦ Real.exp (ppZPot N p.1 p.2) := by
    have h := ppZ_model_summable N hN 0
    simp only [ppZ_model_norm] at h
    exact h
  have h1 := sum_triangle_le_tsum_modelWindow N (fun p ↦ (Real.exp_pos _).le) hs
  have h2 := hK₁ N 0 hN le_rfl
  have e : ∀ p : ℤ × ℤ, (if (0 : ℝ) ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
      Real.exp (ppZPot N p.1 p.2) else 0) = Real.exp (ppZPot N p.1 p.2) := fun p ↦
    ite_eq_left (by positivity)
  simp only [e, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one] at h2
  simp only [Int.cast_natCast] at h1
  exact h1.trans h2

end AJConjecture
