import Mathlib

/-!
# Two elementary facts about sequences (Unit PpZ, node `PpZ_Finite`)

* `ppZ_exists_bound_of_eventually`: a bound `f N ≤ K₁ g N` for `N ≥ N₁`, with `g > 0`, extends to
  all `N ≥ 1` after enlarging the constant: only finitely many `N` remain. Used for the estimates
  that are proved for large `N`. Route: `K = max K₁ (∑_{N < N₁} |f N| / g N)` (or induction on
  `N₁`).
* `ppZ_exp_neg_rpow_le`: `e^{-c N^{2δ-1}} ≤ K N^p` for all `N ≥ 1` (`c > 0`, `δ > 1/2`, any real
  `p`). Route: `N^{-p} e^{-c N^{2δ-1}} → 0`
  (`Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` after the substitution `x = N^{2δ-1}`,
  `N^{-p} = x^{-p/(2δ-1)}`), a convergent sequence is bounded; or `e^{-x} ≤ (m/x)^m`.
-/

noncomputable section

namespace AJConjecture

/-- An eventual bound against a positive sequence holds for all `N ≥ 1` with a larger constant. -/
theorem ppZ_exists_bound_of_eventually {f g : ℕ → ℝ} (hg : ∀ N, 1 ≤ N → 0 < g N) (K₁ : ℝ)
    (N₁ : ℕ) (h : ∀ N, N₁ ≤ N → f N ≤ K₁ * g N) : ∃ K : ℝ, ∀ N, 1 ≤ N → f N ≤ K * g N := by
  refine ⟨|K₁| + ∑ M ∈ Finset.range N₁, |f M / g M|, fun N hN ↦ ?_⟩
  have hgN := hg N hN
  have hs : 0 ≤ ∑ M ∈ Finset.range N₁, |f M / g M| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  rcases le_or_gt N₁ N with hle | hlt
  · refine (h N hle).trans (mul_le_mul_of_nonneg_right ?_ hgN.le)
    linarith [le_abs_self K₁]
  · have h1 : |f N / g N| ≤ ∑ M ∈ Finset.range N₁, |f M / g M| :=
      Finset.single_le_sum (f := fun M ↦ |f M / g M|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.mpr hlt)
    have h2 : f N = f N / g N * g N := by
      field_simp
    rw [h2]
    refine mul_le_mul_of_nonneg_right ?_ hgN.le
    linarith [le_abs_self (f N / g N), abs_nonneg K₁]

/-- `e^{-c N^{2δ-1}} ≤ K N^p` for all `N ≥ 1`. -/
theorem ppZ_exp_neg_rpow_le {c δ : ℝ} (hc : 0 < c) (hδ : 1 / 2 < δ) (p : ℝ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → Real.exp (-c * (N : ℝ) ^ (2 * δ - 1)) ≤ K * (N : ℝ) ^ p := by
  have hd : 0 < 2 * δ - 1 := by linarith
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-p / (2 * δ - 1)) c hc).comp
    ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop)
  obtain ⟨K, hK⟩ := ht.bddAbove_range
  refine ⟨K, fun N hN ↦ ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hK (Set.mem_range_self N)
  simp only [Function.comp_apply] at h1
  rw [← Real.rpow_mul hN'.le, show (2 * δ - 1) * (-p / (2 * δ - 1)) = -p by field_simp,
    Real.rpow_neg hN'.le] at h1
  have hp : 0 < (N : ℝ) ^ p := Real.rpow_pos_of_pos hN' p
  rw [inv_mul_le_iff₀ hp] at h1
  linarith

end AJConjecture
