import Mathlib
import AJPaper.Zheng.PpZKernelPole

/-!
# The contour shift past the `a` poles (Unit PpZ, node `PpZ_KernelShift`)

Source: Zheng, Lemma 5.1, (5.8)–(5.10): `∫_C = ∫_{C + z₀} + (residues at jπi/(pq), 0 < j < pq)`.

`ppZ_kernel_shift`: for `x₀ = ρω` with `(2a-1)π/(2a) < ρ < (2a+1)π/(2a)` (i.e. `|c - N| < N/(2a)`
when `ρ = πc/N`):

  `∫_ℝ F(x) dx = ∫_ℝ e^{-Ax²} (x + ρω)^{2k} τ(ωx + iρ) dx + 2πi ∑_{j<a} Res_j`.

Route. Heights `Y_j = jπ/(a√2)` for `j < a` and `Y_a = ρ/√2 = Im(ρω)`. For every `j < a`,
`Im w_{j-1} < Y_j < Im w_j < Y_{j+1} < Im w_{j+1}` (for `j + 1 = a` this is the hypothesis on `ρ`),
so `ppZ_kernel_cross_pole` applies to each strip `[Y_j, Y_{j+1}]`; add up (`Finset.sum_range_succ`,
telescoping; `Y₀ = 0`). On the last line substitute `x ↦ x + ρ/√2`
(`MeasureTheory.integral_add_right_eq_self`): `x + ρ/√2 + iρ/√2 = x + ρω`, the kernel becomes
`e^{-Ax²} (x + ρω)^{2k} τ(ω(x + ρω))` and `ω · ρω = iρ` (`ppZOmega_sq`, `ppZOmega_eq`).

Checked numerically for `a ∈ {1, 2, 3}`, `k ∈ {0, 1}`, `A ∈ {0.5, 1}`, three values of `ρ`
(`strip3.py`, error `< 10⁻¹¹`); for the values used later also through `kt.py`.
-/

noncomputable section

namespace AJConjecture

/-- The heights of the intermediate lines: `Y_j = jπ/(a√2)` for `j < a` and `Y_j = ρ/√2`
for `j ≥ a`. -/
private def heightPpZKernelShift (a : ℕ) (ρ : ℝ) (j : ℕ) : ℝ :=
  if j < a then j * Real.pi / (a * Real.sqrt 2) else ρ / Real.sqrt 2

/-- Consecutive heights enclose exactly the pole `w_m`. -/
private theorem height_bounds_ppZKernelShift {a : ℕ} {ρ : ℝ}
    (h1 : (2 * (a : ℝ) - 1) * Real.pi / (2 * a) < ρ)
    (h2 : ρ < (2 * (a : ℝ) + 1) * Real.pi / (2 * a)) {m : ℕ} (hm : m < a) :
    ((2 * (m : ℝ) - 1) * Real.pi / (2 * a * Real.sqrt 2) < heightPpZKernelShift a ρ m ∧
      heightPpZKernelShift a ρ m < (2 * (m : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2)) ∧
    (2 * (m : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2) < heightPpZKernelShift a ρ (m + 1) ∧
      heightPpZKernelShift a ρ (m + 1) < (2 * (m : ℝ) + 3) * Real.pi / (2 * a * Real.sqrt 2) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ha : (0 : ℝ) < a := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hpi := Real.pi_pos
  have hmono : ∀ t s : ℝ, t < s →
      t * Real.pi / (2 * a * Real.sqrt 2) < s * Real.pi / (2 * a * Real.sqrt 2) :=
    fun t s hts ↦ by gcongr
  have heq : ∀ t : ℝ, t * Real.pi / (a * Real.sqrt 2) =
      (2 * t) * Real.pi / (2 * a * Real.sqrt 2) := fun t ↦ by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [heightPpZKernelShift, ite_eq_left hm, heq]
    exact ⟨hmono _ _ (by linarith), hmono _ _ (by linarith)⟩
  · by_cases hm' : m + 1 < a
    · rw [heightPpZKernelShift, ite_eq_left hm', Nat.cast_add, Nat.cast_one, heq]
      exact ⟨hmono _ _ (by linarith), hmono _ _ (by linarith)⟩
    · have hma : (a : ℝ) = m + 1 := by exact_mod_cast (by omega : a = m + 1)
      have e1 : (2 * (m : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2) =
          (2 * (a : ℝ) - 1) * Real.pi / (2 * a) / Real.sqrt 2 := by
        rw [hma]
        field_simp
        ring
      have e2 : (2 * (m : ℝ) + 3) * Real.pi / (2 * a * Real.sqrt 2) =
          (2 * (a : ℝ) + 1) * Real.pi / (2 * a) / Real.sqrt 2 := by
        rw [hma]
        field_simp
        ring
      rw [heightPpZKernelShift, ite_eq_right hm', e1, e2]
      exact ⟨div_lt_div_of_pos_right h1 hs2, div_lt_div_of_pos_right h2 hs2⟩

/-- Crossing the first `m` poles, one strip at a time. -/
private theorem kernel_shift_partial_ppZKernelShift (a k : ℕ) (ha : 1 ≤ a) {A ρ : ℝ}
    (hA : 0 < A) (h1 : (2 * (a : ℝ) - 1) * Real.pi / (2 * a) < ρ)
    (h2 : ρ < (2 * (a : ℝ) + 1) * Real.pi / (2 * a)) (x₀ : ℂ) (m : ℕ) (hm : m ≤ a) :
    (∫ x : ℝ, ppZKernel a k A x₀ (x + heightPpZKernelShift a ρ 0 * Complex.I)) -
        ∫ x : ℝ, ppZKernel a k A x₀ (x + heightPpZKernelShift a ρ m * Complex.I) =
      2 * Real.pi * Complex.I * ∑ j ∈ Finset.range m, ppZKernelRes a k A x₀ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨⟨c1, c2⟩, c3, c4⟩ := height_bounds_ppZKernelShift h1 h2 (m := m) (by omega)
    have hstep := ppZ_kernel_cross_pole a k ha hA x₀ m c1 c2 c3 c4
    rw [Finset.sum_range_succ, mul_add, ← ih (by omega), ← hstep]
    ring

/-- **Contour shift** of the kernel integral from `ℝ` to `ℝ + ρω`, with the `a` residues. -/
theorem ppZ_kernel_shift (a k : ℕ) (ha : 1 ≤ a) {A ρ : ℝ} (hA : 0 < A)
    (h1 : (2 * (a : ℝ) - 1) * Real.pi / (2 * a) < ρ)
    (h2 : ρ < (2 * (a : ℝ) + 1) * Real.pi / (2 * a)) :
    ∫ x : ℝ, ppZKernel a k A (ρ * ppZOmega) x =
      (∫ x : ℝ, Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) + ρ * ppZOmega) ^ (2 * k) *
          ppZTau a (ppZOmega * x + ρ * Complex.I)) +
        2 * Real.pi * Complex.I * ∑ j ∈ Finset.range a, ppZKernelRes a k A (ρ * ppZOmega) j := by
  have hs2' : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have hpart := kernel_shift_partial_ppZKernelShift a k ha hA h1 h2 (ρ * ppZOmega) a le_rfl
  have h0 : heightPpZKernelShift a ρ 0 = 0 := by
    rw [heightPpZKernelShift, ite_eq_left (by omega)]
    simp
  have hlast : heightPpZKernelShift a ρ a = ρ / Real.sqrt 2 := by
    rw [heightPpZKernelShift, ite_eq_right (lt_irrefl a)]
  have htrans : (∫ x : ℝ, ppZKernel a k A (ρ * ppZOmega)
      (x + (ρ / Real.sqrt 2 : ℝ) * Complex.I)) =
      ∫ x : ℝ, Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) + ρ * ppZOmega) ^ (2 * k) *
          ppZTau a (ppZOmega * x + ρ * Complex.I) := by
    rw [← MeasureTheory.integral_add_right_eq_self (fun x : ℝ ↦ ppZKernel a k A (ρ * ppZOmega)
      (x + (ρ / Real.sqrt 2 : ℝ) * Complex.I)) (ρ / Real.sqrt 2)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    have e1 : (((x + ρ / Real.sqrt 2 : ℝ) : ℂ) + (ρ / Real.sqrt 2 : ℝ) * Complex.I) =
        (x : ℂ) + ρ * ppZOmega := by
      rw [ppZOmega_eq]
      push_cast
      field_simp
      ring
    have e2 : ppZOmega * ((x : ℂ) + ρ * ppZOmega) = ppZOmega * x + ρ * Complex.I := by
      linear_combination (ρ : ℂ) * ppZOmega_sq
    simp only [e1, ppZKernel, e2, add_sub_cancel_right]
  rw [h0, hlast, htrans] at hpart
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hpart
  rw [← hpart]
  ring

end AJConjecture
