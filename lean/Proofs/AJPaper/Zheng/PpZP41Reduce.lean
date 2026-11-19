import Mathlib
import AJPaper.Zheng.PpZP41Defs

/-!
# `A⁺_{a,2}(N, 1)` as a sum over `a`-th roots of unity (Unit PpZ, node `PpZ_P41Reduce`)

Source: Zheng, (4.2) and (4.17), `q = 2`.

`ppZ_zhengA_eq_conjSum`: for odd `a` and `8u ≡ 1 (mod a)`,
`A⁺_{a,2}(N, 1) = -2a i · e^{-πi(N+4)/(4a)} · ζ_a^{u(N+4)} · R(u)`.

Route. Only odd `j = 2l + 1` contribute (`sin(jπ/2) = (-1)^l`, and `0` for even `j`):
`A = ∑_{l<a} (2l+1)² g(l)`, `g(l) = (-1)^l sin((2l+1)π/a) e^{-πiN(2l+1)²/(4a)}`.
* `g(a-1-l) = -g(l)` (`j ↦ 2a - j`: the sine changes sign, `(-1)^{a-1-l} = (-1)^l` for odd `a`,
  `e^{-πiN(2a-j)²/(4a)} = e^{-πiNj²/(4a)} e^{-πiN(a-j)}` and `a - j` is even). Hence
  `A = ½ ∑ ((2l+1)² - (2a-2l-1)²) g(l) = -2a ∑_l (a - 1 - 2l) g(l)`.
* Write `sin(jπ/a) = (e^{iπj/a} - e^{-iπj/a})/(2i)`; `w_l = (a-1-2l)(-1)^l` satisfies
  `w_{a-1-l} = -w_l`, and `l ↦ a-1-l` swaps `e^{±iπj/a}`; so
  `∑_l w_l y^{j²} (e^{iπj/a} - e^{-iπj/a}) = -2 ∑_l w_l y^{j²} e^{-iπj/a}` and
  `A = -2a i ∑_l w_l e^{πi E(l)/(4a)}`, `E(l) = -Nj² - 4j`.
* `E(l) + N + 4 = -4N l(l+1) - 8l` is divisible by `8`; with `8u ≡ 1 (mod a)`,
  `e^{πi E/(4a)} = e^{-πi(N+4)/(4a)} ζ_a^{(E+N+4)/8} = e^{-πi(N+4)/(4a)} ζ_a^{u(E+N+4)}`.

Checked numerically for `a ∈ {1, 3, 5, 7, 9, 15, 21, 25, 27, 45}`, `-a ≤ N ≤ 2a + 2`
(relative error `5·10⁻¹¹`, `scaf.py`).
-/

noncomputable section

namespace AJConjecture

/-- Splitting a sum over `range (2a)` into even and odd indices. -/
private theorem sum_range_two_mul_P41Reduce (f : ℕ → ℂ) (a : ℕ) :
    ∑ j ∈ Finset.range (2 * a), f j = ∑ l ∈ Finset.range a, (f (2 * l) + f (2 * l + 1)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- `A⁺_{a,2}(N, 1)` as a sum over the odd `j = 2l + 1`. -/
private theorem zhengA_eq_sum_odd_P41Reduce (a : ℕ) (ha : 1 ≤ a) (N : ℤ) :
    geoZhengA a N 1 = ∑ l ∈ Finset.range a,
      Complex.exp (-(N : ℂ) * ((2 * l + 1 : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) *
        ((2 * l + 1 : ℕ) : ℂ) ^ 2 * Real.sin ((2 * l + 1 : ℕ) * Real.pi / a) * (-1) ^ l := by
  set f : ℕ → ℂ := fun j ↦
    Complex.exp (-(N : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) * (j : ℂ) ^ (2 * 1) *
      Real.sin (j * Real.pi / a) * Real.sin (j * Real.pi / 2) with hf
  have hIcc : Finset.Icc 1 (2 * a - 1) = Finset.Ico (0 + 1) (2 * a) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have h0 : f 0 = 0 := by simp [hf]
  have heven : ∀ l, f (2 * l) = 0 := by
    intro l
    have hsin : Real.sin (((2 * l : ℕ) : ℝ) * Real.pi / 2) = 0 := by
      rw [show ((2 * l : ℕ) : ℝ) * Real.pi / 2 = l * Real.pi by push_cast; ring]
      exact Real.sin_nat_mul_pi l
    simp only [hf, hsin, Complex.ofReal_zero, mul_zero]
  have hodd : ∀ l : ℕ, Real.sin (((2 * l + 1 : ℕ) : ℝ) * Real.pi / 2) = (-1) ^ l := by
    intro l
    rw [show ((2 * l + 1 : ℕ) : ℝ) * Real.pi / 2 = l * Real.pi + Real.pi / 2 by push_cast; ring,
      Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  have hsum := Finset.sum_eq_sum_Ico_succ_bot (show 0 < 2 * a by omega) f
  rw [← Finset.range_eq_Ico, h0, zero_add, sum_range_two_mul_P41Reduce] at hsum
  rw [geoZhengA, hIcc, ← hsum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [heven, zero_add]
  simp only [hf, hodd, mul_one, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]

/-- The summand with `e^{-iπj/a}`. -/
private def termMinus_P41Reduce (a : ℕ) (N : ℤ) (j : ℂ) : ℂ :=
  Complex.exp (-(N : ℂ) * j ^ 2 * Real.pi * Complex.I / (4 * a)) *
    Complex.exp (-(j * Real.pi / a) * Complex.I)

/-- The summand with `e^{iπj/a}`. -/
private def termPlus_P41Reduce (a : ℕ) (N : ℤ) (j : ℂ) : ℂ :=
  Complex.exp (-(N : ℂ) * j ^ 2 * Real.pi * Complex.I / (4 * a)) *
    Complex.exp (j * Real.pi / a * Complex.I)

/-- The sine written with exponentials. -/
private theorem sin_term_P41Reduce (a : ℕ) (N : ℤ) (j : ℕ) (σ : ℂ) :
    Complex.exp (-(N : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) * (j : ℂ) ^ 2 *
        Real.sin (j * Real.pi / a) * σ =
      σ * (j : ℂ) ^ 2 * (Complex.I / 2) *
        (termMinus_P41Reduce a N j - termPlus_P41Reduce a N j) := by
  rw [Complex.ofReal_sin, Complex.sin, termMinus_P41Reduce, termPlus_P41Reduce]
  push_cast
  ring

/-- The reflection `j ↦ 2a - j` exchanges the two kinds of summands. -/
private theorem termPlus_reflect_P41Reduce {a : ℕ} (hodd : Odd a) (N : ℤ) {l : ℕ} (hl : l < a) :
    termPlus_P41Reduce a N (2 * (a : ℂ) - (2 * l + 1)) =
      termMinus_P41Reduce a N (2 * l + 1) := by
  obtain ⟨k, rfl⟩ := hodd
  have ha' : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [termPlus_P41Reduce, termMinus_P41Reduce, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-N * ((k : ℤ) - l) + 1, ?_⟩
  push_cast at ha' ⊢
  field_simp
  ring

/-- Each summand is a fixed unit times `ζ_a^{u E(l)}`. -/
private theorem termMinus_eq_P41Reduce {a : ℕ} (ha : 1 ≤ a) (N u : ℤ)
    (hu : 8 * u ≡ 1 [ZMOD (a : ℤ)]) (l : ℕ) :
    termMinus_P41Reduce a N (2 * l + 1) =
      Complex.exp (-(Real.pi * Complex.I * ((N : ℂ) + 4) / (4 * a))) *
        ppZRoot a (u * (N + 4)) * ppZRoot a (u * ppZExp N l) := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨T, hT⟩ : ∃ T : ℤ, (l : ℤ) * (l + 1) = 2 * T := by
    obtain ⟨T, hT⟩ := Int.even_mul_succ_self (l : ℤ)
    exact ⟨T, by rw [hT]; ring⟩
  set K : ℤ := -N * T - l with hK
  have hK8 : ppZExp N l + N + 4 = 8 * K := by
    rw [ppZExp, hK]
    linear_combination (-4 * N) * hT
  have hmod : u * (N + 4) + u * ppZExp N l ≡ K [ZMOD (a : ℤ)] := by
    have h1 : u * (N + 4) + u * ppZExp N l = 8 * u * K := by linear_combination u * hK8
    rw [h1]
    simpa using hu.mul_right K
  have hKc : (K : ℂ) = ((ppZExp N l : ℂ) + N + 4) / 8 := by
    have h2 : ((ppZExp N l + N + 4 : ℤ) : ℂ) = ((8 * K : ℤ) : ℂ) := by rw [hK8]
    push_cast at h2
    rw [h2]
    ring
  rw [mul_assoc, ← ppZRoot_add, ppZRoot_eq_of_modEq ha hmod, ppZRoot, hKc, termMinus_P41Reduce,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [ppZExp]
  push_cast
  field_simp
  ring

/-- `A⁺_{a,2}(N, 1) = -2a i e^{-πi(N+4)/(4a)} ζ_a^{u(N+4)} R(u)` for odd `a`, `8u ≡ 1 (mod a)`. -/
theorem ppZ_zhengA_eq_conjSum (a : ℕ) (hodd : Odd a) (N u : ℤ) (hu : 8 * u ≡ 1 [ZMOD (a : ℤ)]) :
    geoZhengA a N 1 =
      -(2 * (a : ℂ)) * Complex.I *
        Complex.exp (-(Real.pi * Complex.I * ((N : ℂ) + 4) / (4 * a))) *
        ppZRoot a (u * (N + 4)) * ppZConjSum a N u := by
  have ha : 1 ≤ a := hodd.pos
  have hcast : ∀ l : ℕ, ((2 * l + 1 : ℕ) : ℂ) = 2 * (l : ℂ) + 1 := fun l ↦ by push_cast; ring
  set G : ℕ → ℂ := fun l ↦ (-1) ^ l * (2 * (l : ℂ) + 1) ^ 2 * (Complex.I / 2) *
    termPlus_P41Reduce a N (2 * l + 1) with hG
  have hreflect : ∑ l ∈ Finset.range a, G l = ∑ l ∈ Finset.range a,
      (-1) ^ l * (2 * (a : ℂ) - (2 * l + 1)) ^ 2 * (Complex.I / 2) *
        termMinus_P41Reduce a N (2 * l + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' : l < a := Finset.mem_range.mp hl
    have hsign : (-1 : ℂ) ^ (a - 1 - l) = (-1) ^ l := by
      obtain ⟨k, rfl⟩ := hodd
      rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := l)]
      congr 1
      omega
    have hj : 2 * ((a - 1 - l : ℕ) : ℂ) + 1 = 2 * (a : ℂ) - (2 * l + 1) := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [hG, hsign, hj, termPlus_reflect_P41Reduce hodd N hl']
  have hterm : ∀ l : ℕ,
      Complex.exp (-(N : ℂ) * ((2 * l + 1 : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) *
        ((2 * l + 1 : ℕ) : ℂ) ^ 2 * Real.sin ((2 * l + 1 : ℕ) * Real.pi / a) * (-1) ^ l =
      (-1) ^ l * (2 * (l : ℂ) + 1) ^ 2 * (Complex.I / 2) *
        termMinus_P41Reduce a N (2 * l + 1) - G l := by
    intro l
    rw [sin_term_P41Reduce, hcast, hG]
    ring
  rw [zhengA_eq_sum_odd_P41Reduce a ha N]
  simp only [hterm, Finset.sum_sub_distrib]
  rw [hreflect, ← Finset.sum_sub_distrib, ppZConjSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [termMinus_eq_P41Reduce ha N u hu l, ppZWeight]
  push_cast
  ring

end AJConjecture
