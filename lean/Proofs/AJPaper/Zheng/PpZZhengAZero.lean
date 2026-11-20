import Mathlib
import AJHandoff.Geometry.GeoPhysDefs
import AJPaper.Zheng.PpZKernelPole

/-!
# The residue sums are Zheng's `A⁺_{a,2}(N, k)`; `A⁺_{a,2}(N, 0) = 0`
(Unit PpZ, node `PpZ_ZhengAZero`)

Source: Zheng, (4.2), (5.10) and (5.14)–(5.15).

* `ppZ_zhengA_zero`: `A⁺_{a,2}(N, 0) = 0` for odd `a` and every integer `N`. (Zheng obtains this
  indirectly from `Ĵ_N(e^{2πi/N}) = 0`; for `q = 2` it is a symmetry.) Route: the terms with even
  `j` vanish (`sin(jπ/2) = 0`); `j ↦ 2a - j` is an involution of the odd `j ∈ [1, 2a-1]` under
  which `e^{-Nj²πi/(4a)}` is invariant (`(2a-j)² - j² = 4a(a-j)`, `a - j` even), `sin(jπ/2)` is
  invariant (`a` odd) and `sin(jπ/a)` changes sign; the fixed point `j = a` has `sin π = 0`
  (`Finset.sum_involution`, or reflect the sum with `Finset.sum_flip`-type reindexing).
* `ppZ_kernelRes_sum`: for odd `c`, `A = aN/π`, `x₀ = (πc/N)ω`,
  `∑_{j<a} Res_j = -e^{-iπac²/N} (ωπ/(2a))^{2k}/(aω) · A⁺_{a,2}(N, k)`.
  Route: `-A(w_j - x₀)² = -iA(θ_j - πc/N)²`, `θ_j = (2j+1)π/(2a)`, equals
  `-iπN(2j+1)²/(4a) + iπ(2j+1)c - iπac²/N`, and `e^{iπ(2j+1)c} = -1` (odd·odd). In `geoZhengA`
  only the odd `j' = 2j+1` contribute, with `sin(j'π/2) = (-1)^j`
  (`Finset.sum_bij`/`Finset.sum_filter` over odd indices of `Finset.Icc 1 (2a-1)`).
Checked numerically: `|A⁺(N,0)| < 10⁻¹²` and the residue identity to `10⁻¹²` (`strip.py`).
-/

noncomputable section

namespace AJConjecture

/-- `sin(2m · π/2) = 0`. -/
private theorem sin_even_ppZZhengAZero (m : ℕ) :
    Real.sin (((2 * m : ℕ) : ℝ) * Real.pi / 2) = 0 := by
  rw [show ((2 * m : ℕ) : ℝ) * Real.pi / 2 = m * Real.pi by push_cast; ring]
  exact Real.sin_nat_mul_pi m

/-- `sin((2j+1) · π/2) = (-1)^j`. -/
private theorem sin_odd_ppZZhengAZero (j : ℕ) :
    Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi / 2) = (-1) ^ j := by
  rw [show ((2 * j + 1 : ℕ) : ℝ) * Real.pi / 2 = j * Real.pi + Real.pi / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- The summand of `A⁺_{a,2}(N, 0)` changes sign under `j ↦ 2a - j` (`a` odd). -/
private theorem zhengA_term_reflect_ppZZhengAZero (a : ℕ) (hodd : Odd a) (N : ℤ) (j : ℕ)
    (hj : j ≤ 2 * a) :
    Complex.exp (-(N : ℂ) * ((2 * a - j : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) *
        Real.sin (((2 * a - j : ℕ) : ℝ) * Real.pi / a) *
        Real.sin (((2 * a - j : ℕ) : ℝ) * Real.pi / 2) =
      -(Complex.exp (-(N : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) *
        Real.sin ((j : ℝ) * Real.pi / a) * Real.sin ((j : ℝ) * Real.pi / 2)) := by
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · rw [sin_even_ppZZhengAZero, show 2 * a - 2 * m = 2 * (a - m) by omega,
      sin_even_ppZZhengAZero]
    simp
  · have ha0 : 0 < a := hodd.pos
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    obtain ⟨t, ht⟩ : Even ((a : ℤ) - (2 * m + 1 : ℕ)) :=
      (hodd.natCast).sub_odd ((odd_two_mul_add_one m).natCast)
    have htC : (((2 * m + 1 : ℕ) : ℂ)) = a - (t + t) := by
      have := congrArg (Int.cast : ℤ → ℂ) ht
      push_cast at this ⊢
      linear_combination (-1 : ℂ) * this
    have hX : -(N : ℂ) * ((2 * a - (2 * m + 1) : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a) =
        -(N : ℂ) * ((2 * m + 1 : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a) +
          ((-N * t : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [Nat.cast_sub hj, htC]
      push_cast
      field_simp
      ring
    have h1 : Real.sin (((2 * a - (2 * m + 1) : ℕ) : ℝ) * Real.pi / a) =
        -Real.sin (((2 * m + 1 : ℕ) : ℝ) * Real.pi / a) := by
      rw [← Real.sin_two_pi_sub, Nat.cast_sub hj]
      congr 1
      push_cast
      field_simp
    have h2 : Real.sin (((2 * a - (2 * m + 1) : ℕ) : ℝ) * Real.pi / 2) =
        Real.sin (((2 * m + 1 : ℕ) : ℝ) * Real.pi / 2) := by
      have e : ((2 * a - (2 * m + 1) : ℕ) : ℝ) * Real.pi / 2 =
          a * Real.pi - ((2 * m + 1 : ℕ) : ℝ) * Real.pi / 2 := by
        rw [Nat.cast_sub hj]
        push_cast
        ring
      rw [e, Real.sin_nat_mul_pi_sub, hodd.neg_one_pow]
      ring
    rw [hX, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, h1, h2]
    push_cast
    ring

/-- A sum over `[1, 2a-1]` of a function vanishing at even arguments is the sum over the odd
arguments `2j + 1`, `j < a`. -/
private theorem sum_Icc_odd_ppZZhengAZero (a : ℕ) (F : ℕ → ℂ) (hF : ∀ m, F (2 * m) = 0) :
    ∑ j ∈ Finset.Icc 1 (2 * a - 1), F j = ∑ j ∈ Finset.range a, F (2 * j + 1) := by
  have hinj : Set.InjOn (fun j : ℕ ↦ 2 * j + 1) (Finset.range a) := fun x _ y _ h ↦ by
    simpa using h
  have h1 : ∑ j' ∈ (Finset.range a).image (fun j ↦ 2 * j + 1), F j' =
      ∑ j ∈ Finset.range a, F (2 * j + 1) := Finset.sum_image hinj
  rw [← h1]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [Finset.mem_Icc]
    omega
  · intro x hx hnx
    rw [Finset.mem_Icc] at hx
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hnx
    rcases Nat.even_or_odd' x with ⟨m, rfl | rfl⟩
    · exact hF m
    · exact absurd rfl (hnx m (by omega))

/-- `e^{πi m} = -1` for odd `m`. -/
private theorem exp_odd_pi_ppZZhengAZero (m : ℕ) (hm : Odd m) :
    Complex.exp (Real.pi * Complex.I * m) = -1 := by
  obtain ⟨t, rfl⟩ := hm
  have h : (Real.pi * Complex.I * ((2 * t + 1 : ℕ) : ℂ)) =
      Real.pi * Complex.I + t * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- `e^{-A(w_j - x₀)²} = -e^{-iπac²/N} e^{-iπN(2j+1)²/(4a)}` for odd `c`. -/
private theorem kernelRes_exp_ppZZhengAZero (a N c : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) (hc : Odd c)
    (j : ℕ) :
    Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) *
        (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a)) -
          ((Real.pi * c / N : ℝ) : ℂ) * ppZOmega) ^ 2) =
      -(Complex.exp (-(Real.pi * Complex.I * a * (c : ℂ) ^ 2 / N)) *
        Complex.exp (-((N : ℤ) : ℂ) * ((2 * j + 1 : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I /
          (4 * a))) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 := exp_odd_pi_ppZZhengAZero ((2 * j + 1) * c) ((odd_two_mul_add_one j).mul hc)
  have key : Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) *
        (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a)) -
          ((Real.pi * c / N : ℝ) : ℂ) * ppZOmega) ^ 2) =
      Complex.exp (-(Real.pi * Complex.I * a * (c : ℂ) ^ 2 / N)) *
        Complex.exp (-((N : ℤ) : ℂ) * ((2 * j + 1 : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I /
          (4 * a)) * Complex.exp (Real.pi * Complex.I * ((2 * j + 1) * c : ℕ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← ppZOmega_sq]
    congr 1
    push_cast
    field_simp
    ring
  rw [key, h1]
  ring

/-- `A⁺_{a,2}(N, 0) = 0` for odd `a`. -/
theorem ppZ_zhengA_zero (a : ℕ) (hodd : Odd a) (N : ℤ) : geoZhengA a N 0 = 0 := by
  have h : geoZhengA a N 0 = -geoZhengA a N 0 := by
    unfold geoZhengA
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun j ↦ 2 * a - j) (fun j ↦ 2 * a - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      simp only [mul_zero, pow_zero, mul_one]
      rw [zhengA_term_reflect_ppZZhengAZero a hodd N j (by omega), neg_neg]
  exact self_eq_neg.mp h

/-- The sum of the `a` residues is `-e^{-iπac²/N} (ωπ/(2a))^{2k}/(aω) · A⁺_{a,2}(N, k)`. -/
theorem ppZ_kernelRes_sum (a k N c : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) (hc : Odd c) :
    ∑ j ∈ Finset.range a,
        ppZKernelRes a k (a * N / Real.pi) (((Real.pi * c / N : ℝ) : ℂ) * ppZOmega) j =
      -Complex.exp (-(Real.pi * Complex.I * a * (c : ℂ) ^ 2 / N)) *
        (ppZOmega * Real.pi / (2 * a)) ^ (2 * k) / (a * ppZOmega) * geoZhengA a N k := by
  have hA : geoZhengA a N k = ∑ j ∈ Finset.range a,
      Complex.exp (-((N : ℤ) : ℂ) * ((2 * j + 1 : ℕ) : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) *
        ((2 * j + 1 : ℕ) : ℂ) ^ (2 * k) * Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi / a) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi / 2) :=
    sum_Icc_odd_ppZZhengAZero a _ fun m ↦ by
      rw [sin_even_ppZZhengAZero]
      simp
  rw [hA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hp : (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a))) ^ (2 * k) =
      (ppZOmega * Real.pi / (2 * a)) ^ (2 * k) * ((2 * j + 1 : ℕ) : ℂ) ^ (2 * k) := by
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  rw [ppZKernelRes, kernelRes_exp_ppZZhengAZero a N c ha hN hc, sin_odd_ppZZhengAZero, hp]
  push_cast
  ring

end AJConjecture
