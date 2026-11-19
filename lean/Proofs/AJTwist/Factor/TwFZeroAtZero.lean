import Mathlib
import AJTwist.Factor.TwFZeroIntegral

/-!
# The normal form at `x = 0` (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`): "Put `d_0 = ord_{x=0} g`, `s = ∑ k n_k`. At
`x = 0`, the right side is `c(q) q^{s - d_0}`. The coefficients of the Riccati equation there are
`(q⁷, -2q⁸, q⁹, 0)`, giving `r_0(q, 0) = q⁻¹`. Hence `c(q) = q^κ` with `κ = -1 - s + d_0 ∈ ℤ`."

In the forward convention the coefficients at `x = 0` are `(p_0, p_1, p_2, p_3)(q, 0) =
(0, q⁹, -2q⁸, q⁷)` and the Riccati equation there is `q⁷ ρ (q - ρ)² = 0`, so `ρ(0) = q`.

`twf_zero_value_at_zero`: from the integral normal form with `μ = 0`, `∑ ε_j = 2`,

`-e₀ · c_d · t²⁸ ℓ₁ ℓ₃ · τ(g) = c_n · ∏_{j<4} ℓ_j^{ε_j} · τ²(e₁) · g`,

and the Riccati equation: `c_d · t^(32 + 4 i) = c_n · t^(8 v)` in `ℤ[t]`, where
`i = g.natTrailingDegree` and `v = e₁.natTrailingDegree` are the orders at `x = 0`. So `c_n/c_d`
is a power of `t⁴ = q`: the paper's `c(q) = q^κ`.

Route: `Polynomial.natTrailingDegree`, `trailingCoeff` are multiplicative on the domain
`ℤ[t][x]` (`Polynomial.natTrailingDegree_mul`, `trailingCoeff_mul`); `ℓ_j` and `C (t²⁸)` have
order `0` with trailing coefficients `-1`, `t²⁸`; the trailing coefficient of `τ(f)` is `t^(4 i)`
times that of `f`, with the same order. Comparing orders in the normal form gives
`ord e₀ = ord e₁ = v`. The Riccati polynomial is a sum of four terms of orders `2 + 3v`, `3v`,
`3v`, `3v` (`p_0` has a double zero at `x = 0`, `coeff_twfZeroOpX_ends`; `p_1, p_2, p_3` have
the values `t³⁶, -2t³², t²⁸` there), and its coefficient of `x^(3v)` is
`-t^(12 v) e₀' · t²⁸ (t⁴ e₁' + e₀')²` for the trailing coefficients `e₀'`, `e₁'`; hence
`e₀' = -t⁴ e₁'`. Comparing the trailing coefficients of the normal form
(`∏ ℓ_j(0)^{ε_j} = (-1)² = 1`, `ℓ₁(0) ℓ₃(0) = 1`) and cancelling `e₁' g'` gives the claim.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A nonzero polynomial is `x^v` times a polynomial with nonzero value at `x = 0`, `v` its
order at `x = 0`. -/
private theorem exists_X_pow_mul_twfZeroAtZero {p : Coeff} (hp : p ≠ 0) :
    ∃ f : Coeff, p = X ^ p.natTrailingDegree * f ∧ f.eval 0 ≠ 0 := by
  obtain ⟨f, hf⟩ : X ^ p.natTrailingDegree ∣ p :=
    X_pow_dvd_iff.mpr fun d hd ↦ coeff_eq_zero_of_lt_natTrailingDegree hd
  refine ⟨f, hf, ?_⟩
  have hc := coeff_X_pow_mul f p.natTrailingDegree 0
  rw [← hf] at hc
  rw [← coeff_zero_eq_eval_zero, ← hc, zero_add]
  exact trailingCoeff_ne_zero.mpr hp

/-- The order at `x = 0` and the cofactor are determined (ordered case). -/
private theorem eq_of_X_pow_mul_eq_of_le_twfZeroAtZero {a b : ℕ} (hab : a ≤ b) {A B : Coeff}
    (hA : A.eval 0 ≠ 0) (h : X ^ a * A = X ^ b * B) : a = b ∧ A = B := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_assoc] at h
  have hAB : A = X ^ d * B := mul_left_cancel₀ (pow_ne_zero a X_ne_zero) h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pow_zero, one_mul] at hAB
    exact ⟨rfl, hAB⟩
  · exfalso
    apply hA
    rw [hAB, eval_mul, eval_pow, eval_X, zero_pow hd.ne', zero_mul]

/-- The order at `x = 0` and the cofactor are determined. -/
private theorem eq_of_X_pow_mul_eq_twfZeroAtZero {a b : ℕ} {A B : Coeff}
    (hA : A.eval 0 ≠ 0) (hB : B.eval 0 ≠ 0) (h : X ^ a * A = X ^ b * B) : a = b ∧ A = B := by
  rcases le_total a b with hab | hab
  · exact eq_of_X_pow_mul_eq_of_le_twfZeroAtZero hab hA h
  · obtain ⟨h1, h2⟩ := eq_of_X_pow_mul_eq_of_le_twfZeroAtZero hab hB h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- The shift does not change the value at `x = 0`. -/
private theorem eval_zero_twfShiftX_twfZeroAtZero (c : Coeff) :
    (twfShiftX c).eval 0 = c.eval 0 := by
  change (c.comp (C (X ^ 4) * X)).eval 0 = c.eval 0
  rw [eval_comp, eval_mul, eval_X, mul_zero]

/-- The shift of `x^n f`. -/
private theorem twfShiftX_X_pow_mul_twfZeroAtZero (n : ℕ) (f : Coeff) :
    twfShiftX (X ^ n * f) = C (X ^ (4 * n)) * X ^ n * twfShiftX f := by
  have hX : twfShiftX X = C (X ^ 4) * X := X_comp
  rw [map_mul, map_pow, hX, mul_pow, ← C_pow, ← pow_mul]

/-- The shift fixes the polynomials in `t` alone. -/
private theorem twfShiftX_C_twfZeroAtZero (a : ℤ[X]) : twfShiftX (C a) = C a := C_comp

/-- The value at `x = 0` of the linear forms `ℓ_j`. -/
private theorem eval_zero_twfLin_twfZeroAtZero (j : ℕ) : (twfLin j).eval 0 = -1 := by
  rw [twfLin, eval_sub, eval_mul, eval_X, mul_zero, eval_one, zero_sub]

/-- The values at `x = 0` of the coefficients of the explicit operator:
`(0, t³⁶, -2 t³², t²⁸)`. -/
private theorem eval_zero_coeff_twfZeroOpX_twfZeroAtZero :
    (twfZeroOpX.coeff 0).eval 0 = 0 ∧ (twfZeroOpX.coeff 1).eval 0 = X ^ 36 ∧
      (twfZeroOpX.coeff 2).eval 0 = -(2 * X ^ 32) ∧ (twfZeroOpX.coeff 3).eval 0 = X ^ 28 := by
  have hc : ∀ k : Fin 4, (twfZeroOpX.coeff (k : ℕ)).eval 0 =
      (twZeroB (X ^ 4 : ℤ[X]) (Fin.rev k)).eval 0 := by
    intro k
    rw [twfZeroOpX, finsetSum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one, eval_comp, eval_mul, eval_X,
        mul_zero]
    · intro j _ hj
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h ↦ hj (Fin.ext h.symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
    at h0 h1 h2 h3
  rw [h0, h1, h2, h3]
  simp only [twZeroB, show Fin.rev (0 : Fin 4) = 3 from rfl,
    show Fin.rev (1 : Fin 4) = 2 from rfl, show Fin.rev (2 : Fin 4) = 1 from rfl,
    show Fin.rev (3 : Fin 4) = 0 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, eval_mul,
    eval_sub, eval_add, eval_neg, eval_pow, eval_C, eval_X, eval_one, eval_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The Riccati equation at `x = 0`: the trailing coefficients satisfy `a₀ = -t⁴ a₁`. -/
private theorem eval_zero_of_oreRiccati_eq_zero_twfZeroAtZero {f₀ f₁ : Coeff}
    (hf₀ : f₀.eval 0 ≠ 0) (hric : oreRiccati twfShiftX 3 twfZeroOpX f₀ f₁ = 0) :
    f₀.eval 0 = -(X ^ 4 * f₁.eval 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := eval_zero_coeff_twfZeroOpX_twfZeroAtZero
  have h := congrArg (Polynomial.eval 0) hric
  simp only [oreRiccati, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, Finset.prod_Ico_eq_prod_range, Nat.sub_self, Nat.add_zero,
    Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Function.iterate_succ_apply,
    Function.iterate_zero_apply, eval_add, eval_mul, eval_zero_twfShiftX_twfZeroAtZero, h0, h1,
    h2, h3, eval_neg, eval_zero, one_mul, mul_one] at h
  have hsq : X ^ 28 * f₀.eval 0 * (X ^ 4 * f₁.eval 0 + f₀.eval 0) ^ 2 = 0 := by
    linear_combination -h
  have h28 : (X ^ 28 * f₀.eval 0 : ℤ[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hf₀
  have := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp hsq).resolve_left h28)
  linear_combination this

/-- The integral normal form at `x = 0`: the constant `c_n/c_d` is a power of `t⁴`. -/
theorem twf_zero_value_at_zero {e₀ e₁ g : Coeff} {cn cd : ℤ[X]} {ε : Fin 4 → ℕ}
    (he₀ : e₀ ≠ 0) (he₁ : e₁ ≠ 0) (hg : g ≠ 0) (hcn : cn ≠ 0) (hcd : cd ≠ 0)
    (hric : oreRiccati twfShiftX 3 twfZeroOpX e₀ e₁ = 0) (hε : ∑ j : Fin 4, ε j = 2)
    (hI : -e₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g =
      C cn * (∏ j : Fin 4, twfLin j ^ ε j) * twfShiftX (twfShiftX e₁) * g) :
    cd * X ^ (32 + 4 * g.natTrailingDegree) = cn * X ^ (8 * e₁.natTrailingDegree) := by
  obtain ⟨f₀, hf₀eq, hf₀⟩ := exists_X_pow_mul_twfZeroAtZero he₀
  obtain ⟨f₁, hf₁eq, hf₁⟩ := exists_X_pow_mul_twfZeroAtZero he₁
  obtain ⟨γ, hγeq, hγ⟩ := exists_X_pow_mul_twfZeroAtZero hg
  generalize e₀.natTrailingDegree = v₀ at hf₀eq
  generalize e₁.natTrailingDegree = v at hf₁eq ⊢
  generalize g.natTrailingDegree = i at hγeq ⊢
  subst hf₀eq hf₁eq hγeq
  have hprod : (∏ j : Fin 4, twfLin j ^ ε j).eval 0 = 1 := by
    rw [eval_prod]
    simp only [eval_pow, eval_zero_twfLin_twfZeroAtZero, Finset.prod_pow_eq_pow_sum, hε]
    norm_num
  have hA : (-f₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) *
      (C (X ^ (4 * i)) * twfShiftX γ)).eval 0 ≠ 0 := by
    simp only [eval_mul, eval_neg, eval_C, eval_zero_twfLin_twfZeroAtZero,
      eval_zero_twfShiftX_twfZeroAtZero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hf₀) hcd)
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) (neg_ne_zero.mpr one_ne_zero))
        (neg_ne_zero.mpr one_ne_zero))) (mul_ne_zero (pow_ne_zero _ X_ne_zero) hγ)
  have hB : (C cn * (∏ j : Fin 4, twfLin j ^ ε j) *
      (C (X ^ (4 * v)) * (C (X ^ (4 * v)) * twfShiftX (twfShiftX f₁))) * γ).eval 0 ≠ 0 := by
    simp only [eval_mul, eval_C, hprod, eval_zero_twfShiftX_twfZeroAtZero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcn one_ne_zero)
      (mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero (pow_ne_zero _ X_ne_zero) hf₁))) hγ
  have hI' : X ^ (v₀ + i) * (-f₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) *
      (C (X ^ (4 * i)) * twfShiftX γ)) =
      X ^ (v + i) * (C cn * (∏ j : Fin 4, twfLin j ^ ε j) *
        (C (X ^ (4 * v)) * (C (X ^ (4 * v)) * twfShiftX (twfShiftX f₁))) * γ) := by
    have hs₁ : twfShiftX (twfShiftX (X ^ v * f₁)) =
        C (X ^ (4 * v)) * X ^ v * (C (X ^ (4 * v)) * twfShiftX (twfShiftX f₁)) := by
      rw [twfShiftX_X_pow_mul_twfZeroAtZero, mul_assoc, map_mul,
        twfShiftX_C_twfZeroAtZero, twfShiftX_X_pow_mul_twfZeroAtZero]
      ring
    rw [hs₁, twfShiftX_X_pow_mul_twfZeroAtZero] at hI
    rw [pow_add, pow_add]
    linear_combination hI
  obtain ⟨hv, hAB⟩ := eq_of_X_pow_mul_eq_twfZeroAtZero hA hB hI'
  have hv₀ : v₀ = v := Nat.add_right_cancel hv
  have hric' : oreRiccati twfShiftX 3 twfZeroOpX f₀ f₁ = 0 := by
    rw [hv₀, oreRiccati_mul_left] at hric
    refine (mul_eq_zero.mp hric).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ h0 ↦ ?_)
    have hinj : Function.Injective twfShiftX := fun a b hab ↦ twfSq_injective (by
      have := congrArg twfSq hab
      rw [twfSq_twfShiftX, twfSq_twfShiftX] at this
      exact coeffShift_injective this)
    exact pow_ne_zero v X_ne_zero (hinj.iterate k (by rw [h0, iterate_map_zero]))
  have ha₀ := eval_zero_of_oreRiccati_eq_zero_twfZeroAtZero hf₀ hric'
  have hev := congrArg (Polynomial.eval 0) hAB
  simp only [eval_mul, eval_neg, eval_C, eval_zero_twfLin_twfZeroAtZero, hprod,
    eval_zero_twfShiftX_twfZeroAtZero, ha₀] at hev
  refine mul_right_cancel₀ (mul_ne_zero hf₁ hγ) ?_
  linear_combination hev

end AJConjecture
