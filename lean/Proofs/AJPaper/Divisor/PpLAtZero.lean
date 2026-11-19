import Mathlib
import AJPaper.Divisor.PpLIntegral

/-!
# The normal form of the adjoint at `x = 0` (Unit PpL, node `PpL_AtZero`)

Source: Section 5.6 of the paper (`operators.tex`): "At `x = 0`, the right side is
`c(q) q^{s - d_0}`. The coefficients of the Riccati equation there are `(q⁷, -2q⁸, q⁹, 0)`,
giving `r_0(q, 0) = q⁻¹`. Hence `c(q) = q^κ`." Mirror of `AJTwist/Factor/TwFZeroAtZero.lean`.

The values at `x = 0` of the coefficients of the adjoint are
`(p†_0, p†_1, p†_2, p†_3)(t, 0) = (t²⁸, -2 t³², t³⁶, 0)` (the paper's list: the adjoint in the
forward convention has the coefficients of the paper's backward operator), `p†_3` has a double
zero there, and the Riccati equation at `x = 0` is `t²⁸ (1 - t⁴ ρ)² = 0`: `ρ(0) = t⁻⁴ = q⁻¹`.

`ppl_adjoint_value_at_zero`: from the integral normal form with `μ = 2` (the factor `x²`
cancelled) and `∑ ε_j = 2`,

`e₀ · c_d · t⁶⁸ ℓ₃ ℓ₅ · τ(g) = c_n · ∏_{j<4} ℓ_{pplIdx j}^{ε_j} · τ²(e₁) · g`,

and the Riccati equation: `c_d · t^(68 + 4i) = -(c_n · t^(8v + 4))` in `ℤ[t]`, where
`i = g.natTrailingDegree`, `v = e₁.natTrailingDegree`. So `c_n/c_d` is minus a power of
`t⁴ = q`.

Route: as in the template. Write `e₀ = x^(v₀) f₀`, `e₁ = x^v f₁`, `g = x^i γ` with nonzero
values at `x = 0`; comparing orders in the normal form gives `v₀ = v`
(`ℓ_j(0) = -1`, `τ(x^n f) = t^(4n) x^n τ(f)`, `τ` does not change the value at `0`). By
`oreRiccati_mul_left` the pair `(f₀, f₁)` solves the Riccati equation; its value at `x = 0` is
`t²⁸ f₁(0) (f₁(0) + t⁴ f₀(0))²` (coefficients `(t²⁸, -2 t³², t³⁶, 0)` at `0`), so
`f₁(0) = -t⁴ f₀(0)`. The values at `0` of the two sides of the normal form
(`∏ ℓ(0)^{ε} = (-1)² = 1`, `ℓ₃(0) ℓ₅(0) = 1`) give
`f₀(0) c_d t^(68 + 4i) γ(0) = c_n t^(8v) f₁(0) γ(0)`; cancel `f₀(0) γ(0)`.
Checked on generic data (scratch `py/d03_chain.py`, part (a)); the two local branches at
`x = 0` (`ρ(0) = q⁻¹` and the double pole `ρ ∼ q⁻⁴ x⁻²`): scratch `py/d05_branches.py`.

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A nonzero polynomial is `x^v` times a polynomial with nonzero value at `x = 0`, `v` its
order at `x = 0`. -/
private theorem exists_X_pow_mul_pplAtZero {p : Coeff} (hp : p ≠ 0) :
    ∃ f : Coeff, p = X ^ p.natTrailingDegree * f ∧ f.eval 0 ≠ 0 := by
  obtain ⟨f, hf⟩ : X ^ p.natTrailingDegree ∣ p :=
    X_pow_dvd_iff.mpr fun d hd ↦ coeff_eq_zero_of_lt_natTrailingDegree hd
  refine ⟨f, hf, ?_⟩
  have hc := coeff_X_pow_mul f p.natTrailingDegree 0
  rw [← hf] at hc
  rw [← coeff_zero_eq_eval_zero, ← hc, zero_add]
  exact trailingCoeff_ne_zero.mpr hp

/-- The order at `x = 0` and the cofactor are determined (ordered case). -/
private theorem eq_of_X_pow_mul_eq_of_le_pplAtZero {a b : ℕ} (hab : a ≤ b) {A B : Coeff}
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
private theorem eq_of_X_pow_mul_eq_pplAtZero {a b : ℕ} {A B : Coeff}
    (hA : A.eval 0 ≠ 0) (hB : B.eval 0 ≠ 0) (h : X ^ a * A = X ^ b * B) : a = b ∧ A = B := by
  rcases le_total a b with hab | hab
  · exact eq_of_X_pow_mul_eq_of_le_pplAtZero hab hA h
  · obtain ⟨h1, h2⟩ := eq_of_X_pow_mul_eq_of_le_pplAtZero hab hB h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- The shift does not change the value at `x = 0`. -/
private theorem eval_zero_twfShiftX_pplAtZero (c : Coeff) :
    (twfShiftX c).eval 0 = c.eval 0 := by
  change (c.comp (C (X ^ 4) * X)).eval 0 = c.eval 0
  rw [eval_comp, eval_mul, eval_X, mul_zero]

/-- The shift of `x^n f`. -/
private theorem twfShiftX_X_pow_mul_pplAtZero (n : ℕ) (f : Coeff) :
    twfShiftX (X ^ n * f) = C (X ^ (4 * n)) * X ^ n * twfShiftX f := by
  have hX : twfShiftX X = C (X ^ 4) * X := X_comp
  rw [map_mul, map_pow, hX, mul_pow, ← C_pow, ← pow_mul]

/-- The shift fixes the polynomials in `t` alone. -/
private theorem twfShiftX_C_pplAtZero (a : ℤ[X]) : twfShiftX (C a) = C a := C_comp

/-- The value at `x = 0` of the linear forms `ℓ_j`. -/
private theorem eval_zero_twfLin_pplAtZero (j : ℕ) : (twfLin j).eval 0 = -1 := by
  rw [twfLin, eval_sub, eval_mul, eval_X, mul_zero, eval_one, zero_sub]

/-- The values at `x = 0` of the coefficients of the adjoint: `(t²⁸, -2 t³², t³⁶, 0)`. -/
private theorem eval_zero_coeff_pplAdjOpX_pplAtZero :
    (pplAdjOpX.coeff 0).eval 0 = X ^ 28 ∧ (pplAdjOpX.coeff 1).eval 0 = -(2 * X ^ 32) ∧
      (pplAdjOpX.coeff 2).eval 0 = X ^ 36 ∧ (pplAdjOpX.coeff 3).eval 0 = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := coeff_pplAdjOpX_explicit
  rw [h0, h1, h2, h3]
  simp only [twfLin, eval_mul, eval_sub, eval_add, eval_neg, eval_pow, eval_C, eval_X,
    eval_one, eval_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The Riccati equation at `x = 0`: the trailing coefficients satisfy `a₁ = -t⁴ a₀`. -/
private theorem eval_zero_of_oreRiccati_eq_zero_pplAtZero {f₀ f₁ : Coeff}
    (hf₁ : f₁.eval 0 ≠ 0) (hric : oreRiccati twfShiftX 3 pplAdjOpX f₀ f₁ = 0) :
    f₁.eval 0 = -(X ^ 4 * f₀.eval 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := eval_zero_coeff_pplAdjOpX_pplAtZero
  have h := congrArg (Polynomial.eval 0) hric
  simp only [oreRiccati, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, Finset.prod_Ico_eq_prod_range, Nat.sub_self, Nat.add_zero,
    Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Function.iterate_succ_apply,
    Function.iterate_zero_apply, eval_add, eval_mul, eval_zero_twfShiftX_pplAtZero, h0, h1,
    h2, h3, eval_neg, eval_zero, one_mul, mul_one] at h
  have hsq : X ^ 28 * f₁.eval 0 * (f₁.eval 0 + X ^ 4 * f₀.eval 0) ^ 2 = 0 := by
    linear_combination h
  have h28 : (X ^ 28 * f₁.eval 0 : ℤ[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hf₁
  have := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp hsq).resolve_left h28)
  linear_combination this

/-- The integral normal form of the adjoint at `x = 0`: the constant `c_n/c_d` is minus a power
of `t⁴`. -/
theorem ppl_adjoint_value_at_zero {e₀ e₁ g : Coeff} {cn cd : ℤ[X]} {ε : Fin 4 → ℕ}
    (he₀ : e₀ ≠ 0) (he₁ : e₁ ≠ 0) (hg : g ≠ 0) (hcn : cn ≠ 0) (hcd : cd ≠ 0)
    (hric : oreRiccati twfShiftX 3 pplAdjOpX e₀ e₁ = 0) (hε : ∑ j : Fin 4, ε j = 2)
    (hI : e₀ * C cd * (C (X ^ 68) * twfLin 3 * twfLin 5) * twfShiftX g =
      C cn * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) * twfShiftX (twfShiftX e₁) * g) :
    cd * X ^ (68 + 4 * g.natTrailingDegree) = -(cn * X ^ (8 * e₁.natTrailingDegree + 4)) := by
  obtain ⟨f₀, hf₀eq, hf₀⟩ := exists_X_pow_mul_pplAtZero he₀
  obtain ⟨f₁, hf₁eq, hf₁⟩ := exists_X_pow_mul_pplAtZero he₁
  obtain ⟨γ, hγeq, hγ⟩ := exists_X_pow_mul_pplAtZero hg
  generalize e₀.natTrailingDegree = v₀ at hf₀eq
  generalize e₁.natTrailingDegree = v at hf₁eq ⊢
  generalize g.natTrailingDegree = i at hγeq ⊢
  subst hf₀eq hf₁eq hγeq
  have hprod : (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j).eval 0 = 1 := by
    rw [eval_prod]
    simp only [eval_pow, eval_zero_twfLin_pplAtZero, Finset.prod_pow_eq_pow_sum, hε]
    norm_num
  have hA : (f₀ * C cd * (C (X ^ 68) * twfLin 3 * twfLin 5) *
      (C (X ^ (4 * i)) * twfShiftX γ)).eval 0 ≠ 0 := by
    simp only [eval_mul, eval_C, eval_zero_twfLin_pplAtZero, eval_zero_twfShiftX_pplAtZero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hf₀ hcd)
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) (neg_ne_zero.mpr one_ne_zero))
        (neg_ne_zero.mpr one_ne_zero))) (mul_ne_zero (pow_ne_zero _ X_ne_zero) hγ)
  have hB : (C cn * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) *
      (C (X ^ (4 * v)) * (C (X ^ (4 * v)) * twfShiftX (twfShiftX f₁))) * γ).eval 0 ≠ 0 := by
    simp only [eval_mul, eval_C, hprod, eval_zero_twfShiftX_pplAtZero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcn one_ne_zero)
      (mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero (pow_ne_zero _ X_ne_zero) hf₁))) hγ
  have hI' : X ^ (v₀ + i) * (f₀ * C cd * (C (X ^ 68) * twfLin 3 * twfLin 5) *
      (C (X ^ (4 * i)) * twfShiftX γ)) =
      X ^ (v + i) * (C cn * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) *
        (C (X ^ (4 * v)) * (C (X ^ (4 * v)) * twfShiftX (twfShiftX f₁))) * γ) := by
    have hs₁ : twfShiftX (twfShiftX (X ^ v * f₁)) =
        C (X ^ (4 * v)) * X ^ v * (C (X ^ (4 * v)) * twfShiftX (twfShiftX f₁)) := by
      rw [twfShiftX_X_pow_mul_pplAtZero, mul_assoc, map_mul, twfShiftX_C_pplAtZero,
        twfShiftX_X_pow_mul_pplAtZero]
      ring
    rw [hs₁, twfShiftX_X_pow_mul_pplAtZero] at hI
    rw [pow_add, pow_add]
    linear_combination hI
  obtain ⟨hv, hAB⟩ := eq_of_X_pow_mul_eq_pplAtZero hA hB hI'
  have hv₀ : v₀ = v := Nat.add_right_cancel hv
  have hric' : oreRiccati twfShiftX 3 pplAdjOpX f₀ f₁ = 0 := by
    rw [hv₀, oreRiccati_mul_left] at hric
    refine (mul_eq_zero.mp hric).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ h0 ↦ ?_)
    have hinj : Function.Injective twfShiftX := fun a b hab ↦ twfSq_injective (by
      have := congrArg twfSq hab
      rw [twfSq_twfShiftX, twfSq_twfShiftX] at this
      exact coeffShift_injective this)
    exact pow_ne_zero v X_ne_zero (hinj.iterate k (by rw [h0, iterate_map_zero]))
  have ha₁ := eval_zero_of_oreRiccati_eq_zero_pplAtZero hf₁ hric'
  have hev := congrArg (Polynomial.eval 0) hAB
  simp only [eval_mul, eval_C, eval_zero_twfLin_pplAtZero, hprod,
    eval_zero_twfShiftX_pplAtZero, ha₁] at hev
  refine mul_right_cancel₀ (mul_ne_zero hf₀ hγ) ?_
  linear_combination hev

end AJConjecture
