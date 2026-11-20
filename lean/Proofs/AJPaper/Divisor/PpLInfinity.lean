import Mathlib
import AJPaper.Divisor.PpLJetRules
import AJPaper.Divisor.PpLReduce
import AJPaper.Divisor.PpLAtZero

/-!
# The contradiction at infinity for the adjoint (Unit PpL, node `PpL_Infinity`, crux)

Source: Section 5.6 of the paper (`operators.tex`): "On the other hand eq. (riccati-normal)
gives `f(x) = κ - s/(x - 1) - x g_0'(x)/g_0(x)`. At infinity this has integer limit … The actual
first-order equation gives limit `1/2`. This contradiction excludes linear right factors". For a
left factor the actual limit is `3/2` (Section 5.5, the left exponent `s_1`): again not an
integer. Mirror of `AJTwist/Factor/TwFZeroInfinity.lean` for the adjoint.

In the forward convention and with the first jet `∂_t` at `t = -1` (`∂_t = -4 ∂_ε`): the actual
logarithmic jet of `e₀/e₁` is `2 (5x - 3)/(x - 1)`, with limit `10` at infinity, and the normal
form forces a limit in `4ℤ`.

* `ppl_adjoint_jet_infinity`: from the integral normal form with the factor `x²` cancelled
  (`μ = 2`), `∑ ε_j = 2`, the value at zero `c_d t^(68 + 4i) = -(c_n t^(8v + 4))` and the jet
  identity `(ė₀ ē₁ - ē₀ ė₁)(x - 1) = ē₀ ē₁ · 2 (5x - 3)`: `False`.
  Route: apply `coeffJet` to the normal form. With `lj(f) = coeffJet f / f̄`:
  `lj(C (t^n)) = -n` (`n` even), `lj(ℓ_j) = -4j x/(x - 1)`, `lj(τ f) = lj(f) - 4 x f̄'/f̄`, and
  from the value at zero `lj(c_n) - lj(c_d) = 8v + 4 - 68 - 4i`. Hence
  `lj(e₀) - lj(e₁) = 8v + 4 - 4i + (32 - 4s) x/(x - 1) - 8 x ē₁'/ē₁ + 4 x ḡ'/ḡ` with
  `s = ∑ ε_j · pplIdx j`. Multiply by `(x - 1) ē₁ ḡ`, insert the jet identity and compare the
  coefficients of degree `deg ē₁ + deg ḡ + 1`:
  `10 = 8v + 4 - 4i + 32 - 4s - 8 deg ē₁ + 4 deg ḡ`, impossible modulo `4`.
* `ppl_adjoint_no_solution`: the Riccati equation of the adjoint (variable `x`, shift
  `x ↦ t⁴ x`) has no solution `(e₀, e₁)` over `ℤ[t][x]` with `ē₀ = -ē₁ ≠ 0` and logarithmic first
  jet `2 (5x - 3)/(x - 1)`. (Assembly of `ppl_adjoint_integralForm`, `ppl_adjoint_reduce`,
  `ppl_adjoint_value_at_zero`, `ppl_adjoint_jet_infinity`; proved here from them.)

The formula for `lj(e₀) - lj(e₁)` and the limit in `4ℤ` are checked on synthetic data (scratch
`py/d03_chain.py`, part (b)); the linear combination of `jet_equation_pplInfinity` was found by
computer algebra (scratch `py/d04_jeteq.py`).

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value and the first jet of `t⁶⁸`. -/
private theorem coeffJet_C_X_pow_pplInfinity :
    (C (X ^ 68) : Coeff).map (Polynomial.evalRingHom (-1 : ℤ)) = 1 ∧
      coeffJet (C (X ^ 68) : Coeff) = -68 := by
  constructor
  · rw [map_C, coe_evalRingHom, eval_pow, eval_X]
    norm_num
  · rw [ppl_coeffJet_C, ppl_eval_derivative_X_pow]
    norm_num

/-- The logarithmic first jet of `∏ ℓ_{pplIdx j}^{ε_j}` is `4 s x/(x - 1)` for an integer
`s`. -/
private theorem exists_logJet_prod_pplInfinity (ε : Fin 4 → ℕ) :
    ∃ s : ℤ, coeffJet (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) * (X - 1) =
      4 * (s : ℤ[X]) * X *
        (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  rw [Fin.prod_univ_four]
  exact ⟨_, ppl_logJet_mul (ppl_logJet_mul (ppl_logJet_mul
    (ppl_logJet_pow (ppl_logJet_twfLin _) _)
    (ppl_logJet_pow (ppl_logJet_twfLin _) _))
    (ppl_logJet_pow (ppl_logJet_twfLin _) _))
    (ppl_logJet_pow (ppl_logJet_twfLin _) _)⟩

/-- The first jet of the left side of the integral normal form. -/
private theorem coeffJet_left_pplInfinity (e₀ g : Coeff) (cd : ℤ[X]) :
    coeffJet (e₀ * C cd * (C (X ^ 68) * twfLin 3 * twfLin 5) * twfShiftX g) =
      ((coeffJet e₀ * C (cd.eval (-1)) +
          e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * C ((derivative cd).eval (-1))) *
            (X - 1) ^ 2 +
        e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * C (cd.eval (-1)) *
          ((X - 1) * (68 - 100 * X))) * g.map (Polynomial.evalRingHom (-1 : ℤ)) +
      e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * C (cd.eval (-1)) * (X - 1) ^ 2 *
        (coeffJet g - 4 * (X * derivative (g.map (Polynomial.evalRingHom (-1 : ℤ))))) := by
  obtain ⟨h68, hj68⟩ := coeffJet_C_X_pow_pplInfinity
  simp only [ppl_coeffJet_mul, ppl_coeffJet_C, ppl_coeffJet_twfShiftX, ppl_coeffJet_twfLin,
    hj68, h68, Polynomial.map_mul, map_C, coe_evalRingHom, ppl_map_evalRingHom_twfLin,
    map_evalRingHom_twfShiftX, Nat.cast_ofNat]
  ring

/-- The first jet of the right side of the integral normal form. -/
private theorem coeffJet_right_pplInfinity (e₁ g P : Coeff) (cn : ℤ[X]) :
    coeffJet (C cn * P * twfShiftX (twfShiftX e₁) * g) =
      ((C ((derivative cn).eval (-1)) * P.map (Polynomial.evalRingHom (-1 : ℤ)) +
          C (cn.eval (-1)) * coeffJet P) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) +
        C (cn.eval (-1)) * P.map (Polynomial.evalRingHom (-1 : ℤ)) *
          (coeffJet e₁ - 8 * (X * derivative (e₁.map (Polynomial.evalRingHom (-1 : ℤ)))))) *
          g.map (Polynomial.evalRingHom (-1 : ℤ)) +
      C (cn.eval (-1)) * P.map (Polynomial.evalRingHom (-1 : ℤ)) *
        e₁.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet g := by
  simp only [ppl_coeffJet_mul, ppl_coeffJet_C, ppl_coeffJet_twfShiftX, Polynomial.map_mul,
    map_C, coe_evalRingHom, map_evalRingHom_twfShiftX]
  ring

/-- The algebra of the first jet: the jets of the two sides of the normal form, the jet
identity and the relation between `c_n` and `c_d` give a first-order differential equation
for `ē₁` and `ḡ`. -/
private theorem jet_equation_pplInfinity {E G J₀ J₁ JG E' G' P JP D D' N N' S I V : ℤ[X]}
    (hD : D ≠ 0) (hE : E ≠ 0) (hP : P = (X - 1) ^ 2) (hJP : JP * (X - 1) = 4 * S * X * P)
    (hN : N = -D) (hN' : D' - (68 + 4 * I) * D = -(N' - (8 * V + 4) * N))
    (hJ : ((J₀ * D + -E * D') * (X - 1) ^ 2 + -E * D * ((X - 1) * (68 - 100 * X))) * G +
        -E * D * (X - 1) ^ 2 * (JG - 4 * (X * G')) =
      ((N' * P + N * JP) * E + N * P * (J₁ - 8 * (X * E'))) * G + N * P * E * JG)
    (hjet : (J₀ * E - -E * J₁) * (X - 1) = -E * E * (2 * (5 * X - 3))) :
    (4 * I - 8 * V - 4 * S - 26) * (X * (E * G)) + (8 * V - 4 * I - 2) * (E * G) -
      4 * ((X - 1) * (E * (X * G'))) + 8 * ((X - 1) * (X * E' * G)) = 0 := by
  subst hP hN
  have hN'' : N' = -(D' - (68 + 4 * I) * D) + (8 * V + 4) * -D := by linear_combination hN'
  subst hN''
  have hx1 : (X - 1 : ℤ[X]) ≠ 0 := X_sub_C_ne_zero 1
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hD hE) (pow_ne_zero 2 hx1)) ?_
  linear_combination -(E * (X - 1)) * hJ - -D * G * (X - 1) ^ 2 * hjet - G * -D * E ^ 2 * hJP

/-- Comparing the coefficients of top degree in the first-order equation. -/
private theorem leading_coeff_identity_pplInfinity {E G : ℤ[X]} (hE : E ≠ 0) (hG : G ≠ 0)
    (κ κ₀ : ℤ)
    (h : C κ * (X * (E * G)) + C κ₀ * (E * G) - 4 * ((X - 1) * (E * (X * derivative G))) +
      8 * ((X - 1) * (X * derivative E * G)) = 0) :
    κ - 4 * (G.natDegree : ℤ) + 8 * (E.natDegree : ℤ) = 0 := by
  have hΘ : ∀ p : ℤ[X], (X * derivative p).natDegree ≤ p.natDegree := fun p ↦
    natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ by
      rw [ppl_coeff_X_mul_derivative, coeff_eq_zero_of_natDegree_lt hn, mul_zero]
  have h4 : (4 : ℤ[X]) = C 4 := (C_ofNat 4).symm
  have h8 : (8 : ℤ[X]) = C 8 := (C_ofNat 8).symm
  have hlt : E.natDegree + G.natDegree < E.natDegree + G.natDegree + 1 := Nat.lt_succ_self _
  have c1 : (E * G).coeff (E.natDegree + G.natDegree) = E.leadingCoeff * G.leadingCoeff :=
    coeff_mul_degree_add_degree E G
  have c2 : (E * G).coeff (E.natDegree + G.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt hlt)
  have c3 : (E * (X * derivative G)).coeff (E.natDegree + G.natDegree) =
      E.leadingCoeff * ((G.natDegree : ℤ) * G.leadingCoeff) := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl (hΘ G), ppl_coeff_X_mul_derivative]
    rfl
  have c4 : (E * (X * derivative G)).coeff (E.natDegree + G.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((natDegree_mul_le_of_le le_rfl (hΘ G)).trans_lt hlt)
  have c5 : (X * derivative E * G).coeff (E.natDegree + G.natDegree) =
      (E.natDegree : ℤ) * E.leadingCoeff * G.leadingCoeff := by
    rw [coeff_mul_add_eq_of_natDegree_le (hΘ E) le_rfl, ppl_coeff_X_mul_derivative]
    rfl
  have c6 : (X * derivative E * G).coeff (E.natDegree + G.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((natDegree_mul_le_of_le (hΘ E) le_rfl).trans_lt hlt)
  have hc := congrArg (fun p : ℤ[X] ↦ p.coeff (E.natDegree + G.natDegree + 1)) h
  simp only [h4, h8, sub_mul, one_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, c1, c2,
    c3, c4, c5, c6, coeff_zero, mul_zero, sub_zero, add_zero] at hc
  have hne : E.leadingCoeff * G.leadingCoeff ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hE) (leadingCoeff_ne_zero.mpr hG)
  refine mul_right_cancel₀ hne ?_
  linear_combination hc

set_option linter.unusedVariables false in
/-- The first-order contradiction at infinity for the adjoint. -/
theorem ppl_adjoint_jet_infinity {e₀ e₁ g : Coeff} {cn cd : ℤ[X]} {ε : Fin 4 → ℕ}
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₀₁ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hg : g.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (hcn : cn.eval (-1) ≠ 0) (hcd : cd.eval (-1) ≠ 0) (hε : ∑ j : Fin 4, ε j = 2)
    (hI : e₀ * C cd * (C (X ^ 68) * twfLin 3 * twfLin 5) * twfShiftX g =
      C cn * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) * twfShiftX (twfShiftX e₁) * g)
    (hc : cd * X ^ (68 + 4 * g.natTrailingDegree) =
      -(cn * X ^ (8 * e₁.natTrailingDegree + 4)))
    (hjet : (coeffJet e₀ * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) -
        e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet e₁) * (X - 1) =
      e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) *
        (2 * (5 * X - 3))) : False := by
  obtain ⟨s, hJP⟩ := exists_logJet_prod_pplInfinity ε
  have hP : (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j).map (Polynomial.evalRingHom (-1 : ℤ)) =
      (X - 1) ^ 2 := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_pow, ppl_map_evalRingHom_twfLin, Finset.prod_pow_eq_pow_sum, hε]
  have hJ := congrArg coeffJet hI
  rw [coeffJet_left_pplInfinity, coeffJet_right_pplInfinity, h₀₁] at hJ
  rw [h₀₁] at hjet
  have hval := congrArg (Polynomial.eval (-1)) hc
  rw [eval_neg, eval_mul, eval_mul, eval_pow, eval_pow, eval_X,
    Even.neg_one_pow ⟨34 + 2 * g.natTrailingDegree, by ring⟩,
    Even.neg_one_pow ⟨4 * e₁.natTrailingDegree + 2, by ring⟩, mul_one, mul_one] at hval
  have hder := congrArg (fun p : ℤ[X] ↦ (derivative p).eval (-1)) hc
  simp only [derivative_neg, derivative_mul, eval_neg, eval_add, eval_mul, eval_pow, eval_X,
    ppl_eval_derivative_X_pow] at hder
  rw [Even.neg_one_pow ⟨34 + 2 * g.natTrailingDegree, by ring⟩,
    Even.neg_one_pow ⟨4 * e₁.natTrailingDegree + 2, by ring⟩] at hder
  have hN' : C ((derivative cd).eval (-1)) -
      (68 + 4 * (g.natTrailingDegree : ℤ[X])) * C (cd.eval (-1)) =
      -(C ((derivative cn).eval (-1)) -
        (8 * (e₁.natTrailingDegree : ℤ[X]) + 4) * C (cn.eval (-1))) := by
    have h := congrArg (C : ℤ → ℤ[X]) hder
    simp only [eq_intCast (C : ℤ →+* ℤ[X])] at h ⊢
    push_cast at h ⊢
    linear_combination h
  have hNeq : (C (cn.eval (-1)) : ℤ[X]) = -C (cd.eval (-1)) := by
    rw [← C_neg]
    exact congrArg C (by linarith)
  have hstar := jet_equation_pplInfinity (S := (s : ℤ[X])) (C_ne_zero.mpr hcd) h₁ hP hJP
    hNeq hN' hJ hjet
  have hκ : (C (4 * (g.natTrailingDegree : ℤ) - 8 * (e₁.natTrailingDegree : ℤ) - 4 * s - 26) :
      ℤ[X]) = 4 * (g.natTrailingDegree : ℤ[X]) - 8 * (e₁.natTrailingDegree : ℤ[X]) -
        4 * (s : ℤ[X]) - 26 := by
    rw [eq_intCast (C : ℤ →+* ℤ[X])]
    push_cast
    ring
  have hκ₀ : (C (8 * (e₁.natTrailingDegree : ℤ) - 4 * (g.natTrailingDegree : ℤ) - 2) : ℤ[X]) =
      8 * (e₁.natTrailingDegree : ℤ[X]) - 4 * (g.natTrailingDegree : ℤ[X]) - 2 := by
    rw [eq_intCast (C : ℤ →+* ℤ[X])]
    push_cast
    ring
  have hlead := leading_coeff_identity_pplInfinity h₁ hg
    (4 * (g.natTrailingDegree : ℤ) - 8 * (e₁.natTrailingDegree : ℤ) - 4 * s - 26)
    (8 * (e₁.natTrailingDegree : ℤ) - 4 * (g.natTrailingDegree : ℤ) - 2)
    (by rw [hκ, hκ₀]; exact hstar)
  omega

/-- The Riccati equation of the adjoint of the explicit operator of `a = 0` has no solution
over `ℤ[t][x]` that is `1` at `t = -1` and has logarithmic first jet `2 (5x - 3)/(x - 1)`. -/
theorem ppl_adjoint_no_solution {e₀ e₁ : Coeff}
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₀₁ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hric : oreRiccati twfShiftX 3 pplAdjOpX e₀ e₁ = 0)
    (hjet : (coeffJet e₀ * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) -
        e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet e₁) * (X - 1) =
      e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) *
        (2 * (5 * X - 3))) : False := by
  have h₀ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    rw [h₀₁]
    exact neg_ne_zero.mpr h₁
  have he₀ : e₀ ≠ 0 := fun h ↦ h₀ (by rw [h, Polynomial.map_zero])
  have he₁ : e₁ ≠ 0 := fun h ↦ h₁ (by rw [h, Polynomial.map_zero])
  obtain ⟨cn, cd, μ, ε, g, hcn, hcd, hg, -, -, hI⟩ := ppl_adjoint_integralForm h₀ h₁ hric
  obtain ⟨hμ, hε, -⟩ := ppl_adjoint_reduce h₁ h₀₁ hg hcn hcd hI
  subst hμ
  have hI' : e₀ * C cd * (C (X ^ 68) * twfLin 3 * twfLin 5) * twfShiftX g =
      C cn * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) * twfShiftX (twfShiftX e₁) * g := by
    refine mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero : (X : Coeff) ≠ 0)) ?_
    linear_combination hI
  have hg0 : g ≠ 0 := fun h ↦ hg (by rw [h, Polynomial.map_zero])
  have hcn0 : cn ≠ 0 := fun h ↦ hcn (by rw [h, eval_zero])
  have hcd0 : cd ≠ 0 := fun h ↦ hcd (by rw [h, eval_zero])
  exact ppl_adjoint_jet_infinity h₁ h₀₁ hg hcn hcd hε hI'
    (ppl_adjoint_value_at_zero he₀ he₁ hg0 hcn0 hcd0 hric hε hI') hjet

end AJConjecture
