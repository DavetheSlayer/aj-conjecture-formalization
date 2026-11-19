import Mathlib
import AJConjecture.QAlgNodeJet
import AJConjecture.QAlgNodeJetBasic
import AJConjecture.QAlgSpecializeJetOreMul
import AJTwist.Factor.TwFZeroReduce
import AJTwist.Factor.TwFZeroAtZero

/-!
# The contradiction at infinity (TwF, unit F4, crux)

Source: revision 5, Section 5.6 (`operators.tex`): "On the other hand eq. (riccati-normal) gives
`f(x) = κ - s/(x - 1) - x g_0'(x)/g_0(x)`. At infinity this has integer limit given by `κ` minus
the degree difference of numerator and denominator of `g_0`. The actual first-order equation
gives limit `1/2`. This contradiction excludes linear right factors over `ℚ(t, M)`. The
calculation specializes the rational function before taking its degree at infinity, so moving
poles of a hypothetical factor are allowed."

In the forward convention and with the first jet `∂_t` at `t = -1` (`∂_t = -4 ∂_ε`): the actual
logarithmic jet of `e₀/e₁` is `2 (x + 1)/(x - 1)`, with limit `2` at infinity, and the normal form
forces a limit in `4ℤ`.

* `twf_zero_jet_infinity`: from the integral normal form (I) with `μ = 0`, `∑ ε_j = 2`, the value
  at zero `c_d t^(32 + 4i) = c_n t^(8v)` and the jet identity
  `(ė₀ ē₁ - ē₀ ė₁)(x - 1) = ē₀ ē₁ · 2 (x + 1)`: `False`.
  Route: apply the logarithmic first jet at `t = -1` (`coeffJet`, a derivation over
  `Polynomial.map (evalRingHom (-1))`: `coeffJet (a * b) = coeffJet a * b̄ + ā * coeffJet b`, as
  the private `coeffJet_mul_specJetOreMul` of `AJConjecture/QAlgSpecializeJetOreMul.lean`) to (I).
  With `lj(f) = coeffJet f / f̄`: `lj(C (t^n)) = -n`, `lj(ℓ_j) = -4j x/(x - 1)`,
  `lj(τ f) = lj(f) - 4 x f̄'/f̄` (the shift `x ↦ t⁴ x`), and from the value at zero
  `lj(c_n) - lj(c_d) = 8v - 32 - 4i`. Hence
  `lj(e₀) - lj(e₁) = 8v - 4 - 4i + (16 - 4s) x/(x - 1) - 8 x ē₁'/ē₁ + 4 x ḡ'/ḡ`, `s = ∑ j ε_j`.
  Multiply by `(x - 1) ē₁ ḡ`, insert the jet identity and compare the coefficients of degree
  `deg ē₁ + deg ḡ + 1`: `2 = 8v - 4 - 4i + 16 - 4s - 8 deg ē₁ + 4 deg ḡ`, impossible modulo `4`.
* `twf_zero_no_solution`: the Riccati equation of the explicit operator of `a = 0` (variable `x`,
  shift `x ↦ t⁴ x`) has no solution `(e₀, e₁)` over `ℤ[t][x]` with `ē₀ = -ē₁ ≠ 0` and logarithmic
  first jet `2 (x + 1)/(x - 1)`. (Assembly of `twf_zero_integralForm`, `twf_zero_reduce`,
  `twf_zero_value_at_zero`, `twf_zero_jet_infinity`; proved here from them.)
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Base change `ℤ[M] → ℂ[M]` is injective. -/
private theorem map_intCast_injective_twfZeroInfinity :
    Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
  Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int

/-- The first jet of coefficients is additive. -/
private theorem coeffJet_add_twfZeroInfinity (a b : Coeff) :
    coeffJet (a + b) = coeffJet a + coeffJet b := by
  apply map_intCast_injective_twfZeroInfinity
  rw [← complexJet_coeffToComplex, map_add, complexJet_add, Polynomial.map_add,
    complexJet_coeffToComplex, complexJet_coeffToComplex]

/-- The Leibniz rule for the first jet of coefficients. -/
private theorem coeffJet_mul_twfZeroInfinity (a b : Coeff) :
    coeffJet (a * b) = coeffJet a * b.map (Polynomial.evalRingHom (-1)) +
      a.map (Polynomial.evalRingHom (-1)) * coeffJet b := by
  apply map_intCast_injective_twfZeroInfinity
  rw [← complexJet_coeffToComplex, map_mul, complexJet_mul, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_mul, complexJet_coeffToComplex,
    complexJet_coeffToComplex, complexSpec_coeffToComplex, complexSpec_coeffToComplex]

/-- The first jet of a monomial in `x`. -/
private theorem coeffJet_monomial_twfZeroInfinity (n : ℕ) (a : ℤ[X]) :
    coeffJet (monomial n a) = monomial n ((derivative a).eval (-1)) := by
  rw [coeffJet, sum_monomial_index]
  rw [derivative_zero, eval_zero, monomial_zero_right]

/-- The first jet of a polynomial in `t` alone. -/
private theorem coeffJet_C_twfZeroInfinity (a : ℤ[X]) :
    coeffJet (C a) = C ((derivative a).eval (-1)) := by
  rw [← monomial_zero_left, coeffJet_monomial_twfZeroInfinity, monomial_zero_left]

/-- The first jet of `x`. -/
private theorem coeffJet_X_twfZeroInfinity : coeffJet (X : Coeff) = 0 := by
  rw [← monomial_one_one_eq_X, coeffJet_monomial_twfZeroInfinity, derivative_one, eval_zero,
    monomial_zero_right]

/-- The first jet of `1`. -/
private theorem coeffJet_one_twfZeroInfinity : coeffJet (1 : Coeff) = 0 := by
  rw [← C_1, coeffJet_C_twfZeroInfinity, derivative_one, eval_zero, C_0]

/-- The first jet of an opposite. -/
private theorem coeffJet_neg_twfZeroInfinity (a : Coeff) : coeffJet (-a) = -coeffJet a := by
  have h := coeffJet_add_twfZeroInfinity a (-a)
  rw [add_neg_cancel, coeffJet_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The derivative of `t^m` at `t = -1`. -/
private theorem eval_derivative_X_pow_twfZeroInfinity (m : ℕ) :
    (derivative (X ^ m : ℤ[X])).eval (-1) = -((m : ℤ) * (-1) ^ m) := by
  rcases m with _ | m
  · simp
  · rw [derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X, Nat.add_sub_cancel, pow_succ]
    push_cast
    ring

/-- `x ∂_x` multiplies the coefficient of `x^n` by `n`. -/
private theorem coeff_X_mul_derivative_twfZeroInfinity (p : ℤ[X]) (n : ℕ) :
    (X * derivative p).coeff n = (n : ℤ) * p.coeff n := by
  rcases n with _ | n
  · rw [coeff_X_mul_zero, Nat.cast_zero, zero_mul]
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The first jet of a shifted coefficient: `x ↦ t⁴ x` is `x ↦ (1 - 4ε) x` at `t = -1 + ε`. -/
private theorem coeffJet_twfShiftX_twfZeroInfinity (c : Coeff) :
    coeffJet (twfShiftX c) =
      coeffJet c - 4 * (X * derivative (c.map (Polynomial.evalRingHom (-1 : ℤ)))) := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, coeffJet_add_twfZeroInfinity, hp, hq, coeffJet_add_twfZeroInfinity,
      Polynomial.map_add, derivative_add]
    ring
  | monomial n a =>
    have h1 : twfShiftX (monomial n a) = monomial n (a * X ^ (4 * n)) := by
      change (monomial n a).comp (C (X ^ 4) * X) = _
      rw [monomial_comp, mul_pow, ← C_pow, ← pow_mul, ← mul_assoc, ← C_mul,
        C_mul_X_pow_eq_monomial]
    have h4 : (4 : ℤ[X]) = C 4 := (C_ofNat 4).symm
    rw [h1, coeffJet_monomial_twfZeroInfinity, coeffJet_monomial_twfZeroInfinity,
      Polynomial.map_monomial, coe_evalRingHom]
    ext k
    rw [coeff_sub, h4, coeff_C_mul, coeff_X_mul_derivative_twfZeroInfinity,
      coeff_monomial_apply, coeff_monomial_apply, coeff_monomial_apply, derivative_mul,
      eval_add, eval_mul, eval_mul, eval_pow, eval_X, eval_derivative_X_pow_twfZeroInfinity,
      Even.neg_one_pow ⟨2 * n, by ring⟩]
    split_ifs with hk
    · subst hk
      push_cast
      ring
    · ring

/-- At `t = -1` the linear forms `ℓ_j` become `x - 1`. -/
private theorem map_evalRingHom_twfLin_twfZeroInfinity (j : ℕ) :
    (twfLin j).map (Polynomial.evalRingHom (-1 : ℤ)) = X - 1 := by
  rw [twfLin, Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, Polynomial.map_one,
    coe_evalRingHom, eval_pow, eval_X, pow_mul]
  norm_num

/-- The first jet of the linear forms `ℓ_j`. -/
private theorem coeffJet_twfLin_twfZeroInfinity (j : ℕ) :
    coeffJet (twfLin j) = -(4 * (j : ℤ[X]) * X) := by
  have hsub : twfLin j = C (X ^ (4 * j)) * X + -1 := by rw [twfLin, sub_eq_add_neg]
  rw [hsub, coeffJet_add_twfZeroInfinity, coeffJet_neg_twfZeroInfinity,
    coeffJet_one_twfZeroInfinity, coeffJet_mul_twfZeroInfinity, coeffJet_C_twfZeroInfinity,
    coeffJet_X_twfZeroInfinity, map_X, eval_derivative_X_pow_twfZeroInfinity,
    Even.neg_one_pow ⟨2 * j, by ring⟩, mul_zero, add_zero, neg_zero, add_zero, mul_one, C_neg,
    eq_intCast (C : ℤ →+* ℤ[X])]
  push_cast
  ring

/-- The value and the first jet of `t²⁸`. -/
private theorem coeffJet_C_X_pow_twfZeroInfinity :
    (C (X ^ 28) : Coeff).map (Polynomial.evalRingHom (-1 : ℤ)) = 1 ∧
      coeffJet (C (X ^ 28) : Coeff) = -28 := by
  constructor
  · rw [map_C, coe_evalRingHom, eval_pow, eval_X]
    norm_num
  · rw [coeffJet_C_twfZeroInfinity, eval_derivative_X_pow_twfZeroInfinity]
    norm_num

/-- Logarithmic first jets of the form `4 s x/(x - 1)` are closed under products. -/
private theorem logJet_mul_twfZeroInfinity {f g : Coeff} {s r : ℤ}
    (hf : coeffJet f * (X - 1) =
      4 * (s : ℤ[X]) * X * f.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hg : coeffJet g * (X - 1) =
      4 * (r : ℤ[X]) * X * g.map (Polynomial.evalRingHom (-1 : ℤ))) :
    coeffJet (f * g) * (X - 1) =
      4 * ((s + r : ℤ) : ℤ[X]) * X * (f * g).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  rw [coeffJet_mul_twfZeroInfinity, Polynomial.map_mul, Int.cast_add]
  linear_combination g.map (Polynomial.evalRingHom (-1 : ℤ)) * hf +
    f.map (Polynomial.evalRingHom (-1 : ℤ)) * hg

/-- Logarithmic first jets of the form `4 s x/(x - 1)` are closed under powers. -/
private theorem logJet_pow_twfZeroInfinity {f : Coeff} {s : ℤ}
    (hf : coeffJet f * (X - 1) =
      4 * (s : ℤ[X]) * X * f.map (Polynomial.evalRingHom (-1 : ℤ))) (n : ℕ) :
    coeffJet (f ^ n) * (X - 1) =
      4 * (((n : ℤ) * s : ℤ) : ℤ[X]) * X * (f ^ n).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  induction n with
  | zero => simp [coeffJet_one_twfZeroInfinity]
  | succ n ih =>
    have h := logJet_mul_twfZeroInfinity ih hf
    rw [pow_succ, show ((n + 1 : ℕ) : ℤ) * s = (n : ℤ) * s + s by push_cast; ring]
    exact h

/-- The logarithmic first jet of `ℓ_j` is `-4 j x/(x - 1)`. -/
private theorem logJet_twfLin_twfZeroInfinity (j : ℕ) :
    coeffJet (twfLin j) * (X - 1) =
      4 * ((-(j : ℤ) : ℤ) : ℤ[X]) * X * (twfLin j).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  rw [coeffJet_twfLin_twfZeroInfinity, map_evalRingHom_twfLin_twfZeroInfinity]
  push_cast
  ring

/-- The logarithmic first jet of `∏ ℓ_j^{ε_j}` is `4 s x/(x - 1)` for an integer `s`. -/
private theorem exists_logJet_prod_twfZeroInfinity (ε : Fin 4 → ℕ) :
    ∃ s : ℤ, coeffJet (∏ j : Fin 4, twfLin j ^ ε j) * (X - 1) =
      4 * (s : ℤ[X]) * X *
        (∏ j : Fin 4, twfLin j ^ ε j).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  rw [Fin.prod_univ_four]
  exact ⟨_, logJet_mul_twfZeroInfinity (logJet_mul_twfZeroInfinity (logJet_mul_twfZeroInfinity
    (logJet_pow_twfZeroInfinity (logJet_twfLin_twfZeroInfinity _) _)
    (logJet_pow_twfZeroInfinity (logJet_twfLin_twfZeroInfinity _) _))
    (logJet_pow_twfZeroInfinity (logJet_twfLin_twfZeroInfinity _) _))
    (logJet_pow_twfZeroInfinity (logJet_twfLin_twfZeroInfinity _) _)⟩

/-- The first jet of the left side of the integral normal form. -/
private theorem coeffJet_left_twfZeroInfinity (e₀ g : Coeff) (cd : ℤ[X]) :
    coeffJet (-e₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g) =
      ((-coeffJet e₀ * C (cd.eval (-1)) +
          -e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * C ((derivative cd).eval (-1))) *
            (X - 1) ^ 2 +
        -e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * C (cd.eval (-1)) *
          ((X - 1) * (28 - 44 * X))) * g.map (Polynomial.evalRingHom (-1 : ℤ)) +
      -e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * C (cd.eval (-1)) * (X - 1) ^ 2 *
        (coeffJet g - 4 * (X * derivative (g.map (Polynomial.evalRingHom (-1 : ℤ))))) := by
  obtain ⟨h28, hj28⟩ := coeffJet_C_X_pow_twfZeroInfinity
  simp only [coeffJet_mul_twfZeroInfinity, coeffJet_neg_twfZeroInfinity,
    coeffJet_C_twfZeroInfinity, coeffJet_twfShiftX_twfZeroInfinity,
    coeffJet_twfLin_twfZeroInfinity, hj28, h28, Polynomial.map_mul, Polynomial.map_neg, map_C,
    coe_evalRingHom, map_evalRingHom_twfLin_twfZeroInfinity, map_evalRingHom_twfShiftX,
    Nat.cast_one, Nat.cast_ofNat]
  ring

/-- The first jet of the right side of the integral normal form. -/
private theorem coeffJet_right_twfZeroInfinity (e₁ g P : Coeff) (cn : ℤ[X]) :
    coeffJet (C cn * P * twfShiftX (twfShiftX e₁) * g) =
      ((C ((derivative cn).eval (-1)) * P.map (Polynomial.evalRingHom (-1 : ℤ)) +
          C (cn.eval (-1)) * coeffJet P) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) +
        C (cn.eval (-1)) * P.map (Polynomial.evalRingHom (-1 : ℤ)) *
          (coeffJet e₁ - 8 * (X * derivative (e₁.map (Polynomial.evalRingHom (-1 : ℤ)))))) *
          g.map (Polynomial.evalRingHom (-1 : ℤ)) +
      C (cn.eval (-1)) * P.map (Polynomial.evalRingHom (-1 : ℤ)) *
        e₁.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet g := by
  simp only [coeffJet_mul_twfZeroInfinity, coeffJet_C_twfZeroInfinity,
    coeffJet_twfShiftX_twfZeroInfinity, Polynomial.map_mul, map_C, coe_evalRingHom,
    map_evalRingHom_twfShiftX]
  ring

/-- The algebra of the first jet: the jets of the two sides of the normal form, the jet
identity and the relation between `c_n` and `c_d` give a first-order differential equation
for `ē₁` and `ḡ`. -/
private theorem jet_equation_twfZeroInfinity {E G J₀ J₁ JG E' G' P JP D D' N N' S I V : ℤ[X]}
    (hD : D ≠ 0) (hE : E ≠ 0) (hP : P = (X - 1) ^ 2) (hJP : JP * (X - 1) = 4 * S * X * P)
    (hN : N = D) (hN' : D' - (32 + 4 * I) * D = N' - 8 * V * N)
    (hJ : ((-J₀ * D + -(-E) * D') * (X - 1) ^ 2 + -(-E) * D * ((X - 1) * (28 - 44 * X))) * G +
        -(-E) * D * (X - 1) ^ 2 * (JG - 4 * (X * G')) =
      ((N' * P + N * JP) * E + N * P * (J₁ - 8 * (X * E'))) * G + N * P * E * JG)
    (hjet : (J₀ * E - -E * J₁) * (X - 1) = -E * E * (2 * (X + 1))) :
    (4 * I - 8 * V - 4 * S - 10) * (X * (E * G)) + (8 * V - 4 * I - 2) * (E * G) -
      4 * ((X - 1) * (E * (X * G'))) + 8 * ((X - 1) * (X * E' * G)) = 0 := by
  subst hP hN
  have hN'' : N' = D' - (32 + 4 * I) * N + 8 * V * N := by linear_combination -hN'
  subst hN''
  have hx1 : (X - 1 : ℤ[X]) ≠ 0 := X_sub_C_ne_zero 1
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hD hE) (pow_ne_zero 2 hx1)) ?_
  linear_combination E * (X - 1) * hJ + N * G * (X - 1) ^ 2 * hjet + G * N * E ^ 2 * hJP

/-- Comparing the coefficients of top degree in the first-order equation. -/
private theorem leading_coeff_identity_twfZeroInfinity {E G : ℤ[X]} (hE : E ≠ 0) (hG : G ≠ 0)
    (κ κ₀ : ℤ)
    (h : C κ * (X * (E * G)) + C κ₀ * (E * G) - 4 * ((X - 1) * (E * (X * derivative G))) +
      8 * ((X - 1) * (X * derivative E * G)) = 0) :
    κ - 4 * (G.natDegree : ℤ) + 8 * (E.natDegree : ℤ) = 0 := by
  have hΘ : ∀ p : ℤ[X], (X * derivative p).natDegree ≤ p.natDegree := fun p ↦
    natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ by
      rw [coeff_X_mul_derivative_twfZeroInfinity, coeff_eq_zero_of_natDegree_lt hn, mul_zero]
  have h4 : (4 : ℤ[X]) = C 4 := (C_ofNat 4).symm
  have h8 : (8 : ℤ[X]) = C 8 := (C_ofNat 8).symm
  have hlt : E.natDegree + G.natDegree < E.natDegree + G.natDegree + 1 := Nat.lt_succ_self _
  have c1 : (E * G).coeff (E.natDegree + G.natDegree) = E.leadingCoeff * G.leadingCoeff :=
    coeff_mul_degree_add_degree E G
  have c2 : (E * G).coeff (E.natDegree + G.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt hlt)
  have c3 : (E * (X * derivative G)).coeff (E.natDegree + G.natDegree) =
      E.leadingCoeff * ((G.natDegree : ℤ) * G.leadingCoeff) := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl (hΘ G),
      coeff_X_mul_derivative_twfZeroInfinity]
    rfl
  have c4 : (E * (X * derivative G)).coeff (E.natDegree + G.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((natDegree_mul_le_of_le le_rfl (hΘ G)).trans_lt hlt)
  have c5 : (X * derivative E * G).coeff (E.natDegree + G.natDegree) =
      (E.natDegree : ℤ) * E.leadingCoeff * G.leadingCoeff := by
    rw [coeff_mul_add_eq_of_natDegree_le (hΘ E) le_rfl,
      coeff_X_mul_derivative_twfZeroInfinity]
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
/-- The first-order contradiction at infinity. -/
theorem twf_zero_jet_infinity {e₀ e₁ g : Coeff} {cn cd : ℤ[X]} {ε : Fin 4 → ℕ}
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₀₁ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hg : g.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (hcn : cn.eval (-1) ≠ 0) (hcd : cd.eval (-1) ≠ 0) (hε : ∑ j : Fin 4, ε j = 2)
    (hI : -e₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g =
      C cn * (∏ j : Fin 4, twfLin j ^ ε j) * twfShiftX (twfShiftX e₁) * g)
    (hc : cd * X ^ (32 + 4 * g.natTrailingDegree) = cn * X ^ (8 * e₁.natTrailingDegree))
    (hjet : (coeffJet e₀ * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) -
        e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet e₁) * (X - 1) =
      e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) *
        (2 * (X + 1))) : False := by
  obtain ⟨s, hJP⟩ := exists_logJet_prod_twfZeroInfinity ε
  have hP : (∏ j : Fin 4, twfLin j ^ ε j).map (Polynomial.evalRingHom (-1 : ℤ)) =
      (X - 1) ^ 2 := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_pow, map_evalRingHom_twfLin_twfZeroInfinity,
      Finset.prod_pow_eq_pow_sum, hε]
  have hJ := congrArg coeffJet hI
  rw [coeffJet_left_twfZeroInfinity, coeffJet_right_twfZeroInfinity, h₀₁] at hJ
  rw [h₀₁] at hjet
  have hval := congrArg (Polynomial.eval (-1)) hc
  rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X,
    Even.neg_one_pow ⟨16 + 2 * g.natTrailingDegree, by ring⟩,
    Even.neg_one_pow ⟨4 * e₁.natTrailingDegree, by ring⟩, mul_one, mul_one] at hval
  have hder := congrArg (fun p : ℤ[X] ↦ (derivative p).eval (-1)) hc
  simp only [derivative_mul, eval_add, eval_mul, eval_pow, eval_X,
    eval_derivative_X_pow_twfZeroInfinity] at hder
  rw [Even.neg_one_pow ⟨16 + 2 * g.natTrailingDegree, by ring⟩,
    Even.neg_one_pow ⟨4 * e₁.natTrailingDegree, by ring⟩] at hder
  have hN' : C ((derivative cd).eval (-1)) -
      (32 + 4 * (g.natTrailingDegree : ℤ[X])) * C (cd.eval (-1)) =
      C ((derivative cn).eval (-1)) - 8 * (e₁.natTrailingDegree : ℤ[X]) * C (cn.eval (-1)) := by
    have h := congrArg (C : ℤ → ℤ[X]) hder
    simp only [eq_intCast (C : ℤ →+* ℤ[X])] at h ⊢
    push_cast at h ⊢
    linear_combination h
  have hstar := jet_equation_twfZeroInfinity (S := (s : ℤ[X])) (C_ne_zero.mpr hcd) h₁ hP hJP
    (congrArg C hval).symm hN' hJ hjet
  have hκ : (C (4 * (g.natTrailingDegree : ℤ) - 8 * (e₁.natTrailingDegree : ℤ) - 4 * s - 10) :
      ℤ[X]) = 4 * (g.natTrailingDegree : ℤ[X]) - 8 * (e₁.natTrailingDegree : ℤ[X]) -
        4 * (s : ℤ[X]) - 10 := by
    rw [eq_intCast (C : ℤ →+* ℤ[X])]
    push_cast
    ring
  have hκ₀ : (C (8 * (e₁.natTrailingDegree : ℤ) - 4 * (g.natTrailingDegree : ℤ) - 2) : ℤ[X]) =
      8 * (e₁.natTrailingDegree : ℤ[X]) - 4 * (g.natTrailingDegree : ℤ[X]) - 2 := by
    rw [eq_intCast (C : ℤ →+* ℤ[X])]
    push_cast
    ring
  have hlead := leading_coeff_identity_twfZeroInfinity h₁ hg
    (4 * (g.natTrailingDegree : ℤ) - 8 * (e₁.natTrailingDegree : ℤ) - 4 * s - 10)
    (8 * (e₁.natTrailingDegree : ℤ) - 4 * (g.natTrailingDegree : ℤ) - 2)
    (by rw [hκ, hκ₀]; exact hstar)
  omega

/-- The Riccati equation of the explicit operator of `a = 0` has no solution over `ℤ[t][x]` that
is `1` at `t = -1` and has logarithmic first jet `2 (x + 1)/(x - 1)`. -/
theorem twf_zero_no_solution {e₀ e₁ : Coeff}
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₀₁ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hric : oreRiccati twfShiftX 3 twfZeroOpX e₀ e₁ = 0)
    (hjet : (coeffJet e₀ * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) -
        e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet e₁) * (X - 1) =
      e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) *
        (2 * (X + 1))) : False := by
  have h₀ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    rw [h₀₁]
    exact neg_ne_zero.mpr h₁
  have he₀ : e₀ ≠ 0 := fun h ↦ h₀ (by rw [h, Polynomial.map_zero])
  have he₁ : e₁ ≠ 0 := fun h ↦ h₁ (by rw [h, Polynomial.map_zero])
  obtain ⟨cn, cd, μ, ε, g, hcn, hcd, hg, -, -, hI⟩ := twf_zero_integralForm h₀ h₁ hric
  obtain ⟨hμ, hε, -⟩ := twf_zero_reduce h₁ h₀₁ hg hcn hcd hI
  subst hμ
  rw [pow_zero, mul_one] at hI
  have hg0 : g ≠ 0 := fun h ↦ hg (by rw [h, Polynomial.map_zero])
  have hcn0 : cn ≠ 0 := fun h ↦ hcn (by rw [h, eval_zero])
  have hcd0 : cd ≠ 0 := fun h ↦ hcd (by rw [h, eval_zero])
  exact twf_zero_jet_infinity h₁ h₀₁ hg hcn hcd hε hI
    (twf_zero_value_at_zero he₀ he₁ hg0 hcn0 hcd0 hric hε hI) hjet

end AJConjecture
