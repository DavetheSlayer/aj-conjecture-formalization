import Mathlib
import AJConjecture.QAlgSymbolNodeDerivatives
import AJConjecture.QAlgInnerDerivativeBasic
import AJConjecture.QAlgNodeIndexEuler
import AJTwist.Factor.TwFSymbolHessian

/-!
# The mixed second derivative of the symbol of the operator of a target (TwF, generic)

Source: revision 5, Section 5.2, eq. (physical-derivatives):
`D_x = D_* ∂_K + (J² - 1)/D_* ∂_J` (the fixed-`u` derivative in `x`).

Continuation of `AJTwist/Factor/TwFSymbolHessian.lean`. At a double point `(x₀, J₀) = (m₀², J₀)`
of the target `p = twfTargetOne T` (`p = ∂_J p = ∂_x p = 0`), with `l₀ = (1 - x₀J₀)/(J₀ - x₀)`:

`γ (x₀² - 1)² (L ∂_L)(M ∂_M) P₀
   = 2 x₀ det (1 - x₀J₀)(J₀ - x₀) ((x₀² - 1) ∂_x∂_J p - (1 - J₀²) ∂_J² p)`.

Route: apply `coeffDerivative` and then `derivative` to the Cramer identity at `q = 1`
(`sum_twCoeff_mul_twBasisPoly d (1 : ℤ)`), evaluate at `(x₀, J₀)`; with
`P_i(1; x, J) = γ(x, J) l(x, J)^(d-i)` the mixed derivative of the left side is
`γ (l_J/l) · ∑_k k l₀^k c_(d-k)'(x₀) + γ l_x l_J ∂_L² P₀` at a double point (`P₀ = ∂_L P₀ = 0`
and `∑_i c_i'(x₀) l₀^(d-i) = 0`), where `l_J = (x² - 1)/(J - x)²`, `l_x = (1 - J²)/(J - x)²`;
`(L ∂_L)(M ∂_M) P₀ = 2 x₀ ∑_k k l₀^k c_(d-k)'(x₀)` since the coefficients are functions of
`x = M²` (`coeff_eulerEuler`, `eulerEuler_eq`, `specialize_twCramerOp_eq_sum`); then
`evalIntPoint_derivative_derivative_specialize_twCramerOp_node` for `∂_L² P₀`.
Checked at random points for `d = 3, 4, 5` and random targets with a double point (scratch
`check_generic_parts.py` (A), level 3).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Evaluation at a complex point, as a ring homomorphism. -/
private def evalIntHomTwfMixed (x J : ℂ) : ℤ[X][X] →+* ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.evalRingHom x) J).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ)))

/-- `evalIntPoint` is the evaluation homomorphism. -/
private theorem evalIntPoint_eq_TwfMixed (p : ℤ[X][X]) (x J : ℂ) :
    evalIntPoint p x J = evalIntHomTwfMixed x J p :=
  rfl

/-- The value of a polynomial constant in the outer variable. -/
private theorem evalIntHomTwfMixed_C (x J : ℂ) (κ : ℤ[X]) :
    evalIntHomTwfMixed x J (C κ) = (κ.map (Int.castRingHom ℂ)).eval x := by
  simp [evalIntHomTwfMixed]

/-- The value of the outer variable. -/
private theorem evalIntHomTwfMixed_X (x J : ℂ) : evalIntHomTwfMixed x J X = J := by
  simp [evalIntHomTwfMixed]

/-- The factor `(1 - x)(x - J)` of the basis polynomials at `q = 1`. -/
private def basisFactorATwfMixed : ℤ[X][X] := C (1 - X) * (C X - X)

/-- The factor `(x - 1)(1 - x J)` of the basis polynomials at `q = 1`. -/
private def basisFactorBTwfMixed : ℤ[X][X] := C (X - 1) * (1 - C X * X)

/-- The basis polynomials at `q = 1` are products of powers of the two factors. -/
private theorem twBasisPoly_one_eq_TwfMixed (d i : ℕ) :
    twBasisPoly d (1 : ℤ) i = basisFactorATwfMixed ^ i * basisFactorBTwfMixed ^ (d - i) := by
  simp [twBasisPoly, basisFactorATwfMixed, basisFactorBTwfMixed, Finset.prod_const, Nat.card_Ico]

/-- The Cramer identity at `q = 1`, with the sum reversed. -/
private theorem sum_rev_twCoeff_mul_TwfMixed (d : ℕ) (p : ℤ[X][X]) (hp : p.natDegree ≤ d) :
    ∑ k : Fin (d + 1), C (twCoeff d (1 : ℤ) p (Fin.rev k)) * basisFactorATwfMixed ^ (d - (k : ℕ)) *
        basisFactorBTwfMixed ^ (k : ℕ) = C (twDet d (1 : ℤ)) * p := by
  rw [← sum_twCoeff_mul_twBasisPoly d (1 : ℤ) p hp]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k ↦ ?_
  rw [Fin.revPerm_apply, twBasisPoly_one_eq_TwfMixed, Fin.val_rev, mul_assoc]
  congr 3 <;> omega

/-- The value of a term `c A^i B^k`. -/
private theorem map_term_TwfMixed (E : ℤ[X][X] →+* ℂ) (c : ℤ[X]) (A B : ℤ[X][X]) (i k : ℕ) :
    E (C c * A ^ i * B ^ k) = E (C c) * (E A ^ i * E B ^ k) := by
  rw [map_mul, map_mul, map_pow, map_pow, mul_assoc]

/-- The value of the derivative of a term `c A^i B^k`. -/
private theorem map_derivative_term_TwfMixed (E : ℤ[X][X] →+* ℂ) (c : ℤ[X]) (A B : ℤ[X][X])
    (i k : ℕ) :
    E (derivative (C c * A ^ i * B ^ k)) =
      E (C c) * ((i : ℂ) * E A ^ (i - 1) * E B ^ k * E (derivative A) +
        (k : ℂ) * E A ^ i * E B ^ (k - 1) * E (derivative B)) := by
  rw [derivative_mul, derivative_mul, derivative_C, derivative_pow, derivative_pow]
  simp only [map_add, map_mul, map_pow, map_zero, map_natCast]
  ring

/-- The value of the second derivative of a term `c A^i B^k`. -/
private theorem map_derivative_derivative_term_TwfMixed (E : ℤ[X][X] →+* ℂ) (c : ℤ[X])
    (A B : ℤ[X][X]) (i k : ℕ) :
    E (derivative (derivative (C c * A ^ i * B ^ k))) =
      E (C c) * ((i : ℂ) * ((i - 1 : ℕ) : ℂ) * E A ^ (i - 1 - 1) * E B ^ k *
            E (derivative A) ^ 2 +
          2 * ((i : ℂ) * (k : ℂ) * E A ^ (i - 1) * E B ^ (k - 1)) *
            (E (derivative A) * E (derivative B)) +
          (k : ℂ) * ((k - 1 : ℕ) : ℂ) * E A ^ i * E B ^ (k - 1 - 1) * E (derivative B) ^ 2 +
          (i : ℂ) * E A ^ (i - 1) * E B ^ k * E (derivative (derivative A)) +
          (k : ℂ) * E A ^ i * E B ^ (k - 1) * E (derivative (derivative B))) := by
  simp only [derivative_mul, derivative_pow, derivative_C, derivative_natCast, map_add, map_mul,
    map_pow, map_zero, map_natCast]
  ring

/-- The derivative in `J` of the first factor. -/
private theorem derivative_basisFactorATwfMixed : derivative basisFactorATwfMixed = C (X - 1) := by
  simp only [basisFactorATwfMixed, derivative_mul, derivative_C, derivative_sub, derivative_X,
    derivative_one, C_sub, C_1]
  ring

/-- The derivative in `J` of the second factor. -/
private theorem derivative_basisFactorBTwfMixed :
    derivative basisFactorBTwfMixed = C (X - X ^ 2) := by
  simp only [basisFactorBTwfMixed, derivative_mul, derivative_C, derivative_sub, derivative_X,
    derivative_one, C_sub, C_1, C_pow]
  ring

/-- The values of the two factors and of their derivatives in `J`. -/
private theorem evalIntHomTwfMixed_basisFactor (x J : ℂ) :
    evalIntHomTwfMixed x J basisFactorATwfMixed = (1 - x) * (x - J) ∧
      evalIntHomTwfMixed x J basisFactorBTwfMixed = (x - 1) * (1 - x * J) ∧
      evalIntHomTwfMixed x J (derivative basisFactorATwfMixed) = -(1 - x) ∧
      evalIntHomTwfMixed x J (derivative basisFactorBTwfMixed) = -((x - 1) * x) ∧
      evalIntHomTwfMixed x J (derivative (derivative basisFactorATwfMixed)) = 0 ∧
      evalIntHomTwfMixed x J (derivative (derivative basisFactorBTwfMixed)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [basisFactorATwfMixed, evalIntHomTwfMixed_C, evalIntHomTwfMixed_X]
  · simp [basisFactorBTwfMixed, evalIntHomTwfMixed_C, evalIntHomTwfMixed_X]
  · rw [derivative_basisFactorATwfMixed, evalIntHomTwfMixed_C]
    simp
  · rw [derivative_basisFactorBTwfMixed, evalIntHomTwfMixed_C]
    simp
    ring
  · rw [derivative_basisFactorATwfMixed, derivative_C, map_zero]
  · rw [derivative_basisFactorBTwfMixed, derivative_C, map_zero]

/-- `n a^(n-1) a = n a^n`. -/
private theorem natCast_mul_pow_pred_mul_TwfMixed (n : ℕ) (a : ℂ) :
    (n : ℂ) * a ^ (n - 1) * a = (n : ℂ) * a ^ n := by
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    ring

/-- `n (n-1) a^(n-2) a = (n - 1) (n a^(n-1))`. -/
private theorem natCast_mul_pred_mul_pow_mul_TwfMixed (n : ℕ) (a : ℂ) :
    (n : ℂ) * ((n - 1 : ℕ) : ℂ) * a ^ (n - 1 - 1) * a =
      ((n : ℂ) - 1) * ((n : ℂ) * a ^ (n - 1)) := by
  rcases n with _ | n
  · simp
  · have h := natCast_mul_pow_pred_mul_TwfMixed n a
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination ((n : ℂ) + 1) * h

/-- Euler's relations for the partial derivatives of the monomial `α^i β^k`. -/
private theorem euler_monomial_TwfMixed (i k : ℕ) (α β : ℂ) :
    α * ((i : ℂ) * α ^ (i - 1) * β ^ k) + β * ((k : ℂ) * α ^ i * β ^ (k - 1)) =
        ((i + k : ℕ) : ℂ) * (α ^ i * β ^ k) ∧
      α * ((i : ℂ) * ((i - 1 : ℕ) : ℂ) * α ^ (i - 1 - 1) * β ^ k) +
          β * ((i : ℂ) * (k : ℂ) * α ^ (i - 1) * β ^ (k - 1)) =
        (((i + k : ℕ) : ℂ) - 1) * ((i : ℂ) * α ^ (i - 1) * β ^ k) ∧
      α * ((i : ℂ) * (k : ℂ) * α ^ (i - 1) * β ^ (k - 1)) +
          β * ((k : ℂ) * ((k - 1 : ℕ) : ℂ) * α ^ i * β ^ (k - 1 - 1)) =
        (((i + k : ℕ) : ℂ) - 1) * ((k : ℂ) * α ^ i * β ^ (k - 1)) := by
  have h1 := natCast_mul_pow_pred_mul_TwfMixed i α
  have h2 := natCast_mul_pow_pred_mul_TwfMixed k β
  have h3 := natCast_mul_pred_mul_pow_mul_TwfMixed i α
  have h4 := natCast_mul_pred_mul_pow_mul_TwfMixed k β
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination β ^ k * h1 + α ^ i * h2
  · linear_combination β ^ k * h3 + (i : ℂ) * α ^ (i - 1) * h2
  · linear_combination (k : ℂ) * β ^ (k - 1) * h1 + α ^ i * h4

/-- The inner derivative of the outer variable vanishes. -/
private theorem innerDerivative_X_TwfMixed : innerDerivative (X : ℤ[X][X]) = 0 := by
  rw [← monomial_one_one_eq_X]
  simp [innerDerivative]

/-- The inner derivative of `1` vanishes. -/
private theorem innerDerivative_one_TwfMixed : innerDerivative (1 : ℤ[X][X]) = 0 := by
  rw [← C_1, innerDerivative_C, derivative_one, C_0]

/-- The inner derivative is subtractive. -/
private theorem innerDerivative_sub_TwfMixed (p q : ℤ[X][X]) :
    innerDerivative (p - q) = innerDerivative p - innerDerivative q := by
  rw [eq_sub_iff_add_eq, ← innerDerivative_add, sub_add_cancel]

/-- The inner derivative commutes with finite sums. -/
private theorem innerDerivative_sum_TwfMixed {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) :
    innerDerivative (∑ i ∈ s, f i) = ∑ i ∈ s, innerDerivative (f i) :=
  map_sum (AddMonoidHom.mk' (innerDerivative : ℤ[X][X] → ℤ[X][X]) innerDerivative_add) f s

/-- The power rule for the inner derivative. -/
private theorem innerDerivative_pow_TwfMixed (p : ℤ[X][X]) (n : ℕ) :
    innerDerivative (p ^ n) = C (n : ℤ[X]) * p ^ (n - 1) * innerDerivative p := by
  induction n with
  | zero =>
    rw [pow_zero, ← C_1, innerDerivative_C, derivative_one]
    simp
  | succ n ih =>
    rw [pow_succ, innerDerivative_mul, ih, Nat.add_sub_cancel]
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ p n]
      push_cast
      simp only [C_add, C_1]
      ring

/-- The value of the derivative in `x` of a term `c A^i B^k`. -/
private theorem map_innerDerivative_term_TwfMixed (E : ℤ[X][X] →+* ℂ) (c : ℤ[X])
    (A B : ℤ[X][X]) (i k : ℕ) :
    E (innerDerivative (C c * A ^ i * B ^ k)) =
      E (C (derivative c)) * (E A ^ i * E B ^ k) +
        E (C c) * ((i : ℂ) * E A ^ (i - 1) * E B ^ k * E (innerDerivative A) +
          (k : ℂ) * E A ^ i * E B ^ (k - 1) * E (innerDerivative B)) := by
  rw [innerDerivative_mul, innerDerivative_mul, innerDerivative_C, innerDerivative_pow_TwfMixed,
    innerDerivative_pow_TwfMixed]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

/-- The value of the mixed derivative of a term `c A^i B^k`. -/
private theorem map_derivative_innerDerivative_term_TwfMixed (E : ℤ[X][X] →+* ℂ) (c : ℤ[X])
    (A B : ℤ[X][X]) (i k : ℕ) :
    E (derivative (innerDerivative (C c * A ^ i * B ^ k))) =
      E (C (derivative c)) * ((i : ℂ) * E A ^ (i - 1) * E B ^ k * E (derivative A) +
          (k : ℂ) * E A ^ i * E B ^ (k - 1) * E (derivative B)) +
        E (C c) * ((i : ℂ) * ((i - 1 : ℕ) : ℂ) * E A ^ (i - 1 - 1) * E B ^ k *
              (E (derivative A) * E (innerDerivative A)) +
            (i : ℂ) * (k : ℂ) * E A ^ (i - 1) * E B ^ (k - 1) *
              (E (derivative A) * E (innerDerivative B) +
                E (derivative B) * E (innerDerivative A)) +
            (k : ℂ) * ((k - 1 : ℕ) : ℂ) * E A ^ i * E B ^ (k - 1 - 1) *
              (E (derivative B) * E (innerDerivative B)) +
            (i : ℂ) * E A ^ (i - 1) * E B ^ k * E (derivative (innerDerivative A)) +
            (k : ℂ) * E A ^ i * E B ^ (k - 1) * E (derivative (innerDerivative B))) := by
  rw [innerDerivative_mul, innerDerivative_mul, innerDerivative_C, innerDerivative_pow_TwfMixed,
    innerDerivative_pow_TwfMixed]
  simp only [derivative_mul, derivative_pow, derivative_C, derivative_natCast,
    map_add, map_mul, map_pow, map_zero, map_natCast]
  ring

/-- The derivative in `x` of the first factor. -/
private theorem innerDerivative_basisFactorATwfMixed :
    innerDerivative basisFactorATwfMixed = C (1 - 2 * X) + X := by
  simp only [basisFactorATwfMixed, innerDerivative_mul, innerDerivative_C,
    innerDerivative_sub_TwfMixed, innerDerivative_X_TwfMixed, innerDerivative_one_TwfMixed,
    derivative_X, C_sub, C_1, C_mul, C_ofNat]
  ring

/-- The derivative in `x` of the second factor. -/
private theorem innerDerivative_basisFactorBTwfMixed :
    innerDerivative basisFactorBTwfMixed = 1 + C (1 - 2 * X) * X := by
  simp only [basisFactorBTwfMixed, innerDerivative_mul, innerDerivative_C,
    innerDerivative_sub_TwfMixed, innerDerivative_X_TwfMixed, innerDerivative_one_TwfMixed,
    derivative_X, C_sub, C_1, C_mul, C_ofNat]
  ring

/-- The values of the derivatives in `x` of the two factors and of their derivatives in `J`. -/
private theorem evalIntHomTwfMixed_innerDerivative_basisFactor (x J : ℂ) :
    evalIntHomTwfMixed x J (innerDerivative basisFactorATwfMixed) = 1 - 2 * x + J ∧
      evalIntHomTwfMixed x J (innerDerivative basisFactorBTwfMixed) = 1 - 2 * x * J + J ∧
      evalIntHomTwfMixed x J (derivative (innerDerivative basisFactorATwfMixed)) = 1 ∧
      evalIntHomTwfMixed x J (derivative (innerDerivative basisFactorBTwfMixed)) =
        1 - 2 * x := by
  have h : evalIntHomTwfMixed x J (C (1 - 2 * X)) = 1 - 2 * x := by
    simp [evalIntHomTwfMixed_C]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [innerDerivative_basisFactorATwfMixed, map_add, h, evalIntHomTwfMixed_X]
  · rw [innerDerivative_basisFactorBTwfMixed, map_add, map_mul, map_one, h,
      evalIntHomTwfMixed_X]
    ring
  · rw [innerDerivative_basisFactorATwfMixed, derivative_add, derivative_C, derivative_X,
      zero_add, map_one]
  · rw [innerDerivative_basisFactorBTwfMixed, derivative_add, derivative_one, derivative_mul,
      derivative_C, derivative_X, zero_mul, zero_add, zero_add, mul_one, h]

/-- The mixed derivative of the Cramer identity, for free values of the partial derivatives of a
homogeneous monomial. -/
private theorem mixed_identity_TwfMixed (x J c c' d m mU mV mUU mUV mVV α β : ℂ)
    (hα : α = (1 - x) * (x - J)) (hβ : β = (x - 1) * (1 - x * J))
    (R0 : α * mU + β * mV = d * m) (RU : α * mUU + β * mUV = (d - 1) * mU)
    (RV : α * mUV + β * mVV = (d - 1) * mV) :
    (1 - x * J) * (J - x) *
        ((x ^ 2 - 1) * (c' * (mU * -(1 - x) + mV * -((x - 1) * x)) +
            c * (mUU * (-(1 - x) * (1 - 2 * x + J)) +
              mUV * (-(1 - x) * (1 - 2 * x * J + J) + -((x - 1) * x) * (1 - 2 * x + J)) +
              mVV * (-((x - 1) * x) * (1 - 2 * x * J + J)) + mU * 1 + mV * (1 - 2 * x))) -
          (1 - J ^ 2) * (c * (mUU * (-(1 - x)) ^ 2 + 2 * mUV * (-(1 - x) * -((x - 1) * x)) +
            mVV * (-((x - 1) * x)) ^ 2))) =
      (x ^ 2 - 1) ^ 2 * (c' * (β * mV)) +
        d * (x ^ 2 - 1) * (1 - x * J) *
          (c' * m + c * (mU * (1 - 2 * x + J) + mV * (1 - 2 * x * J + J))) +
        (1 - x * J) * (-d * (1 - J ^ 2) + (J - x) * d * (J + 2 * x + 1) - 2 * J * (J - x)) *
          (c * (mU * -(1 - x) + mV * -((x - 1) * x))) +
        d * (1 - x * J) * (-d * (J + 2 * x + 1) - (x + J) + 2 * J) * (c * m) := by
  subst hα hβ
  linear_combination
    (-(x * J - 1) * (-J * c * d + J * c - 2 * c * d * x - c * d - c * x + c' * x ^ 2 - c')) * R0 +
      c * (x - J) * (x - 1) * (x * J - 1) * (J + 2 * x + 1) * RU +
      (-c * x * (x - J) * (x - 1) * (x * J - 1) * (J + 2 * x + 1)) * RV

/-- The monomial `α^i (α l)^k` times the logarithmic derivative in the second variable, in terms
of `α^(i+k)` and the powers of `l`. -/
private theorem mul_monomial_eq_gamma_mul_TwfMixed (i k : ℕ) (α l : ℂ) :
    α * l * ((k : ℂ) * α ^ i * (α * l) ^ (k - 1)) =
      α ^ (i + k) * (l * ((k : ℂ) * l ^ (k - 1))) := by
  rcases k with _ | k
  · simp
  · rw [Nat.add_sub_cancel]
    ring

/-- The mixed derivative of a term of the Cramer identity at `q = 1`, in terms of its value, its
first derivatives, its second derivative in `J` and the powers of `l = (1 - x J)/(J - x)`. -/
private theorem term_TwfMixed (i k : ℕ) (c : ℤ[X]) {x J : ℂ} (hJ : x ≠ J) :
    (1 - x * J) * (J - x) *
        ((x ^ 2 - 1) * evalIntHomTwfMixed x J (derivative (innerDerivative
            (C c * basisFactorATwfMixed ^ i * basisFactorBTwfMixed ^ k))) -
          (1 - J ^ 2) * evalIntHomTwfMixed x J (derivative (derivative
            (C c * basisFactorATwfMixed ^ i * basisFactorBTwfMixed ^ k)))) =
      (x ^ 2 - 1) ^ 2 * (twBasisGamma (i + k) x J * (famNodeL x J *
          (((derivative c).map (Int.castRingHom ℂ)).eval x *
            ((k : ℂ) * famNodeL x J ^ (k - 1))))) +
        ((i + k : ℕ) : ℂ) * (x ^ 2 - 1) * (1 - x * J) * evalIntHomTwfMixed x J
          (innerDerivative (C c * basisFactorATwfMixed ^ i * basisFactorBTwfMixed ^ k)) +
        (1 - x * J) * (-((i + k : ℕ) : ℂ) * (1 - J ^ 2) +
            (J - x) * ((i + k : ℕ) : ℂ) * (J + 2 * x + 1) - 2 * J * (J - x)) *
          evalIntHomTwfMixed x J
            (derivative (C c * basisFactorATwfMixed ^ i * basisFactorBTwfMixed ^ k)) +
        ((i + k : ℕ) : ℂ) * (1 - x * J) *
            (-((i + k : ℕ) : ℂ) * (J + 2 * x + 1) - (x + J) + 2 * J) *
          evalIntHomTwfMixed x J (C c * basisFactorATwfMixed ^ i * basisFactorBTwfMixed ^ k) := by
  obtain ⟨hA, hB, hdA, hdB, hddA, hddB⟩ := evalIntHomTwfMixed_basisFactor x J
  obtain ⟨hiA, hiB, hdiA, hdiB⟩ := evalIntHomTwfMixed_innerDerivative_basisFactor x J
  have hl : (x - 1) * (1 - x * J) = (1 - x) * (x - J) * famNodeL x J := by
    have hne : J - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hJ)
    rw [famNodeL]
    field_simp
    ring
  rw [map_term_TwfMixed, map_derivative_term_TwfMixed, map_derivative_derivative_term_TwfMixed,
    map_innerDerivative_term_TwfMixed, map_derivative_innerDerivative_term_TwfMixed,
    hdA, hdB, hddA, hddB, hiA, hiB, hdiA, hdiB, evalIntHomTwfMixed_C, evalIntHomTwfMixed_C,
    twBasisGamma, ← hA]
  generalize evalIntHomTwfMixed x J basisFactorATwfMixed = α at hA ⊢
  generalize evalIntHomTwfMixed x J basisFactorBTwfMixed = β at hB ⊢
  generalize (c.map (Int.castRingHom ℂ)).eval x = c₀
  generalize ((derivative c).map (Int.castRingHom ℂ)).eval x = c₁
  have hβ : β = α * famNodeL x J := by rw [hB, hA, hl]
  generalize famNodeL x J = l at hβ ⊢
  obtain ⟨R0, RU, RV⟩ := euler_monomial_TwfMixed i k α β
  have CM := mul_monomial_eq_gamma_mul_TwfMixed i k α l
  rw [← hβ] at CM
  have h := mixed_identity_TwfMixed x J c₀ c₁ _ _ _ _ _ _ _ α β hA hB R0 RU RV
  linear_combination h + (x ^ 2 - 1) ^ 2 * c₁ * CM

/-- The value at `(m, l)` of the mixed derivative `(L ∂_L)(M ∂_M)` of the symbol of the operator
of a target. -/
private theorem evalIntPoint_eulerEuler_specialize_twCramerOp_sum_TwfMixed (d : ℕ)
    (T : ℤ[X][X][X]) (m l : ℂ) :
    evalIntPoint (eulerEuler (specialize (twCramerOp d T))) m l =
      2 * m ^ 2 * (l * ∑ k : Fin (d + 1),
        ((derivative (twCoeff d (1 : ℤ) (twfTargetOne T) (Fin.rev k))).map
          (Int.castRingHom ℂ)).eval (m ^ 2) * (((k : ℕ) : ℂ) * l ^ ((k : ℕ) - 1))) := by
  have hcomp : ∀ c : ℤ[X], ((derivative (c.comp (X ^ 2))).map (Int.castRingHom ℂ)).eval m =
      2 * m * ((derivative c).map (Int.castRingHom ℂ)).eval (m ^ 2) := fun c ↦ by
    simp [derivative_comp, Polynomial.map_comp, eval_comp]
  unfold twfTargetOne
  rw [evalIntPoint_eulerEuler, specialize_twCramerOp_eq_sum, coeffDerivative_eq_innerDerivative,
    innerDerivative_sum_TwfMixed, derivative_sum, evalIntPoint_eq_TwfMixed, map_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [innerDerivative_mul, innerDerivative_C, innerDerivative_pow_TwfMixed,
    innerDerivative_X_TwfMixed, mul_zero, mul_zero, add_zero, derivative_C_mul_X_pow, map_mul,
    map_pow, evalIntHomTwfMixed_C, evalIntHomTwfMixed_X, Polynomial.map_mul, eval_mul, hcomp,
    Polynomial.map_natCast, eval_natCast]
  ring

/-- The mixed derivative of the Cramer identity at `q = 1` at a double point `(x, J)` of the
target, in terms of the values at `l = (1 - x J)/(J - x)` of the derivatives of the coefficients
of the symbol. -/
private theorem cramer_one_mixed_TwfMixed (d : ℕ) (p : ℤ[X][X]) (hp : p.natDegree ≤ d)
    {x J : ℂ} (hJ : x ≠ J) (h0 : evalIntHomTwfMixed x J p = 0)
    (hpJ : evalIntHomTwfMixed x J (derivative p) = 0)
    (hpx : evalIntHomTwfMixed x J (innerDerivative p) = 0) :
    (1 - x * J) * (J - x) * (((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
        ((x ^ 2 - 1) * evalIntHomTwfMixed x J (derivative (innerDerivative p)) -
          (1 - J ^ 2) * evalIntHomTwfMixed x J (derivative (derivative p)))) =
      (x ^ 2 - 1) ^ 2 * (twBasisGamma d x J * (famNodeL x J * ∑ k : Fin (d + 1),
        ((derivative (twCoeff d (1 : ℤ) p (Fin.rev k))).map (Int.castRingHom ℂ)).eval x *
          (((k : ℕ) : ℂ) * famNodeL x J ^ ((k : ℕ) - 1)))) := by
  have hC := sum_rev_twCoeff_mul_TwfMixed d p hp
  have e0 : ∑ k : Fin (d + 1), evalIntHomTwfMixed x J (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
      basisFactorATwfMixed ^ (d - (k : ℕ)) * basisFactorBTwfMixed ^ (k : ℕ)) = 0 := by
    rw [← map_sum, hC, map_mul, h0, mul_zero]
  have e1 : ∑ k : Fin (d + 1), evalIntHomTwfMixed x J (derivative
      (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
        basisFactorATwfMixed ^ (d - (k : ℕ)) * basisFactorBTwfMixed ^ (k : ℕ))) = 0 := by
    rw [← map_sum, ← derivative_sum, hC, derivative_C_mul, map_mul, hpJ, mul_zero]
  have e2 : ∑ k : Fin (d + 1), evalIntHomTwfMixed x J (derivative (derivative
      (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
        basisFactorATwfMixed ^ (d - (k : ℕ)) * basisFactorBTwfMixed ^ (k : ℕ)))) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
        evalIntHomTwfMixed x J (derivative (derivative p)) := by
    rw [← map_sum, ← derivative_sum, ← derivative_sum, hC, derivative_C_mul, derivative_C_mul,
      map_mul, evalIntHomTwfMixed_C]
  have ex : ∑ k : Fin (d + 1), evalIntHomTwfMixed x J (innerDerivative
      (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
        basisFactorATwfMixed ^ (d - (k : ℕ)) * basisFactorBTwfMixed ^ (k : ℕ))) = 0 := by
    rw [← map_sum, ← innerDerivative_sum_TwfMixed, hC, innerDerivative_mul, innerDerivative_C,
      map_add, map_mul, map_mul, h0, hpx, mul_zero, mul_zero, add_zero]
  have eJx : ∑ k : Fin (d + 1), evalIntHomTwfMixed x J (derivative (innerDerivative
      (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
        basisFactorATwfMixed ^ (d - (k : ℕ)) * basisFactorBTwfMixed ^ (k : ℕ)))) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
        evalIntHomTwfMixed x J (derivative (innerDerivative p)) := by
    rw [← map_sum, ← derivative_sum, ← innerDerivative_sum_TwfMixed, hC, innerDerivative_mul,
      innerDerivative_C, derivative_add, derivative_C_mul, derivative_C_mul, map_add, map_mul,
      map_mul, hpJ, mul_zero, zero_add, evalIntHomTwfMixed_C]
  have ht : ∀ k : Fin (d + 1), _ :=
    fun k ↦ term_TwfMixed (d - (k : ℕ)) (k : ℕ) (twCoeff d (1 : ℤ) p (Fin.rev k)) hJ
  simp only [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Fin.is_lt _))] at ht
  have key := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ ht k
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  rw [eJx, e2, ex, e1, e0] at key
  linear_combination key

/-- The mixed derivative `(L ∂_L)(M ∂_M)` of the symbol at a double point of the target. -/
theorem evalIntPoint_eulerEuler_specialize_twCramerOp_node (d : ℕ) (T : ℤ[X][X][X])
    (hT : T.natDegree ≤ d) {m₀ J₀ : ℂ} (hJ : m₀ ^ 2 ≠ J₀)
    (hp : evalIntPoint (twfTargetOne T) (m₀ ^ 2) J₀ = 0)
    (hpJ : evalIntPoint (derivative (twfTargetOne T)) (m₀ ^ 2) J₀ = 0)
    (hpx : evalIntPoint (coeffDerivative (twfTargetOne T)) (m₀ ^ 2) J₀ = 0) :
    twBasisGamma d (m₀ ^ 2) J₀ * ((m₀ ^ 2) ^ 2 - 1) ^ 2 *
        evalIntPoint (eulerEuler (specialize (twCramerOp d T))) m₀ (famNodeL (m₀ ^ 2) J₀) =
      2 * m₀ ^ 2 * ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
        ((1 - m₀ ^ 2 * J₀) * (J₀ - m₀ ^ 2)) *
        (((m₀ ^ 2) ^ 2 - 1) *
            evalIntPoint (derivative (coeffDerivative (twfTargetOne T))) (m₀ ^ 2) J₀ -
          (1 - J₀ ^ 2) *
            evalIntPoint (derivative (derivative (twfTargetOne T))) (m₀ ^ 2) J₀) := by
  have h := cramer_one_mixed_TwfMixed d (twfTargetOne T) (natDegree_map_le.trans hT) hJ hp hpJ hpx
  rw [evalIntPoint_eulerEuler_specialize_twCramerOp_sum_TwfMixed, evalIntPoint_eq_TwfMixed,
    evalIntPoint_eq_TwfMixed, coeffDerivative_eq_innerDerivative]
  linear_combination (-2 * m₀ ^ 2) * h

end AJConjecture
