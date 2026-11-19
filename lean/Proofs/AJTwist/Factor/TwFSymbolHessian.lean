import Mathlib
import AJConjecture.QAlgWeylSymbol
import AJConjecture.QAlgInnerDerivativeBasic
import AJTwist.Factor.TwFBasisJet

/-!
# The symbol of the operator of a target near a point, in the coordinates `(x, J)` (TwF, generic)

Source: revision 5, Section 3.4 (`transfer.tex`, "The characteristic factor": with the shift basis
`R_i|_{q=1} = ((J - x)/(1 - x J))^i` the symbol of the row is `(1 - x J)^(-d) Π`) and Section 5.2,
eq. (physical-derivatives) (`D_u = (A_*/D_*) ∂_J`, `D_x = D_* ∂_K + (J² - 1)/D_* ∂_J`).

Let `p = twfTargetOne T` be the target at `q = 1`, a polynomial in `J` over `ℤ[x]`, and
`P₀(M, L)` the symbol of `twCramerOp d T`. The Cramer identity at `q = 1` reads
`γ(x, J) P₀(x, l(x, J)) = det(x) p(x, J)` with `γ = ((1 - x)(x - J))^d`,
`l = (1 - x J)/(J - x)`. Differentiating it at a point `(x₀, J₀) = (m₀², J₀)`:

* `evalIntPoint_specialize_twCramerOp_node`: `γ P₀ = det · p`;
* `evalIntPoint_derivative_specialize_twCramerOp_node` (`p = 0`):
  `γ (x₀² - 1) ∂_L P₀ = det (J₀ - x₀)² ∂_J p`;
* `evalIntPoint_derivative_derivative_specialize_twCramerOp_node` (`p = ∂_J p = 0`):
  `γ (x₀² - 1)² ∂_L² P₀ = det (J₀ - x₀)⁴ ∂_J² p`;
The mixed derivative `(L ∂_L)(M ∂_M) P₀` is in `AJTwist/Factor/TwFSymbolMixed.lean`.

Here `evalIntPoint f x₀ J₀` evaluates a polynomial of `ℤ[x][J]` at `x = x₀`, `J = J₀`;
`derivative` is `∂_J` and `coeffDerivative` is `∂_x`.

Route: `sum_twCoeff_mul_twBasisPoly d (1 : ℤ)` (the Cramer identity at `q = 1`, a polynomial
identity in `ℤ[x][J]`), with `twBasisPoly d 1 i = (1 - x)^i (x - J)^i (x - 1)^(d-i) (1 - x J)^(d-i)`
(product of constant factors), `specialize_twCramerOp_eq_sum` for the coefficients of `P₀`
(`c_(d-k)(1, M²)`), and the derivations `derivative`, `coeffDerivative` applied to the identity
and evaluated at `(x₀, J₀)`.
The identities were checked at random points for `d = 3, 4, 5` and random targets (scratch
`check_generic_parts.py` (A)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Evaluation at a complex point, as a ring homomorphism. -/
private def evalIntHomTwfHess (x J : ℂ) : ℤ[X][X] →+* ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.evalRingHom x) J).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ)))

/-- `evalIntPoint` is the evaluation homomorphism. -/
private theorem evalIntPoint_eq_TwfHess (p : ℤ[X][X]) (x J : ℂ) :
    evalIntPoint p x J = evalIntHomTwfHess x J p :=
  rfl

/-- The value of a polynomial constant in the outer variable. -/
private theorem evalIntHomTwfHess_C (x J : ℂ) (κ : ℤ[X]) :
    evalIntHomTwfHess x J (C κ) = (κ.map (Int.castRingHom ℂ)).eval x := by
  simp [evalIntHomTwfHess]

/-- The value of the outer variable. -/
private theorem evalIntHomTwfHess_X (x J : ℂ) : evalIntHomTwfHess x J X = J := by
  simp [evalIntHomTwfHess]

/-- The factor `(1 - x)(x - J)` of the basis polynomials at `q = 1`. -/
private def basisFactorATwfHess : ℤ[X][X] := C (1 - X) * (C X - X)

/-- The factor `(x - 1)(1 - x J)` of the basis polynomials at `q = 1`. -/
private def basisFactorBTwfHess : ℤ[X][X] := C (X - 1) * (1 - C X * X)

/-- The basis polynomials at `q = 1` are products of powers of the two factors. -/
private theorem twBasisPoly_one_eq_TwfHess (d i : ℕ) :
    twBasisPoly d (1 : ℤ) i = basisFactorATwfHess ^ i * basisFactorBTwfHess ^ (d - i) := by
  simp [twBasisPoly, basisFactorATwfHess, basisFactorBTwfHess, Finset.prod_const, Nat.card_Ico]

/-- The Cramer identity at `q = 1`, with the sum reversed. -/
private theorem sum_rev_twCoeff_mul_TwfHess (d : ℕ) (p : ℤ[X][X]) (hp : p.natDegree ≤ d) :
    ∑ k : Fin (d + 1), C (twCoeff d (1 : ℤ) p (Fin.rev k)) * basisFactorATwfHess ^ (d - (k : ℕ)) *
        basisFactorBTwfHess ^ (k : ℕ) = C (twDet d (1 : ℤ)) * p := by
  rw [← sum_twCoeff_mul_twBasisPoly d (1 : ℤ) p hp]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k ↦ ?_
  rw [Fin.revPerm_apply, twBasisPoly_one_eq_TwfHess, Fin.val_rev, mul_assoc]
  congr 3 <;> omega

/-- The value of a term `c A^i B^k`. -/
private theorem map_term_TwfHess (E : ℤ[X][X] →+* ℂ) (c : ℤ[X]) (A B : ℤ[X][X]) (i k : ℕ) :
    E (C c * A ^ i * B ^ k) = E (C c) * (E A ^ i * E B ^ k) := by
  rw [map_mul, map_mul, map_pow, map_pow, mul_assoc]

/-- The value of the derivative of a term `c A^i B^k`. -/
private theorem map_derivative_term_TwfHess (E : ℤ[X][X] →+* ℂ) (c : ℤ[X]) (A B : ℤ[X][X])
    (i k : ℕ) :
    E (derivative (C c * A ^ i * B ^ k)) =
      E (C c) * ((i : ℂ) * E A ^ (i - 1) * E B ^ k * E (derivative A) +
        (k : ℂ) * E A ^ i * E B ^ (k - 1) * E (derivative B)) := by
  rw [derivative_mul, derivative_mul, derivative_C, derivative_pow, derivative_pow]
  simp only [map_add, map_mul, map_pow, map_zero, map_natCast]
  ring

/-- The value of the second derivative of a term `c A^i B^k`. -/
private theorem map_derivative_derivative_term_TwfHess (E : ℤ[X][X] →+* ℂ) (c : ℤ[X])
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
private theorem derivative_basisFactorATwfHess : derivative basisFactorATwfHess = C (X - 1) := by
  simp only [basisFactorATwfHess, derivative_mul, derivative_C, derivative_sub, derivative_X,
    derivative_one, C_sub, C_1]
  ring

/-- The derivative in `J` of the second factor. -/
private theorem derivative_basisFactorBTwfHess :
    derivative basisFactorBTwfHess = C (X - X ^ 2) := by
  simp only [basisFactorBTwfHess, derivative_mul, derivative_C, derivative_sub, derivative_X,
    derivative_one, C_sub, C_1, C_pow]
  ring

/-- The values of the two factors and of their derivatives in `J`. -/
private theorem evalIntHomTwfHess_basisFactor (x J : ℂ) :
    evalIntHomTwfHess x J basisFactorATwfHess = (1 - x) * (x - J) ∧
      evalIntHomTwfHess x J basisFactorBTwfHess = (x - 1) * (1 - x * J) ∧
      evalIntHomTwfHess x J (derivative basisFactorATwfHess) = -(1 - x) ∧
      evalIntHomTwfHess x J (derivative basisFactorBTwfHess) = -((x - 1) * x) ∧
      evalIntHomTwfHess x J (derivative (derivative basisFactorATwfHess)) = 0 ∧
      evalIntHomTwfHess x J (derivative (derivative basisFactorBTwfHess)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [basisFactorATwfHess, evalIntHomTwfHess_C, evalIntHomTwfHess_X]
  · simp [basisFactorBTwfHess, evalIntHomTwfHess_C, evalIntHomTwfHess_X]
  · rw [derivative_basisFactorATwfHess, evalIntHomTwfHess_C]
    simp
  · rw [derivative_basisFactorBTwfHess, evalIntHomTwfHess_C]
    simp
    ring
  · rw [derivative_basisFactorATwfHess, derivative_C, map_zero]
  · rw [derivative_basisFactorBTwfHess, derivative_C, map_zero]

/-- `n a^(n-1) a = n a^n`. -/
private theorem natCast_mul_pow_pred_mul_TwfHess (n : ℕ) (a : ℂ) :
    (n : ℂ) * a ^ (n - 1) * a = (n : ℂ) * a ^ n := by
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    ring

/-- `n (n-1) a^(n-2) a = (n - 1) (n a^(n-1))`. -/
private theorem natCast_mul_pred_mul_pow_mul_TwfHess (n : ℕ) (a : ℂ) :
    (n : ℂ) * ((n - 1 : ℕ) : ℂ) * a ^ (n - 1 - 1) * a =
      ((n : ℂ) - 1) * ((n : ℂ) * a ^ (n - 1)) := by
  rcases n with _ | n
  · simp
  · have h := natCast_mul_pow_pred_mul_TwfHess n a
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination ((n : ℂ) + 1) * h

/-- The first derivative in `J` of the Cramer identity, for free values of the partial
derivatives of a homogeneous monomial. -/
private theorem hessian_first_TwfHess (x J c d m mU mV α β : ℂ) (hα : α = (1 - x) * (x - J))
    (hβ : β = (x - 1) * (1 - x * J)) (R0 : α * mU + β * mV = d * m) :
    (J - x) ^ 2 * (c * (mU * -(1 - x) + mV * -((x - 1) * x))) =
      (J - x) * d * (c * m) + (x ^ 2 - 1) * (c * (α * mV)) := by
  subst hα hβ
  linear_combination c * (J - x) * R0

/-- The second derivative in `J` of the Cramer identity, for free values of the partial
derivatives of a homogeneous monomial. -/
private theorem hessian_second_TwfHess (x J c d m mU mV mUU mUV mVV α β : ℂ)
    (hα : α = (1 - x) * (x - J)) (hβ : β = (x - 1) * (1 - x * J))
    (R0 : α * mU + β * mV = d * m) (RU : α * mUU + β * mUV = (d - 1) * mU)
    (RV : α * mUV + β * mVV = (d - 1) * mV) :
    (J - x) ^ 4 * (c * (mUU * (-(1 - x)) ^ 2 + 2 * mUV * (-(1 - x) * -((x - 1) * x)) +
        mVV * (-((x - 1) * x)) ^ 2)) =
      -(d * (d - 1)) * (J - x) ^ 2 * (c * m) +
        2 * (d - 1) * (J - x) ^ 3 * (c * (mU * -(1 - x) + mV * -((x - 1) * x))) +
        (x ^ 2 - 1) ^ 2 * (c * (α ^ 2 * mVV)) := by
  subst hα hβ
  linear_combination (-c * (x - J) ^ 2 * (d - 1)) * R0 + (-c * (x - J) ^ 3 * (x - 1)) * RU +
    c * (x - J) ^ 2 * (x - 1) * (2 * x ^ 2 - x * J - 1) * RV

/-- Euler's relations for the partial derivatives of the monomial `α^i β^k`. -/
private theorem euler_monomial_TwfHess (i k : ℕ) (α β : ℂ) :
    α * ((i : ℂ) * α ^ (i - 1) * β ^ k) + β * ((k : ℂ) * α ^ i * β ^ (k - 1)) =
        ((i + k : ℕ) : ℂ) * (α ^ i * β ^ k) ∧
      α * ((i : ℂ) * ((i - 1 : ℕ) : ℂ) * α ^ (i - 1 - 1) * β ^ k) +
          β * ((i : ℂ) * (k : ℂ) * α ^ (i - 1) * β ^ (k - 1)) =
        (((i + k : ℕ) : ℂ) - 1) * ((i : ℂ) * α ^ (i - 1) * β ^ k) ∧
      α * ((i : ℂ) * (k : ℂ) * α ^ (i - 1) * β ^ (k - 1)) +
          β * ((k : ℂ) * ((k - 1 : ℕ) : ℂ) * α ^ i * β ^ (k - 1 - 1)) =
        (((i + k : ℕ) : ℂ) - 1) * ((k : ℂ) * α ^ i * β ^ (k - 1)) := by
  have h1 := natCast_mul_pow_pred_mul_TwfHess i α
  have h2 := natCast_mul_pow_pred_mul_TwfHess k β
  have h3 := natCast_mul_pred_mul_pow_mul_TwfHess i α
  have h4 := natCast_mul_pred_mul_pow_mul_TwfHess k β
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination β ^ k * h1 + α ^ i * h2
  · linear_combination β ^ k * h3 + (i : ℂ) * α ^ (i - 1) * h2
  · linear_combination (k : ℂ) * β ^ (k - 1) * h1 + α ^ i * h4

/-- The monomial `α^i (α l)^k` and its partial derivatives in the second variable, in terms of
`α^(i+k)` and the powers of `l`. -/
private theorem monomial_eq_gamma_mul_TwfHess (i k : ℕ) (α l : ℂ) :
    α ^ i * (α * l) ^ k = α ^ (i + k) * l ^ k ∧
      α * ((k : ℂ) * α ^ i * (α * l) ^ (k - 1)) = α ^ (i + k) * ((k : ℂ) * l ^ (k - 1)) ∧
      α ^ 2 * ((k : ℂ) * ((k - 1 : ℕ) : ℂ) * α ^ i * (α * l) ^ (k - 1 - 1)) =
        α ^ (i + k) * ((k : ℂ) * ((k - 1 : ℕ) : ℂ) * l ^ (k - 1 - 1)) := by
  refine ⟨by ring, ?_, ?_⟩
  · rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel]
      ring
  · rcases k with _ | _ | k
    · simp
    · simp
    · simp only [Nat.add_sub_cancel]
      ring

/-- The value and the first two derivatives in `J` of a term of the Cramer identity at `q = 1`,
in terms of the powers of `l = (1 - x J)/(J - x)`. -/
private theorem term_TwfHess (i k : ℕ) (c : ℤ[X]) {x J : ℂ} (hJ : x ≠ J) :
    evalIntHomTwfHess x J (C c * basisFactorATwfHess ^ i * basisFactorBTwfHess ^ k) =
        twBasisGamma (i + k) x J * ((c.map (Int.castRingHom ℂ)).eval x * famNodeL x J ^ k) ∧
      (J - x) ^ 2 * evalIntHomTwfHess x J
          (derivative (C c * basisFactorATwfHess ^ i * basisFactorBTwfHess ^ k)) =
        (J - x) * ((i + k : ℕ) : ℂ) *
            evalIntHomTwfHess x J (C c * basisFactorATwfHess ^ i * basisFactorBTwfHess ^ k) +
          (x ^ 2 - 1) * (twBasisGamma (i + k) x J *
            ((c.map (Int.castRingHom ℂ)).eval x * ((k : ℂ) * famNodeL x J ^ (k - 1)))) ∧
      (J - x) ^ 4 * evalIntHomTwfHess x J
          (derivative (derivative (C c * basisFactorATwfHess ^ i * basisFactorBTwfHess ^ k))) =
        -(((i + k : ℕ) : ℂ) * (((i + k : ℕ) : ℂ) - 1)) * (J - x) ^ 2 *
            evalIntHomTwfHess x J (C c * basisFactorATwfHess ^ i * basisFactorBTwfHess ^ k) +
          2 * (((i + k : ℕ) : ℂ) - 1) * (J - x) ^ 3 * evalIntHomTwfHess x J
            (derivative (C c * basisFactorATwfHess ^ i * basisFactorBTwfHess ^ k)) +
          (x ^ 2 - 1) ^ 2 * (twBasisGamma (i + k) x J * ((c.map (Int.castRingHom ℂ)).eval x *
            ((k : ℂ) * ((k - 1 : ℕ) : ℂ) * famNodeL x J ^ (k - 1 - 1)))) := by
  obtain ⟨hA, hB, hdA, hdB, hddA, hddB⟩ := evalIntHomTwfHess_basisFactor x J
  have hl : (x - 1) * (1 - x * J) = (1 - x) * (x - J) * famNodeL x J := by
    have hne : J - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hJ)
    rw [famNodeL]
    field_simp
    ring
  rw [map_term_TwfHess, map_derivative_term_TwfHess, map_derivative_derivative_term_TwfHess,
    hdA, hdB, hddA, hddB, evalIntHomTwfHess_C, twBasisGamma, ← hA]
  generalize evalIntHomTwfHess x J basisFactorATwfHess = α at hA ⊢
  generalize evalIntHomTwfHess x J basisFactorBTwfHess = β at hB ⊢
  generalize (c.map (Int.castRingHom ℂ)).eval x = c₀
  have hβ : β = α * famNodeL x J := by rw [hB, hA, hl]
  generalize famNodeL x J = l at hβ ⊢
  obtain ⟨R0, RU, RV⟩ := euler_monomial_TwfHess i k α β
  obtain ⟨C0, C1, C2⟩ := monomial_eq_gamma_mul_TwfHess i k α l
  rw [← hβ] at C0 C1 C2
  have h1 := hessian_first_TwfHess x J c₀ _ _ _ _ α β hA hB R0
  have h2 := hessian_second_TwfHess x J c₀ _ _ _ _ _ _ _ α β hA hB R0 RU RV
  refine ⟨?_, ?_, ?_⟩
  · linear_combination c₀ * C0
  · linear_combination h1 + (x ^ 2 - 1) * c₀ * C1
  · linear_combination h2 + (x ^ 2 - 1) ^ 2 * c₀ * C2

/-- The target at `t = -1` (`q = 1`): a polynomial in `J` with coefficients in `ℤ[x]`. -/
def twfTargetOne (T : ℤ[X][X][X]) : ℤ[X][X] :=
  T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ)))

/-- The values at `(m, l)` of the symbol of the operator of a target and of its first two
derivatives in `L`. -/
private theorem evalIntPoint_specialize_twCramerOp_sums_TwfHess (d : ℕ) (T : ℤ[X][X][X])
    (m l : ℂ) :
    evalIntPoint (specialize (twCramerOp d T)) m l =
        ∑ k : Fin (d + 1), ((twCoeff d (1 : ℤ) (twfTargetOne T) (Fin.rev k)).map
          (Int.castRingHom ℂ)).eval (m ^ 2) * l ^ (k : ℕ) ∧
      evalIntPoint (derivative (specialize (twCramerOp d T))) m l =
        ∑ k : Fin (d + 1), ((twCoeff d (1 : ℤ) (twfTargetOne T) (Fin.rev k)).map
          (Int.castRingHom ℂ)).eval (m ^ 2) * (((k : ℕ) : ℂ) * l ^ ((k : ℕ) - 1)) ∧
      evalIntPoint (derivative (derivative (specialize (twCramerOp d T)))) m l =
        ∑ k : Fin (d + 1), ((twCoeff d (1 : ℤ) (twfTargetOne T) (Fin.rev k)).map
          (Int.castRingHom ℂ)).eval (m ^ 2) *
            (((k : ℕ) : ℂ) * (((k : ℕ) - 1 : ℕ) : ℂ) * l ^ ((k : ℕ) - 1 - 1)) := by
  have hcomp : ∀ c : ℤ[X], ((c.comp (X ^ 2)).map (Int.castRingHom ℂ)).eval m =
      (c.map (Int.castRingHom ℂ)).eval (m ^ 2) := fun c ↦ by
    simp [Polynomial.map_comp, eval_comp]
  unfold twfTargetOne
  rw [specialize_twCramerOp_eq_sum, evalIntPoint_eq_TwfHess, evalIntPoint_eq_TwfHess,
    evalIntPoint_eq_TwfHess, derivative_sum, derivative_sum, map_sum, map_sum, map_sum]
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, evalIntHomTwfHess_C, evalIntHomTwfHess_X, hcomp]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [derivative_C_mul_X_pow, map_mul, map_pow, evalIntHomTwfHess_C, evalIntHomTwfHess_X,
      Polynomial.map_mul, eval_mul, hcomp, Polynomial.map_natCast, eval_natCast]
    ring
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [derivative_C_mul_X_pow, derivative_C_mul_X_pow, map_mul, map_pow, evalIntHomTwfHess_C,
      evalIntHomTwfHess_X, Polynomial.map_mul, Polynomial.map_mul, eval_mul, eval_mul, hcomp,
      Polynomial.map_natCast, eval_natCast, Polynomial.map_natCast, eval_natCast]
    ring

/-- The Cramer identity at `q = 1` and its first two derivatives in `J` at a point `(x, J)`, in
terms of the values at `l = (1 - x J)/(J - x)` of the symbol and of its derivatives. -/
private theorem cramer_one_jets_TwfHess (d : ℕ) (p : ℤ[X][X]) (hp : p.natDegree ≤ d) {x J : ℂ}
    (hJ : x ≠ J) :
    ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x * evalIntHomTwfHess x J p =
        twBasisGamma d x J * ∑ k : Fin (d + 1),
          ((twCoeff d (1 : ℤ) p (Fin.rev k)).map (Int.castRingHom ℂ)).eval x *
            famNodeL x J ^ (k : ℕ) ∧
      (J - x) ^ 2 * (((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
          evalIntHomTwfHess x J (derivative p)) =
        (J - x) * (d : ℂ) * (((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
            evalIntHomTwfHess x J p) +
          (x ^ 2 - 1) * (twBasisGamma d x J * ∑ k : Fin (d + 1),
            ((twCoeff d (1 : ℤ) p (Fin.rev k)).map (Int.castRingHom ℂ)).eval x *
              (((k : ℕ) : ℂ) * famNodeL x J ^ ((k : ℕ) - 1))) ∧
      (J - x) ^ 4 * (((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
          evalIntHomTwfHess x J (derivative (derivative p))) =
        -((d : ℂ) * ((d : ℂ) - 1)) * (J - x) ^ 2 *
            (((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x * evalIntHomTwfHess x J p) +
          2 * ((d : ℂ) - 1) * (J - x) ^ 3 *
            (((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
              evalIntHomTwfHess x J (derivative p)) +
          (x ^ 2 - 1) ^ 2 * (twBasisGamma d x J * ∑ k : Fin (d + 1),
            ((twCoeff d (1 : ℤ) p (Fin.rev k)).map (Int.castRingHom ℂ)).eval x *
              (((k : ℕ) : ℂ) * (((k : ℕ) - 1 : ℕ) : ℂ) * famNodeL x J ^ ((k : ℕ) - 1 - 1))) := by
  have hC := sum_rev_twCoeff_mul_TwfHess d p hp
  have e0 : ∑ k : Fin (d + 1), evalIntHomTwfHess x J (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
      basisFactorATwfHess ^ (d - (k : ℕ)) * basisFactorBTwfHess ^ (k : ℕ)) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x * evalIntHomTwfHess x J p := by
    rw [← map_sum, hC, map_mul, evalIntHomTwfHess_C]
  have e1 : ∑ k : Fin (d + 1), evalIntHomTwfHess x J (derivative
      (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
        basisFactorATwfHess ^ (d - (k : ℕ)) * basisFactorBTwfHess ^ (k : ℕ))) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
        evalIntHomTwfHess x J (derivative p) := by
    rw [← map_sum, ← derivative_sum, hC, derivative_C_mul, map_mul, evalIntHomTwfHess_C]
  have e2 : ∑ k : Fin (d + 1), evalIntHomTwfHess x J (derivative (derivative
      (C (twCoeff d (1 : ℤ) p (Fin.rev k)) *
        basisFactorATwfHess ^ (d - (k : ℕ)) * basisFactorBTwfHess ^ (k : ℕ)))) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x *
        evalIntHomTwfHess x J (derivative (derivative p)) := by
    rw [← map_sum, ← derivative_sum, ← derivative_sum, hC, derivative_C_mul, derivative_C_mul,
      map_mul, evalIntHomTwfHess_C]
  have ht : ∀ k : Fin (d + 1), _ :=
    fun k ↦ term_TwfHess (d - (k : ℕ)) (k : ℕ) (twCoeff d (1 : ℤ) p (Fin.rev k)) hJ
  simp only [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Fin.is_lt _))] at ht
  have s0 := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ (ht k).1
  have s1 := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ (ht k).2.1
  have s2 := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ (ht k).2.2
  rw [← Finset.mul_sum, e0] at s0
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, e1, e0] at s1
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, e2, e1, e0] at s2
  exact ⟨s0, s1, s2⟩

/-- The symbol at the point `(m₀, l(m₀², J₀))` is the target at `(m₀², J₀)`, up to units. -/
theorem evalIntPoint_specialize_twCramerOp_node (d : ℕ) (T : ℤ[X][X][X]) (hT : T.natDegree ≤ d)
    {m₀ J₀ : ℂ} (hJ : m₀ ^ 2 ≠ J₀) :
    twBasisGamma d (m₀ ^ 2) J₀ *
        evalIntPoint (specialize (twCramerOp d T)) m₀ (famNodeL (m₀ ^ 2) J₀) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
        evalIntPoint (twfTargetOne T) (m₀ ^ 2) J₀ := by
  obtain ⟨hv0, -, -⟩ :=
    evalIntPoint_specialize_twCramerOp_sums_TwfHess d T m₀ (famNodeL (m₀ ^ 2) J₀)
  obtain ⟨h0, -, -⟩ := cramer_one_jets_TwfHess d (twfTargetOne T) (natDegree_map_le.trans hT) hJ
  rw [hv0, evalIntPoint_eq_TwfHess]
  exact h0.symm

/-- The `L`-derivative of the symbol at a zero of the target. -/
theorem evalIntPoint_derivative_specialize_twCramerOp_node (d : ℕ) (T : ℤ[X][X][X])
    (hT : T.natDegree ≤ d) {m₀ J₀ : ℂ} (hJ : m₀ ^ 2 ≠ J₀)
    (hp : evalIntPoint (twfTargetOne T) (m₀ ^ 2) J₀ = 0) :
    twBasisGamma d (m₀ ^ 2) J₀ * ((m₀ ^ 2) ^ 2 - 1) *
        evalIntPoint (derivative (specialize (twCramerOp d T))) m₀ (famNodeL (m₀ ^ 2) J₀) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) * (J₀ - m₀ ^ 2) ^ 2 *
        evalIntPoint (derivative (twfTargetOne T)) (m₀ ^ 2) J₀ := by
  obtain ⟨-, hv1, -⟩ :=
    evalIntPoint_specialize_twCramerOp_sums_TwfHess d T m₀ (famNodeL (m₀ ^ 2) J₀)
  obtain ⟨-, h1, -⟩ := cramer_one_jets_TwfHess d (twfTargetOne T) (natDegree_map_le.trans hT) hJ
  rw [evalIntPoint_eq_TwfHess] at hp
  rw [hp, mul_zero, mul_zero, zero_add] at h1
  rw [hv1, evalIntPoint_eq_TwfHess]
  linear_combination -h1

/-- The second `L`-derivative of the symbol at a double zero (in `J`) of the target. -/
theorem evalIntPoint_derivative_derivative_specialize_twCramerOp_node (d : ℕ)
    (T : ℤ[X][X][X]) (hT : T.natDegree ≤ d) {m₀ J₀ : ℂ} (hJ : m₀ ^ 2 ≠ J₀)
    (hp : evalIntPoint (twfTargetOne T) (m₀ ^ 2) J₀ = 0)
    (hpJ : evalIntPoint (derivative (twfTargetOne T)) (m₀ ^ 2) J₀ = 0) :
    twBasisGamma d (m₀ ^ 2) J₀ * ((m₀ ^ 2) ^ 2 - 1) ^ 2 *
        evalIntPoint (derivative (derivative (specialize (twCramerOp d T)))) m₀
          (famNodeL (m₀ ^ 2) J₀) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) * (J₀ - m₀ ^ 2) ^ 4 *
        evalIntPoint (derivative (derivative (twfTargetOne T))) (m₀ ^ 2) J₀ := by
  obtain ⟨-, -, hv2⟩ :=
    evalIntPoint_specialize_twCramerOp_sums_TwfHess d T m₀ (famNodeL (m₀ ^ 2) J₀)
  obtain ⟨-, -, h2⟩ := cramer_one_jets_TwfHess d (twfTargetOne T) (natDegree_map_le.trans hT) hJ
  rw [evalIntPoint_eq_TwfHess] at hp hpJ
  rw [hp, hpJ, mul_zero, mul_zero, mul_zero, zero_add, zero_add] at h2
  rw [hv2, evalIntPoint_eq_TwfHess]
  linear_combination -h2

end AJConjecture
