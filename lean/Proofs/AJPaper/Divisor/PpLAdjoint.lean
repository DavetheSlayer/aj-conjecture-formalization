import Mathlib
import AJTwist.Factor.TwFRiccati
import AJTwist.Factor.TwFZeroNormal

/-!
# The adjoint of the operator `P_0` (Unit PpL, node `PpL_Adjoint`)

Source: Section 8.4 of the paper (`conclusion.tex`): "At `a = 0` we only need the factor
`L - 1` … even if the selected divisor specializes to the quadratic alone." The paper proves
only that `P_0` has no right divisor of order one (Section 5.6) and takes `L - 1 ∣ f_S` from
the literature. This package proves instead that `P_0` has no right divisor of order two
either, so that `P_0` is irreducible and the selected divisor is all of `P_0`.

A right divisor of order two is the cofactor of a left divisor of order one, and left divisors
of order one of `P` are right divisors of order one of the adjoint operator.

* `pplOreAdjoint σ d P = ∑_{k ≤ d} σ^k(p_(d-k)) L^k`, the adjoint of `P = ∑ p_k L^k` of order
  at most `d` (`L^d P^*` for the anti-automorphism `L ↦ L⁻¹` fixing the coefficients).
* `ppl_oreMul_linear_quadratic`: the four coefficients of `(s₁ L + s₀) ⋆ (a₂ L² + a₁ L + a₀)`.
* `ppl_oreRiccati_adjoint_of_linear_left`: if `γ P = S ⋆ R` with `S = s₁ L + s₀` of degree at
  most one and `R` of degree at most two, then `(r₀, r₁) = (s₁ σ(γ), σ(s₀) γ)` solves the
  Riccati equation of the adjoint of `P`, i.e. `σ(s₀) γ L + s₁ σ(γ)` is a right factor of it.
* `pplAdjOp`, `pplAdjOpX`: the adjoints of the explicit operator `twZeroExplicitOp` of
  eq. (zero-coeff) (variable `M`, shift `M ↦ t² M`) and of `twfZeroOpX` (variable `x = M²`,
  shift `x ↦ t⁴ x`); `pplAdjOpX.map twfSq = pplAdjOp`.
* `coeff_pplAdjOpX`: the coefficient of `L^k` is `b_k(t⁴, t^(12 + 4k) x)`.
* `coeff_pplAdjOpX_explicit`: the four coefficients in factored form, with the linear forms
  `twfLin j = t^(4j) x - 1`:
  `p†_0 = t²⁸ ℓ₁ ℓ₃`, `p†_1 = -t³² ℓ₃² (t²⁰ x² - t¹² x - 3 t⁸ x + 2)`,
  `p†_2 = t³⁶ ℓ₃² (2 t²⁸ x² - t¹⁶ x - 3 t¹² x + 1)`, `p†_3 = -t⁶⁸ x² ℓ₃ ℓ₅`.

Checked by exact computation from the library's `twZeroB` (scratch `py/d01_adjoint.py`).

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The adjoint `∑_{k ≤ d} σ^k(p_(d-k)) L^k` of an operator `P = ∑ p_k L^k` of order at most
`d`, for the shift `σ`. -/
def pplOreAdjoint {A : Type*} [Semiring A] (σ : A →+* A) (d : ℕ) (P : A[X]) : A[X] :=
  ∑ k ∈ Finset.range (d + 1), monomial k (σ^[k] (P.coeff (d - k)))

/-- The coefficients of the adjoint. -/
theorem coeff_pplOreAdjoint {A : Type*} [Semiring A] (σ : A →+* A) (d : ℕ) (P : A[X]) {k : ℕ}
    (hk : k ≤ d) : (pplOreAdjoint σ d P).coeff k = σ^[k] (P.coeff (d - k)) := by
  rw [pplOreAdjoint, finsetSum_coeff, Finset.sum_eq_single k]
  · rw [coeff_monomial_same]
  · intro j _ hj
    rw [coeff_monomial_of_ne _ (Ne.symm hj)]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h

/-- The adjoint of order `d` has degree at most `d`. -/
theorem natDegree_pplOreAdjoint_le {A : Type*} [Semiring A] (σ : A →+* A) (d : ℕ) (P : A[X]) :
    (pplOreAdjoint σ d P).natDegree ≤ d := by
  unfold pplOreAdjoint
  refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
  exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- The adjoint commutes with homomorphisms intertwining the shifts. -/
theorem map_pplOreAdjoint {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (σ : A →+* A)
    (τ : B →+* B) (hf : ∀ a, f (σ a) = τ (f a)) (d : ℕ) (P : A[X]) :
    (pplOreAdjoint σ d P).map f = pplOreAdjoint τ d (P.map f) := by
  have hit : ∀ (i : ℕ) (a : A), f (σ^[i] a) = τ^[i] (f a) := by
    intro i
    induction i with
    | zero => intro a; rfl
    | succ i ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hf, ih]
  simp only [pplOreAdjoint, Polynomial.map_sum, Polynomial.map_monomial, hit, coeff_map]

/-- The coefficient identity behind `ppl_oreRiccati_adjoint_of_linear_left`. -/
private theorem oreRiccati_adjoint_coeff_pplAdjoint {A : Type*} [CommRing A] (σ : A →+* A)
    (γ s₀ s₁ a₀ a₁ a₂ p₀ p₁ p₂ p₃ : A) (Pd : A[X])
    (h0 : γ * p₀ = s₀ * a₀) (h1 : γ * p₁ = s₁ * σ a₀ + s₀ * a₁)
    (h2 : γ * p₂ = s₁ * σ a₁ + s₀ * a₂) (h3 : γ * p₃ = s₁ * σ a₂)
    (d0 : Pd.coeff 0 = p₃) (d1 : Pd.coeff 1 = σ p₂) (d2 : Pd.coeff 2 = σ (σ p₁))
    (d3 : Pd.coeff 3 = σ (σ (σ p₀))) :
    oreRiccati σ 3 Pd (s₁ * σ γ) (σ s₀ * γ) = 0 := by
  have e1 := congrArg σ h2
  have e2 := congrArg (fun a ↦ σ (σ a)) h1
  have e3 := congrArg (fun a ↦ σ (σ (σ a))) h0
  simp only [map_mul, map_add] at e1 e2 e3
  simp only [oreRiccati, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, Finset.prod_Ico_eq_prod_range, d0, d1, d2, d3,
    Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, map_mul, map_neg]
  norm_num
  linear_combination (σ s₀ * σ (σ s₀) * σ (σ (σ s₀)) * σ γ * σ (σ γ)) * h3
    - (s₁ * σ (σ s₀) * σ (σ (σ s₀)) * σ γ * σ (σ γ)) * e1
    + (s₁ * σ s₁ * σ (σ (σ s₀)) * σ γ * σ (σ γ)) * e2
    - (s₁ * σ s₁ * σ (σ s₁) * σ γ * σ (σ γ)) * e3

/-- The Ore product of an operator of degree at most one and one of degree at most two. -/
theorem ppl_oreMul_linear_quadratic {A : Type*} [CommRing A] (σ : A →+* A)
    {S R : A[X]} (hS : S.natDegree ≤ 1) (hR : R.natDegree ≤ 2) :
    oreMul σ S R = monomial 3 (S.coeff 1 * σ (R.coeff 2)) +
        monomial 2 (S.coeff 1 * σ (R.coeff 1) + S.coeff 0 * R.coeff 2) +
        monomial 1 (S.coeff 1 * σ (R.coeff 0) + S.coeff 0 * R.coeff 1) +
        monomial 0 (S.coeff 0 * R.coeff 0) := by
  conv_lhs => rw [S.as_sum_range' 2 (by omega), R.as_sum_range' 3 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, oreMul_add_left,
    oreMul_add_right, oreMul_monomial_monomial, Function.iterate_succ, Function.iterate_zero,
    Function.comp, id, map_add]
  abel

/-- **Left factors of order one and the adjoint.** If `γ P = S ⋆ R` with `S = s₁ L + s₀` of
degree at most one and `R` of degree at most two, then `(s₁ σ(γ), σ(s₀) γ)` solves the Riccati
equation of the adjoint of `P`: the operator `σ(s₀) γ L + s₁ σ(γ)` is a right factor of the
adjoint. -/
theorem ppl_oreRiccati_adjoint_of_linear_left {A : Type*} [CommRing A] (σ : A →+* A) {γ : A}
    {P S R : A[X]} (hS : S.natDegree ≤ 1) (hR : R.natDegree ≤ 2)
    (h : C γ * P = oreMul σ S R) :
    oreRiccati σ 3 (pplOreAdjoint σ 3 P) (S.coeff 1 * σ γ) (σ (S.coeff 0) * γ) = 0 := by
  have hc := ppl_oreMul_linear_quadratic σ hS hR
  rw [← h] at hc
  have c0 := congrArg (fun p : A[X] ↦ p.coeff 0) hc
  have c1 := congrArg (fun p : A[X] ↦ p.coeff 1) hc
  have c2 := congrArg (fun p : A[X] ↦ p.coeff 2) hc
  have c3 := congrArg (fun p : A[X] ↦ p.coeff 3) hc
  simp [coeff_monomial] at c0 c1 c2 c3
  exact oreRiccati_adjoint_coeff_pplAdjoint σ γ (S.coeff 0) (S.coeff 1) (R.coeff 0) (R.coeff 1)
    (R.coeff 2) (P.coeff 0) (P.coeff 1) (P.coeff 2) (P.coeff 3) _ c0 c1 c2 c3
    (coeff_pplOreAdjoint σ 3 P (by omega)) (coeff_pplOreAdjoint σ 3 P (by omega))
    (coeff_pplOreAdjoint σ 3 P (by omega)) (coeff_pplOreAdjoint σ 3 P (by omega))

/-- The adjoint of the explicit operator `twZeroExplicitOp` of `a = 0` (variable `M`, shift
`M ↦ t² M`). -/
def pplAdjOp : RecOp := pplOreAdjoint coeffShift 3 twZeroExplicitOp

/-- The adjoint of the explicit operator `twfZeroOpX` of `a = 0` in the variable `x = M²`
(shift `x ↦ t⁴ x`). -/
def pplAdjOpX : RecOp := pplOreAdjoint twfShiftX 3 twfZeroOpX

/-- The substitution `x ↦ M²` maps the adjoint in the variable `x` to the adjoint in the
variable `M`. -/
theorem map_twfSq_pplAdjOpX : pplAdjOpX.map twfSq = pplAdjOp := by
  rw [pplAdjOpX, map_pplOreAdjoint twfSq twfShiftX coeffShift twfSq_twfShiftX,
    map_twfSq_twfZeroOpX, pplAdjOp]

/-- The coefficient of `L^k` of the adjoint is `b_k(t⁴, t^(12 + 4k) x)`. -/
theorem coeff_pplAdjOpX (k : Fin 4) :
    pplAdjOpX.coeff (k : ℕ) =
      (twZeroB (X ^ 4 : ℤ[X]) k).comp (C (X ^ (12 + 4 * (k : ℕ))) * X) := by
  have hk : (k : ℕ) ≤ 3 := Nat.lt_succ_iff.mp k.isLt
  have hc : ∀ j : Fin 4, twfZeroOpX.coeff (j : ℕ) =
      (twZeroB (X ^ 4 : ℤ[X]) (Fin.rev j)).comp (C (X ^ 12) * X) := by
    intro j
    rw [twfZeroOpX, finsetSum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one]
    · intro i _ hi
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h ↦ hi (Fin.ext h.symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hit : ∀ (i : ℕ) (b : Coeff), twfShiftX^[i] (b.comp (C (X ^ 12) * X)) =
      b.comp (C (X ^ (12 + 4 * i)) * X) := by
    intro i
    induction i with
    | zero => intro b; rfl
    | succ i ih =>
      intro b
      have hq : (C (X ^ (12 + 4 * i)) * X : Coeff).comp (C (X ^ 4) * X) =
          C (X ^ (12 + 4 * (i + 1))) * X := by
        rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, ← pow_add]
        ring_nf
      rw [Function.iterate_succ_apply', ih]
      change (b.comp (C (X ^ (12 + 4 * i)) * X)).comp (C (X ^ 4) * X) = _
      rw [comp_assoc, hq]
  have h3 : 3 - (k : ℕ) = ((Fin.rev k : Fin 4) : ℕ) := by
    rw [Fin.val_rev]
    omega
  rw [pplAdjOpX, coeff_pplOreAdjoint _ _ _ hk, h3, hc, Fin.rev_rev, hit]

/-- The four coefficients of the adjoint in factored form. -/
theorem coeff_pplAdjOpX_explicit :
    pplAdjOpX.coeff 0 = C (X ^ 28) * twfLin 1 * twfLin 3 ∧
      pplAdjOpX.coeff 1 = -(C (X ^ 32) * twfLin 3 ^ 2 *
        (C (X ^ 20) * X ^ 2 - C (X ^ 12) * X - 3 * C (X ^ 8) * X + 2)) ∧
      pplAdjOpX.coeff 2 = C (X ^ 36) * twfLin 3 ^ 2 *
        (2 * C (X ^ 28) * X ^ 2 - C (X ^ 16) * X - 3 * C (X ^ 12) * X + 1) ∧
      pplAdjOpX.coeff 3 = -(C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5) := by
  have h0 := coeff_pplAdjOpX 0
  have h1 := coeff_pplAdjOpX 1
  have h2 := coeff_pplAdjOpX 2
  have h3 := coeff_pplAdjOpX 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
    at h0 h1 h2 h3
  rw [h0, h1, h2, h3]
  simp only [twZeroB, twfLin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_comp, sub_comp, add_comp,
    neg_comp, pow_comp, C_comp, X_comp, one_comp, ofNat_comp, Nat.cast_ofNat, C_pow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

end AJConjecture
