import Mathlib
import AJTwist.Quantum.TwQTransferOp
import AJTwist.Quantum.TwQWindowDetOne

/-!
# The explicit coefficients of `P_0` (Unit Q3)

Source: revision 5, Section 5.5 (`operators.tex`, "First-order right divisors at `a = 0`"),
eq. (zero-coeff): the three-pole solve at `a = 0`, after multiplication by
`x (x - q)(x - q²)(x² - q³)(x - 1)`, gives
`b_0 = q⁵ (x - q²)(x - 1)`, `b_1 = -q³ (x - q)² (2q³ - q² x - 3 q x + x²)`,
`b_2 = q² (x - q²)² (q³ - q² x - 3 q x + 2 x²)`, `b_3 = -q x² (x - q³)(x - q)`.

In the cleared pole basis of the scaffolds this is the polynomial identity
`∑_i b_i P_i = β · twZeroTarget q` with `β = (x - q)² (x - q²)² (x - q³)(x² - q³)(x - 1)`
(`sum_twZeroB_mul_twBasisPoly`), over every commutative ring; by Cramer's rule
`det · b_i = β · c_i` for the Cramer numerators `c_i` of `P_0` (`twDet_mul_twZeroB`), so
`twTransferOp 0` and the explicit operator `twZeroExplicitOp` differ by nonzero left scalars
(`twZeroExplicitOp_mul_eq`). The factor theory at `a = 0` (the Riccati equation
`b_0 + b_1 r + b_2 r σ(r) + b_3 r σ(r) σ²(r) = 0`) uses the explicit form.

Checked: eq. (zero-coeff) with the stated multiplier, symbolically (scratch `check_ops.py 0`);
the two identities at random points (scratch `check_misc.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficients `b_0, …, b_3` of eq. (zero-coeff), as polynomials in `x` over a ring
containing `q`. -/
def twZeroB {R : Type*} [CommRing R] (q : R) : Fin 4 → R[X] :=
  ![C (q ^ 5) * (X - C (q ^ 2)) * (X - 1),
    -(C (q ^ 3) * (X - C q) ^ 2 * (2 * C (q ^ 3) - C (q ^ 2) * X - 3 * C q * X + X ^ 2)),
    C (q ^ 2) * (X - C (q ^ 2)) ^ 2 * (C (q ^ 3) - C (q ^ 2) * X - 3 * C q * X + 2 * X ^ 2),
    -(C q * X ^ 2 * (X - C (q ^ 3)) * (X - C q))]

/-- The multiplier `β = (x - q)² (x - q²)² (x - q³)(x² - q³)(x - 1)`. -/
def twZeroBeta {R : Type*} [CommRing R] (q : R) : R[X] :=
  (X - C q) ^ 2 * (X - C (q ^ 2)) ^ 2 * (X - C (q ^ 3)) * (X ^ 2 - C (q ^ 3)) * (X - 1)

/-- The explicit operator `∑_k b_(3-k)(t⁴, t¹² M²) L^k` of eq. (zero-coeff), in the forward
convention. -/
def twZeroExplicitOp : RecOp :=
  ∑ k : Fin 4,
    C ((twZeroB (X ^ 4 : ℤ[X]) (Fin.rev k)).comp (C (X ^ 12) * X ^ 2)) * X ^ (k : ℕ)

/-- Division by `X` undoes multiplication by `X` on the left. -/
private theorem divX_X_mul_zeroCoeff {A : Type*} [Semiring A] (p : A[X]) :
    divX (X * p) = p := by
  ext k
  rw [coeff_divX, coeff_X_mul]

/-- The cleared numerator at `a = 0`, with the division by `J` carried out. -/
private theorem twZeroTarget_eq_explicit_zeroCoeff {R : Type*} [CommRing R] (q : R) :
    twZeroTarget q =
      C (C q) * (C (C q ^ 3 * X) * X * (1 - X) +
        ((C (X ^ 2 + C q ^ 3 - C q ^ 2 * X + 2 * C q ^ 3 * X) -
          C (C q * X + 2 * C q * (X ^ 2 + C q ^ 3) + C q ^ 4 * X) * X +
          C (2 * C q ^ 2 * X + C q ^ 2 * (X ^ 2 + C q ^ 3)) * X ^ 2 -
          C (C q ^ 3 * X) * X ^ 3))) +
        2 * C (C q ^ 3 * X) * (1 - C (C q) * X) := by
  have hinner : C (C (q ^ (3 - 1)) * X) * (1 - X) -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (3 - 1))) - C X * X) *
        (1 - X : R[X][X]).comp (C (C q) * X) =
      X * ((C (X ^ 2 + C q ^ 3 - C q ^ 2 * X + 2 * C q ^ 3 * X) -
          C (C q * X + 2 * C q * (X ^ 2 + C q ^ 3) + C q ^ 4 * X) * X +
          C (2 * C q ^ 2 * X + C q ^ 2 * (X ^ 2 + C q ^ 3)) * X ^ 2 -
          C (C q ^ 3 * X) * X ^ 3)) := by
    simp only [sub_comp, one_comp, X_comp, C_add, C_sub, C_mul, C_pow, C_ofNat,
      show 3 - 1 = 2 from rfl]
    ring
  rw [twZeroTarget, twAdjoint, hinner, divX_X_mul_zeroCoeff]
  simp only [C_pow]

/-- The four basis polynomials of the window `3`. -/
private theorem twBasisPoly_three_zeroCoeff {R : Type*} [CommRing R] (q : R) :
    twBasisPoly 3 q 0 = (C (X - C (q ^ 1)) * (C (C (q ^ 0)) - C X * X)) *
        (C (X - C (q ^ 2)) * (C (C (q ^ 1)) - C X * X)) *
        (C (X - C (q ^ 3)) * (C (C (q ^ 2)) - C X * X)) ∧
      twBasisPoly 3 q 1 = (C (C (q ^ 0) - X) * (C X - C (C (q ^ 1)) * X)) *
        ((C (X - C (q ^ 2)) * (C (C (q ^ 1)) - C X * X)) *
        (C (X - C (q ^ 3)) * (C (C (q ^ 2)) - C X * X))) ∧
      twBasisPoly 3 q 2 = (C (C (q ^ 0) - X) * (C X - C (C (q ^ 1)) * X)) *
        (C (C (q ^ 1) - X) * (C X - C (C (q ^ 2)) * X)) *
        (C (X - C (q ^ 3)) * (C (C (q ^ 2)) - C X * X)) ∧
      twBasisPoly 3 q 3 = (C (C (q ^ 0) - X) * (C X - C (C (q ^ 1)) * X)) *
        (C (C (q ^ 1) - X) * (C X - C (C (q ^ 2)) * X)) *
        (C (C (q ^ 2) - X) * (C X - C (C (q ^ 3)) * X)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [twBasisPoly, Finset.prod_range_succ]
  · simp [twBasisPoly, Finset.prod_Ico_succ_top]
  · simp [twBasisPoly, Finset.prod_range_succ]
  · simp [twBasisPoly, Finset.prod_range_succ]

/-- Eq. (zero-coeff) in the cleared pole basis: `∑_i b_i P_i = β · twZeroTarget q`. -/
theorem sum_twZeroB_mul_twBasisPoly {R : Type*} [CommRing R] (q : R) :
    ∑ i : Fin 4, C (twZeroB q i) * twBasisPoly 3 q i = C (twZeroBeta q) * twZeroTarget q := by
  obtain ⟨h0, h1, h2, h3⟩ := twBasisPoly_three_zeroCoeff q
  rw [Fin.sum_univ_four, twZeroTarget_eq_explicit_zeroCoeff]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h0, h1, h2,
    show ((3 : Fin 4) : ℕ) = 3 from rfl, h3, twZeroB, twZeroBeta, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, C_add, C_sub, C_mul, C_pow, C_ofNat, C_neg, C_1, pow_zero, pow_one]
  ring

/-- The explicit coefficients are proportional to the Cramer numerators of `P_0`. -/
theorem twDet_mul_twZeroB {R : Type*} [CommRing R] (q : R) (i : Fin 4) :
    twDet 3 q * twZeroB q i = twZeroBeta q * twCoeff 3 q (twZeroTarget q) i := by
  have hmv : (twMatrix 3 q).mulVec (twZeroB q) =
      twZeroBeta q • fun k : Fin 4 ↦ (twZeroTarget q).coeff k := by
    funext k
    have h := congrArg (fun p : R[X][X] ↦ p.coeff (k : ℕ)) (sum_twZeroB_mul_twBasisPoly q)
    simp only [finsetSum_coeff, coeff_C_mul] at h
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [twMatrix, Matrix.of_apply, mul_comm]
  have hc := congrFun (congrArg (Matrix.cramer (twMatrix 3 q)) hmv) i
  rw [map_smul, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul] at hc
  exact hc

/-- `P_0` and the explicit operator of eq. (zero-coeff) differ by left scalars. -/
theorem twZeroExplicitOp_mul_eq :
    C ((twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)) * twZeroExplicitOp =
      C ((twZeroBeta (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)) * twTransferOp 0 := by
  rw [twTransferOp_zero, twZeroExplicitOp, twCramerOp, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := congrArg (fun p : ℤ[X][X] ↦ p.comp (C (X ^ 12) * X ^ 2))
    (twDet_mul_twZeroB (X ^ 4 : ℤ[X]) (Fin.rev k))
  simp only [mul_comp] at h
  rw [← mul_assoc, ← C_mul, h, show 4 * 3 = 12 from rfl, C_mul, mul_assoc]

/-- The two left scalars are not zero. -/
theorem twZero_scalars_ne_zero :
    (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2) ≠ 0 ∧
      (twZeroBeta (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2) ≠ 0 := by
  have hs : (C (X ^ 12) * X ^ 2 : ℤ[X][X]).natDegree = 2 :=
    natDegree_C_mul_X_pow 2 _ (pow_ne_zero 12 X_ne_zero)
  have hcomp : ∀ p : ℤ[X][X], p ≠ 0 → p.comp (C (X ^ 12) * X ^ 2) ≠ 0 := by
    intro p hp h
    have hd := congrArg natDegree h
    rw [natDegree_comp, hs, natDegree_zero] at hd
    have hp0 : p.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero hp0, C_comp] at h
    rw [eq_C_of_natDegree_eq_zero hp0, h] at hp
    exact hp rfl
  refine ⟨hcomp _ fun h ↦ ?_, hcomp _ ?_⟩
  · have h1 := map_twDet (Polynomial.evalRingHom (-1 : ℤ)) 3 (X ^ 4 : ℤ[X])
    have hq : (Polynomial.evalRingHom (-1 : ℤ)) (X ^ 4) = 1 := by
      rw [coe_evalRingHom, eval_pow, eval_X]
      norm_num
    rw [h, Polynomial.map_zero, hq] at h1
    have h0 := twDet_one_eval_ne_zero 3 (x₀ := 0) (by norm_num) (by norm_num)
    rw [← h1, Polynomial.map_zero, eval_zero] at h0
    exact h0 rfl
  · have hm : (twZeroBeta (X ^ 4 : ℤ[X])).Monic := by
      unfold twZeroBeta
      exact ((((monic_X_sub_C _).pow 2).mul ((monic_X_sub_C _).pow 2)).mul
        (monic_X_sub_C _)).mul (monic_X_pow_sub_C _ two_ne_zero) |>.mul
          (by simpa using monic_X_sub_C (1 : ℤ[X]))
    exact hm.ne_zero

end AJConjecture
