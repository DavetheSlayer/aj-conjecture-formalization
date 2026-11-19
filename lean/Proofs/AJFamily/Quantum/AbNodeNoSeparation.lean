import Mathlib
import AJConjecture.QAlgTwistFactorPrime
import AJFamily.Quantum.AbNodeCollision
import AJFamily.Quantum.AbNodeWeyl
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.NodeCriterionCollision
import AJFamily.Quantum.TwistPolyPrime

/-!
# Abelian node: `L - 1` and `B_m` are not separated

`toComparison_X_sub_one_dvd_iff_twistPoly_dvd`: by the index criterion at the abelian node, the
symbol of a right pseudo-factor of `famTransferOp m` is divisible by `L - 1` exactly when it is
divisible by `B_m`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The value of `∂_L (L - 1)` at a point. -/
private theorem evalIntPoint_derivative_X_sub_one_abNoSep (m l : ℂ) :
    evalIntPoint (derivative (X - 1)) m l = 1 := by
  simp [evalIntPoint, evalPoint]

/-- `L - 1` does not depend on `M`. -/
private theorem evalIntPoint_coeffDerivative_X_sub_one_abNoSep (m l : ℂ) :
    evalIntPoint (coeffDerivative (X - 1)) m l = 0 := by
  have h0 : coeffDerivative (X - 1 : ℤ[X][X]) = 0 := by
    rw [coeffDerivative, Polynomial.sum_def]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    rw [coeff_sub, coeff_X, coeff_one]
    split_ifs <;> simp
  simp [h0, evalIntPoint, evalPoint]

/-- The first polynomial in `M` of the family symbol identity does not vanish away from
`M² = ±1`. -/
theorem eval_symbolLeft_ne_zero (m : ℕ) {m₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h2 : m₀ ^ 2 ≠ -1) :
    ((((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3) : ℤ[X])).map
      (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
  have h4 : m₀ ^ 4 - 1 = (m₀ ^ 2 - 1) * (m₀ ^ 2 + 1) := by ring
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    map_X, eval_mul, eval_pow, eval_sub, eval_X, eval_one, h4]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h1)) (pow_ne_zero _ (mul_ne_zero
    (sub_ne_zero.mpr h1) (fun h ↦ h2 (eq_neg_of_add_eq_zero_left h))))

/-- The second polynomial in `M` of the family symbol identity does not vanish away from
`M² = ±1`. -/
theorem eval_symbolRight_ne_zero (m : ℕ) {m₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h2 : m₀ ^ 2 ≠ -1) :
    ((((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)) : ℤ[X])).map
      (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_comp, map_X, eval_mul, eval_pow, eval_sub, eval_add,
    eval_X, eval_one, eval_comp]
  exact mul_ne_zero (famDet_one_eval_ne_zero m h1 h2) (mul_ne_zero (pow_ne_zero _
    (fun h ↦ h2 (eq_neg_of_add_eq_zero_left h))) (sub_ne_zero.mpr h1))

/-- The leading coefficient of `(L - 1) E B_m` is `M ^ (4m)`. -/
theorem leadingCoeff_symbol (m : ℕ) :
    ((X - 1) * extraFactor * twistPoly m : ℤ[X][X]).leadingCoeff = X ^ (4 * m) := by
  have hmonic : (X - 1 : ℤ[X][X]).Monic := by simpa using monic_X_sub_C (1 : ℤ[X])
  rw [leadingCoeff_mul, leadingCoeff_mul, hmonic.leadingCoeff,
    extraFactor_monic.leadingCoeff, leadingCoeff_twistPoly, one_mul, one_mul]

/-- The constant coefficient of `(L - 1) E B_m` is `-M ^ (4m + 4)`. -/
private theorem coeff_zero_symbol_abNoSep (m : ℕ) :
    ((X - 1) * extraFactor * twistPoly m : ℤ[X][X]).coeff 0 = -X ^ (4 * m + 4) := by
  have hE : extraFactor.coeff 0 = X ^ 4 := by
    simp only [extraFactor, coeff_add, coeff_sub, coeff_C_zero, coeff_X_pow, mul_coeff_zero,
      coeff_X_zero]
    simp
  have hX : (X - 1 : ℤ[X][X]).coeff 0 = -1 := by
    simp
  rw [mul_coeff_zero, mul_coeff_zero, coeff_zero_twistPoly, hE, hX]
  ring

/-- If `κ₁ a = κ₂ b` in `ℤ[M]` and `κ₂`, `b` do not vanish at a point, neither does `a`. -/
theorem eval_ne_zero_of_mul_eq_mul {κ₁ κ₂ a b : ℤ[X]} (h : κ₁ * a = κ₂ * b)
    {m : ℂ} (hκ₂ : (κ₂.map (Int.castRingHom ℂ)).eval m ≠ 0)
    (hb : (b.map (Int.castRingHom ℂ)).eval m ≠ 0) :
    (a.map (Int.castRingHom ℂ)).eval m ≠ 0 := by
  intro ha
  have he := congrArg (fun c : ℤ[X] ↦ (c.map (Int.castRingHom ℂ)).eval m) h
  simp only [Polynomial.map_mul, eval_mul, ha, mul_zero] at he
  exact mul_ne_zero hκ₂ hb he.symm

/-- The leading and the constant coefficient of the symbol of the family transfer operator do
not vanish at a point with `M ≠ 0`, `M² ≠ ±1`. -/
theorem eval_coeff_specialize_famTransferOp_ne_zero (m : ℕ) (hm : 1 ≤ m)
    {m₀ : ℂ} (h0 : m₀ ≠ 0) (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ -1) :
    ((specialize (famTransferOp m)).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0 ∧
      (((specialize (famTransferOp m)).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
  have hκ₂ := eval_symbolRight_ne_zero m h1 h2
  have hlead := congrArg leadingCoeff (specialize_famTransferOp_mul_eq m hm)
  have hconst := congrArg (fun p : ℤ[X][X] ↦ p.coeff 0) (specialize_famTransferOp_mul_eq m hm)
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_symbol] at hlead
  simp only [coeff_C_mul, coeff_zero_symbol_abNoSep] at hconst
  exact ⟨eval_ne_zero_of_mul_eq_mul hlead hκ₂ (by simp [h0]),
    eval_ne_zero_of_mul_eq_mul hconst hκ₂ (by simp [h0])⟩

/-- There is a point `m₀` of the abelian node: `m (m₀²)² - (2m + 1) m₀² + m = 0`. -/
private theorem exists_abNode_point (m : ℕ) (hm : 2 ≤ m) :
    ∃ m₀ : ℂ, (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (discrim (m : ℂ) (-(2 * m + 1)) m)
    (n := 2) (by norm_num)
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hmC ⟨s, by rw [← hs]; ring⟩
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 2) (by norm_num)
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- No right pseudo-factor of the family transfer operator separates `L - 1` from `B_m`: its
symbol is divisible by `L - 1` exactly when it is divisible by `B_m`. -/
theorem toComparison_X_sub_one_dvd_iff_twistPoly_dvd (m : ℕ) (hm : 2 ≤ m) {β : Coeff} (hβ : β ≠ 0)
    {S R : RecOp} (h : C β * famTransferOp m = oreMul coeffShift S R) :
    toComparison (X - 1) ∣ toComparison (specialize R) ↔
      toComparison (twistPoly m) ∣ toComparison (specialize R) := by
  obtain ⟨m₀, hab⟩ := exists_abNode_point m hm
  obtain ⟨h0, h1, h2, hB, hE, hBL, hBM⟩ := abNode_facts m hm hab
  obtain ⟨hlead, hconst⟩ :=
    eval_coeff_specialize_famTransferOp_ne_zero m (by omega) h0 h1 h2
  have hdeg : (specialize (famTransferOp m)).natDegree = (famTransferOp m).natDegree := by
    rw [natDegree_specialize_famTransferOp m (by omega), natDegree_famTransferOp m (by omega)]
  have hG : evalIntPoint (X - 1) m₀ 1 = 0 := by
    rw [evalIntPoint_X_sub_one, sub_self]
  have hGL : evalIntPoint (derivative (X - 1)) m₀ 1 ≠ 0 := by
    rw [evalIntPoint_derivative_X_sub_one_abNoSep]
    exact one_ne_zero
  have hcoll := abNode_collisionFree m hm hab
  constructor
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := X - 1)
      (D := twistPoly m) (T := extraFactor) ?_ (prime_toComparison_twistPoly m hm) h0
      one_ne_zero (eval_symbolLeft_ne_zero m h1 h2)
      (eval_symbolRight_ne_zero m h1 h2) hdeg hlead hconst hG hB hE hGL hBL ?_ hcoll
      (evalIntPoint_weylSymbol_famTransferOp_abNode m hm hab) hβ h
    · rw [specialize_famTransferOp_mul_eq m (by omega)]
      ring
    · rw [evalIntPoint_derivative_X_sub_one_abNoSep,
        evalIntPoint_coeffDerivative_X_sub_one_abNoSep, one_mul, zero_mul, sub_zero]
      exact hBM
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := twistPoly m)
      (D := X - 1) (T := extraFactor) ?_ prime_toComparison_X_sub_one h0
      one_ne_zero (eval_symbolLeft_ne_zero m h1 h2)
      (eval_symbolRight_ne_zero m h1 h2) hdeg hlead hconst hB hG hE hBL hGL ?_
      hcoll.symm (evalIntPoint_weylSymbol_famTransferOp_abNode m hm hab) hβ h
    · rw [specialize_famTransferOp_mul_eq m (by omega)]
      ring
    · rw [evalIntPoint_derivative_X_sub_one_abNoSep,
        evalIntPoint_coeffDerivative_X_sub_one_abNoSep, mul_zero, mul_one, zero_sub]
      exact neg_ne_zero.mpr hBM

end AJConjecture
