import Mathlib
import AJConjecture.ExtraFactorPrime
import AJFamily.Quantum.NodeCriterionCollision
import AJFamily.Quantum.AbNodeNoSeparation
import AJTwist.Quantum.TwQSymbolEnds
import AJTwist.Factor.TwFNegAbNode
import AJTwist.Factor.TwFNegAbCollision
import AJTwist.Factor.TwFNegEbWeyl
import AJTwist.Factor.TwFNegEbCollision
import AJTwist.Factor.TwFNegPrime

/-!
# No right factor of `P_(-b)` separates the blocks (TwF, unit F2)

Source: revision 5, Section 5.4, the display
`L - 1 ←(-1/2, -1/2)→ C_b ←(-1/2, -1/2)→ E`: "Each edge records the two indices for retaining
either incident block. … the resulting connected graph obstructs factorization".

* `toComparison_X_sub_one_dvd_iff_twistPolyNeg_dvd`: the symbol of a right pseudo-factor of
  `P_(-b)` is divisible by `L - 1` exactly when it is divisible by `C_b`.
* `toComparison_extraFactor_dvd_iff_twistPolyNeg_dvd`: … by `E` exactly when by `C_b`.

Route: the library's index criterion
`toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision`, applied in both directions at each
node, exactly as in `toComparison_X_sub_one_dvd_iff_twistPoly_dvd`
(`AJFamily/Quantum/AbNodeNoSeparation.lean`) and `toComparison_extraFactor_dvd_iff_twistPoly_dvd`
(`EbNodeNoSeparation.lean`), with
`specialize_famTransferOp_mul_eq → specialize_twTransferOp_neg_mul_eq`
(`κ₁ = (M² - 1)^d (M⁴ - 1)^d`, `κ₂ = -det|_{q=1}(M²)(M² + 1)²(M² - 1)`, `d = 2b + 2`; their
values at `m₀` are nonzero by `twDet_one_eval_ne_zero`),
`eval_coeff_specialize_twTransferOp_ne_zero`, `natDegree_specialize_twTransferOp`,
`natDegree_twTransferOp`, the node facts `twNeg_abNode_facts`, `twNeg_ebNode_facts`,
`twNeg_abNode_collisionFree`, `twNeg_ebNode_collisionFree`, the Weyl symbols
`evalIntPoint_weylSymbol_twTransferOp_neg_abNode`, `…_ebNode`, and the primes
`prime_toComparison_twistPolyNeg`, `prime_toComparison_X_sub_one`,
`prime_toComparison_extraFactor`. A node point `m₀` exists because `ℂ` is algebraically closed
(`exists_abNode_point` there is private: restate).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `L - 1` does not depend on `M`. -/
private theorem evalIntPoint_coeffDerivative_X_sub_one_twfNegNoSep (m l : ℂ) :
    evalIntPoint (coeffDerivative (X - 1)) m l = 0 := by
  have h0 : coeffDerivative (X - 1 : ℤ[X][X]) = 0 := by
    rw [coeffDerivative, Polynomial.sum_def]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    rw [coeff_sub, coeff_X, coeff_one]
    split_ifs <;> simp
  simp [h0, evalIntPoint, evalPoint]

/-- The first polynomial in `M` of the symbol identity of `P_(-b)` does not vanish away from
`M² = ±1`. -/
private theorem eval_symbolLeft_ne_zero_twfNegNoSep (b : ℕ) {m₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h2 : m₀ ^ 2 ≠ -1) :
    ((((X ^ 2 - 1) ^ (2 * b + 2) * (X ^ 4 - 1) ^ (2 * b + 2) : ℤ[X])).map
      (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
  have h4 : m₀ ^ 4 - 1 = (m₀ ^ 2 - 1) * (m₀ ^ 2 + 1) := by ring
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    map_X, eval_mul, eval_pow, eval_sub, eval_X, eval_one, h4]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h1)) (pow_ne_zero _ (mul_ne_zero
    (sub_ne_zero.mpr h1) (fun h ↦ h2 (eq_neg_of_add_eq_zero_left h))))

/-- The second polynomial in `M` of the symbol identity of `P_(-b)` does not vanish away from
`M² = ±1`. -/
private theorem eval_symbolRight_ne_zero_twfNegNoSep (b : ℕ) {m₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h2 : m₀ ^ 2 ≠ -1) :
    (((-((twDet (2 * b + 2) (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) :
      ℤ[X])).map (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
  simp only [Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_one, Polynomial.map_comp, map_X, eval_neg, eval_mul,
    eval_pow, eval_sub, eval_add, eval_X, eval_one, eval_comp]
  exact neg_ne_zero.mpr (mul_ne_zero (twDet_one_eval_ne_zero (2 * b + 2) h1 h2)
    (mul_ne_zero (pow_ne_zero _ (fun h ↦ h2 (eq_neg_of_add_eq_zero_left h)))
      (sub_ne_zero.mpr h1)))

/-- The symbol of `P_(-b)` has the full degree. -/
private theorem natDegree_specialize_twTransferOp_neg_twfNegNoSep (b : ℕ) :
    (specialize (twTransferOp (-(b : ℤ)))).natDegree = (twTransferOp (-(b : ℤ))).natDegree := by
  rw [natDegree_specialize_twTransferOp, natDegree_twTransferOp]

/-- There is a point `m₀` of the abelian node: `b (m₀²)² - (2b - 1) m₀² + b = 0`. -/
private theorem exists_abNode_point_twfNegNoSep (b : ℕ) (hb : 1 ≤ b) :
    ∃ m₀ : ℂ, (b : ℂ) * (m₀ ^ 2) ^ 2 - (2 * b - 1) * m₀ ^ 2 + b = 0 := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hbC (IsAlgClosed.isSquare
    (discrim (b : ℂ) (-(2 * b - 1)) b))
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- There is a point `m₀` of the `E/C_b` node equation. -/
private theorem exists_ebNode_point_twfNegNoSep (b : ℕ) (hb : 1 ≤ b) : ∃ m₀ : ℂ,
    (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0 := by
  have h2b : (2 * (b : ℂ) - 1) ≠ 0 := by
    have h : ((2 * b - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * b - 1 ≠ 0)
    rwa [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  have ha : (b : ℂ) * (2 * b - 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : b ≠ 0)) h2b
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha (IsAlgClosed.isSquare
    (discrim ((b : ℂ) * (2 * b - 1)) (4 * b ^ 2 - 2 * b + 1) (b * (2 * b - 1))))
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- No right pseudo-factor of `P_(-b)` separates `L - 1` from `C_b`. -/
theorem toComparison_X_sub_one_dvd_iff_twistPolyNeg_dvd (b : ℕ) (hb : 1 ≤ b) {β : Coeff}
    (hβ : β ≠ 0) {S R : RecOp} (h : C β * twTransferOp (-(b : ℤ)) = oreMul coeffShift S R) :
    toComparison (X - 1) ∣ toComparison (specialize R) ↔
      toComparison (twistPolyNeg b) ∣ toComparison (specialize R) := by
  obtain ⟨m₀, hab⟩ := exists_abNode_point_twfNegNoSep b hb
  obtain ⟨h0, h1, h2, hB, hE, hBL, hBM⟩ := twNeg_abNode_facts b hb hab
  obtain ⟨hlead, hconst⟩ := eval_coeff_specialize_twTransferOp_ne_zero (-(b : ℤ)) h0 h1 h2
  have hdeg := natDegree_specialize_twTransferOp_neg_twfNegNoSep b
  have hG : evalIntPoint (X - 1) m₀ 1 = 0 := by
    rw [evalIntPoint_X_sub_one, sub_self]
  have hGL : evalIntPoint (derivative (X - 1)) m₀ 1 ≠ 0 := by
    rw [evalIntPoint_derivative_X_sub_one]
    exact one_ne_zero
  have hcoll := twNeg_abNode_collisionFree b hb hab
  have hW := evalIntPoint_weylSymbol_twTransferOp_neg_abNode b hb hab
  constructor
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := X - 1)
      (D := twistPolyNeg b) (T := extraFactor) ?_ (prime_toComparison_twistPolyNeg b hb) h0
      one_ne_zero (eval_symbolLeft_ne_zero_twfNegNoSep b h1 h2)
      (eval_symbolRight_ne_zero_twfNegNoSep b h1 h2) hdeg hlead hconst hG hB hE hGL hBL ?_ hcoll
      hW hβ h
    · rw [specialize_twTransferOp_neg_mul_eq b hb]
      ring
    · rw [evalIntPoint_derivative_X_sub_one,
        evalIntPoint_coeffDerivative_X_sub_one_twfNegNoSep, one_mul, zero_mul, sub_zero]
      exact hBM
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := twistPolyNeg b)
      (D := X - 1) (T := extraFactor) ?_ prime_toComparison_X_sub_one h0
      one_ne_zero (eval_symbolLeft_ne_zero_twfNegNoSep b h1 h2)
      (eval_symbolRight_ne_zero_twfNegNoSep b h1 h2) hdeg hlead hconst hB hG hE hBL hGL ?_
      hcoll.symm hW hβ h
    · rw [specialize_twTransferOp_neg_mul_eq b hb]
      ring
    · rw [evalIntPoint_derivative_X_sub_one,
        evalIntPoint_coeffDerivative_X_sub_one_twfNegNoSep, mul_zero, mul_one, zero_sub]
      exact neg_ne_zero.mpr hBM

/-- No right pseudo-factor of `P_(-b)` separates `E` from `C_b`. -/
theorem toComparison_extraFactor_dvd_iff_twistPolyNeg_dvd (b : ℕ) (hb : 1 ≤ b) {β : Coeff}
    (hβ : β ≠ 0) {S R : RecOp} (h : C β * twTransferOp (-(b : ℤ)) = oreMul coeffShift S R) :
    toComparison extraFactor ∣ toComparison (specialize R) ↔
      toComparison (twistPolyNeg b) ∣ toComparison (specialize R) := by
  obtain ⟨m₀, heb⟩ := exists_ebNode_point_twfNegNoSep b hb
  obtain ⟨h0, h1, h2, -, -, hl0, hT, hE, hB, hEL, hBL, hJac⟩ := twNeg_ebNode_facts b hb heb
  obtain ⟨hlead, hconst⟩ := eval_coeff_specialize_twTransferOp_ne_zero (-(b : ℤ)) h0 h1 h2
  have hdeg := natDegree_specialize_twTransferOp_neg_twfNegNoSep b
  have hcoll := twNeg_ebNode_collisionFree b hb heb
  have hW := evalIntPoint_weylSymbol_twTransferOp_neg_ebNode b hb heb
  constructor
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := extraFactor)
      (D := twistPolyNeg b) (T := X - 1) ?_ (prime_toComparison_twistPolyNeg b hb) h0 hl0
      (eval_symbolLeft_ne_zero_twfNegNoSep b h1 h2) (eval_symbolRight_ne_zero_twfNegNoSep b h1 h2)
      hdeg hlead hconst hE hB hT hEL hBL hJac hcoll hW hβ h
    rw [specialize_twTransferOp_neg_mul_eq b hb]
    ring
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := twistPolyNeg b)
      (D := extraFactor) (T := X - 1) ?_ prime_toComparison_extraFactor h0 hl0
      (eval_symbolLeft_ne_zero_twfNegNoSep b h1 h2) (eval_symbolRight_ne_zero_twfNegNoSep b h1 h2)
      hdeg hlead hconst hB hE hT hBL hEL ?_ hcoll.symm hW hβ h
    · rw [specialize_twTransferOp_neg_mul_eq b hb]
      ring
    · intro hJ
      exact hJac (by linear_combination -hJ)

end AJConjecture
