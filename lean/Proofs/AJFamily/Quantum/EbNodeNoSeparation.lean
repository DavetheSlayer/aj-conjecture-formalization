import Mathlib
import AJFamily.Quantum.AbNodeNoSeparation
import AJConjecture.ExtraFactorPrime
import AJFamily.Quantum.EbNodeCollision
import AJFamily.Quantum.EbNodeWeyl
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.NodeCriterionCollision
import AJFamily.Quantum.TwistPolyPrime

/-!
# E/B node: `E` and `B_m` are not separated

`toComparison_extraFactor_dvd_iff_twistPoly_dvd`: by the index criterion at the E/B node, the
symbol of a right pseudo-factor of `famTransferOp m` is divisible by `E` exactly when it is
divisible by `B_m`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The constant coefficient of `(L - 1) E B_m` is `-M ^ (4m + 4)`. -/
private theorem coeff_zero_symbol_ebNoSep (m : ℕ) :
    ((X - 1) * extraFactor * twistPoly m : ℤ[X][X]).coeff 0 = -(X ^ 4 * X ^ (4 * m)) := by
  have hE : extraFactor.coeff 0 = X ^ 4 := by
    simp only [extraFactor, coeff_add, coeff_sub, coeff_C_zero, coeff_X_pow, mul_coeff_zero,
      coeff_X_zero]
    simp
  have hX : (X - 1 : ℤ[X][X]).coeff 0 = -1 := by
    simp
  rw [mul_coeff_zero, mul_coeff_zero, coeff_zero_twistPoly, hE, hX]
  ring

/-- There is a point `m₀` of the E/B node equation. -/
private theorem exists_ebNode_root (m : ℕ) (hm : 2 ≤ m) : ∃ m₀ : ℂ,
    (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0 := by
  have ha : (m : ℂ) * (2 * m + 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0))
      (by exact_mod_cast (by omega : 2 * m + 1 ≠ 0))
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha (IsAlgClosed.isSquare
    (discrim ((m : ℂ) * (2 * m + 1)) (4 * m ^ 2 + 2 * m + 1) (m * (2 * m + 1))))
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- No right pseudo-factor of the family transfer operator separates `E` from `B_m`: its symbol
is divisible by `E` exactly when it is divisible by `B_m`. -/
theorem toComparison_extraFactor_dvd_iff_twistPoly_dvd (m : ℕ) (hm : 2 ≤ m) {β : Coeff}
    (hβ : β ≠ 0) {S R : RecOp} (h : C β * famTransferOp m = oreMul coeffShift S R) :
    toComparison extraFactor ∣ toComparison (specialize R) ↔
      toComparison (twistPoly m) ∣ toComparison (specialize R) := by
  obtain ⟨m₀, heb⟩ := exists_ebNode_root m hm
  obtain ⟨h0, h1, h2, -, -, hl0, hT, hE, hB, hEL, hBL, hJac⟩ := ebNode_facts m hm heb
  obtain ⟨hlead, hconst⟩ :=
    eval_coeff_specialize_famTransferOp_ne_zero m (by omega) h0 h1 h2
  have hdeg : (specialize (famTransferOp m)).natDegree = (famTransferOp m).natDegree := by
    rw [natDegree_specialize_famTransferOp m (by omega), natDegree_famTransferOp m (by omega)]
  have hcoll := ebNode_collisionFree m hm heb
  have hW := evalIntPoint_weylSymbol_famTransferOp_ebNode m hm heb
  constructor
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := extraFactor)
      (D := twistPoly m) (T := X - 1) ?_ (prime_toComparison_twistPoly m hm) h0 hl0
      (eval_symbolLeft_ne_zero m h1 h2) (eval_symbolRight_ne_zero m h1 h2)
      hdeg hlead hconst hE hB hT hEL hBL hJac hcoll hW hβ h
    rw [specialize_famTransferOp_mul_eq m (by omega)]
    ring
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := twistPoly m)
      (D := extraFactor) (T := X - 1) ?_ prime_toComparison_extraFactor h0 hl0
      (eval_symbolLeft_ne_zero m h1 h2) (eval_symbolRight_ne_zero m h1 h2)
      hdeg hlead hconst hB hE hT hBL hEL ?_ hcoll.symm hW hβ h
    · rw [specialize_famTransferOp_mul_eq m (by omega)]
      ring
    · intro hJ
      exact hJac (by linear_combination -hJ)

end AJConjecture
