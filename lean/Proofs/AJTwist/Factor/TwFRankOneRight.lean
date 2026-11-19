import Mathlib
import AJConjecture.QAlgNodeIndexIntegral
import AJConjecture.QAlgSymbolNodeDerivatives
import AJConjecture.QAlgNodeDenomNeZero
import AJFamily.Quantum.AbNodeCertificateIdentity
import AJHandoff.LocalTheory.LocResidue
import AJTwist.Factor.TwFRankOneJet

/-!
# The rank-one test for a right factor `L - 1` (TwF, generic)

Source: revision 5, Section 5.5: "The rank-one determinant starts with `1 - ε r_1` on the right …
With shift vector field `-x ∂_x`, the normalized indices are `Res_{x₀} r_1 dx/x = -1/2` … The
right index must be integral by Lemma (Quotient determinant)."

`not_rankOne_right_of_weylSymbol_eq_zero`: let `(m₀, 1)` be a point where the end coefficients of
the symbol `P₀` do not vanish, `H(M) = (∂_L P₀)(M, 1)` has a simple zero at `m₀`, and the Weyl
subprincipal symbol of `P` vanishes at `(m₀, 1)`. Then `P` has no right pseudo-factor of degree
one whose symbol vanishes at `L = 1`.

No hypothesis is made on the other roots of `P₀(m₀, ·)`: `L = 1` may be a multiple root of the
cofactor (at `a = 1`, `K = 3`, it is a double root of `B_1`). This is the case that the library's
node criterion (`pow_dvd_nodeNumer_of_separating_collision`, hypothesis `hDL`) does not cover.

Route: `nodeNumer_mul_of_rankOne_right` gives `N_R/Δ_R = -P₁(M, 1)/H(M)`. Since
`W(m₀, 1) = P₁(m₀, 1) + m₀ H'(m₀) = 0` (`weylSymbol`, `eulerEuler_eq`: at `L = 1` the operator
`(L ∂_L)(M ∂_M)` is `M ∂_M` of `∂_L P₀`; `eval_one_coeffDerivative`) and `H(m₀) = 0 ≠ H'(m₀)`,
the function `-P₁(M, 1)/H(M)` has a simple pole at `m₀` with residue `m₀`
(`HasSimpleResidue`, `hasSimpleResidue_of_pow_dvd`). By the library's integrality theorem
`exists_nat_pow_dvd_nodeNumer_of_pseudoFactor` (hypotheses from `hlead`, `hconst`, `hdeg` as in
`not_separating_of_weylSymbol_eq_zero_collision`, `AJFamily/Quantum/NodeCriterionCollision.lean`)
the residue of `N_R/Δ_R` at `m₀` is `-2 j m₀` with `j ∈ ℕ`. Uniqueness of the residue
(`HasSimpleResidue.unique`) gives `(2j + 1) m₀ = 0`, a contradiction. (`Δ_R = -r̄₁² ≠ 0` since
`β̄ P₀ = S₀ R₀ ≠ 0`.) In the paper's normalization the residue `m₀` is the index `-1/2`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The derivatives in `L` and in `M` commute. -/
private theorem coeffDerivative_derivative_rankOneRight (p : ℤ[X][X]) :
    coeffDerivative (derivative p) = derivative (coeffDerivative p) := by
  ext k : 2
  rw [coeff_coeffDerivative, coeff_derivative, coeff_derivative, coeff_coeffDerivative,
    derivative_mul]
  have h1 : derivative ((k : ℤ[X]) + 1) = 0 := by
    rw [derivative_add, derivative_natCast, derivative_one, add_zero]
  rw [h1, mul_zero, add_zero]

/-- The value at `(m₀, 1)` of the Weyl symbol: `W(m₀, 1) = P₁(m₀, 1) + m₀ H'(m₀)`. -/
private theorem evalIntPoint_weylSymbol_one_rankOneRight (P : RecOp) (m₀ : ℂ) :
    evalIntPoint (weylSymbol P) m₀ 1 =
      (((specializeJet P).eval 1).map (Int.castRingHom ℂ)).eval m₀ +
        m₀ * (derivative (((derivative (specialize P)).eval 1).map
          (Int.castRingHom ℂ))).eval m₀ := by
  rw [evalIntPoint_at_one, weylSymbol, eulerEuler_eq, eval_add, eval_mul, eval_mul, eval_C,
    eval_X, one_mul, ← coeffDerivative_derivative_rankOneRight, eval_one_coeffDerivative,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, eval_add, eval_mul, eval_X,
    derivative_map]

/-- The polynomial core of the rank-one test: if `N/Δ = -P₁/H`, `H` has a simple zero at `m₀`
and `P₁(m₀) + m₀ H'(m₀) = 0`, then the residue of `N/Δ` at `m₀` is not `-2 j m₀`. -/
private theorem false_of_residue_rankOneRight {N Δ H P₁ : ℂ[X]} {m₀ : ℂ} (hm₀ : m₀ ≠ 0)
    (hΔ : Δ ≠ 0) (hid : N * H = -(Δ * P₁)) (hH0 : H.eval m₀ = 0)
    (hH1 : (derivative H).eval m₀ ≠ 0) (hW : P₁.eval m₀ + m₀ * (derivative H).eval m₀ = 0)
    {j : ℕ} (hj : (X - C m₀) ^ (Δ.rootMultiplicity m₀ + 1) ∣
      (X - C m₀) * N + C (2 * j * m₀) * Δ) : False := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hH0
  have hq1 : (derivative H).eval m₀ = q.eval m₀ := by
    rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  obtain ⟨u, hΔu, hu⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Δ hΔ m₀
  have hdvd : (X - C m₀) ^ (Δ.rootMultiplicity m₀ + 1) ∣
      (X - C m₀) ^ Δ.rootMultiplicity m₀ * (u * (C (2 * j * m₀) * q - P₁)) := by
    have h1 := dvd_mul_of_dvd_left hj q
    have h2 : ((X - C m₀) * N + C (2 * j * m₀) * Δ) * q =
        Δ * (C (2 * j * m₀) * q - P₁) := by
      linear_combination hid - N * hq
    rw [h2] at h1
    conv_rhs at h1 => rw [hΔu]
    rwa [mul_assoc] at h1
  rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ (X_sub_C_ne_zero m₀))] at hdvd
  have h3 := ((prime_X_sub_C m₀).dvd_or_dvd hdvd).resolve_left hu
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_mul, eval_C] at h3
  rw [hq1] at hW hH1
  have h4 : (2 * (j : ℂ) + 1) * m₀ * q.eval m₀ = 0 := by linear_combination h3 + hW
  have hj0 : (2 * (j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * j)
  exact mul_ne_zero (mul_ne_zero hj0 hm₀) hH1 h4

/-- At a point `(m₀, 1)` where `(∂_L P₀)(·, 1)` has a simple zero and the Weyl symbol vanishes,
no right pseudo-factor of degree one has a symbol vanishing at `L = 1`. -/
theorem not_rankOne_right_of_weylSymbol_eq_zero {P : RecOp} {m₀ : ℂ} (hm₀ : m₀ ≠ 0)
    (hdeg : (specialize P).natDegree = P.natDegree)
    (hlead : ((specialize P).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hconst : (((specialize P).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hH0 : evalIntPoint (derivative (specialize P)) m₀ 1 = 0)
    (hH1 : evalIntPoint (coeffDerivative (derivative (specialize P))) m₀ 1 ≠ 0)
    (hW : evalIntPoint (weylSymbol P) m₀ 1 = 0)
    {β : Coeff} (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S R : RecOp}
    (h : C β * P = oreMul coeffShift S R) (hR : R.natDegree = 1)
    (hR1 : (specialize R).eval 1 = 0) : False := by
  have hconst0 : (specialize P).coeff 0 ≠ 0 := fun h0 ↦
    hconst (by rw [h0, Polynomial.map_zero, eval_zero])
  have hΔ0 : nodeDenom R ≠ 0 := nodeDenom_ne_zero_of_pseudoFactor hβ h hdeg hconst0
  have hΔ : (nodeDenom R).map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hΔ0
  have hβ0 : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  have hlead' : (complexSpec (coeffToComplex P.leadingCoeff)).eval m₀ ≠ 0 := by
    rw [complexSpec_coeffToComplex, Polynomial.leadingCoeff, ← coeff_specialize, ← hdeg]
    exact hlead
  have hconst' : (complexSpec (coeffToComplex (P.coeff 0))).eval m₀ ≠ 0 := by
    rw [complexSpec_coeffToComplex, ← coeff_specialize]
    exact hconst
  obtain ⟨j, hj⟩ := exists_nat_pow_dvd_nodeNumer_of_pseudoFactor hβ0 h hlead' hconst'
  have hid := congrArg (Polynomial.map (Int.castRingHom ℂ))
    (nodeNumer_mul_of_rankOne_right hβ h hR hR1)
  rw [Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_mul] at hid
  rw [evalIntPoint_at_one] at hH0
  rw [evalIntPoint_at_one, eval_one_coeffDerivative, ← derivative_map] at hH1
  rw [evalIntPoint_weylSymbol_one_rankOneRight] at hW
  exact false_of_residue_rankOneRight hm₀ hΔ hid hH0 hH1 hW hj

end AJConjecture
