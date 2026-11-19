import Mathlib
import AJConjecture.QAlgNodeJet
import AJConjecture.QAlgSpecializeJetOreMul
import AJConjecture.QAlgSpecializeOreMul
import AJFamily.Quantum.AbNodeCertificateIdentity

/-!
# The first jet of a rank-one factor at `L = 1` (TwF, generic)

Source: revision 5, Section 5.5 (`operators.tex`, "The rank-one split at `a = 1`"): with `P`
monic and `H_0 = P̄/(u - 1)`, "If a right factor is `u - 1 + ε r_1 + ⋯`, evaluating
eq. (orelinear) at `u = 1` yields `r_1 = Ṗ(x, 1)/H_0(x, 1)`. If a left factor is
`u - 1 + ε s_1 + ⋯`, the same product formula yields
`s_1 = (Ṗ(x, 1) - δ H_0(x, 1))/H_0(x, 1)`"; Section 4, eq. (orelinear):
`P_1 = S_1 R_0 + S_0 R_1 + (u ∂_u S_0) δ R_0`.

In the library's forward convention, with the first jet `specializeJet` at `t = -1`
(`specializeJet_oreMul`: `(S ⋆ R)₁ = S₁ R₀ + S₀ R₁ - 2 (L ∂_L S₀)(M ∂_M R₀)`), write
`H(M) = (∂_L P₀)(M, 1)` and `P₁(M, 1)` for the first jet at `L = 1`. Let `β P = S ⋆ R` with
`β(-1, M) ≠ 0`, and let `N/Δ = nodeNumer/nodeDenom` be the logarithmic first jet of the ratio of
the constant to the leading coefficient of a factor.

* `nodeNumer_mul_of_rankOne_right`: if `R` has degree `1` and `R₀(M, 1) = 0` (`R₀ ∝ L - 1`), then
  `N_R · H = -Δ_R · P₁(·, 1)`, i.e. `N_R/Δ_R = -P₁(M, 1)/H(M)`.
* `nodeNumer_mul_of_rankOne_left`: if `S` has degree `1` and `S₀(M, 1) = 0`, then with
  `ρ₀(M) = R₀(M, 1)`:
  `N_S · (H ρ₀) = -Δ_S · (P₁(·, 1) ρ₀ + 2 H · M ρ₀')`, i.e.
  `N_S/Δ_S = -P₁(M, 1)/H(M) - 2 M ρ₀'/ρ₀`.

Route: apply `specializeJet` and `specialize` to `C β * P = oreMul coeffShift S R`
(`specializeJet_C_mul`, `specializeJet_oreMul`, `specialize_oreMul`), evaluate at `L = 1`
(`eval_mul`, `eval_one_coeffDerivative`, `derivative_mul`), use `r̄₀ = -r̄₁` (resp. `s̄₀ = -s̄₁`)
and cancel `β(-1, M) ≠ 0` in `ℤ[M]`. For the right factor: `β̄ P₁(1) = S₀(1)(ṙ₀ + ṙ₁)`,
`β̄ H = S₀(1) r̄₁`, `N_R = r̄₁ (ṙ₀ + ṙ₁)`, `Δ_R = -r̄₁²`. For the left factor:
`β̄ P₁(1) = (ṡ₀ + ṡ₁) ρ₀ - 2 s̄₁ M ρ₀'`, `β̄ H = s̄₁ ρ₀`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value at `L = 1` of a polynomial of degree at most one in `L`. -/
private theorem eval_one_of_natDegree_le_one_rankOneJet {p : ℤ[X][X]} (hp : p.natDegree ≤ 1) :
    p.eval 1 = p.coeff 0 + p.coeff 1 := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  simp [Finset.sum_range_succ]

/-- The value at `L = 1` of the `L`-derivative of a polynomial of degree at most one in `L`. -/
private theorem eval_one_derivative_of_natDegree_le_one_rankOneJet {p : ℤ[X][X]}
    (hp : p.natDegree ≤ 1) : (derivative p).eval 1 = p.coeff 1 := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
  simp

/-- The first jet of an operator has at most the degree of the operator. -/
private theorem natDegree_specializeJet_le_rankOneJet (R : RecOp) :
    (specializeJet R).natDegree ≤ R.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_specializeJet, coeff_eq_zero_of_natDegree_lt hk, coeffJet_zero]

/-- The three identities at `L = 1` obtained from `β P = S ⋆ R`: the symbol, its `L`-derivative
and the first jet. -/
private theorem eval_one_identities_rankOneJet {P S R : RecOp} {β : Coeff}
    (h : C β * P = oreMul coeffShift S R) :
    β.map (Polynomial.evalRingHom (-1 : ℤ)) * (specialize P).eval 1 =
        (specialize S).eval 1 * (specialize R).eval 1 ∧
      β.map (Polynomial.evalRingHom (-1 : ℤ)) * (derivative (specialize P)).eval 1 =
        (derivative (specialize S)).eval 1 * (specialize R).eval 1 +
          (specialize S).eval 1 * (derivative (specialize R)).eval 1 ∧
      coeffJet β * (specialize P).eval 1 +
          β.map (Polynomial.evalRingHom (-1 : ℤ)) * (specializeJet P).eval 1 =
        (specializeJet S).eval 1 * (specialize R).eval 1 +
          (specialize S).eval 1 * (specializeJet R).eval 1 -
            2 * (derivative (specialize S)).eval 1 *
              (X * derivative ((specialize R).eval 1)) := by
  have h0 : C (β.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize P =
      specialize S * specialize R := by
    rw [← specialize_oreMul, ← h, map_mul]
    congr 1
    rw [specialize, coe_mapRingHom, map_C, coe_mapRingHom]
  have h1 := specializeJet_oreMul S R
  rw [← h, specializeJet_C_mul] at h1
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun p : ℤ[X][X] ↦ p.eval 1) h0
    simpa only [eval_mul, eval_C] using this
  · have := congrArg (fun p : ℤ[X][X] ↦ (derivative p).eval 1) h0
    simp only [derivative_mul, derivative_C, eval_mul, eval_C, eval_add, zero_mul,
      zero_add] at this
    exact this
  · have := congrArg (fun p : ℤ[X][X] ↦ p.eval 1) h1
    simpa only [eval_mul, eval_C, eval_add, eval_sub, eval_X, one_mul, eval_ofNat,
      eval_one_coeffDerivative] using this

/-- The logarithmic first jet of a right pseudo-factor of degree one whose symbol vanishes at
`L = 1`: `N_R · H = -Δ_R · P₁(·, 1)`. -/
theorem nodeNumer_mul_of_rankOne_right {P S R : RecOp} {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h : C β * P = oreMul coeffShift S R) (hR : R.natDegree = 1)
    (hR1 : (specialize R).eval 1 = 0) :
    nodeNumer R * (derivative (specialize P)).eval 1 =
      -(nodeDenom R * (specializeJet P).eval 1) := by
  obtain ⟨e0, e1, e2⟩ := eval_one_identities_rankOneJet h
  have hR0 : (specialize R).natDegree ≤ 1 := hR ▸ natDegree_map_le
  have hRJ : (specializeJet R).natDegree ≤ 1 := hR ▸ natDegree_specializeJet_le_rankOneJet R
  have hr := eval_one_of_natDegree_le_one_rankOneJet hR0
  rw [hR1] at hr
  rw [hR1, mul_zero] at e0
  have hP0 : (specialize P).eval 1 = 0 := (mul_eq_zero.mp e0).resolve_left hβ
  rw [hP0, hR1, mul_zero, zero_add, mul_zero, zero_add, derivative_zero, mul_zero, mul_zero,
    sub_zero, eval_one_of_natDegree_le_one_rankOneJet hRJ] at e2
  rw [hR1, mul_zero, zero_add, eval_one_derivative_of_natDegree_le_one_rankOneJet hR0] at e1
  apply mul_left_cancel₀ hβ
  rw [nodeNumer, nodeDenom, hR]
  linear_combination ((specializeJet R).coeff 0 * (specialize R).coeff 1 -
      (specialize R).coeff 0 * (specializeJet R).coeff 1) * e1 +
    (specialize R).coeff 0 * (specialize R).coeff 1 * e2 -
    (specialize S).eval 1 * (specialize R).coeff 1 * (specializeJet R).coeff 0 * hr

/-- The logarithmic first jet of a left pseudo-factor of degree one whose symbol vanishes at
`L = 1`: `N_S · (H ρ₀) = -Δ_S · (P₁(·, 1) ρ₀ + 2 H M ρ₀')`, `ρ₀ = R₀(·, 1)`. -/
theorem nodeNumer_mul_of_rankOne_left {P S R : RecOp} {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h : C β * P = oreMul coeffShift S R) (hS : S.natDegree = 1)
    (hS1 : (specialize S).eval 1 = 0) :
    nodeNumer S * ((derivative (specialize P)).eval 1 * (specialize R).eval 1) =
      -(nodeDenom S * ((specializeJet P).eval 1 * (specialize R).eval 1 +
        2 * (derivative (specialize P)).eval 1 * (X * derivative ((specialize R).eval 1)))) := by
  obtain ⟨e0, e1, e2⟩ := eval_one_identities_rankOneJet h
  have hS0 : (specialize S).natDegree ≤ 1 := hS ▸ natDegree_map_le
  have hSJ : (specializeJet S).natDegree ≤ 1 := hS ▸ natDegree_specializeJet_le_rankOneJet S
  have hs := eval_one_of_natDegree_le_one_rankOneJet hS0
  rw [hS1] at hs
  rw [hS1, zero_mul] at e0
  have hP0 : (specialize P).eval 1 = 0 := (mul_eq_zero.mp e0).resolve_left hβ
  rw [hP0, hS1, mul_zero, zero_add, zero_mul, add_zero,
    eval_one_of_natDegree_le_one_rankOneJet hSJ,
    eval_one_derivative_of_natDegree_le_one_rankOneJet hS0] at e2
  rw [hS1, zero_mul, add_zero, eval_one_derivative_of_natDegree_le_one_rankOneJet hS0] at e1
  apply mul_left_cancel₀ hβ
  rw [nodeNumer, nodeDenom, hS]
  linear_combination (((specializeJet S).coeff 0 * (specialize S).coeff 1 -
        (specialize S).coeff 0 * (specializeJet S).coeff 1) * (specialize R).eval 1 +
      2 * ((specialize S).coeff 0 * (specialize S).coeff 1) *
        (X * derivative ((specialize R).eval 1))) * e1 +
    (specialize S).coeff 0 * (specialize S).coeff 1 * (specialize R).eval 1 * e2 -
    (specialize R).eval 1 ^ 2 * (specialize S).coeff 1 * (specializeJet S).coeff 0 * hs

end AJConjecture
