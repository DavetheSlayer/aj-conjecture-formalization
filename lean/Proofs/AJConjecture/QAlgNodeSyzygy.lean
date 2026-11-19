import Mathlib
import AJConjecture.QAlgSpecializeJetOreMul
import AJConjecture.QAlgSpecializeOreMul

/-!
# The first-jet equation of a pseudo-factorisation, cleared of leading coefficients

For an operator `Q` of degree `d` put
`jetNumer Q = q_d⁰ Q₁ - q_d¹ Q₀`, the numerator of the first jet of the monic operator
`Q / q_d` (`Q₀ = specialize Q`, `Q₁ = specializeJet Q`; it has degree less than `d` in `L`, and
its constant coefficient is `nodeNumer Q`).

Let `β P = S ⋆ R` with `deg P = deg S + deg R`, `s`, `r` the values at `t = -1` of the leading
coefficients of `S`, `R`, and `e = deg S`. Then
`S₀ · (s · jetNumer R) + R₀ · U = β₀² · jetNumer P + 2 s (L ∂_L S₀)(r M ∂_M R₀ - M r' R₀)`
with `U = r · jetNumer S - 2 s M r' (L ∂_L S₀ - e S₀)`.

Proof. Pure algebra from four identities: `β₀ P₀ = S₀ R₀` (`specialize_oreMul`), its leading
coefficient `β₀ p = s r`, the first jet
`β₁ P₀ + β₀ P₁ = S₁ R₀ + S₀ R₁ - 2 (L ∂_L S₀)(M ∂_M R₀)` (`specializeJet_oreMul`,
`specializeJet_C_mul`), and its leading coefficient
`β₁ p + β₀ p₁ = s₁ r + s r₁ - 2 e s M r'`. Multiply the first jet by `s r = β₀ p` and
substitute; the identity is linear in these four relations (`linear_combination`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The numerator `q_d⁰ Q₁ - q_d¹ Q₀` of the first jet of the monic normalisation of `Q`. -/
def jetNumer (Q : RecOp) : ℤ[X][X] :=
  C ((specialize Q).coeff Q.natDegree) * specializeJet Q -
    C ((specializeJet Q).coeff Q.natDegree) * specialize Q

/-- The constant coefficient of `jetNumer` is `nodeNumer`. -/
theorem coeff_zero_jetNumer (Q : RecOp) : (jetNumer Q).coeff 0 = nodeNumer Q := by
  rw [jetNumer, nodeNumer, coeff_sub, coeff_C_mul, coeff_C_mul]
  ring

/-- The coefficients of the derivative in `M`. -/
private theorem coeff_coeffDerivative_nodeSyzygy (p : ℤ[X][X]) (k : ℕ) :
    (coeffDerivative p).coeff k = derivative (p.coeff k) := by
  unfold coeffDerivative
  rw [Polynomial.sum_def, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h, derivative_zero]

/-- The first jet does not raise the degree in `L`. -/
private theorem natDegree_specializeJet_le_nodeSyzygy (Q : RecOp) :
    (specializeJet Q).natDegree ≤ Q.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  rw [coeff_specializeJet, coeff_eq_zero_of_natDegree_lt hN, coeffJet_zero]

/-- The value at `t = -1` does not raise the degree in `L`. -/
private theorem natDegree_specialize_le_nodeSyzygy (Q : RecOp) :
    (specialize Q).natDegree ≤ Q.natDegree := by
  rw [specialize, coe_mapRingHom]
  exact natDegree_map_le

/-- The coefficients of `L ∂_L p`. -/
private theorem coeff_X_mul_derivative_nodeSyzygy (p : ℤ[X][X]) (n : ℕ) :
    (X * derivative p).coeff n = (n : ℤ[X]) * p.coeff n := by
  cases n with
  | zero => rw [coeff_X_mul_zero, Nat.cast_zero, zero_mul]
  | succ n =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- `L ∂_L` does not raise the degree in `L`. -/
private theorem natDegree_X_mul_derivative_le_nodeSyzygy {p : ℤ[X][X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (X * derivative p).natDegree ≤ d := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  rw [coeff_X_mul_derivative_nodeSyzygy, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hN),
    mul_zero]

/-- `M ∂_M` does not raise the degree in `L`. -/
private theorem natDegree_C_X_mul_coeffDerivative_le_nodeSyzygy {p : ℤ[X][X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (C X * coeffDerivative p).natDegree ≤ d := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  rw [coeff_C_mul, coeff_coeffDerivative_nodeSyzygy,
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hN), derivative_zero, mul_zero]

/-- `jetNumer Q` has degree less than `deg Q` in `L` (for `Q` of positive degree). -/
theorem natDegree_jetNumer_lt {Q : RecOp} (hQ : 0 < Q.natDegree) :
    (jetNumer Q).natDegree < Q.natDegree := by
  have hle : (jetNumer Q).natDegree ≤ Q.natDegree - 1 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
    rw [jetNumer, coeff_sub, coeff_C_mul, coeff_C_mul]
    rcases Nat.lt_or_ge Q.natDegree N with h | h
    · rw [coeff_specializeJet Q N, coeff_specialize Q N, coeff_eq_zero_of_natDegree_lt h,
        coeffJet_zero, Polynomial.map_zero, mul_zero, mul_zero, sub_zero]
    · obtain rfl : N = Q.natDegree := by omega
      ring
  omega

/-- The leading coefficient of the first-jet equation of `β P = S ⋆ R`. -/
private theorem coeff_jet_equation_nodeSyzygy {P S R : RecOp} {β : Coeff}
    (h : C β * P = oreMul coeffShift S R) (hn : P.natDegree = S.natDegree + R.natDegree) :
    coeffJet β * (specialize P).coeff P.natDegree +
        β.map (Polynomial.evalRingHom (-1)) * (specializeJet P).coeff P.natDegree =
      (specializeJet S).coeff S.natDegree * (specialize R).coeff R.natDegree +
          (specialize S).coeff S.natDegree * (specializeJet R).coeff R.natDegree -
        2 * ((S.natDegree : ℤ[X]) * (specialize S).coeff S.natDegree *
          (X * derivative ((specialize R).coeff R.natDegree))) := by
  have hS0 := natDegree_specialize_le_nodeSyzygy S
  have hR0 := natDegree_specialize_le_nodeSyzygy R
  have hS1 := natDegree_specializeJet_le_nodeSyzygy S
  have hR1 := natDegree_specializeJet_le_nodeSyzygy R
  have I3 : C (coeffJet β) * specialize P +
      C (β.map (Polynomial.evalRingHom (-1))) * specializeJet P =
      specializeJet S * specialize R + specialize S * specializeJet R -
        2 * ((X * derivative (specialize S)) * (C X * coeffDerivative (specialize R))) := by
    rw [← specializeJet_C_mul, h, specializeJet_oreMul, mul_assoc]
  have h4 := congrArg (fun q ↦ q.coeff (S.natDegree + R.natDegree)) I3
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_ofNat_mul,
    coeff_mul_add_eq_of_natDegree_le hS1 hR0, coeff_mul_add_eq_of_natDegree_le hS0 hR1,
    coeff_mul_add_eq_of_natDegree_le (natDegree_X_mul_derivative_le_nodeSyzygy hS0)
      (natDegree_C_X_mul_coeffDerivative_le_nodeSyzygy hR0),
    coeff_X_mul_derivative_nodeSyzygy, coeff_coeffDerivative_nodeSyzygy] at h4
  rw [hn]
  exact h4

/-- The first-jet equation of `β P = S ⋆ R` in terms of the jets of the monic
normalisations. -/
theorem specialize_mul_jetNumer_add {P S R : RecOp} {β : Coeff}
    (h : C β * P = oreMul coeffShift S R) (hn : P.natDegree = S.natDegree + R.natDegree) :
    specialize S * (C ((specialize S).coeff S.natDegree) * jetNumer R) +
        specialize R *
          (C ((specialize R).coeff R.natDegree) * jetNumer S -
            C (2 * (specialize S).coeff S.natDegree *
                (X * derivative ((specialize R).coeff R.natDegree))) *
              (X * derivative (specialize S) - (S.natDegree : ℤ[X][X]) * specialize S)) =
      C (β.map (Polynomial.evalRingHom (-1)) ^ 2) * jetNumer P +
        C (2 * (specialize S).coeff S.natDegree) * (X * derivative (specialize S)) *
          (C ((specialize R).coeff R.natDegree) * (C X * coeffDerivative (specialize R)) -
            C (X * derivative ((specialize R).coeff R.natDegree)) * specialize R) := by
  have hspecC : specialize (C β) = C (β.map (Polynomial.evalRingHom (-1))) := by
    rw [specialize, coe_mapRingHom, Polynomial.map_C, coe_mapRingHom]
  have I1 : C (β.map (Polynomial.evalRingHom (-1))) * specialize P =
      specialize S * specialize R := by
    rw [← specialize_oreMul, ← h, map_mul, hspecC]
  have I3 : C (coeffJet β) * specialize P +
      C (β.map (Polynomial.evalRingHom (-1))) * specializeJet P =
      specializeJet S * specialize R + specialize S * specializeJet R -
        2 * (X * derivative (specialize S)) * (C X * coeffDerivative (specialize R)) := by
    rw [← specializeJet_C_mul, h, specializeJet_oreMul]
  have I2 : β.map (Polynomial.evalRingHom (-1)) * (specialize P).coeff P.natDegree =
      (specialize S).coeff S.natDegree * (specialize R).coeff R.natDegree := by
    have h2 := congrArg (fun q ↦ q.coeff (S.natDegree + R.natDegree)) I1
    simp only [coeff_C_mul, coeff_mul_add_eq_of_natDegree_le (natDegree_specialize_le_nodeSyzygy S)
      (natDegree_specialize_le_nodeSyzygy R)] at h2
    rw [hn]
    exact h2
  have I2' := congrArg (C : ℤ[X] → ℤ[X][X]) I2
  have I4' := congrArg (C : ℤ[X] → ℤ[X][X]) (coeff_jet_equation_nodeSyzygy h hn)
  simp only [C_mul, C_add, C_sub, C_ofNat, map_natCast] at I2' I4'
  simp only [jetNumer, C_mul, C_pow, C_ofNat]
  linear_combination (-(C ((specialize S).coeff S.natDegree) *
      C ((specialize R).coeff R.natDegree))) * I3 +
    (specialize S * specialize R) * I4' -
    (C (coeffJet β) * specialize P +
      C (β.map (Polynomial.evalRingHom (-1))) * specializeJet P) * I2' +
    (C (coeffJet β) * C ((specialize P).coeff P.natDegree) +
      C (β.map (Polynomial.evalRingHom (-1))) * C ((specializeJet P).coeff P.natDegree)) * I1

end AJConjecture
