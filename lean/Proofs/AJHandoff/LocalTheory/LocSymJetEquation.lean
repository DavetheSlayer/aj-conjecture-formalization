import Mathlib
import AJHandoff.LocalTheory.LocOpJets

/-!
# The first-jet equation of a pseudo-factorization

For `Q` of degree `d` with leading coefficient `q_d`, `𝒩(Q) = (q_d)₀ Q₁ - (q_d)₁ Q₀`; when
`(q_d)₀ ≠ 0`, `𝒩(Q)/(q_d)₀²` is the first jet of the monic operator `q_d⁻¹ Q`. Its constant
coefficient is the numerator `locLogJetNum Q` of the logarithmic first jet of `q₀/q_d`, and its
degree is below `d`.

From `β P = S ⋆ R` with `deg P = deg S + deg R`, write `e = deg S`, `s = (S₀)_e`, `r = (R₀)_d`.
Formula (6) and its top coefficient give the Bézout-type relation
`S₀ (s 𝒩(R)) + R₀ (r 𝒩(S) + c s (z r')(u ∂_u S₀ - e S₀))
  = β₀² 𝒩(P) - c s (u ∂_u S₀)(r z ∂_z R₀ - z r' R₀)`.
This is the library's `specialize_mul_jetNumer_add` (Step 1 of Theorem C) with the shift
constant `-2` of `M ↦ t² M` at `t = -1` replaced by `c`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first jet of `0` is `0`. -/
private theorem locJet1_zero_symJet : locJet1 0 = 0 := by
  ext n
  rw [coeff_locJet1, coeff_zero, map_zero, coeff_zero]

/-- The residual symbol does not raise the degree. -/
private theorem natDegree_opJet0_le_symJet (Q : LocOp) : (opJet0 Q).natDegree ≤ Q.natDegree :=
  natDegree_map_le

/-- The first jet does not raise the degree. -/
private theorem natDegree_opJet1_le_symJet (Q : LocOp) : (opJet1 Q).natDegree ≤ Q.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  rw [coeff_opJet1, coeff_eq_zero_of_natDegree_lt hN, locJet1_zero_symJet]

/-- The coefficients of the inner derivative. -/
private theorem coeff_innerDerivative_symJet (p : ℂ[X][X]) (k : ℕ) :
    (innerDerivative p).coeff k = derivative (p.coeff k) := by
  unfold innerDerivative
  rw [Polynomial.sum_def, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h, derivative_zero]

/-- The coefficients of `u ∂_u p`. -/
private theorem coeff_X_mul_derivative_symJet (p : ℂ[X][X]) (n : ℕ) :
    (X * derivative p).coeff n = (n : ℂ[X]) * p.coeff n := by
  cases n with
  | zero => rw [coeff_X_mul_zero, Nat.cast_zero, zero_mul]
  | succ n =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- `u ∂_u` does not raise the degree. -/
private theorem natDegree_X_mul_derivative_le_symJet {p : ℂ[X][X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (X * derivative p).natDegree ≤ d := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  rw [coeff_X_mul_derivative_symJet, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hN),
    mul_zero]

/-- `z ∂_z` does not raise the degree. -/
private theorem natDegree_C_X_mul_innerDerivative_le_symJet {p : ℂ[X][X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (C X * innerDerivative p).natDegree ≤ d := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  rw [coeff_C_mul, coeff_innerDerivative_symJet,
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hN), derivative_zero, mul_zero]

/-- The residual symbol of `C β * P`. -/
private theorem opJet0_C_mul_symJet (β : LocPoly) (P : LocOp) :
    opJet0 (C β * P) = C (locJet0 β) * opJet0 P := by
  rw [opJet0, Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- The leading coefficient of the first-jet equation of `β P = S ⋆ R`. -/
private theorem coeff_jet_equation_symJet (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (h : C β * P = oreMul δ.shiftHom S R) (hn : P.natDegree = S.natDegree + R.natDegree) :
    locJet1 β * (opJet0 P).coeff P.natDegree + locJet0 β * (opJet1 P).coeff P.natDegree =
      (opJet1 S).coeff S.natDegree * (opJet0 R).coeff R.natDegree +
          (opJet0 S).coeff S.natDegree * (opJet1 R).coeff R.natDegree +
        C δ.c * ((S.natDegree : ℂ[X]) * (opJet0 S).coeff S.natDegree *
          (X * derivative ((opJet0 R).coeff R.natDegree))) := by
  have hS0 := natDegree_opJet0_le_symJet S
  have hR0 := natDegree_opJet0_le_symJet R
  have hS1 := natDegree_opJet1_le_symJet S
  have hR1 := natDegree_opJet1_le_symJet R
  have I3 : C (locJet1 β) * opJet0 P + C (locJet0 β) * opJet1 P =
      opJet1 S * opJet0 R + opJet0 S * opJet1 R +
        C (C δ.c) * ((X * derivative (opJet0 S)) * (C X * innerDerivative (opJet0 R))) := by
    rw [← opJet1_C_mul, h, opJet1_oreMul, mul_assoc]
  have h4 := congrArg (fun q ↦ q.coeff (S.natDegree + R.natDegree)) I3
  simp only [coeff_add, coeff_C_mul,
    coeff_mul_add_eq_of_natDegree_le hS1 hR0, coeff_mul_add_eq_of_natDegree_le hS0 hR1,
    coeff_mul_add_eq_of_natDegree_le (natDegree_X_mul_derivative_le_symJet hS0)
      (natDegree_C_X_mul_innerDerivative_le_symJet hR0),
    coeff_X_mul_derivative_symJet, coeff_innerDerivative_symJet] at h4
  rw [hn, h4]

/-- `𝒩(Q) = (q_d)₀ Q₁ - (q_d)₁ Q₀`. -/
def locJetNumer (Q : LocOp) : ℂ[X][X] :=
  C ((opJet0 Q).coeff Q.natDegree) * opJet1 Q - C ((opJet1 Q).coeff Q.natDegree) * opJet0 Q

theorem coeff_zero_locJetNumer (Q : LocOp) : (locJetNumer Q).coeff 0 = locLogJetNum Q := by
  rw [locJetNumer, locLogJetNum, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_opJet1, coeff_opJet1,
    opJet0, coeff_map, coeff_map, leadingCoeff]
  ring

theorem natDegree_locJetNumer_lt {Q : LocOp} (hQ : 0 < Q.natDegree) :
    (locJetNumer Q).natDegree < Q.natDegree := by
  have hle : (locJetNumer Q).natDegree ≤ Q.natDegree - 1 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
    rw [locJetNumer, coeff_sub, coeff_C_mul, coeff_C_mul]
    rcases Nat.lt_or_ge Q.natDegree N with h | h
    · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_opJet1_le_symJet Q).trans_lt h),
        coeff_eq_zero_of_natDegree_lt ((natDegree_opJet0_le_symJet Q).trans_lt h), mul_zero,
        mul_zero, sub_zero]
    · obtain rfl : N = Q.natDegree := by omega
      ring
  omega

/-- The first-jet equation of `β P = S ⋆ R` (Step 1 of Theorem C). -/
theorem opJet0_mul_locJetNumer_add (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (h : C β * P = oreMul δ.shiftHom S R) (hn : P.natDegree = S.natDegree + R.natDegree) :
    opJet0 S * (C ((opJet0 S).coeff S.natDegree) * locJetNumer R) +
        opJet0 R *
          (C ((opJet0 R).coeff R.natDegree) * locJetNumer S +
            C (C δ.c * (opJet0 S).coeff S.natDegree *
                (X * derivative ((opJet0 R).coeff R.natDegree))) *
              (X * derivative (opJet0 S) - (S.natDegree : ℂ[X][X]) * opJet0 S)) =
      C (locJet0 β ^ 2) * locJetNumer P -
        C (C δ.c * (opJet0 S).coeff S.natDegree) * (X * derivative (opJet0 S)) *
          (C ((opJet0 R).coeff R.natDegree) * (C X * innerDerivative (opJet0 R)) -
            C (X * derivative ((opJet0 R).coeff R.natDegree)) * opJet0 R) := by
  have I1 : C (locJet0 β) * opJet0 P = opJet0 S * opJet0 R := by
    rw [← opJet0_oreMul δ, ← h, opJet0_C_mul_symJet]
  have I3 : C (locJet1 β) * opJet0 P + C (locJet0 β) * opJet1 P =
      opJet1 S * opJet0 R + opJet0 S * opJet1 R +
        C (C δ.c) * (X * derivative (opJet0 S)) * (C X * innerDerivative (opJet0 R)) := by
    rw [← opJet1_C_mul, h, opJet1_oreMul]
  have I2 : locJet0 β * (opJet0 P).coeff P.natDegree =
      (opJet0 S).coeff S.natDegree * (opJet0 R).coeff R.natDegree := by
    have h2 := congrArg (fun q ↦ q.coeff (S.natDegree + R.natDegree)) I1
    simp only [coeff_C_mul, coeff_mul_add_eq_of_natDegree_le (natDegree_opJet0_le_symJet S)
      (natDegree_opJet0_le_symJet R)] at h2
    rw [hn]
    exact h2
  have I2' := congrArg (C : ℂ[X] → ℂ[X][X]) I2
  have I4' := congrArg (C : ℂ[X] → ℂ[X][X]) (coeff_jet_equation_symJet δ h hn)
  simp only [C_mul, C_add, map_natCast] at I2' I4'
  simp only [locJetNumer, C_mul, C_pow]
  linear_combination (-(C ((opJet0 S).coeff S.natDegree) *
      C ((opJet0 R).coeff R.natDegree))) * I3 +
    (opJet0 S * opJet0 R) * I4' -
    (C (locJet1 β) * opJet0 P + C (locJet0 β) * opJet1 P) * I2' +
    (C (locJet1 β) * C ((opJet0 P).coeff P.natDegree) +
      C (locJet0 β) * C ((opJet1 P).coeff P.natDegree)) * I1

end AJConjecture
