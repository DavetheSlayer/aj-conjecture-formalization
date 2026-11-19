import Mathlib
import AJConjecture.QAlgNodeIndexIntegral
import AJConjecture.QAlgSymbolNodeDerivatives
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgNodeDenomNeZero
import AJFamily.Quantum.AbNodeCertificateIdentity
import AJHandoff.LocalTheory.LocResidue
import AJTwist.Factor.TwFRankOneJet

/-!
# The rank-one test for a left factor `L - 1` (TwF, generic, crux)

Source: revision 5, Section 5.5: "… and `1 - ε s_1` on the left. … `Res_{x₀} s_1 dx/x = +1/2`.
… For the left factor use the dual quotient described in Section 4. Its ambient shift matrix
`(A⁻¹)^t` and inverse are jointly regular. The determinant of the rank-one dual is reciprocal to
the submodule determinant, so integrality on the dual quotient implies integrality of the left
index."

`not_rankOne_left_of_weylSymbol_eq_zero`: under the hypotheses of
`not_rankOne_right_of_weylSymbol_eq_zero` on `P` and `m₀`, `P` has no left pseudo-factor of degree
one whose symbol vanishes at `L = 1`.

Route (no dual module is needed). Let `β P = S ⋆ R`, `S = s₁ L + s₀`, `R` of degree `f`, and write
`lj(c)` for the logarithmic first jet at `t = -1` of a coefficient `c` with `c(-1, M) ≠ 0`.
1. *The determinant is multiplicative.* The end coefficients of the Ore product are
   `β p_0 = s₀ r₀` and `β p_d = s₁ τ(r_f)` (`coeff_oreMul_natDegree_add`), and
   `lj(τ c) = lj(c) - 2 M c̄'/c̄` (`specializeJet_oreMul` on monomials). Hence
   `N_S/Δ_S = lj(s₀/s₁) = lj(p_0/p_d) - N_R/Δ_R - 2 M r̄_f'/r̄_f`.
   At `m₀`: `lj(p_0/p_d)` is regular (`hlead`, `hconst`, `hdeg`); `N_R/Δ_R` has residue `-2 j m₀`,
   `j ∈ ℕ`, by `exists_nat_pow_dvd_nodeNumer_of_pseudoFactor` applied to the **right** factor
   `R`; `2 M r̄_f'/r̄_f` has residue `2 m₀ ord_{m₀}(r̄_f)` (`hasSimpleResidue_logDeriv`). So the
   residue of `N_S/Δ_S` is an even multiple of `m₀`.
2. *The first jet of the left factor.* By `nodeNumer_mul_of_rankOne_left`,
   `N_S/Δ_S = -P₁(M, 1)/H(M) - 2 M ρ₀'/ρ₀`; the first term has residue `m₀` (as in the right
   test, from `hW`, `hH0`, `hH1`) and the second `-2 m₀ ord_{m₀}(ρ₀)`: an odd multiple of `m₀`.
3. `HasSimpleResidue.unique` and `m₀ ≠ 0` give a parity contradiction.
All coefficients involved have nonzero specialization because `β̄ p̄_0 = s̄₀ r̄₀`,
`β̄ p̄_d = s̄₁ r̄_f` and `β̄ H = s̄₁ ρ₀` are nonzero polynomials (`hβ`, `hlead`, `hconst`, `hH1`).
In the paper's normalization the residues `m₀ (1 - 2n)` are the indices `-1/2 + n`; the paper's
value `+1/2` is `n = 1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The derivatives in `L` and in `M` commute. -/
private theorem coeffDerivative_derivative_rankOneLeft (p : ℤ[X][X]) :
    coeffDerivative (derivative p) = derivative (coeffDerivative p) := by
  ext k : 2
  rw [coeff_coeffDerivative, coeff_derivative, coeff_derivative, coeff_coeffDerivative,
    derivative_mul]
  have h1 : derivative ((k : ℤ[X]) + 1) = 0 := by
    rw [derivative_add, derivative_natCast, derivative_one, add_zero]
  rw [h1, mul_zero, add_zero]

/-- The value at `(m₀, 1)` of the Weyl symbol: `W(m₀, 1) = P₁(m₀, 1) + m₀ H'(m₀)`. -/
private theorem evalIntPoint_weylSymbol_one_rankOneLeft (P : RecOp) (m₀ : ℂ) :
    evalIntPoint (weylSymbol P) m₀ 1 =
      (((specializeJet P).eval 1).map (Int.castRingHom ℂ)).eval m₀ +
        m₀ * (derivative (((derivative (specialize P)).eval 1).map
          (Int.castRingHom ℂ))).eval m₀ := by
  rw [evalIntPoint_at_one, weylSymbol, eulerEuler_eq, eval_add, eval_mul, eval_mul, eval_C,
    eval_X, one_mul, ← coeffDerivative_derivative_rankOneLeft, eval_one_coeffDerivative,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, eval_add, eval_mul, eval_X,
    derivative_map]

/-- `X - z₀` is a nonzero rational function. -/
private theorem ratFunc_X_sub_C_ne_zero_rankOneLeft (z₀ : ℂ) :
    (RatFunc.X - RatFunc.C z₀ : RatFunc ℂ) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 (X_sub_C_ne_zero z₀)

/-- A polynomial times a function with a simple pole at `z₀`: the residue is multiplied by the
value of the polynomial at `z₀`. -/
private theorem hasSimpleResidue_algebraMap_mul_rankOneLeft {f : RatFunc ℂ} {z₀ ι : ℂ}
    (hf : HasSimpleResidue f z₀ ι) (p : ℂ[X]) :
    HasSimpleResidue (algebraMap ℂ[X] (RatFunc ℂ) p * f) z₀ (p.eval z₀ * ι) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := z₀) (p := p)
  have hX := ratFunc_X_sub_C_ne_zero_rankOneLeft z₀
  have heq : algebraMap ℂ[X] (RatFunc ℂ) p * f -
      RatFunc.C (p.eval z₀ * ι) / (RatFunc.X - RatFunc.C z₀) =
      algebraMap ℂ[X] (RatFunc ℂ) p * (f - RatFunc.C ι / (RatFunc.X - RatFunc.C z₀)) +
        algebraMap ℂ[X] (RatFunc ℂ) (C ι * q) := by
    have hq' := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hq
    simp only [map_sub, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at hq'
    rw [map_mul, map_mul, RatFunc.algebraMap_C]
    field_simp
    linear_combination RatFunc.C ι * hq'
  unfold HasSimpleResidue
  rw [heq]
  exact isRegularAt_add (isRegularAt_mul (isRegularAt_algebraMap z₀ p) hf)
    (isRegularAt_algebraMap z₀ _)

/-- If `H` has a simple zero at `m₀` and `P₁(m₀) + m₀ H'(m₀) = 0`, then `-P₁/H` has a simple
pole at `m₀` with residue `m₀`. -/
private theorem hasSimpleResidue_neg_div_rankOneLeft {H P₁ : ℂ[X]} {m₀ : ℂ}
    (hH0 : H.eval m₀ = 0) (hH1 : (derivative H).eval m₀ ≠ 0)
    (hW : P₁.eval m₀ + m₀ * (derivative H).eval m₀ = 0) :
    HasSimpleResidue (algebraMap ℂ[X] (RatFunc ℂ) (-P₁) / algebraMap ℂ[X] (RatFunc ℂ) H)
      m₀ m₀ := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hH0
  have hq1 : (derivative H).eval m₀ = q.eval m₀ := by
    rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  rw [hq1] at hH1 hW
  obtain ⟨w, hw⟩ : X - C m₀ ∣ -P₁ - C m₀ * q := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_neg, eval_mul, eval_C]
    linear_combination -hW
  have hX := ratFunc_X_sub_C_ne_zero_rankOneLeft m₀
  have hq0 : algebraMap ℂ[X] (RatFunc ℂ) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2
      (by rintro rfl; simp at hH1)
  have hw' := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hw
  simp only [map_sub, map_mul, map_neg, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at hw'
  refine ⟨w, q, hH1, ?_⟩
  rw [hq, map_mul, map_neg, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  field_simp
  linear_combination hw'

/-- The polynomial core of the rank-one test for a left factor: the two expressions of the
logarithmic first jet `N_S/Δ_S` have residues at `m₀` of different parity. -/
private theorem false_of_residue_rankOneLeft {NS ΔS NP ΔP NR ΔR rf H ρ P₁ : ℂ[X]} {m₀ : ℂ}
    (hm₀ : m₀ ≠ 0) (hΔS : ΔS ≠ 0) (hΔR : ΔR ≠ 0) (hrf : rf ≠ 0) (hρ : ρ ≠ 0)
    (hΔP : ΔP.eval m₀ ≠ 0)
    (hA : NS * ΔP * ΔR * rf = ΔS * (NP * ΔR * rf - NR * ΔP * rf -
      2 * (X * derivative rf) * ΔP * ΔR))
    (hB : NS * (H * ρ) = -(ΔS * (P₁ * ρ + 2 * H * (X * derivative ρ))))
    (hH0 : H.eval m₀ = 0) (hH1 : (derivative H).eval m₀ ≠ 0)
    (hW : P₁.eval m₀ + m₀ * (derivative H).eval m₀ = 0) {j : ℕ}
    (hj : (X - C m₀) ^ (ΔR.rootMultiplicity m₀ + 1) ∣
      (X - C m₀) * NR + C (2 * j * m₀) * ΔR) : False := by
  have hne : ∀ p : ℂ[X], p ≠ 0 → algebraMap ℂ[X] (RatFunc ℂ) p ≠ 0 := fun p hp ↦
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 hp
  have hH : H ≠ 0 := by rintro rfl; simp at hH1
  have hΔP0 : ΔP ≠ 0 := by rintro rfl; simp at hΔP
  have r1 : HasSimpleResidue
      (algebraMap ℂ[X] (RatFunc ℂ) NP / algebraMap ℂ[X] (RatFunc ℂ) ΔP) m₀ 0 := by
    apply hasSimpleResidue_of_pow_dvd hΔP0
    rw [rootMultiplicity_eq_zero hΔP, zero_add, pow_one, C_0, zero_mul, sub_zero]
    exact dvd_mul_right _ _
  have r2 : HasSimpleResidue
      (algebraMap ℂ[X] (RatFunc ℂ) NR / algebraMap ℂ[X] (RatFunc ℂ) ΔR) m₀ (-(2 * j * m₀)) := by
    apply hasSimpleResidue_of_pow_dvd hΔR
    rwa [C_neg, neg_mul, sub_neg_eq_add]
  have hL := (r1.add (hasSimpleResidue_algebraMap_mul_rankOneLeft r2 (C (-1)))).add
    (hasSimpleResidue_algebraMap_mul_rankOneLeft (hasSimpleResidue_logDeriv hrf m₀) (C (-2) * X))
  have hR := (hasSimpleResidue_neg_div_rankOneLeft hH0 hH1 hW).add
    (hasSimpleResidue_algebraMap_mul_rankOneLeft (hasSimpleResidue_logDeriv hρ m₀) (C (-2) * X))
  have heq : algebraMap ℂ[X] (RatFunc ℂ) NP / algebraMap ℂ[X] (RatFunc ℂ) ΔP +
      algebraMap ℂ[X] (RatFunc ℂ) (C (-1)) *
        (algebraMap ℂ[X] (RatFunc ℂ) NR / algebraMap ℂ[X] (RatFunc ℂ) ΔR) +
      algebraMap ℂ[X] (RatFunc ℂ) (C (-2) * X) *
        (algebraMap ℂ[X] (RatFunc ℂ) (derivative rf) / algebraMap ℂ[X] (RatFunc ℂ) rf) =
      algebraMap ℂ[X] (RatFunc ℂ) (-P₁) / algebraMap ℂ[X] (RatFunc ℂ) H +
      algebraMap ℂ[X] (RatFunc ℂ) (C (-2) * X) *
        (algebraMap ℂ[X] (RatFunc ℂ) (derivative ρ) / algebraMap ℂ[X] (RatFunc ℂ) ρ) := by
    have hA' := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hA
    have hB' := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hB
    have h1 := hne _ hΔS
    have h2 := hne _ hΔP0
    have h3 := hne _ hΔR
    have h4 := hne _ hrf
    have h5 := hne _ hρ
    have h6 := hne _ hH
    simp only [map_mul, map_sub, map_neg, map_add, map_ofNat, map_one] at hA' hB' ⊢
    have e1 : algebraMap ℂ[X] (RatFunc ℂ) NS / algebraMap ℂ[X] (RatFunc ℂ) ΔS =
        algebraMap ℂ[X] (RatFunc ℂ) NP / algebraMap ℂ[X] (RatFunc ℂ) ΔP -
          algebraMap ℂ[X] (RatFunc ℂ) NR / algebraMap ℂ[X] (RatFunc ℂ) ΔR -
          2 * algebraMap ℂ[X] (RatFunc ℂ) X * algebraMap ℂ[X] (RatFunc ℂ) (derivative rf) /
            algebraMap ℂ[X] (RatFunc ℂ) rf := by
      field_simp
      linear_combination hA'
    have e2 : algebraMap ℂ[X] (RatFunc ℂ) NS / algebraMap ℂ[X] (RatFunc ℂ) ΔS =
        -algebraMap ℂ[X] (RatFunc ℂ) P₁ / algebraMap ℂ[X] (RatFunc ℂ) H -
          2 * algebraMap ℂ[X] (RatFunc ℂ) X * algebraMap ℂ[X] (RatFunc ℂ) (derivative ρ) /
            algebraMap ℂ[X] (RatFunc ℂ) ρ := by
      field_simp
      linear_combination hB'
    linear_combination e2 - e1
  rw [heq] at hL
  have hu := hL.unique hR
  simp only [eval_mul, eval_C, eval_X] at hu
  have hnat : ((2 * j + 2 * ρ.rootMultiplicity m₀ : ℕ) : ℂ) =
      ((2 * rf.rootMultiplicity m₀ + 1 : ℕ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ hm₀
    linear_combination hu
  have := Nat.cast_injective hnat
  omega

/-- The symbol and the first jet of `β P = S ⋆ R`. -/
private theorem specialize_identities_rankOneLeft {P S R : RecOp} {β : Coeff}
    (h : C β * P = oreMul coeffShift S R) :
    C (β.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize P = specialize S * specialize R ∧
      C (coeffJet β) * specialize P +
          C (β.map (Polynomial.evalRingHom (-1 : ℤ))) * specializeJet P =
        specializeJet S * specialize R + specialize S * specializeJet R -
          2 * (X * derivative (specialize S)) * (C X * coeffDerivative (specialize R)) := by
  refine ⟨?_, ?_⟩
  · rw [← specialize_oreMul, ← h, map_mul]
    congr 1
    rw [specialize, coe_mapRingHom, map_C, coe_mapRingHom]
  · rw [← specializeJet_oreMul, ← h, specializeJet_C_mul]

/-- The first jet of an operator has at most the degree of the operator. -/
private theorem natDegree_specializeJet_le_rankOneLeft (R : RecOp) :
    (specializeJet R).natDegree ≤ R.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_specializeJet, coeff_eq_zero_of_natDegree_lt hk, coeffJet_zero]

/-- The derivative in `M` does not raise the degree in `L`. -/
private theorem natDegree_coeffDerivative_le_rankOneLeft (p : ℤ[X][X]) :
    (coeffDerivative p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_coeffDerivative, coeff_eq_zero_of_natDegree_lt hk, derivative_zero]

/-- The end coefficients of the symbol and of the first jet of `β P = S ⋆ R` with `S` of degree
one: `β̄ p̄₀ = s̄₀ r̄₀`, `β̄ p̄_d = s̄₁ r̄_f`, and their first jets. -/
private theorem end_coeff_identities_rankOneLeft {P S R : RecOp} {β : Coeff}
    (h : C β * P = oreMul coeffShift S R) (hS : S.natDegree = 1) :
    β.map (Polynomial.evalRingHom (-1 : ℤ)) * (specialize P).coeff 0 =
        (specialize S).coeff 0 * (specialize R).coeff 0 ∧
      coeffJet β * (specialize P).coeff 0 +
          β.map (Polynomial.evalRingHom (-1 : ℤ)) * (specializeJet P).coeff 0 =
        (specializeJet S).coeff 0 * (specialize R).coeff 0 +
          (specialize S).coeff 0 * (specializeJet R).coeff 0 ∧
      β.map (Polynomial.evalRingHom (-1 : ℤ)) * (specialize P).coeff (1 + R.natDegree) =
        (specialize S).coeff 1 * (specialize R).coeff R.natDegree ∧
      coeffJet β * (specialize P).coeff (1 + R.natDegree) +
          β.map (Polynomial.evalRingHom (-1 : ℤ)) * (specializeJet P).coeff (1 + R.natDegree) =
        (specializeJet S).coeff 1 * (specialize R).coeff R.natDegree +
          (specialize S).coeff 1 * (specializeJet R).coeff R.natDegree -
            2 * (specialize S).coeff 1 * (X * derivative ((specialize R).coeff R.natDegree)) := by
  obtain ⟨I0, I1⟩ := specialize_identities_rankOneLeft h
  have hS0 : (specialize S).natDegree ≤ 1 := hS ▸ natDegree_map_le
  have hSJ : (specializeJet S).natDegree ≤ 1 := hS ▸ natDegree_specializeJet_le_rankOneLeft S
  have hR0 : (specialize R).natDegree ≤ R.natDegree := natDegree_map_le
  have hRJ := natDegree_specializeJet_le_rankOneLeft R
  have hXS : (2 * (X * derivative (specialize S))).natDegree ≤ 1 := by
    have h1 : (derivative (specialize S)).natDegree ≤ 0 :=
      (natDegree_derivative_le _).trans (by omega)
    have h2 : (X * derivative (specialize S)).natDegree ≤ 1 + 0 :=
      natDegree_mul_le_of_le natDegree_X_le h1
    exact (natDegree_mul_le_of_le (natDegree_ofNat 2).le h2).trans (by omega)
  have hXR : (C X * coeffDerivative (specialize R)).natDegree ≤ R.natDegree :=
    (natDegree_C_mul_le _ _).trans ((natDegree_coeffDerivative_le_rankOneLeft _).trans hR0)
  have hc : (2 * (X * derivative (specialize S))).coeff 1 = 2 * (specialize S).coeff 1 := by
    rw [coeff_ofNat_mul, coeff_X_mul, coeff_derivative]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (fun p : ℤ[X][X] ↦ p.coeff 0) I0
    simpa only [mul_coeff_zero, coeff_C_zero] using this
  · have := congrArg (fun p : ℤ[X][X] ↦ p.coeff 0) I1
    simpa only [coeff_add, coeff_sub, mul_coeff_zero, coeff_C_zero, coeff_X_zero, zero_mul,
      mul_zero, sub_zero] using this
  · have := congrArg (fun p : ℤ[X][X] ↦ p.coeff (1 + R.natDegree)) I0
    simpa only [coeff_C_mul, coeff_mul_add_eq_of_natDegree_le hS0 hR0] using this
  · have := congrArg (fun p : ℤ[X][X] ↦ p.coeff (1 + R.natDegree)) I1
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_mul_add_eq_of_natDegree_le hS0 hRJ,
      coeff_mul_add_eq_of_natDegree_le hSJ hR0, coeff_mul_add_eq_of_natDegree_le hXS hXR, hc,
      coeff_coeffDerivative] at this
    exact this

/-- The multiplicativity of the end coefficients, on the level of logarithmic first jets:
`N_S/Δ_S = N_P/Δ_P - N_R/Δ_R - 2 D/r_f`, cleared of denominators. -/
private theorem endJet_algebra_rankOneLeft {A : Type*} [CommRing A]
    {b b' p0 p0' pd pd' s0 s0' s1 s1' r0 r0' rf rf' D : A}
    (E1 : b * p0 = s0 * r0) (E2 : b' * p0 + b * p0' = s0' * r0 + s0 * r0')
    (E3 : b * pd = s1 * rf) (E4 : b' * pd + b * pd' = s1' * rf + s1 * rf' - 2 * s1 * D) :
    b ^ 2 * ((s0' * s1 - s0 * s1') * (p0 * pd) * (r0 * rf) * rf) =
      b ^ 2 * (s0 * s1 * ((p0' * pd - p0 * pd') * (r0 * rf) * rf -
        (r0' * rf - r0 * rf') * (p0 * pd) * rf - 2 * D * (p0 * pd) * (r0 * rf))) := by
  linear_combination
    (rf * ((s0' * r0 + s0 * r0') * s1 * rf - (s1' * rf + s1 * rf' - 2 * s1 * D) * s0 * r0) *
        b * pd + s0 * s1 * (r0 * rf) * rf * (s1' * rf + s1 * rf' - 2 * s1 * D)) * E1 -
      s0 * s1 * (r0 * rf) * rf * b * pd * E2 +
      (rf * ((s0' * r0 + s0 * r0') * s1 * rf - (s1' * rf + s1 * rf' - 2 * s1 * D) * s0 * r0) *
        s0 * r0 - s0 * s1 * (r0 * rf) * rf * (s0' * r0 + s0 * r0')) * E3 +
      s0 * s1 * (r0 * rf) * rf * b * p0 * E4

/-- At a point `(m₀, 1)` where `(∂_L P₀)(·, 1)` has a simple zero and the Weyl symbol vanishes,
no left pseudo-factor of degree one has a symbol vanishing at `L = 1`. -/
theorem not_rankOne_left_of_weylSymbol_eq_zero {P : RecOp} {m₀ : ℂ} (hm₀ : m₀ ≠ 0)
    (hdeg : (specialize P).natDegree = P.natDegree)
    (hlead : ((specialize P).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hconst : (((specialize P).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hH0 : evalIntPoint (derivative (specialize P)) m₀ 1 = 0)
    (hH1 : evalIntPoint (coeffDerivative (derivative (specialize P))) m₀ 1 ≠ 0)
    (hW : evalIntPoint (weylSymbol P) m₀ 1 = 0)
    {β : Coeff} (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S R : RecOp}
    (h : C β * P = oreMul coeffShift S R) (hS : S.natDegree = 1)
    (hS1 : (specialize S).eval 1 = 0) : False := by
  have hconst0 : (specialize P).coeff 0 ≠ 0 := fun h0 ↦
    hconst (by rw [h0, Polynomial.map_zero, eval_zero])
  have hlead0 : (specialize P).leadingCoeff ≠ 0 := fun h0 ↦
    hlead (by rw [h0, Polynomial.map_zero, eval_zero])
  have hβ0 : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  obtain ⟨I0, -⟩ := specialize_identities_rankOneLeft h
  have hprod : specialize S * specialize R ≠ 0 := by
    rw [← I0]
    exact mul_ne_zero (C_ne_zero.mpr hβ) (leadingCoeff_ne_zero.mp hlead0)
  have hSne : S ≠ 0 := fun h0 ↦ left_ne_zero_of_mul hprod (by rw [h0, map_zero])
  have hRne : R ≠ 0 := fun h0 ↦ right_ne_zero_of_mul hprod (by rw [h0, map_zero])
  have hn : P.natDegree = 1 + R.natDegree := by
    rw [← hS, ← natDegree_oreMul coeffShift_injective hSne hRne, ← h, natDegree_C_mul hβ0]
  obtain ⟨E1, E2, E3, E4⟩ := end_coeff_identities_rankOneLeft h hS
  rw [← hn] at E3 E4
  have hpd : (specialize P).coeff P.natDegree ≠ 0 := by
    rw [← hdeg]
    exact hlead0
  have hΔR0 : nodeDenom R ≠ 0 := nodeDenom_ne_zero_of_pseudoFactor hβ h hdeg hconst0
  have hΔS0 : nodeDenom S ≠ 0 := by
    rw [nodeDenom, hS]
    exact mul_ne_zero (left_ne_zero_of_mul (E1 ▸ mul_ne_zero hβ hconst0))
      (left_ne_zero_of_mul (E3 ▸ mul_ne_zero hβ hpd))
  have hrf0 : (specialize R).coeff R.natDegree ≠ 0 := right_ne_zero_of_mul hΔR0
  have hA : nodeNumer S * nodeDenom P * nodeDenom R * (specialize R).coeff R.natDegree =
      nodeDenom S * (nodeNumer P * nodeDenom R * (specialize R).coeff R.natDegree -
        nodeNumer R * nodeDenom P * (specialize R).coeff R.natDegree -
        2 * (X * derivative ((specialize R).coeff R.natDegree)) * nodeDenom P *
          nodeDenom R) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hβ)
    rw [nodeNumer, nodeNumer, nodeNumer, nodeDenom, nodeDenom, nodeDenom, hS]
    exact endJet_algebra_rankOneLeft E1 E2 E3 E4
  have hB := nodeNumer_mul_of_rankOne_left hβ h hS hS1
  rw [evalIntPoint_at_one] at hH0
  rw [evalIntPoint_at_one, eval_one_coeffDerivative, ← derivative_map] at hH1
  rw [evalIntPoint_weylSymbol_one_rankOneLeft] at hW
  have hH : (derivative (specialize P)).eval 1 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero, derivative_zero, eval_zero] at hH1
    exact hH1 rfl
  have hρ0 : (specialize R).eval 1 ≠ 0 := by
    intro h0
    have := congrArg (fun p : ℤ[X][X] ↦ (derivative p).eval 1) I0
    simp only [derivative_mul, derivative_C, eval_mul, eval_C, eval_add, zero_mul, zero_add,
      h0, hS1, mul_zero, add_zero] at this
    exact mul_ne_zero hβ hH this
  have hmap : ∀ p : ℤ[X], p ≠ 0 → p.map (Int.castRingHom ℂ) ≠ 0 := fun p hp ↦
    (Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hp
  have hlead' : (complexSpec (coeffToComplex P.leadingCoeff)).eval m₀ ≠ 0 := by
    rw [complexSpec_coeffToComplex, Polynomial.leadingCoeff, ← coeff_specialize, ← hdeg]
    exact hlead
  have hconst' : (complexSpec (coeffToComplex (P.coeff 0))).eval m₀ ≠ 0 := by
    rw [complexSpec_coeffToComplex, ← coeff_specialize]
    exact hconst
  obtain ⟨j, hj⟩ := exists_nat_pow_dvd_nodeNumer_of_pseudoFactor hβ0 h hlead' hconst'
  have hΔP : ((nodeDenom P).map (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
    rw [nodeDenom, Polynomial.map_mul, eval_mul, ← hdeg]
    exact mul_ne_zero hconst hlead
  have hA' := congrArg (Polynomial.map (Int.castRingHom ℂ)) hA
  have hB' := congrArg (Polynomial.map (Int.castRingHom ℂ)) hB
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_add,
    Polynomial.map_ofNat, Polynomial.map_X, ← derivative_map] at hA' hB'
  exact false_of_residue_rankOneLeft hm₀ (hmap _ hΔS0) (hmap _ hΔR0) (hmap _ hrf0)
    (hmap _ hρ0) hΔP hA' hB' hH0 hH1 hW hj

end AJConjecture
