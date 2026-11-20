import Mathlib
import AJConjecture.QAlgPseudoFactorNormalize
import AJConjecture.QAlgSpecializeOreMul
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgTwistFactorPrime
import AJTwist.Factor.TwFBlockCount
import AJTwist.Main.TwMClauses
import AJTwist.Main.TwMReflectComparison
import AJPaper.Divisor.PpLSymbol

/-!
# Right factors of order one of the adjoint of `P_0`: symbol and cofactor (Unit PpL, node
`PpL_Cofactor`)

Source: Section 5.6 of the paper (`operators.tex`): "A monic linear right divisor over
`ℂ(t, M)` must reduce to `u - 1`. Two distinct such divisors would have a monic degree-two least
common left multiple right-dividing `P` … Its degree-two residual divisor of `P̄` would be
`E_back`. Degree-preserving reduction of its factorization by one of the linear divisors would
make `u - 1` divide `E_back`, contrary to `E_back(1) = 4/x`." The same argument for the adjoint,
whose symbol is `-(M² - 1)² (L - 1) E^∨` (`specialize_pplAdjOp`) with `E^∨` prime of degree `2`
in `ℚ(M)[L, L⁻¹]` (`prime_toComparison_extraFactorMirror`) and `E^∨(M, 1) = 4 M² ≠ 0`.

Mirror of `AJTwist/Factor/TwFZeroCofactor.lean`, with `pplAdjOp` for `twTransferOp 0` and
`extraFactorMirror` for `extraFactor`:

* `ppl_adjoint_rightFactor_symbol`: the symbol of a right pseudo-factor of degree one (with
  `β(-1, M) ≠ 0`) vanishes at `L = 1`.
  Route: `β̄ P̄† = S̄ R̄` (`specialize_oreMul`), `deg S̄ ≤ 2`, `deg R̄ ≤ 1`, both nonzero. In the
  comparison ring `E^∨` is prime and does not divide `R̄` (`natDegree_le_of_toComparison_dvd`,
  `extraFactorMirror.coeff 0 = 1`), so `E^∨ ∣ S̄`. Also `L - 1` is prime
  (`prime_toComparison_X_sub_one`) and divides `S̄ R̄`. If it divided `S̄`, the product
  `(L - 1) E^∨` of two non-associated primes (`E^∨(M, 1) = 4 M² ≠ 0`,
  `eval_one_eq_zero_of_toComparison_X_sub_one_dvd`) would divide `S̄`, of degree `3 > 2`
  (`natDegree_le_of_toComparison_dvd` with constant coefficient `-1`). Hence `L - 1 ∣ R̄` and
  `R̄(M, 1) = 0` (`eval_one_eq_zero_of_toComparison_X_sub_one_dvd`). (The template instead
  descends `E ∣ S̄` to `ℤ[M][L]`; for `E^∨`, which is not monic, the route above avoids the
  descent.)
* `ppl_adjoint_no_linear_cofactor`: the cofactor `S` of a right pseudo-factor of degree one has
  no right pseudo-factor of degree one. Route: verbatim the template
  (`twf_zero_no_linear_cofactor`): `β₂ β P† = S₂ ⋆ (R₂ ⋆ R)`, normalise the three factors of
  degree one at `t = -1` (`exists_pow_mul_map_ne_zero`, `exists_pow_mul_specialize_ne_zero`,
  `eq_of_pow_mul_eq_pow_mul`; a polynomial in `t` alone commutes with the Ore product), and the
  prime `E^∨` of degree two would divide one of three symbols of degree at most one.

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The specialisation at `t = -1` does not raise the degree in `L`. -/
private theorem natDegree_specialize_le_pplCofactor (P : RecOp) :
    (specialize P).natDegree ≤ P.natDegree := by
  rw [specialize, coe_mapRingHom]
  exact natDegree_map_le

/-- The specialisation of a constant operator. -/
private theorem specialize_C_pplCofactor (β : Coeff) :
    specialize (C β) = C (β.map (Polynomial.evalRingHom (-1 : ℤ))) :=
  Polynomial.map_C _

/-- The symbol of the adjoint is `(L - 1) E^∨` up to polynomials in `M`, the left one
nonzero. -/
private theorem exists_symbol_pplCofactor :
    ∃ κ₁ : ℤ[X], κ₁ ≠ 0 ∧ ∃ κ₂ : ℤ[X],
      C κ₁ * specialize pplAdjOp = C κ₂ * ((X - 1) * extraFactorMirror) :=
  ⟨1, one_ne_zero, -(X ^ 2 - 1) ^ 2, by rw [specialize_pplAdjOp, C_1, one_mul, C_neg]; ring⟩

/-- The symbol identity transported to a factorisation of the symbol. -/
private theorem symbol_mul_pplCofactor {κ₁ κ₂ b : ℤ[X]} {p g q : ℤ[X][X]}
    (hsym : C κ₁ * p = C κ₂ * g) (hsp : C b * p = q) : C κ₁ * q = C (b * κ₂) * g := by
  rw [← hsp, C_mul]
  linear_combination C b * hsym

/-- The powers of `t + 1` are nonzero coefficients. -/
private theorem C_X_add_one_pow_ne_zero_pplCofactor (n : ℕ) :
    (C ((X + 1 : ℤ[X]) ^ n) : Coeff) ≠ 0 :=
  C_ne_zero.mpr (pow_ne_zero _ (X_add_C_ne_zero (1 : ℤ)))

/-- The mirror factor has degree two in `L`. -/
private theorem natDegree_extraFactorMirror_pplCofactor : extraFactorMirror.natDegree = 2 := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_)
    (le_natDegree_of_ne_zero ?_)
  · rw [coeff_extraFactorMirror, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  · have h2 : extraFactorMirror.coeff 2 = X ^ 4 := by
      rw [coeff_extraFactorMirror]
      rfl
    rw [h2]
    exact pow_ne_zero 4 X_ne_zero

/-- The mirror factor does not divide, in the comparison ring, a nonzero polynomial of degree at
most one in `L`. -/
private theorem not_toComparison_extraFactorMirror_dvd_pplCofactor {g : ℤ[X][X]} (hg : g ≠ 0)
    (hdeg : g.natDegree ≤ 1) : ¬ toComparison extraFactorMirror ∣ toComparison g := by
  intro hdvd
  have hc : extraFactorMirror.coeff 0 ≠ 0 := by
    rw [coeff_extraFactorMirror, ite_eq_left rfl]
    exact one_ne_zero
  have hle := natDegree_le_of_toComparison_dvd hc hg hdvd
  rw [natDegree_extraFactorMirror_pplCofactor] at hle
  omega

/-- A polynomial in `t` alone is fixed by the iterated shift. -/
private theorem iterate_coeffShift_C_pplCofactor (i : ℕ) (r : ℤ[X]) :
    coeffShift^[i] (C r) = C r := by
  have hfix : coeffShift (C r) = C r := by
    have hcomp : coeffShift (C r) = (C r : Coeff).comp (C (X ^ 2) * X : Coeff) := rfl
    rw [hcomp, Polynomial.C_comp]
  exact Function.iterate_fixed hfix i

/-- A polynomial in `t` alone moves out of the right factor of an Ore product. -/
private theorem oreMul_C_C_mul_right_pplCofactor (r : ℤ[X]) (S R : RecOp) :
    oreMul coeffShift S (C (C r) * R) = C (C r) * oreMul coeffShift S R := by
  induction S using Polynomial.induction_on' with
  | add p p' hp hp' => rw [oreMul_add_left, oreMul_add_left, hp, hp', mul_add]
  | monomial i a =>
    induction R using Polynomial.induction_on' with
    | add q q' hq hq' => rw [mul_add, oreMul_add_right, oreMul_add_right, hq, hq', mul_add]
    | monomial k b =>
      rw [Polynomial.C_mul_monomial, oreMul_monomial_monomial, oreMul_monomial_monomial,
        Polynomial.C_mul_monomial, iterate_map_mul, iterate_coeffShift_C_pplCofactor,
        mul_left_comm]

/-- A constant moves into the left factor of an Ore product. -/
private theorem C_mul_oreMul_pplCofactor (c : Coeff) (P Q : RecOp) :
    C c * oreMul coeffShift P Q = oreMul coeffShift (C c * P) Q := by
  rw [← oreMul_C_left coeffShift c (oreMul coeffShift P Q), ← oreMul_assoc, oreMul_C_left]

/-- The Ore product with `0` on the left is `0`. -/
private theorem oreMul_zero_left_pplCofactor (Q : RecOp) : oreMul coeffShift 0 Q = 0 := by
  rw [← C_0, oreMul_C_left, C_0, zero_mul]

/-- The symbol of a right pseudo-factor of degree one of the adjoint of `P_0` vanishes at
`L = 1`. -/
theorem ppl_adjoint_rightFactor_symbol {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S R : RecOp}
    (h : C β * pplAdjOp = oreMul coeffShift S R) (hR : R.natDegree = 1) :
    (specialize R).eval 1 = 0 := by
  have hβ0 : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  have hP := specialize_pplAdjOp_ne_zero
  have hP0 : pplAdjOp ≠ 0 := fun h0 ↦ hP (by rw [h0, map_zero])
  have hne : oreMul coeffShift S R ≠ 0 := h ▸ mul_ne_zero (C_ne_zero.mpr hβ0) hP0
  have hS0 : S ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_left_pplCofactor R)
  have hR0 : R ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hR
    exact zero_ne_one hR
  have hSdeg : S.natDegree = 2 := by
    have hd := congrArg natDegree h
    rw [natDegree_C_mul hβ0, natDegree_pplAdjOp,
      natDegree_oreMul coeffShift_injective hS0 hR0, hR] at hd
    omega
  have hsp : C (β.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize pplAdjOp =
      specialize S * specialize R := by
    rw [← specialize_oreMul, ← h, map_mul, specialize_C_pplCofactor]
  have hsr : specialize S * specialize R ≠ 0 := hsp ▸ mul_ne_zero (C_ne_zero.mpr hβ) hP
  have hs0 : specialize S ≠ 0 := left_ne_zero_of_mul hsr
  have hr0 : specialize R ≠ 0 := right_ne_zero_of_mul hsr
  have hsdeg : (specialize S).natDegree ≤ 2 := hSdeg ▸ natDegree_specialize_le_pplCofactor S
  have hrdeg : (specialize R).natDegree ≤ 1 := hR ▸ natDegree_specialize_le_pplCofactor R
  have hcmp : toComparison (specialize S) * toComparison (specialize R) =
      toComparison (C (-(β.map (Polynomial.evalRingHom (-1 : ℤ)) * (X ^ 2 - 1) ^ 2))) *
        (toComparison (X - 1) * toComparison extraFactorMirror) := by
    have e1 : toComparison (specialize S) * toComparison (specialize R) =
        toComparison (specialize S * specialize R) := (map_mul toComparison _ _).symm
    rw [e1, ← hsp, specialize_pplAdjOp]
    simp only [map_mul, map_neg]
    ring
  have hE : toComparison extraFactorMirror ∣ toComparison (specialize S) :=
    (prime_toComparison_extraFactorMirror.dvd_or_dvd
      ⟨toComparison (C (-(β.map (Polynomial.evalRingHom (-1 : ℤ)) * (X ^ 2 - 1) ^ 2))) *
        toComparison (X - 1), by rw [hcmp]; ring⟩).resolve_right
      (not_toComparison_extraFactorMirror_dvd_pplCofactor hr0 hrdeg)
  have hL : toComparison (X - 1) ∣ toComparison (specialize S) * toComparison (specialize R) :=
    ⟨toComparison (C (-(β.map (Polynomial.evalRingHom (-1 : ℤ)) * (X ^ 2 - 1) ^ 2))) *
      toComparison extraFactorMirror, by rw [hcmp]; ring⟩
  rcases prime_toComparison_X_sub_one.dvd_or_dvd hL with h1 | h1
  · exfalso
    obtain ⟨c, hc⟩ := hE
    have h2 : toComparison (X - 1) ∣ toComparison extraFactorMirror * c := by
      rw [← hc]
      exact h1
    rcases prime_toComparison_X_sub_one.dvd_or_dvd h2 with h3 | h3
    · have hev := eval_one_eq_zero_of_toComparison_X_sub_one_dvd h3
      have h4 : extraFactorMirror.eval 1 = 4 * X ^ 2 := by
        simp only [extraFactorMirror, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
          eval_one, one_pow, mul_one]
        ring
      rw [h4] at hev
      have h4' : (4 : ℤ[X]) ≠ 0 := by
        rw [← C_ofNat]
        exact C_ne_zero.mpr (by norm_num)
      exact mul_ne_zero h4' (pow_ne_zero 2 X_ne_zero) hev
    · obtain ⟨c', rfl⟩ := h3
      have hdvd : toComparison ((X - 1) * extraFactorMirror) ∣ toComparison (specialize S) :=
        ⟨c', by rw [hc, map_mul]; ring⟩
      have hc0 : ((X - 1) * extraFactorMirror : ℤ[X][X]).coeff 0 ≠ 0 := by
        rw [mul_coeff_zero, coeff_extraFactorMirror, ite_eq_left rfl]
        simp
      have hXC : (X - 1 : ℤ[X][X]) = X - C 1 := by rw [C_1]
      have hEm0 : extraFactorMirror ≠ 0 := fun h0 ↦ by
        have := natDegree_extraFactorMirror_pplCofactor
        rw [h0, natDegree_zero] at this
        omega
      have hle := natDegree_le_of_toComparison_dvd hc0 hs0 hdvd
      rw [natDegree_mul (hXC ▸ X_sub_C_ne_zero 1) hEm0, hXC, natDegree_X_sub_C,
        natDegree_extraFactorMirror_pplCofactor] at hle
      omega
  · exact eval_one_eq_zero_of_toComparison_X_sub_one_dvd h1

/-- The cofactor of a right pseudo-factor of degree one of the adjoint of `P_0` has no right
pseudo-factor of degree one. -/
theorem ppl_adjoint_no_linear_cofactor {β β₂ : Coeff} (hβ : β ≠ 0) (hβ₂ : β₂ ≠ 0)
    {S R S₂ R₂ : RecOp} (h : C β * pplAdjOp = oreMul coeffShift S R)
    (hR : R.natDegree = 1) (h₂ : C β₂ * S = oreMul coeffShift S₂ R₂) : R₂.natDegree ≠ 1 := by
  intro hR₂
  have hP := specialize_pplAdjOp_ne_zero
  have hP0 : pplAdjOp ≠ 0 := fun h0 ↦ hP (by rw [h0, map_zero])
  have hββ : β₂ * β ≠ 0 := mul_ne_zero hβ₂ hβ
  have hkey : C (β₂ * β) * pplAdjOp = oreMul coeffShift S₂ (oreMul coeffShift R₂ R) := by
    rw [C_mul, mul_assoc, h, C_mul_oreMul_pplCofactor, h₂, oreMul_assoc]
  have hR0 : R ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hR
    exact zero_ne_one hR
  have hR₂0 : R₂ ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hR₂
    exact zero_ne_one hR₂
  have hS₂0 : S₂ ≠ 0 := by
    rintro rfl
    rw [oreMul_zero_left_pplCofactor] at hkey
    exact mul_ne_zero (C_ne_zero.mpr hββ) hP0 hkey
  have hS₂deg : S₂.natDegree = 1 := by
    have hd := congrArg natDegree hkey
    rw [natDegree_C_mul hββ, natDegree_pplAdjOp,
      natDegree_oreMul coeffShift_injective hS₂0
        (oreMul_ne_zero coeffShift_injective hR₂0 hR0),
      natDegree_oreMul coeffShift_injective hR₂0 hR0, hR, hR₂] at hd
    omega
  obtain ⟨a, β', hβ', hβeq⟩ := exists_pow_mul_map_ne_zero hββ
  obtain ⟨b, S₂', hS₂', hS₂eq⟩ := exists_pow_mul_specialize_ne_zero hS₂0
  obtain ⟨c, R₂', hR₂', hR₂eq⟩ := exists_pow_mul_specialize_ne_zero hR₂0
  obtain ⟨d, R', hR', hReq⟩ := exists_pow_mul_specialize_ne_zero hR0
  have hdS : (specialize S₂').natDegree ≤ 1 := by
    rw [hS₂eq, natDegree_C_mul (C_X_add_one_pow_ne_zero_pplCofactor b)] at hS₂deg
    exact hS₂deg ▸ natDegree_specialize_le_pplCofactor S₂'
  have hdR₂ : (specialize R₂').natDegree ≤ 1 := by
    rw [hR₂eq, natDegree_C_mul (C_X_add_one_pow_ne_zero_pplCofactor c)] at hR₂
    exact hR₂ ▸ natDegree_specialize_le_pplCofactor R₂'
  have hdR : (specialize R').natDegree ≤ 1 := by
    rw [hReq, natDegree_C_mul (C_X_add_one_pow_ne_zero_pplCofactor d)] at hR
    exact hR ▸ natDegree_specialize_le_pplCofactor R'
  have hnorm : C (C ((X + 1 : ℤ[X]) ^ a)) * (C β' * pplAdjOp) =
      C (C ((X + 1 : ℤ[X]) ^ (b + c + d))) *
        oreMul coeffShift S₂' (oreMul coeffShift R₂' R') := by
    rw [← mul_assoc, ← C_mul, ← hβeq, hkey, hS₂eq, hR₂eq, hReq,
      oreMul_C_C_mul_right_pplCofactor, ← C_mul_oreMul_pplCofactor,
      oreMul_C_C_mul_right_pplCofactor, ← C_mul_oreMul_pplCofactor,
      oreMul_C_C_mul_right_pplCofactor, pow_add, pow_add, C_mul, C_mul, C_mul, C_mul]
    ring
  have hU : specialize (C β' * pplAdjOp) ≠ 0 := by
    rw [map_mul, specialize_C_pplCofactor]
    exact mul_ne_zero (C_ne_zero.mpr hβ') hP
  have hV : specialize (oreMul coeffShift S₂' (oreMul coeffShift R₂' R')) ≠ 0 := by
    rw [specialize_oreMul, specialize_oreMul]
    exact mul_ne_zero hS₂' (mul_ne_zero hR₂' hR')
  have hfac := eq_of_pow_mul_eq_pow_mul hU hV hnorm
  have hsp : C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize pplAdjOp =
      specialize S₂' * (specialize R₂' * specialize R') := by
    rw [← specialize_oreMul, ← specialize_oreMul, ← hfac, map_mul, specialize_C_pplCofactor]
  obtain ⟨κ₁, hκ₁, κ₂, hsymP⟩ := exists_symbol_pplCofactor
  have hsym := symbol_mul_pplCofactor hsymP hsp
  have h1 : toComparison extraFactorMirror ∣ toComparison (C κ₁) *
      (toComparison (specialize S₂') *
        (toComparison (specialize R₂') * toComparison (specialize R'))) := by
    rw [← map_mul, ← map_mul, ← map_mul, hsym]
    exact map_dvd _ ((dvd_mul_left _ _).mul_left _)
  rw [(isUnit_toComparison_coeff_of_ne_zero hκ₁).dvd_mul_left] at h1
  rcases prime_toComparison_extraFactorMirror.dvd_or_dvd h1 with h2 | h2
  · exact not_toComparison_extraFactorMirror_dvd_pplCofactor hS₂' hdS h2
  rcases prime_toComparison_extraFactorMirror.dvd_or_dvd h2 with h3 | h3
  · exact not_toComparison_extraFactorMirror_dvd_pplCofactor hR₂' hdR₂ h3
  · exact not_toComparison_extraFactorMirror_dvd_pplCofactor hR' hdR h3

end AJConjecture
