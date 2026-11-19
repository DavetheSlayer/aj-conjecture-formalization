import Mathlib
import AJConjecture.ExtraFactorPrime
import AJConjecture.QAlgPseudoFactorNormalize
import AJConjecture.QAlgSpecializeOreMul
import AJConjecture.QAlgOreMulAssoc
import AJTwist.Quantum.TwQSymbolFacts
import AJTwist.Factor.TwFBlockCount

/-!
# Right factors of order one of `P_0`: symbol and cofactor (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`): "A monic linear right divisor over `ℂ(t, M)`
must reduce to `u - 1`. Two distinct such divisors would have a monic degree-two least common left
multiple right-dividing `P`, by the right Euclidean algorithm. Its degree-two residual divisor of
`P̄` would be `E_back`. Degree-preserving reduction of its factorization by one of the linear
divisors would make `u - 1` divide `E_back`, contrary to `E_back(1) = 4/x`. Thus the monic linear
right divisor is unique if it exists."

In the library's language, for `P_0 = twTransferOp 0` (order `3`, symbol `(L - 1) E` up to units,
`specialize_twTransferOp_zero_mul_eq`):

* `twf_zero_rightFactor_symbol`: the symbol of a right pseudo-factor of degree one (with
  `β(-1, M) ≠ 0`) vanishes at `L = 1`. (`β̄ P₀ = S₀ R₀`, `deg S₀ ≤ 2`, `deg R₀ ≤ 1`; `E` is prime
  of degree `2`, so `E ∣ S₀`; if `L - 1` divided `S₀` too, `(L - 1) E` of degree `3` would divide
  `S₀`.)
* `twf_zero_no_linear_cofactor`: the cofactor `S` of a right pseudo-factor of degree one has no
  right pseudo-factor of degree one. (Otherwise `β₂ β P_0 = S₂ ⋆ (R₂ ⋆ R)` by `oreMul_assoc`;
  normalising twice with `exists_normalized_pseudoFactor`, the symbol of `R₂ ⋆ R`, of degree at
  most `2`, is divisible by the prime `E` and is a product of two polynomials of degree at
  most `1`: contradiction with `natDegree_le_of_toComparison_dvd`.)
The uniqueness statement is in `AJTwist/Factor/TwFZeroUnique.lean`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The specialisation at `t = -1` does not raise the degree in `L`. -/
private theorem natDegree_specialize_le_twfZeroCofactor (P : RecOp) :
    (specialize P).natDegree ≤ P.natDegree := by
  rw [specialize, coe_mapRingHom]
  exact natDegree_map_le

/-- The specialisation of a constant operator. -/
private theorem specialize_C_twfZeroCofactor (β : Coeff) :
    specialize (C β) = C (β.map (Polynomial.evalRingHom (-1 : ℤ))) :=
  Polynomial.map_C _

/-- The symbol of `P_0` is `(L - 1) E` up to polynomials in `M`, the left one nonzero. -/
private theorem exists_symbol_twfZeroCofactor :
    ∃ κ₁ : ℤ[X], κ₁ ≠ 0 ∧ ∃ κ₂ : ℤ[X],
      C κ₁ * specialize (twTransferOp 0) = C κ₂ * ((X - 1) * extraFactor) := by
  have h2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : ℤ) (two_ne_zero)).ne_zero
    rwa [map_one] at this
  have h4 : (X ^ 4 - 1 : ℤ[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : ℤ) (four_ne_zero)).ne_zero
    rwa [map_one] at this
  exact ⟨_, mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 3 h4), _,
    specialize_twTransferOp_zero_mul_eq⟩

/-- The symbol identity transported to a factorisation of the symbol. -/
private theorem symbol_mul_twfZeroCofactor {κ₁ κ₂ b : ℤ[X]} {p g q : ℤ[X][X]}
    (hsym : C κ₁ * p = C κ₂ * g) (hsp : C b * p = q) : C κ₁ * q = C (b * κ₂) * g := by
  rw [← hsp, C_mul]
  linear_combination C b * hsym

/-- The powers of `t + 1` are nonzero coefficients. -/
private theorem C_X_add_one_pow_ne_zero_twfZeroCofactor (n : ℕ) :
    (C ((X + 1 : ℤ[X]) ^ n) : Coeff) ≠ 0 :=
  C_ne_zero.mpr (pow_ne_zero _ (X_add_C_ne_zero (1 : ℤ)))

/-- The extra factor does not divide, in the comparison ring, a nonzero polynomial of degree at
most one in `L`. -/
private theorem not_toComparison_extraFactor_dvd_twfZeroCofactor {g : ℤ[X][X]} (hg : g ≠ 0)
    (hdeg : g.natDegree ≤ 1) : ¬ toComparison extraFactor ∣ toComparison g := by
  intro hdvd
  have hc : extraFactor.coeff 0 ≠ 0 := by
    rw [extraFactor_coeff_zero]
    exact pow_ne_zero 4 X_ne_zero
  have hle := natDegree_le_of_toComparison_dvd hc hg hdvd
  rw [natDegree_extraFactor] at hle
  omega

/-- A polynomial in `t` alone is fixed by the iterated shift. -/
private theorem iterate_coeffShift_C_twfZeroCofactor (i : ℕ) (r : ℤ[X]) :
    coeffShift^[i] (C r) = C r := by
  have hfix : coeffShift (C r) = C r := by
    have hcomp : coeffShift (C r) = (C r : Coeff).comp (C (X ^ 2) * X : Coeff) := rfl
    rw [hcomp, Polynomial.C_comp]
  exact Function.iterate_fixed hfix i

/-- A polynomial in `t` alone moves out of the right factor of an Ore product. -/
private theorem oreMul_C_C_mul_right_twfZeroCofactor (r : ℤ[X]) (S R : RecOp) :
    oreMul coeffShift S (C (C r) * R) = C (C r) * oreMul coeffShift S R := by
  induction S using Polynomial.induction_on' with
  | add p p' hp hp' => rw [oreMul_add_left, oreMul_add_left, hp, hp', mul_add]
  | monomial i a =>
    induction R using Polynomial.induction_on' with
    | add q q' hq hq' => rw [mul_add, oreMul_add_right, oreMul_add_right, hq, hq', mul_add]
    | monomial k b =>
      rw [Polynomial.C_mul_monomial, oreMul_monomial_monomial, oreMul_monomial_monomial,
        Polynomial.C_mul_monomial, iterate_map_mul, iterate_coeffShift_C_twfZeroCofactor,
        mul_left_comm]

/-- A constant moves into the left factor of an Ore product. -/
private theorem C_mul_oreMul_twfZeroCofactor (c : Coeff) (P Q : RecOp) :
    C c * oreMul coeffShift P Q = oreMul coeffShift (C c * P) Q := by
  rw [← oreMul_C_left coeffShift c (oreMul coeffShift P Q), ← oreMul_assoc, oreMul_C_left]

/-- The Ore product with `0` on the left is `0`. -/
private theorem oreMul_zero_left_twfZeroCofactor (Q : RecOp) : oreMul coeffShift 0 Q = 0 := by
  rw [← C_0, oreMul_C_left, C_0, zero_mul]

/-- The symbol of a right pseudo-factor of degree one of `P_0` vanishes at `L = 1`. -/
theorem twf_zero_rightFactor_symbol {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp 0 = oreMul coeffShift S R) (hR : R.natDegree = 1) :
    (specialize R).eval 1 = 0 := by
  have hβ0 : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  have hP := specialize_twTransferOp_ne_zero 0
  have hP0 : twTransferOp 0 ≠ 0 := fun h0 ↦ hP (by rw [h0, map_zero])
  have hne : oreMul coeffShift S R ≠ 0 := h ▸ mul_ne_zero (C_ne_zero.mpr hβ0) hP0
  have hS0 : S ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_left_twfZeroCofactor R)
  have hR0 : R ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hR
    exact zero_ne_one hR
  have hSdeg : S.natDegree = 2 := by
    have hd := congrArg natDegree h
    rw [natDegree_C_mul hβ0, natDegree_twTransferOp, twWindow_zero,
      natDegree_oreMul coeffShift_injective hS0 hR0, hR] at hd
    omega
  have hsp : C (β.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize (twTransferOp 0) =
      specialize S * specialize R := by
    rw [← specialize_oreMul, ← h, map_mul, specialize_C_twfZeroCofactor]
  have hsr : specialize S * specialize R ≠ 0 := hsp ▸ mul_ne_zero (C_ne_zero.mpr hβ) hP
  have hs0 : specialize S ≠ 0 := left_ne_zero_of_mul hsr
  have hr0 : specialize R ≠ 0 := right_ne_zero_of_mul hsr
  have hsdeg : (specialize S).natDegree ≤ 2 :=
    hSdeg ▸ natDegree_specialize_le_twfZeroCofactor S
  have hrdeg : (specialize R).natDegree ≤ 1 := hR ▸ natDegree_specialize_le_twfZeroCofactor R
  obtain ⟨κ₁, hκ₁, κ₂, hsymP⟩ := exists_symbol_twfZeroCofactor
  have hsym := symbol_mul_twfZeroCofactor hsymP hsp
  have hdvd : toComparison extraFactor ∣ toComparison (specialize S) := by
    have h1 : toComparison extraFactor ∣ toComparison (C κ₁) *
        (toComparison (specialize S) * toComparison (specialize R)) := by
      rw [← map_mul, ← map_mul, hsym]
      exact map_dvd _ ((dvd_mul_left _ _).mul_left _)
    rw [(isUnit_toComparison_coeff_of_ne_zero hκ₁).dvd_mul_left] at h1
    exact (prime_toComparison_extraFactor.dvd_or_dvd h1).resolve_right
      (not_toComparison_extraFactor_dvd_twfZeroCofactor hr0 hrdeg)
  obtain ⟨s', hs'⟩ := extraFactor_dvd_of_toComparison_dvd hdvd
  have hE0 : extraFactor ≠ 0 := extraFactor_monic.ne_zero
  have hs'0 : s' ≠ 0 := fun h0 ↦ hs0 (by rw [hs', h0, mul_zero])
  have hcancel : C κ₁ * (s' * specialize R) =
      C (β.map (Polynomial.evalRingHom (-1 : ℤ)) * κ₂) * (X - 1) := by
    refine mul_left_cancel₀ hE0 ?_
    rw [hs'] at hsym
    linear_combination hsym
  have hev := congrArg (Polynomial.eval 1) hcancel
  simp only [eval_mul, eval_C, eval_sub, eval_X, eval_one, sub_self, mul_zero] at hev
  rcases mul_eq_zero.mp hev with h0 | h0
  · exact absurd h0 hκ₁
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exfalso
    obtain ⟨s'', hs''⟩ := dvd_iff_isRoot.mpr h1
    have hs''0 : s'' ≠ 0 := fun h0 ↦ hs'0 (by rw [hs'', h0, mul_zero])
    have hXC : (X - C (1 : ℤ[X]) : ℤ[X][X]) ≠ 0 := X_sub_C_ne_zero 1
    have hd : (specialize S).natDegree = 2 + (1 + s''.natDegree) := by
      rw [hs', hs'', natDegree_mul hE0 (mul_ne_zero hXC hs''0), natDegree_mul hXC hs''0,
        natDegree_extraFactor, natDegree_X_sub_C]
    omega
  · exact h1

/-- The cofactor of a right pseudo-factor of degree one of `P_0` has no right pseudo-factor of
degree one. -/
theorem twf_zero_no_linear_cofactor {β β₂ : Coeff} (hβ : β ≠ 0) (hβ₂ : β₂ ≠ 0)
    {S R S₂ R₂ : RecOp} (h : C β * twTransferOp 0 = oreMul coeffShift S R)
    (hR : R.natDegree = 1) (h₂ : C β₂ * S = oreMul coeffShift S₂ R₂) : R₂.natDegree ≠ 1 := by
  intro hR₂
  have hP := specialize_twTransferOp_ne_zero 0
  have hP0 : twTransferOp 0 ≠ 0 := fun h0 ↦ hP (by rw [h0, map_zero])
  have hββ : β₂ * β ≠ 0 := mul_ne_zero hβ₂ hβ
  have hkey : C (β₂ * β) * twTransferOp 0 =
      oreMul coeffShift S₂ (oreMul coeffShift R₂ R) := by
    rw [C_mul, mul_assoc, h, C_mul_oreMul_twfZeroCofactor, h₂, oreMul_assoc]
  have hR0 : R ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hR
    exact zero_ne_one hR
  have hR₂0 : R₂ ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hR₂
    exact zero_ne_one hR₂
  have hS₂0 : S₂ ≠ 0 := by
    rintro rfl
    rw [oreMul_zero_left_twfZeroCofactor] at hkey
    exact mul_ne_zero (C_ne_zero.mpr hββ) hP0 hkey
  have hS₂deg : S₂.natDegree = 1 := by
    have hd := congrArg natDegree hkey
    rw [natDegree_C_mul hββ, natDegree_twTransferOp, twWindow_zero,
      natDegree_oreMul coeffShift_injective hS₂0
        (oreMul_ne_zero coeffShift_injective hR₂0 hR0),
      natDegree_oreMul coeffShift_injective hR₂0 hR0, hR, hR₂] at hd
    omega
  obtain ⟨a, β', hβ', hβeq⟩ := exists_pow_mul_map_ne_zero hββ
  obtain ⟨b, S₂', hS₂', hS₂eq⟩ := exists_pow_mul_specialize_ne_zero hS₂0
  obtain ⟨c, R₂', hR₂', hR₂eq⟩ := exists_pow_mul_specialize_ne_zero hR₂0
  obtain ⟨d, R', hR', hReq⟩ := exists_pow_mul_specialize_ne_zero hR0
  have hdS : (specialize S₂').natDegree ≤ 1 := by
    rw [hS₂eq, natDegree_C_mul (C_X_add_one_pow_ne_zero_twfZeroCofactor b)] at hS₂deg
    exact hS₂deg ▸ natDegree_specialize_le_twfZeroCofactor S₂'
  have hdR₂ : (specialize R₂').natDegree ≤ 1 := by
    rw [hR₂eq, natDegree_C_mul (C_X_add_one_pow_ne_zero_twfZeroCofactor c)] at hR₂
    exact hR₂ ▸ natDegree_specialize_le_twfZeroCofactor R₂'
  have hdR : (specialize R').natDegree ≤ 1 := by
    rw [hReq, natDegree_C_mul (C_X_add_one_pow_ne_zero_twfZeroCofactor d)] at hR
    exact hR ▸ natDegree_specialize_le_twfZeroCofactor R'
  have hnorm : C (C ((X + 1 : ℤ[X]) ^ a)) * (C β' * twTransferOp 0) =
      C (C ((X + 1 : ℤ[X]) ^ (b + c + d))) *
        oreMul coeffShift S₂' (oreMul coeffShift R₂' R') := by
    rw [← mul_assoc, ← C_mul, ← hβeq, hkey, hS₂eq, hR₂eq, hReq,
      oreMul_C_C_mul_right_twfZeroCofactor, ← C_mul_oreMul_twfZeroCofactor,
      oreMul_C_C_mul_right_twfZeroCofactor, ← C_mul_oreMul_twfZeroCofactor,
      oreMul_C_C_mul_right_twfZeroCofactor, pow_add, pow_add, C_mul, C_mul, C_mul, C_mul]
    ring
  have hU : specialize (C β' * twTransferOp 0) ≠ 0 := by
    rw [map_mul, specialize_C_twfZeroCofactor]
    exact mul_ne_zero (C_ne_zero.mpr hβ') hP
  have hV : specialize (oreMul coeffShift S₂' (oreMul coeffShift R₂' R')) ≠ 0 := by
    rw [specialize_oreMul, specialize_oreMul]
    exact mul_ne_zero hS₂' (mul_ne_zero hR₂' hR')
  have hfac := eq_of_pow_mul_eq_pow_mul hU hV hnorm
  have hsp : C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize (twTransferOp 0) =
      specialize S₂' * (specialize R₂' * specialize R') := by
    rw [← specialize_oreMul, ← specialize_oreMul, ← hfac, map_mul,
      specialize_C_twfZeroCofactor]
  obtain ⟨κ₁, hκ₁, κ₂, hsymP⟩ := exists_symbol_twfZeroCofactor
  have hsym := symbol_mul_twfZeroCofactor hsymP hsp
  have h1 : toComparison extraFactor ∣ toComparison (C κ₁) *
      (toComparison (specialize S₂') *
        (toComparison (specialize R₂') * toComparison (specialize R'))) := by
    rw [← map_mul, ← map_mul, ← map_mul, hsym]
    exact map_dvd _ ((dvd_mul_left _ _).mul_left _)
  rw [(isUnit_toComparison_coeff_of_ne_zero hκ₁).dvd_mul_left] at h1
  rcases prime_toComparison_extraFactor.dvd_or_dvd h1 with h2 | h2
  · exact not_toComparison_extraFactor_dvd_twfZeroCofactor hS₂' hdS h2
  rcases prime_toComparison_extraFactor.dvd_or_dvd h2 with h3 | h3
  · exact not_toComparison_extraFactor_dvd_twfZeroCofactor hR₂' hdR₂ h3
  · exact not_toComparison_extraFactor_dvd_twfZeroCofactor hR' hdR h3

end AJConjecture
