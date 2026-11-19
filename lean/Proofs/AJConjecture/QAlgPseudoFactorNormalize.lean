import Mathlib
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgSpecializeNeZero
import AJConjecture.QAlgSpecializeOreMul

/-!
# Normalisation of a pseudo-factorisation at `t = -1`

In a pseudo-factorisation `β P = S ⋆ R` of an operator `P` with nonzero specialisation, the
powers of `t + 1` can be divided out of `β`, `S` and `R`: `t + 1` is central and invariant under
the shift, `specialize` is multiplicative and `ℤ[M][L]` is a domain, so the valuations add up.
-/

open Polynomial

namespace AJConjecture

/-- `t + 1` is not a unit of `ℤ[t]`. -/
theorem not_isUnit_X_add_one : ¬IsUnit (X + 1 : ℤ[X]) := by
  have hX : (X + 1 : ℤ[X]) = X - C (-1) := by
    rw [map_neg, sub_neg_eq_add, map_one]
  rw [hX]
  exact Polynomial.not_isUnit_X_sub_C _

/-- The powers of `t + 1` are nonzero coefficients. -/
private theorem C_X_add_one_pow_ne_zero_pseudoFactor (a : ℕ) :
    (C ((X + 1 : ℤ[X]) ^ a) : Coeff) ≠ 0 :=
  Polynomial.C_ne_zero.mpr (pow_ne_zero _ (Polynomial.X_add_C_ne_zero (1 : ℤ)))

/-- The powers of `t + 1` are nonzero constants of the algebra of recurrence operators. -/
private theorem C_C_X_add_one_pow_ne_zero_pseudoFactor (a : ℕ) :
    (C (C ((X + 1 : ℤ[X]) ^ a)) : RecOp) ≠ 0 :=
  Polynomial.C_ne_zero.mpr (C_X_add_one_pow_ne_zero_pseudoFactor a)

/-- The specialisation at `t = -1` kills the powers `(t + 1) ^ (d + 1)`. -/
theorem specialize_C_C_X_add_one_pow_succ (d : ℕ) :
    specialize (C (C ((X + 1 : ℤ[X]) ^ (d + 1)))) = 0 := by
  simp [specialize]

/-- A nonzero operator is a power of `t + 1` times an operator with nonzero specialisation. -/
theorem exists_pow_mul_specialize_ne_zero {T : RecOp} (hT : T ≠ 0) :
    ∃ (b : ℕ) (T' : RecOp), specialize T' ≠ 0 ∧ T = C (C ((X + 1 : ℤ[X]) ^ b)) * T' := by
  have hu : ¬IsUnit (C (C (X + 1 : ℤ[X])) : RecOp) := by
    rw [Polynomial.isUnit_C, Polynomial.isUnit_C]
    exact not_isUnit_X_add_one
  obtain ⟨n, a, hna, h⟩ := WfDvdMonoid.max_power_factor' (α := RecOp) hT hu
  exact ⟨n, a, fun h0 ↦ hna ((specialize_eq_zero_iff_dvd a).mp h0), by rw [h, C_pow, C_pow]⟩

/-- A nonzero coefficient is a power of `t + 1` times a coefficient not vanishing at
`t = -1`. -/
theorem exists_pow_mul_map_ne_zero {β : Coeff} (hβ : β ≠ 0) :
    ∃ (a : ℕ) (β' : Coeff), β'.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      β = C ((X + 1 : ℤ[X]) ^ a) * β' := by
  have hu : ¬IsUnit (C (X + 1 : ℤ[X]) : Coeff) := by
    rw [Polynomial.isUnit_C]
    exact not_isUnit_X_add_one
  obtain ⟨n, β', hna, h⟩ := WfDvdMonoid.max_power_factor' (α := Coeff) hβ hu
  refine ⟨n, β', fun h0 ↦ hna ?_, by rw [h, C_pow]⟩
  have h1 : specialize (C β') = 0 := by
    simp only [specialize, coe_mapRingHom, Polynomial.map_C, h0, map_zero]
  have h2 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp ((specialize_eq_zero_iff_dvd _).mp h1) 0
  rwa [Polynomial.coeff_C_zero] at h2

/-- Powers of `t + 1` cancel between operators with nonzero specialisation (ordered case). -/
theorem eq_of_pow_mul_eq_pow_mul_of_le {a b : ℕ} (hab : a ≤ b)
    {U V : RecOp} (hU : specialize U ≠ 0)
    (h : C (C ((X + 1 : ℤ[X]) ^ a)) * U = C (C ((X + 1 : ℤ[X]) ^ b)) * V) : U = V := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, C_mul, C_mul, mul_assoc] at h
  have hUV : U = C (C ((X + 1 : ℤ[X]) ^ d)) * V :=
    mul_left_cancel₀ (C_C_X_add_one_pow_ne_zero_pseudoFactor a) h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [hUV, pow_zero, C_1, C_1, one_mul]
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    exact absurd (by rw [hUV, map_mul, specialize_C_C_X_add_one_pow_succ,
      zero_mul]) hU

/-- Powers of `t + 1` cancel between operators with nonzero specialisation. -/
theorem eq_of_pow_mul_eq_pow_mul {a b : ℕ} {U V : RecOp}
    (hU : specialize U ≠ 0) (hV : specialize V ≠ 0)
    (h : C (C ((X + 1 : ℤ[X]) ^ a)) * U = C (C ((X + 1 : ℤ[X]) ^ b)) * V) : U = V := by
  rcases le_total a b with hab | hab
  · exact eq_of_pow_mul_eq_pow_mul_of_le hab hU h
  · exact (eq_of_pow_mul_eq_pow_mul_of_le hab hV h.symm).symm

/-- The iterated shift fixes the coefficients that are polynomials in `t` alone. -/
private theorem iterate_coeffShift_C_pseudoFactor (i : ℕ) (r : ℤ[X]) :
    coeffShift^[i] (C r) = C r := by
  have hfix : coeffShift (C r) = C r := by
    have hcomp : coeffShift (C r) = (C r : Coeff).comp (C (X ^ 2) * X : Coeff) := rfl
    rw [hcomp, Polynomial.C_comp]
  exact Function.iterate_fixed hfix i

/-- A polynomial in `t` alone is central for the Ore product: it moves out of the right
factor. -/
private theorem oreMul_C_C_mul_right_pseudoFactor (r : ℤ[X]) (S R : RecOp) :
    oreMul coeffShift S (C (C r) * R) = C (C r) * oreMul coeffShift S R := by
  induction S using Polynomial.induction_on' with
  | add p p' hp hp' => rw [oreMul_add_left, oreMul_add_left, hp, hp', mul_add]
  | monomial i a =>
    induction R using Polynomial.induction_on' with
    | add q q' hq hq' => rw [mul_add, oreMul_add_right, oreMul_add_right, hq, hq', mul_add]
    | monomial k b =>
      rw [Polynomial.C_mul_monomial, oreMul_monomial_monomial, oreMul_monomial_monomial,
        Polynomial.C_mul_monomial, iterate_map_mul, iterate_coeffShift_C_pseudoFactor,
        mul_left_comm]

/-- A pseudo-factorisation of an operator with nonzero specialisation can be normalised so that
the constant and both factors have nonzero specialisation, without changing the degrees. -/
theorem exists_normalized_pseudoFactor {P : RecOp} (hP : specialize P ≠ 0) {β : Coeff}
    (hβ : β ≠ 0) {S R : RecOp} (h : C β * P = oreMul coeffShift S R) :
    ∃ (β' : Coeff) (S' R' : RecOp), β'.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      specialize S' ≠ 0 ∧ specialize R' ≠ 0 ∧ S'.natDegree = S.natDegree ∧
      R'.natDegree = R.natDegree ∧ C β' * P = oreMul coeffShift S' R' ∧
      ∃ a : ℕ, R = C (C ((X + 1 : ℤ[X]) ^ a)) * R' := by
  have hP0 : P ≠ 0 := fun h0 ↦ hP (by rw [h0, map_zero])
  have hne : oreMul coeffShift S R ≠ 0 := h ▸ mul_ne_zero (Polynomial.C_ne_zero.mpr hβ) hP0
  have hS : S ≠ 0 := by
    rintro rfl
    exact hne (by rw [← Polynomial.C_0, oreMul_C_left, Polynomial.C_0, zero_mul])
  have hR : R ≠ 0 := by
    rintro rfl
    have hz := oreMul_C_C_mul_right_pseudoFactor 0 S 0
    rw [mul_zero, Polynomial.C_0, Polynomial.C_0, zero_mul] at hz
    exact hne hz
  obtain ⟨a, β', hβ', rfl⟩ := exists_pow_mul_map_ne_zero hβ
  obtain ⟨b, S', hS', rfl⟩ := exists_pow_mul_specialize_ne_zero hS
  obtain ⟨c, R', hR', rfl⟩ := exists_pow_mul_specialize_ne_zero hR
  have hC : C (C ((X + 1 : ℤ[X]) ^ b)) * S' =
      oreMul coeffShift (C (C ((X + 1 : ℤ[X]) ^ b))) S' := (oreMul_C_left _ _ _).symm
  rw [hC, oreMul_assoc, oreMul_C_left, oreMul_C_C_mul_right_pseudoFactor, C_mul, mul_assoc,
    ← mul_assoc (C (C ((X + 1 : ℤ[X]) ^ b))), ← C_mul, ← C_mul, ← pow_add] at h
  have hU : specialize (C β' * P) ≠ 0 := by
    have hsU : specialize (C β' * P) = C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) *
        specialize P := by
      rw [map_mul]
      simp only [specialize, coe_mapRingHom, Polynomial.map_C]
    rw [hsU]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβ') hP
  have hV : specialize (oreMul coeffShift S' R') ≠ 0 := by
    rw [specialize_oreMul]
    exact mul_ne_zero hS' hR'
  have hdS : S'.natDegree = (C (C ((X + 1 : ℤ[X]) ^ b)) * S').natDegree :=
    (Polynomial.natDegree_C_mul (C_X_add_one_pow_ne_zero_pseudoFactor b)).symm
  have hdR : R'.natDegree = (C (C ((X + 1 : ℤ[X]) ^ c)) * R').natDegree :=
    (Polynomial.natDegree_C_mul (C_X_add_one_pow_ne_zero_pseudoFactor c)).symm
  exact ⟨β', S', R', hβ', hS', hR', hdS, hdR,
    eq_of_pow_mul_eq_pow_mul hU hV h, c, rfl⟩

end AJConjecture
