import Mathlib

/-!
# The content at `M = m₀` of a polynomial of `k[M][L]`

Let `μ = M - m₀`. A nonzero `F ∈ k[M][L]` is `μ^a F*` with `F*` of nonzero fibre at `M = m₀`
(the fibre is `F.map (evalRingHom m₀) ∈ k[L]`), and this decomposition is unique.

Proofs. Existence: induction on the degree of the leading coefficient of `F`; if the fibre of
`F` is zero every coefficient is divisible by `μ` (`Polynomial.dvd_iff_isRoot`), so
`F = C μ * F'` and the leading coefficient of `F'` has smaller degree. Comparison: `C μ` is not a
zero divisor and the fibre of `C (μ^c) * A` is zero for `c > 0`.
-/

open Polynomial

namespace AJConjecture

/-- A polynomial whose fibre at `M = m₀` vanishes is divisible by `M - m₀`. -/
theorem exists_eq_C_mul_of {k : Type*} [Field k] {m₀ : k}
    {p : k[X][X]} (h : p.map (Polynomial.evalRingHom m₀) = 0) :
    ∃ q : k[X][X], p = C (X - C m₀) * q := by
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ ?_
  rw [Polynomial.dvd_iff_isRoot, IsRoot.def]
  have hi := congrArg (fun q ↦ q.coeff i) h
  simpa only [coeff_map, coe_evalRingHom, coeff_zero] using hi

/-- The splitting of the content, by induction on the degree of the leading coefficient. -/
private theorem exists_eq_C_pow_mul_of_natDegree_leadingCoeff_contentSplit {k : Type*} [Field k]
    (m₀ : k) (n : ℕ) :
    ∀ F : k[X][X], F ≠ 0 → F.leadingCoeff.natDegree = n →
      ∃ (a : ℕ) (Fs : k[X][X]),
        F = C ((X - C m₀) ^ a) * Fs ∧ Fs.map (Polynomial.evalRingHom m₀) ≠ 0 := by
  induction n with
  | zero =>
    intro F hF hn
    refine ⟨0, F, by rw [pow_zero, C_1, one_mul], fun h0 ↦ ?_⟩
    obtain ⟨q, rfl⟩ := exists_eq_C_mul_of h0
    have hq : q ≠ 0 := right_ne_zero_of_mul hF
    rw [leadingCoeff_mul, leadingCoeff_C,
      natDegree_mul (X_sub_C_ne_zero m₀) (leadingCoeff_ne_zero.mpr hq), natDegree_X_sub_C] at hn
    omega
  | succ n ih =>
    intro F hF hn
    by_cases h0 : F.map (Polynomial.evalRingHom m₀) = 0
    · obtain ⟨q, rfl⟩ := exists_eq_C_mul_of h0
      have hq : q ≠ 0 := right_ne_zero_of_mul hF
      rw [leadingCoeff_mul, leadingCoeff_C,
        natDegree_mul (X_sub_C_ne_zero m₀) (leadingCoeff_ne_zero.mpr hq), natDegree_X_sub_C] at hn
      obtain ⟨a, Fs, rfl, hFs⟩ := ih q hq (by omega)
      exact ⟨a + 1, Fs, by rw [pow_succ', C_mul, mul_assoc], hFs⟩
    · exact ⟨0, F, by rw [pow_zero, C_1, one_mul], h0⟩

/-- A nonzero polynomial of `k[M][L]` is a power of `M - m₀` times a polynomial whose fibre at
`M = m₀` is not zero. -/
theorem exists_eq_C_pow_mul_fibre_ne_zero {k : Type*} [Field k] (m₀ : k) {F : k[X][X]}
    (hF : F ≠ 0) :
    ∃ (a : ℕ) (Fs : k[X][X]),
      F = C ((X - C m₀) ^ a) * Fs ∧ Fs.map (Polynomial.evalRingHom m₀) ≠ 0 :=
  exists_eq_C_pow_mul_of_natDegree_leadingCoeff_contentSplit m₀ _ F hF rfl

/-- If `μ^a A = μ^b B` and the fibre of `B` at `m₀` is not zero, then `a ≤ b` and
`A = μ^(b - a) B`. -/
theorem eq_C_pow_mul_of_C_pow_mul_eq {k : Type*} [Field k] {m₀ : k} {a b : ℕ} {A B : k[X][X]}
    (h : C ((X - C m₀) ^ a) * A = C ((X - C m₀) ^ b) * B)
    (hB : B.map (Polynomial.evalRingHom m₀) ≠ 0) :
    a ≤ b ∧ A = C ((X - C m₀) ^ (b - a)) * B := by
  have hμ : ∀ n : ℕ, (C ((X - C m₀) ^ n) : k[X][X]) ≠ 0 := fun n ↦
    C_ne_zero.mpr (pow_ne_zero n (X_sub_C_ne_zero m₀))
  by_cases hab : a ≤ b
  · refine ⟨hab, ?_⟩
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [Nat.add_sub_cancel_left]
    apply mul_left_cancel₀ (hμ a)
    rw [h, pow_add, C_mul, mul_assoc]
  · exfalso
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_not_le hab)
    have hBA : B = C ((X - C m₀) ^ (c + 1)) * A := by
      apply mul_left_cancel₀ (hμ b)
      rw [← h, ← mul_assoc, ← C_mul, ← pow_add, add_assoc]
    apply hB
    rw [hBA, Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom, eval_pow, eval_sub, eval_X,
      eval_C, sub_self, zero_pow (Nat.succ_ne_zero c), C_0, zero_mul]

end AJConjecture
