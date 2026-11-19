import Mathlib
import AJTwist.Quantum.TwQCramerOp

/-!
# Clearing denominators: from `ℚ(t)[J]` to `ℤ[t][J]`

The relation of the finite-rank lemma has coefficients in `ℚ(t)[J]`; the recurrence operators of
the library have coefficients in `ℤ[t][M]`. Every finite family of polynomials over `ℚ(t)`
becomes, after multiplication by one nonzero element of `ℤ[t]`, the image of a family over
`ℤ[t]` under the coefficient map `twTHom : ℤ[t] → ℚ(t)`.

Route: `ℚ(t)` is the fraction field of `ℚ[t]` (`IsFractionRing.div_surjective`) and every
element of `ℚ[t]` is an integer polynomial divided by a nonzero integer
(`IsLocalization.integerNormalization`), as in the private lemmas of
`AJFamily/Quantum/FamTransferRhsRational.lean` (`exists_intPoly_mul_eq_of_ratFunc_fam`) and
`AJConjecture/QAlgNodeFibreClearDenominators.lean`; then induction on the polynomial
(`Polynomial.induction_on'`) and on the size of the family (`Fin.consInduction` or
`Finset` products of the denominators).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Every element of `ℚ(t)` is a quotient of two elements of `ℤ[t]`. -/
theorem twH_exists_twTHom_mul_eq (e : RatFunc ℚ) :
    ∃ a b : ℤ[X], twTHom b ≠ 0 ∧ twTHom b * e = twTHom a := by
  have hφ : twTHom =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [twTHom]
    · simp [twTHom, RatFunc.algebraMap_X]
  obtain ⟨c, hc, hnum⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) e.num
  obtain ⟨d, hd, hden⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) e.denom
  have hc0 : (c : RatFunc ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hc
  have hd0 : (d : RatFunc ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  have hD : algebraMap ℚ[X] (RatFunc ℚ) e.denom ≠ 0 := RatFunc.algebraMap_ne_zero e.denom_ne_zero
  have hp : twTHom (C d * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.num) =
      d * (c * algebraMap ℚ[X] (RatFunc ℚ) e.num) := by
    rw [hφ, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_mul, map_C,
      ← algebraMap_int_eq, hnum, zsmul_eq_mul, map_mul, map_mul, map_intCast]
    simp
  have hq : twTHom (C c * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.denom) =
      c * (d * algebraMap ℚ[X] (RatFunc ℚ) e.denom) := by
    rw [hφ, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_mul, map_C,
      ← algebraMap_int_eq, hden, zsmul_eq_mul, map_mul, map_mul, map_intCast]
    simp
  refine ⟨C d * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.num,
    C c * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.denom, ?_, ?_⟩
  · rw [hq]
    exact mul_ne_zero hc0 (mul_ne_zero hd0 hD)
  · have hquot : ∀ x : RatFunc ℚ,
        x = algebraMap ℚ[X] (RatFunc ℚ) e.num / algebraMap ℚ[X] (RatFunc ℚ) e.denom →
          c * (d * algebraMap ℚ[X] (RatFunc ℚ) e.denom) * x =
            d * (c * algebraMap ℚ[X] (RatFunc ℚ) e.num) := by
      rintro x rfl
      field_simp
    rw [hq, hp]
    exact hquot e (RatFunc.num_div_denom e).symm

/-- A nonzero multiple by an element of `ℤ[t]` of a polynomial over `ℚ(t)` has coefficients in
`ℤ[t]`. -/
theorem twH_exists_map_twTHom_eq (p : (RatFunc ℚ)[X]) :
    ∃ (b : ℤ[X]) (p' : ℤ[X][X]), twTHom b ≠ 0 ∧ p'.map twTHom = C (twTHom b) * p := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨b₁, p₁, h₁, e₁⟩ := hp
    obtain ⟨b₂, p₂, h₂, e₂⟩ := hr
    refine ⟨b₁ * b₂, C b₂ * p₁ + C b₁ * p₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero h₁ h₂
    · rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, e₁, e₂,
        map_mul, C_mul]
      ring
  | monomial k e =>
    obtain ⟨a, b, hb, hab⟩ := twH_exists_twTHom_mul_eq e
    exact ⟨b, monomial k a, hb, by rw [map_monomial, ← hab, C_mul_monomial]⟩

/-- The same for a finite family, with a common multiplier. -/
theorem twH_exists_map_twTHom_eq_family {n : ℕ} (ρ : Fin n → (RatFunc ℚ)[X]) :
    ∃ (b : ℤ[X]) (ρ' : Fin n → ℤ[X][X]), twTHom b ≠ 0 ∧
      ∀ i, (ρ' i).map twTHom = C (twTHom b) * ρ i := by
  choose b p' hb hp using fun i ↦ twH_exists_map_twTHom_eq (ρ i)
  refine ⟨∏ i, b i, fun i ↦ C (∏ k ∈ Finset.univ.erase i, b k) * p' i, ?_, fun i ↦ ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hb i
  · rw [Polynomial.map_mul, map_C, hp, ← mul_assoc, ← C_mul, ← map_mul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

end AJConjecture
