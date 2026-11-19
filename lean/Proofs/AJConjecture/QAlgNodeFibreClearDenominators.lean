import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# Divisibility in the comparison ring, with denominators cleared

If `toComparison G ∣ toComparison F` in `ℚ(M)[L, L⁻¹]` then `c L^n F = G Q` in `ℤ[M][L]` for
some nonzero `c ∈ ℤ[M]`, `n ∈ ℕ` and `Q ∈ ℤ[M][L]`.

Proof. Let `toComparison F = toComparison G * q`. Write `q = T^(-n) toLaurent q'` with
`q' ∈ ℚ(M)[L]` (`LaurentPolynomial.exists_T_pow`), and clear the denominators of the finitely
many coefficients of `q'`: there are `c ∈ ℤ[M]`, `c ≠ 0`, and `Q ∈ ℤ[M][L]` with `c q'` the
image of `Q` (`IsLocalization.integerNormalization` for `ℚ[M] → ℚ(M)`, then the integer
denominators of the coefficients of `ℚ[M]`; or `IsFractionRing` for the composite, which is the
fraction map of `ℤ[M]` into `ℚ(M)`). Then `toComparison (C c * X^n * F) = toComparison (G * Q)`
and `toComparison` is injective (`Polynomial.toLaurent_injective`, `Polynomial.map_injective`,
`IsFractionRing.injective`, `Int.cast_injective`).
-/

open Polynomial

namespace AJConjecture

/-- The coefficient map `ℤ[M] → ℚ(M)` of `toComparison`. -/
private noncomputable def comparisonCoeffHom : ℤ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- `toComparison` is the base change along the coefficient map followed by `toLaurent`. -/
private theorem toComparison_eq_toLaurent_map_clearDenominators (p : ℤ[X][X]) :
    toComparison p = Polynomial.toLaurent (p.map comparisonCoeffHom) :=
  rfl

/-- The coefficient map `ℤ[M] → ℚ(M)` is injective. -/
private theorem comparisonCoeffHom_injective : Function.Injective comparisonCoeffHom :=
  (RatFunc.algebraMap_injective ℚ).comp
    (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)

/-- `toComparison` is injective. -/
private theorem toComparison_injective_clearDenominators : Function.Injective toComparison :=
  Polynomial.toLaurent_injective.comp
    (Polynomial.map_injective comparisonCoeffHom comparisonCoeffHom_injective)

/-- A nonzero integer multiple of a polynomial of `ℚ[M]` has integer coefficients. -/
private theorem exists_intCast_mul_eq_map_clearDenominators (p : ℚ[X]) :
    ∃ (b : ℤ) (p' : ℤ[X]), b ≠ 0 ∧ p'.map (Int.castRingHom ℚ) = C (b : ℚ) * p := by
  obtain ⟨b, hb, hp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  refine ⟨b, IsLocalization.integerNormalization (nonZeroDivisors ℤ) p,
    nonZeroDivisors.ne_zero hb, ?_⟩
  rw [algebraMap_int_eq] at hp
  rw [hp, zsmul_eq_mul, ← map_intCast (C : ℚ →+* ℚ[X])]

/-- A nonzero multiple by an element of `ℤ[M]` of an element of `ℚ(M)` lies in `ℤ[M]`. -/
private theorem exists_comparisonCoeffHom_eq_mul_clearDenominators (r : RatFunc ℚ) :
    ∃ c d : ℤ[X], c ≠ 0 ∧ comparisonCoeffHom d = comparisonCoeffHom c * r := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective ℚ[X] r
  obtain ⟨b₁, x', hb₁, hx'⟩ := exists_intCast_mul_eq_map_clearDenominators x
  obtain ⟨b₂, y', hb₂, hy'⟩ := exists_intCast_mul_eq_map_clearDenominators y
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hαy : algebraMap ℚ[X] (RatFunc ℚ) y ≠ 0 := fun h0 ↦
    hy0 ((map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp h0)
  refine ⟨C b₁ * y', C b₂ * x', mul_ne_zero (C_ne_zero.mpr hb₁) fun h0 ↦ ?_, ?_⟩
  · rw [h0, Polynomial.map_zero] at hy'
    exact mul_ne_zero (C_ne_zero.mpr (Int.cast_ne_zero.mpr hb₂)) hy0 hy'.symm
  · have hcomp : ∀ p : ℤ[X], comparisonCoeffHom p =
        algebraMap ℚ[X] (RatFunc ℚ) (p.map (Int.castRingHom ℚ)) := fun _ ↦ rfl
    rw [hcomp, hcomp, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      hx', hy', map_mul, map_mul, map_mul, map_mul, eq_intCast, eq_intCast]
    field_simp

/-- A nonzero multiple by an element of `ℤ[M]` of a polynomial over `ℚ(M)` comes from
`ℤ[M][L]`. -/
private theorem exists_map_comparisonCoeffHom_eq_mul_clearDenominators (q : (RatFunc ℚ)[X]) :
    ∃ (c : ℤ[X]) (Q : ℤ[X][X]), c ≠ 0 ∧
      Q.map comparisonCoeffHom = C (comparisonCoeffHom c) * q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨c₁, Q₁, hc₁, hQ₁⟩ := hp
    obtain ⟨c₂, Q₂, hc₂, hQ₂⟩ := hq
    refine ⟨c₁ * c₂, C c₂ * Q₁ + C c₁ * Q₂, mul_ne_zero hc₁ hc₂, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_C, hQ₁, hQ₂, map_mul, C_mul]
    ring
  | monomial n r =>
    obtain ⟨c, d, hc, hd⟩ := exists_comparisonCoeffHom_eq_mul_clearDenominators r
    refine ⟨c, monomial n d, hc, ?_⟩
    rw [Polynomial.map_monomial, hd, C_mul_monomial]

/-- Divisibility in the comparison ring is divisibility in `ℤ[M][L]` up to a nonzero element
of `ℤ[M]` and a power of `L`. -/
theorem exists_C_mul_X_pow_mul_eq_of_toComparison_dvd {G F : ℤ[X][X]}
    (h : toComparison G ∣ toComparison F) :
    ∃ (c : ℤ[X]) (n : ℕ) (Q : ℤ[X][X]), c ≠ 0 ∧ C c * X ^ n * F = G * Q := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨n, q', hq'⟩ := LaurentPolynomial.exists_T_pow q
  obtain ⟨c, Q, hc, hQ⟩ := exists_map_comparisonCoeffHom_eq_mul_clearDenominators q'
  refine ⟨c, n, Q, hc, toComparison_injective_clearDenominators ?_⟩
  have hQ' : toComparison Q = toComparison (C c) * (q * LaurentPolynomial.T n) := by
    rw [toComparison_eq_toLaurent_map_clearDenominators,
      toComparison_eq_toLaurent_map_clearDenominators, hQ, map_mul, hq', Polynomial.map_C]
  have hX : toComparison (X ^ n) = LaurentPolynomial.T n := by
    rw [toComparison_eq_toLaurent_map_clearDenominators, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.toLaurent_X_pow]
  rw [map_mul, map_mul, map_mul, hQ', hX, hq]
  ring

end AJConjecture
