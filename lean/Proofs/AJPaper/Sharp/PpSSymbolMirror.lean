import Mathlib
import AJTwist.Classical.TwCReverse
import AJPaper.Sharp.PpSSymbol
import AJPaper.Sharp.PpSTwPInvNeg

/-!
# The mirrored symbol `(L - 1) E^∨ 𝒫_a^rev` (Unit PpS, node `PpS_SymbolMirror`)

Source: Section 8.2 and 8.4 of the paper (`conclusion.tex`): for the positive clasp the
quantum factor is the meridian inversion `((L - 1) E 𝒫_a)(M⁻¹, L)` of the symbol of the mirror
knot. The library writes the classical bound of the positive clasp with `L` inverted
(`(twBound ℓ (-a)).reverse`, `AJTwist.Main.TwMTheorem`). The two forms agree up to units of
`R = ℚ(M)[L, L⁻¹]`:

* `pps_twP_mInv_associated`: `𝒫_k(M⁻¹, L) ≐ 𝒫_k.reverse = L^deg 𝒫_k(M, L⁻¹)`
  (`pps_twistPoly_inv`, `pps_twistPolyNeg_inv`, `toComparison_reverse`);
* `pps_extraFactor_mInv_associated`: `E(M⁻¹, L) ≐ E^∨` (`twmMReflect_extraFactor`,
  `toComparison_twmMReflect`);
* `ppsSymbolMirror a = (L - 1) E^∨ 𝒫_a.reverse`, and
  `pps_symbol_mInv_associated`: `((L - 1) E 𝒫_a)(M⁻¹, L) ≐ ppsSymbolMirror a`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The mirrored symbol `(L - 1) E^∨ 𝒫_a^rev`, where `𝒫_a^rev = L^deg 𝒫_a(M, L⁻¹)`: up to a
unit of `ℚ(M)[L, L⁻¹]` it is `((L - 1) E 𝒫_a)(M⁻¹, L)` (`pps_symbol_mInv_associated`). -/
def ppsSymbolMirror (a : ℤ) : ℤ[X][X] :=
  (X - 1) * extraFactorMirror * (twP a).reverse

/-- A polynomial with `P(M, L) = c L^n P(M⁻¹, L⁻¹)` in the comparison ring, `c ≠ 0`: its
meridian inversion is associated to its reverse in `L`. -/
private theorem mInv_associated_reverse_ppsSymbolMirror {P : ℤ[X][X]} {c : RatFunc ℚ}
    (hc : c ≠ 0) {n : ℤ}
    (h : toComparison P = LaurentPolynomial.C c * LaurentPolynomial.T n *
      LaurentPolynomial.invert (ppsMInv (toComparison P))) :
    Associated (ppsMInv (toComparison P)) (toComparison P.reverse) := by
  have h' := congrArg LaurentPolynomial.invert h
  rw [map_mul, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
    LaurentPolynomial.involutive_invert (ppsMInv (toComparison P))] at h'
  have hu : IsUnit (LaurentPolynomial.C c * LaurentPolynomial.T (-n) *
      LaurentPolynomial.T (P.natDegree : ℤ) : ComparisonRing) :=
    ((((IsUnit.mk0 c hc).map LaurentPolynomial.C).mul (LaurentPolynomial.isUnit_T _)).mul
      (LaurentPolynomial.isUnit_T _))
  have he : toComparison P.reverse = LaurentPolynomial.C c * LaurentPolynomial.T (-n) *
      LaurentPolynomial.T (P.natDegree : ℤ) * ppsMInv (toComparison P) := by
    rw [toComparison_reverse, h']
    ring
  rw [he, associated_isUnit_mul_right_iff hu]
  exact Associated.refl _

/-- The reverse of the constant polynomial `1` is `1`. -/
private theorem reverse_one_ppsSymbolMirror : (1 : ℤ[X][X]).reverse = 1 := by
  rw [← C_1, reverse_C]

/-- The reverse of `L - 1` is `1 - L`. -/
private theorem reverse_X_sub_one_ppsSymbolMirror : (X - 1 : ℤ[X][X]).reverse = 1 - X := by
  have h : (X - 1 : ℤ[X][X]) = X + C (-1) := by
    rw [map_neg, map_one, sub_eq_add_neg]
  have hX : (X : ℤ[X][X]).reverse = 1 := by
    have h1 := reverse_mul_X (1 : ℤ[X][X])
    rwa [one_mul, reverse_one_ppsSymbolMirror] at h1
  rw [h, reverse_add_C, natDegree_X, hX, map_neg, map_one]
  ring

/-- `E^∨` and `L - 1` are coprime in the comparison ring. -/
private theorem isCoprime_extraFactorMirror_sub_one_ppsSymbolMirror :
    IsCoprime (toComparison extraFactorMirror) (toComparison (X - 1)) := by
  have hc := isCoprime_extraFactorMirror_twBound_reverse 0 0
  rw [twBound, twP_zero, mul_one, mul_one, reverse_X_sub_one_ppsSymbolMirror,
    show (1 - X : ℤ[X][X]) = -(X - 1) by ring, map_neg] at hc
  exact (IsCoprime.neg_right_iff _ _).mp hc

/-- `𝒫_k(M⁻¹, L)` is the reverse of `𝒫_k` in `L`, up to a unit of `ℚ(M)[L, L⁻¹]`. -/
theorem pps_twP_mInv_associated (k : ℤ) :
    Associated (ppsMInv (toComparison (twP k))) (toComparison (twP k).reverse) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    rw [twP_natCast]
    exact mInv_associated_reverse_ppsSymbolMirror (pow_ne_zero _ hX) (pps_twistPoly_inv m)
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, k = -(b : ℤ) := ⟨(-k).toNat, by omega⟩
    have hb : 1 ≤ b := by omega
    rw [twP_neg_natCast b hb]
    exact mInv_associated_reverse_ppsSymbolMirror (pow_ne_zero _ hX)
      (pps_twistPolyNeg_inv b hb)

/-- `E(M⁻¹, L)` is `E^∨` up to a unit of `ℚ(M)[L, L⁻¹]`. -/
theorem pps_extraFactor_mInv_associated :
    Associated (ppsMInv (toComparison extraFactor)) (toComparison extraFactorMirror) := by
  have h := toComparison_twmMReflect 4 extraFactor natDegree_coeff_extraFactor_le
  have hu : IsUnit (LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ 4) : ComparisonRing) :=
    (IsUnit.mk0 _ (pow_ne_zero 4 RatFunc.X_ne_zero)).map LaurentPolynomial.C
  rw [twmMReflect_extraFactor] at h
  rw [h, associated_isUnit_mul_right_iff hu]
  exact Associated.refl _

/-- The meridian inversion of the symbol `(L - 1) E 𝒫_a` is the mirrored symbol
`(L - 1) E^∨ 𝒫_a^rev`, up to a unit of `ℚ(M)[L, L⁻¹]`. -/
theorem pps_symbol_mInv_associated (a : ℤ) :
    Associated (ppsMInv (toComparison (ppsSymbol a))) (toComparison (ppsSymbolMirror a)) := by
  have h1 : ppsMInv (toComparison (X - 1)) = toComparison (X - 1) := by
    have hX : toComparison X = LaurentPolynomial.T 1 := by simp [toComparison]
    rw [map_sub, map_one, hX, map_sub, map_one, ppsMInv_T]
  rw [ppsSymbol, ppsSymbolMirror]
  simp only [map_mul]
  rw [h1]
  exact ((Associated.refl _).mul_mul pps_extraFactor_mInv_associated).mul_mul
    (pps_twP_mInv_associated a)

/-- At index `0` the mirrored symbol `(L - 1) E^∨` divides every element of `ℚ(M)[L, L⁻¹]`
divisible by `L - 1` and by `E^∨`. -/
theorem pps_symbolMirror_zero_dvd {F : ComparisonRing} (h1 : toComparison (X - 1) ∣ F)
    (hE : toComparison extraFactorMirror ∣ F) : toComparison (ppsSymbolMirror 0) ∣ F := by
  rw [ppsSymbolMirror, twP_zero, reverse_one_ppsSymbolMirror, mul_one, map_mul]
  exact isCoprime_extraFactorMirror_sub_one_ppsSymbolMirror.symm.mul_dvd h1 hE

end AJConjecture
