import Mathlib
import AJHandoff.TorusKnot.PairKReverse
import AJHandoff.TorusKnot.PairKTheoremT
import AJFamily.Classical.FamilyPoint

/-!
# The refutation does not depend on the chirality pairing of the two sides

The weak AJ identity compares the classical limit of the recurrence polynomial of a knot with
its A-polynomial, both in the variables `(M, L)`. Passing to the mirror image of the knot on one
side only replaces `L` by `L⁻¹` on that side (equivalently `M` by `M⁻¹`, since the eigenvalue set
is invariant under `(M, L) ↦ (M⁻¹, L⁻¹)`). The extra factor `E = L² - (M⁴ - 4M² + 1) L + M⁴` is not
invariant under `L ↦ L⁻¹`: its image is, up to the unit `L²`, the *mirror factor*
`E' = M⁴ L² - (M⁴ - 4M² + 1) L + 1`. So if the conventions of the two sides of the formal statement
were mirror to each other, the true comparison would be between `E` and the A-polynomial with `L`
inverted, that is between `E'` and the A-polynomial as it stands.

This file proves that `E'` too is coprime to the classical bound `(L - 1) B_m` for every `m ≥ 1`,
hence to every A-polynomial of the doubles `Wh⁻₀(T(r, s))`, and that the weak AJ identity fails
for these knots also when the A-polynomial is replaced by its mirror
(`not_ajSquareFree_mirror_pair`). The refutation is therefore independent of how the chirality
conventions of the coloured Jones side and of the peripheral side are paired.

The witness point for `E'` is `M² = 6`, `L = 1/4`: there `B_m < 0` for every `m ≥ 1`
(`P = 15/4`, `Q = 25/4`, `k = 1875/8`, `τ = 18225/16 ≥ 2k`, `A = -425/2`; the sequence
`Ŝ_m` is positive and `Ŝ_{m+1} ≥ (τ/2) Ŝ_m`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The mirror of the extra factor: `E'(M, L) = M⁴ L² - (M⁴ - 4M² + 1) L + 1`, which is
`L² E(M, L⁻¹) = M⁴ E(M⁻¹, L)`. -/
def extraFactorMirror : ℤ[X][X] :=
  C (X ^ 4) * X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + 1

/-- `E'` is the image of `E` under `L ↦ L⁻¹`, up to the unit `L²`. -/
theorem toComparison_extraFactorMirror :
    toComparison extraFactorMirror =
      LaurentPolynomial.T 2 * LaurentPolynomial.invert (toComparison extraFactor) := by
  simp only [toComparison, extraFactor, extraFactorMirror, RingHom.comp_apply, coe_mapRingHom,
    Polynomial.map_C, Polynomial.map_X, map_add, map_sub, map_mul, map_pow,
    map_one, toLaurent_C, toLaurent_X, LaurentPolynomial.invert_T, LaurentPolynomial.invert_C,
    LaurentPolynomial.T_pow]
  rw [mul_add, mul_sub, mul_left_comm (LaurentPolynomial.T 2), ← LaurentPolynomial.T_add,
    ← LaurentPolynomial.T_add]
  norm_num
  ring

/-- Positivity and growth of the homogenised Chebyshev sequence at the mirror witness:
`Ŝ_n ≥ 0`, `Ŝ_{n+1} > 0` and `Ŝ_{n+1} ≥ (τ/2) Ŝ_n` for `τ = 18225/16`, `k = 1875/8`. -/
private theorem homCheb_pos_growth_mirror (n : ℕ) :
    0 ≤ homCheb (18225 / 16 : ℝ) (1875 / 8) n ∧
      0 < homCheb (18225 / 16 : ℝ) (1875 / 8) (n + 1) ∧
      18225 / 32 * homCheb (18225 / 16 : ℝ) (1875 / 8) n ≤
        homCheb (18225 / 16 : ℝ) (1875 / 8) (n + 1) := by
  induction n with
  | zero => simp [homCheb]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hrec : homCheb (18225 / 16 : ℝ) (1875 / 8) (n + 2) =
        18225 / 16 * homCheb (18225 / 16 : ℝ) (1875 / 8) (n + 1) -
          (1875 / 8) ^ 2 * homCheb (18225 / 16 : ℝ) (1875 / 8) n := rfl
    have hstep : 18225 / 32 * homCheb (18225 / 16 : ℝ) (1875 / 8) (n + 1) ≤
        homCheb (18225 / 16 : ℝ) (1875 / 8) (n + 2) := by
      rw [hrec]
      linarith
    exact ⟨h1.le, by linarith, hstep⟩

/-- The value of `B_{n+1}` at the mirror witness `(c, 1/4)`, `c² = 6`, is a real number. -/
private theorem evalPoint_famB_witness_mirror (c : ℂ) (hc : c ^ 2 = 6) (n : ℕ) :
    evalPoint (mapC (famB (n + 1))) (c, 1 / 4) =
      ((-425 / 2 * homCheb (18225 / 16 : ℝ) (1875 / 8) (n + 1) -
        (1875 / 8) ^ 2 * homCheb (18225 / 16 : ℝ) (1875 / 8) n : ℝ) : ℂ) := by
  have h4 : c ^ 4 = 36 := by
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]
    norm_num
  have hK : evalPoint (mapC famK) (c, 1 / 4) = ((1875 / 8 : ℝ) : ℂ) := by
    rw [evalPoint_famK, hc]
    push_cast
    norm_num
  have hT : evalPoint (mapC famTau) (c, 1 / 4) = ((18225 / 16 : ℝ) : ℂ) := by
    rw [evalPoint_famTau]
    simp only [hc, h4]
    push_cast
    norm_num
  have hA : evalPoint (mapC famA) (c, 1 / 4) = ((-425 / 2 : ℝ) : ℂ) := by
    rw [evalPoint_famA]
    simp only [hc, h4]
    push_cast
    norm_num
  have hS : ∀ j : ℕ, homCheb ((18225 / 16 : ℝ) : ℂ) ((1875 / 8 : ℝ) : ℂ) j =
      ((homCheb (18225 / 16 : ℝ) (1875 / 8) j : ℝ) : ℂ) :=
    fun j ↦ (map_homCheb Complex.ofRealHom _ _ j).symm
  rw [evalPoint_famB, hK, hT, hA, Nat.add_sub_cancel, hS, hS]
  push_cast
  ring

/-- The bound `(L - 1) B_m` does not vanish at the mirror witness `(c, 1/4)`, `c² = 6`. -/
private theorem evalPoint_famBound_witness_ne_zero_mirror (c : ℂ) (hc : c ^ 2 = 6) {m : ℕ}
    (hm : 0 < m) : evalPoint (mapC (famBound m)) (c, 1 / 4) ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hmul : evalPoint (mapC (famBound (n + 1))) (c, 1 / 4) =
      (1 / 4 - 1) * evalPoint (mapC (famB (n + 1))) (c, 1 / 4) := by
    simp only [mapC, evalPoint, famBound, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one]
  rw [hmul, evalPoint_famB_witness_mirror c hc]
  refine mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_lt ?_))
  obtain ⟨h0, h1, -⟩ := homCheb_pos_growth_mirror n
  nlinarith

/-- The mirror factor vanishes at the mirror witness `(c, 1/4)`, `c² = 6`. -/
private theorem evalPoint_extraFactorMirror_witness_mirror (c : ℂ) (hc : c ^ 2 = 6) :
    evalPoint (mapC extraFactorMirror) (c, 1 / 4) = 0 := by
  have h4 : c ^ 4 = 36 := by
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]
    norm_num
  simp only [mapC, evalPoint, extraFactorMirror, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_ofNat, eval₂_add, eval₂_sub,
    eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_one, Polynomial.coe_evalRingHom, eval_add,
    eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_ofNat, hc, h4]
  norm_num

/-- The extra factor vanishes at the inverted witness `(c, 4)`, `c² = 6`. -/
private theorem evalPoint_extraFactor_witness_mirror (c : ℂ) (hc : c ^ 2 = 6) :
    evalPoint (mapC extraFactor) (c, 4) = 0 := by
  have h4 : c ^ 4 = 36 := by
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]
    norm_num
  simp only [mapC, evalPoint, extraFactor, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_ofNat, eval₂_add, eval₂_sub,
    eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, Polynomial.coe_evalRingHom, eval_add,
    eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_ofNat, hc, h4]
  norm_num

/-- Some zero of the mirror factor `E'` is not a zero of the bound `(L - 1) B_m`. -/
theorem exists_extraFactorMirror_zero_not_famBound_zero {m : ℕ} (hm : 0 < m) :
    ∃ p : ℂ × ℂ, evalPoint (mapC extraFactorMirror) p = 0 ∧
      evalPoint (mapC (famBound m)) p ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ 2 = 6 := IsAlgClosed.exists_pow_nat_eq 6 (by norm_num)
  exact ⟨(c, 1 / 4), evalPoint_extraFactorMirror_witness_mirror c hc,
    evalPoint_famBound_witness_ne_zero_mirror c hc hm⟩

/-- The Laurent polynomial ring over a field is a principal ideal ring: it is the localisation
of the principal ideal domain `F[X]` at the powers of `X`. -/
private theorem isPrincipalIdealRing_laurentPolynomial_mirror (F : Type) [Field F] :
    IsPrincipalIdealRing (LaurentPolynomial F) := by
  refine ⟨fun J ↦ ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (X : F[X])) (LaurentPolynomial F) J]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (J.under F[X])
  refine ⟨algebraMap F[X] (LaurentPolynomial F) g, ?_⟩
  rw [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

/-- The mirror factor `E'` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
private theorem prime_comparison_factor_mirror :
    Prime (toComparison extraFactorMirror) := by
  rw [toComparison_extraFactorMirror]
  have hp : Prime (LaurentPolynomial.invert (toComparison extraFactor)) :=
    (MulEquiv.prime_iff LaurentPolynomial.invert).mpr prime_toComparison_extraFactor
  exact (associated_unit_mul_left _ _ (LaurentPolynomial.isUnit_T 2)).symm.prime hp

/-- If `E'` divides `F` in the comparison ring, then `E` divides the reverse of `F` in
`ℤ[M][L]`. -/
private theorem extraFactor_dvd_reverse_of_dvd_mirror {F : ℤ[X][X]}
    (h : toComparison extraFactorMirror ∣ toComparison F) : extraFactor ∣ F.reverse := by
  apply extraFactor_dvd_of_toComparison_dvd
  rw [toComparison_extraFactorMirror] at h
  have h1 : LaurentPolynomial.invert (toComparison extraFactor) ∣ toComparison F :=
    (dvd_mul_left _ _).trans h
  have h2 : toComparison extraFactor ∣ LaurentPolynomial.invert (toComparison F) := by
    have h3 := map_dvd LaurentPolynomial.invert h1
    rwa [LaurentPolynomial.involutive_invert _] at h3
  have h3 : toComparison F.reverse =
      LaurentPolynomial.invert (toComparison F) * LaurentPolynomial.T F.natDegree := by
    have hrev : (F.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ)))).reverse =
        F.reverse.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
          (Polynomial.mapRingHom (Int.castRingHom ℚ))) := by
      rw [reverse, reverse, reflect_map, natDegree_map_eq_of_injective intPolyToRatFunc_injective]
    simp only [toComparison, RingHom.comp_apply, coe_mapRingHom]
    rw [← hrev, LaurentPolynomial.toLaurent_reverse,
      natDegree_map_eq_of_injective intPolyToRatFunc_injective]
  rw [h3]
  exact h2.mul_right _

/-- The mirror factor is coprime to the classical bound `(L - 1) B_m` in `ℚ(M)[L, L⁻¹]`. -/
theorem isCoprime_extraFactorMirror_famBound {m : ℕ} (hm : 0 < m) :
    IsCoprime (toComparison extraFactorMirror) (toComparison (famBound m)) := by
  have hnd : ¬ toComparison extraFactorMirror ∣ toComparison (famBound m) := by
    intro hdvd
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ 2 = 6 := IsAlgClosed.exists_pow_nat_eq 6 (by norm_num)
    obtain ⟨G, hG⟩ := extraFactor_dvd_reverse_of_dvd_mirror hdvd
    have h0 : evalPoint (mapC (famBound m).reverse) (c, 4) = 0 := by
      rw [hG, mapC, Polynomial.map_mul, evalPoint, eval₂_mul, ← evalPoint,
        evalPoint_extraFactor_witness_mirror c hc, zero_mul]
    have hrev : mapC (famBound m).reverse = (mapC (famBound m)).reverse := by
      rw [mapC, reverse, reverse, reflect_map,
        natDegree_map_eq_of_injective (Polynomial.map_injective _ Int.cast_injective)]
    have : Invertible (1 / 4 : ℂ) := invertibleOfNonzero (by norm_num)
    have h4 : (4 : ℂ) = ⅟(1 / 4 : ℂ) := by
      rw [invOf_eq_inv]
      norm_num
    rw [hrev, evalPoint, h4, eval₂_reverse_eq_zero_iff] at h0
    exact evalPoint_famBound_witness_ne_zero_mirror c hc hm h0
  have := isPrincipalIdealRing_laurentPolynomial_mirror (RatFunc ℚ)
  exact (prime_comparison_factor_mirror.coprime_iff_not_dvd).mpr hnd

/-- The mirror factor is coprime to every A-polynomial of `Wh⁻₀(T(r, s))`. -/
theorem isCoprime_extraFactorMirror_pair {r s : ℕ} (h : IsTorusPair r s) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A) :
    IsCoprime (toComparison extraFactorMirror) (toComparison A) := by
  obtain ⟨u, hu⟩ := aPolynomial_pair_associated_famBound h hA
  have hcop := isCoprime_extraFactorMirror_famBound (Nat.mul_pos (by have := h.1; omega)
    (by have := h.1; have := h.2.1; omega) : 0 < r * s)
  rw [← hu] at hcop
  exact hcop.of_mul_right_left

/-- **Chirality-robust refutation.** For `Wh⁻₀(T(r, s))` the weak AJ identity fails also when the
A-polynomial is replaced by its mirror `A(M, L⁻¹)`: the radical of the classical limit of a
recurrence polynomial is not the ideal of the mirrored A-polynomial either. -/
theorem not_ajSquareFree_mirror_pair {r s : ℕ} (h : IsTorusPair r s) (α : RecOp)
    (hα : IsRecurrencePolynomial (coloredJones (pairWhiteheadKnot r s h)) α) (A : ℤ[X][X])
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A) :
    Ideal.radical (Ideal.span {toComparison (specialize α)}) ≠
      Ideal.span {LaurentPolynomial.invert (toComparison A)} := by
  intro heq
  have hE : toComparison extraFactor ∣ toComparison (specialize α) :=
    ((theoremT.1 r s h).2.2.1 α hα.1 hα.2.2.2 hα.2.1).2
  have hmem : LaurentPolynomial.invert (toComparison A) ∈
      Ideal.radical (Ideal.span {toComparison (specialize α)}) := by
    rw [heq]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨n, hn⟩ := hmem
  rw [Ideal.mem_span_singleton] at hn
  have h1 : toComparison extraFactor ∣ LaurentPolynomial.invert (toComparison A) :=
    prime_toComparison_extraFactor.dvd_of_dvd_pow (hE.trans hn)
  have h2 : toComparison extraFactorMirror ∣ toComparison A := by
    rw [toComparison_extraFactorMirror, (LaurentPolynomial.isUnit_T 2).mul_left_dvd]
    have h3 := map_dvd LaurentPolynomial.invert h1
    rwa [LaurentPolynomial.involutive_invert _] at h3
  exact prime_comparison_factor_mirror.not_isUnit
    ((isCoprime_extraFactorMirror_pair h hA).isUnit_of_dvd' dvd_rfl h2)

end AJConjecture
