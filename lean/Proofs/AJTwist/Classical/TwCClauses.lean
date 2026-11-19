import Mathlib
import AJConjecture.APolynomialUnique
import AJFamily.Classical.APolynomialOfStable
import AJTwist.Classical.TwCCoprime

/-!
# The classical clauses from a bound (Unit C3)

`TwClassClauses K G P` collects the classical clauses of `PairTClauses`
(`AJHandoff.TorusKnot.PairKTheoremT`) for a knot `K`, an obstruction polynomial `G` and a bound
`P`: an A-polynomial of the eigenvalue set of `K` exists, and every A-polynomial `A` satisfies
`A ∣ P` and `gcd(G, A) = 1` in `R = ℚ(M)[L, L⁻¹]`.

* `twClassClauses_of_bound`: the clauses follow from a nonzero integer polynomial `P` vanishing
  at every point of the eigenvalue set and coprime to `G` in `R`. Route: an A-polynomial `A₀`
  with `mapC A₀ ∣ mapC P` exists by `exists_isAPolynomialOf_of_isAutStable` and
  `eigenvalueSet_isAutStable` (no reverse inclusion is needed); divisibility over `ℂ` descends
  to `R` (restate the private `toComparison_dvd_of_mapC_dvd` of
  `AJHandoff.TorusKnot.PairKAPolyHorizontal`); any other `A` is associated to `A₀` in `R`
  (`isAPolynomialOf_toComparison_associated`); coprimality passes to divisors
  (`IsCoprime.of_isCoprime_of_dvd_right`).
* `twClassClauses_neg`: negative clasp, `G = E`, `P = twBound k₁ k₂`.
* `twClassClauses_pos`: positive clasp, `G = E^∨`, `P = (twBound k₁ k₂).reverse`, from the bound
  at the points `(M, L⁻¹)`.

What stays interpretation, as in the library: that `IsAPolynomialOf (eigenvalueSet K)` is the
horizontal part of the A-polynomial of the paper (Lemma 7.1, `boundary.tex`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The classical clauses for a knot `K`, an obstruction polynomial `G` and a bound `P`: an
A-polynomial exists, and every A-polynomial divides `P` and is coprime to `G` in
`ℚ(M)[L, L⁻¹]`. -/
def TwClassClauses (K : BraidKnot) (G P : ℤ[X][X]) : Prop :=
  (∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A) ∧
    ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      toComparison A ∣ toComparison P ∧ IsCoprime (toComparison G) (toComparison A)

/-- Divisibility over `ℂ` of two integer polynomials descends to the comparison ring
`ℚ(M)[L, L⁻¹]`: polynomial division over the field `ℚ(M)` is unchanged in `ℂ(M)`. -/
private theorem toComparison_dvd_of_mapC_dvd_twCClauses {A B : ℤ[X][X]}
    (h : mapC A ∣ mapC B) : toComparison A ∣ toComparison B := by
  set ψ : ℤ[X] →+* RatFunc ℚ :=
    (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) with hψ
  set φ : ℚ[X] →+* RatFunc ℂ :=
    (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (algebraMap ℚ ℂ)) with hφ
  have hφinj : Function.Injective φ :=
    (RatFunc.algebraMap_injective ℂ).comp
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
  set ι : RatFunc ℚ →+* RatFunc ℂ := RatFunc.liftRingHom φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj) with hι
  have hιX : ι (algebraMap ℚ[X] (RatFunc ℚ) X) = algebraMap ℂ[X] (RatFunc ℂ) X := by
    have hd := RatFunc.liftRingHom_apply_div φ
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj) X 1
    rw [map_one, div_one, map_one, div_one] at hd
    rw [hι, hd, hφ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
  have hcomm : ι.comp ψ =
      (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [eq_intCast, map_intCast]
    · simp only [RingHom.comp_apply, hψ, Polynomial.coe_mapRingHom, Polynomial.map_X, hιX]
  have hmap : ∀ P : ℤ[X][X], (mapC P).map (algebraMap ℂ[X] (RatFunc ℂ)) =
      (P.map ψ).map ι := by
    intro P
    rw [mapC, Polynomial.map_map, Polynomial.map_map, hcomm]
  have h1 := Polynomial.map_dvd (algebraMap ℂ[X] (RatFunc ℂ)) h
  rw [hmap, hmap, Polynomial.map_dvd_map'] at h1
  exact map_dvd Polynomial.toLaurent h1

/-- The classical clauses from a nonzero bound vanishing on the whole eigenvalue set and
coprime to `G` in the comparison ring. -/
theorem twClassClauses_of_bound {K : BraidKnot} {G P : ℤ[X][X]} (hP0 : P ≠ 0)
    (hP : ∀ p ∈ eigenvalueSet K, evalPoint (mapC P) p = 0)
    (hcop : IsCoprime (toComparison G) (toComparison P)) : TwClassClauses K G P := by
  obtain ⟨A₀, hA₀, hdvd⟩ :=
    exists_isAPolynomialOf_of_isAutStable hP0 hP (eigenvalueSet_isAutStable K)
  have h0 : toComparison A₀ ∣ toComparison P := toComparison_dvd_of_mapC_dvd_twCClauses hdvd
  refine ⟨⟨A₀, hA₀⟩, fun A hA ↦ ?_⟩
  have hAP : toComparison A ∣ toComparison P :=
    (isAPolynomialOf_toComparison_associated hA hA₀).dvd_iff_dvd_left.2 h0
  exact ⟨hAP, hcop.of_isCoprime_of_dvd_right hAP⟩

/-- Negative clasp: the clauses with `G = E` from the bound `(L - 1) 𝒫_(k₁) 𝒫_(k₂)`. -/
theorem twClassClauses_neg {K : BraidKnot} {k₁ k₂ : ℤ}
    (h : ∀ p ∈ eigenvalueSet K, evalPoint (mapC (twBound k₁ k₂)) p = 0) :
    TwClassClauses K extraFactor (twBound k₁ k₂) :=
  twClassClauses_of_bound (twBound_ne_zero k₁ k₂) h (isCoprime_extraFactor_twBound k₁ k₂)

/-- Positive clasp: the clauses with `G = E^∨` from the bound at the points `(M, L⁻¹)`. -/
theorem twClassClauses_pos {K : BraidKnot} {k₁ k₂ : ℤ}
    (h : ∀ p ∈ eigenvalueSet K, evalPoint (mapC (twBound k₁ k₂)) (p.1, p.2⁻¹) = 0) :
    TwClassClauses K extraFactorMirror (twBound k₁ k₂).reverse := by
  refine twClassClauses_of_bound (twBound_reverse_ne_zero k₁ k₂) (fun p hp ↦ ?_)
    (isCoprime_extraFactorMirror_twBound_reverse k₁ k₂)
  have hL : p.2⁻¹ ≠ 0 := inv_ne_zero (snd_ne_zero_of_mem_eigenvalueSet hp)
  have h1 := (evalPoint_mapC_reverse_eq_zero_iff (twBound k₁ k₂) p.1 p.2⁻¹ hL).mpr (h p hp)
  rwa [inv_inv] at h1

end AJConjecture
