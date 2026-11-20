import Mathlib
import AJConjecture.ZeroSetDvd
import AJPaper.Filling.PpADescent

/-!
# Generic points of a prime curve and divisibility of the A-polynomial (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`): "The realizations are dense in that
curve", together with Lemma 7.1 (`boundary.tex`).

`ppa_toComparison_dvd_of_generic`: let `A` be an A-polynomial of a set `S` (`IsAPolynomialOf`),
and `P ∈ ℤ[M][L]` prime in `R = ℚ(M)[L, L⁻¹]` with nonzero constant coefficient in `L`. If every
zero of `P` off the zero set of a polynomial `Bad` lies in `S`, and no irreducible factor of `P`
of positive `L`-degree over `ℂ` divides `Bad`, then `P ∣ A` in `R`.

Route.
1. `P.map ψ` is irreducible over `ℚ(M)` (`ppa_irreducible_of_prime_toLaurent`), so `P` has
   positive `L`-degree and `mapC P` has an irreducible factor `g` of positive `L`-degree (an
   irreducible factor of its primitive part, as the private
   `exists_irreducible_horizontal_factor_rev` of `AJHandoff.TorusKnot.PairKReverse`).
2. `ppa_dvd_mapC_of_generic`: the zero set of `g` lies in the Zariski closure of `S`: for `Q`
   vanishing on `S`, `Q * mapC Bad` vanishes on the zero set of `g`, so `g ∣ Q * mapC Bad`
   (`dvd_of_forall_evalPoint_eq_zero`) and `g ∣ Q` (`g` is prime and does not divide
   `mapC Bad`); hence `g ∣ mapC A` by the definition of `IsAPolynomialOf` (as
   `pair_reverse_inclusion`).
3. `ppa_toComparison_dvd_of_common_factor`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Evaluation at a point is multiplicative. -/
private theorem evalPoint_mul_ppaGenericDvd (P Q : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (P * Q) p = evalPoint P p * evalPoint Q p := by
  simp [evalPoint, Polynomial.eval₂_mul]

/-- A polynomial of positive `L`-degree over `ℂ[M]` has an irreducible factor of positive
`L`-degree (an irreducible factor of its primitive part). -/
private theorem exists_irreducible_horizontal_factor_ppaGenericDvd {P : ℂ[X][X]}
    (hP : 0 < P.natDegree) : ∃ g : ℂ[X][X], Irreducible g ∧ 0 < g.natDegree ∧ g ∣ P := by
  have hpd : P.primPart.natDegree = P.natDegree := natDegree_primPart P
  have hnu : ¬ IsUnit P.primPart := fun hu ↦ by
    have := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hnu (primPart_ne_zero P)
  refine ⟨g, hg, Nat.pos_of_ne_zero fun h0 ↦ hg.not_isUnit ?_, hgd.trans (primPart_dvd P)⟩
  have hgp : g.IsPrimitive := fun c hc ↦ isPrimitive_primPart P c (hc.trans hgd)
  rw [eq_C_of_natDegree_eq_zero h0] at hgp ⊢
  exact isUnit_C.2 (hgp _ dvd_rfl)

/-- An irreducible polynomial whose zeros off the zero set of `Bad` lie in `S`, and which does
not divide `Bad`, divides every A-polynomial of `S` over `ℂ`. -/
theorem ppa_dvd_mapC_of_generic {S : Set (ℂ × ℂ)} {A : ℤ[X][X]} (hA : IsAPolynomialOf S A)
    {g Bad : ℂ[X][X]} (hg : Irreducible g) (hgB : ¬ g ∣ Bad)
    (hgen : ∀ p : ℂ × ℂ, evalPoint g p = 0 → evalPoint Bad p ≠ 0 → p ∈ S) : g ∣ mapC A := by
  refine (hA.2 g hg).2 fun p hp Q hQ ↦ ?_
  have hQB : g ∣ Q * Bad := dvd_of_forall_evalPoint_eq_zero hg fun q hq ↦ by
    rw [evalPoint_mul_ppaGenericDvd]
    by_cases hz : evalPoint Bad q = 0
    · rw [hz, mul_zero]
    · rw [hQ q (hgen q hq hz), zero_mul]
  rcases hg.prime.dvd_or_dvd hQB with h1 | h1
  · obtain ⟨k, rfl⟩ := h1
    rw [evalPoint_mul_ppaGenericDvd, hp, zero_mul]
  · exact absurd h1 hgB

/-- A prime `P` of the comparison ring whose generic zeros lie in `S` divides every
A-polynomial of `S` in the comparison ring. -/
theorem ppa_toComparison_dvd_of_generic {S : Set (ℂ × ℂ)} {A P Bad : ℤ[X][X]}
    (hA : IsAPolynomialOf S A) (hP : Prime (toComparison P)) (hP0 : P.coeff 0 ≠ 0)
    (hBad : ∀ g : ℂ[X][X], Irreducible g → 0 < g.natDegree → g ∣ mapC P → ¬ g ∣ mapC Bad)
    (hgen : ∀ p : ℂ × ℂ, evalPoint (mapC P) p = 0 → evalPoint (mapC Bad) p ≠ 0 → p ∈ S) :
    toComparison P ∣ toComparison A := by
  have hp0 : (P.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ)))).coeff 0 ≠ 0 := by
    rw [coeff_map]
    exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr hP0
  have hirr : Irreducible (P.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ)))) :=
    ppa_irreducible_of_prime_toLaurent hP hp0
  have hdeg : 0 < (mapC P).natDegree := by
    rw [mapC, natDegree_map_eq_of_injective
      (Polynomial.map_injective _ (Int.cast_injective (α := ℂ))),
      ← natDegree_map_eq_of_injective intPolyToRatFunc_injective]
    exact hirr.natDegree_pos
  obtain ⟨g, hg, hgdeg, hgP⟩ := exists_irreducible_horizontal_factor_ppaGenericDvd hdeg
  refine ppa_toComparison_dvd_of_common_factor hP hP0 hgdeg hgP ?_
  refine ppa_dvd_mapC_of_generic hA hg (hBad g hg hgdeg hgP) fun p hp hB ↦ hgen p ?_ hB
  obtain ⟨k, hk⟩ := hgP
  rw [hk, evalPoint_mul_ppaGenericDvd, hp, zero_mul]

end AJConjecture
