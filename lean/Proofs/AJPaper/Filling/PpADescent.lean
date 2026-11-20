import Mathlib
import AJConjecture.APolynomial
import AJConjecture.RecurrenceIdeal
import AJConjecture.QAlgTwistFactorPrime
import AJConjecture.ComparisonDvdDescent
import AJFamily.Classical.FamilyPolynomials

/-!
# From a common factor over `ℂ` to divisibility in the comparison ring (PpA)

Source: arXiv:2611.24826v1, Lemma 7.1 (`boundary.tex`), last paragraph: "Monic polynomial
division over `ℚ(M)` gives the same zero remainder after scalar extension, proving divisibility
over `ℚ(M)`."

`ppa_toComparison_dvd_of_common_factor`: let `P, A ∈ ℤ[M][L]` with `P` prime in
`R = ℚ(M)[L, L⁻¹]` and with nonzero constant coefficient in `L`. If `P` and `A` have a common
factor of positive `L`-degree over `ℂ`, then `P ∣ A` in `R`.

This replaces irreducibility over `ℂ(M)` (used in `AJHandoff.TorusKnot.PairKReverse` for `B_m`,
`m ≥ 2`) by primality over `ℚ(M)`, which the library has for every `𝒫_k`, `k ≠ 0`, including
`B_1`; one irreducible factor over `ℂ` is enough.

Route. Put `p = P.map ψ`, `a = A.map ψ` in `ℚ(M)[L]` (`ψ : ℤ[M] → ℚ(M)`), so
`toComparison P = toLaurent p`.
1. `ppa_irreducible_of_prime_toLaurent`: `p` is irreducible in `ℚ(M)[L]`: a factorization
   `p = u v` gives a unit `toLaurent u` (say), hence `toLaurent u ∣ toLaurent 1`, and
   `u.coeff 0 ≠ 0` (`p.coeff 0 = u.coeff 0 * v.coeff 0`), so `u ∣ 1` by `dvd_of_toLaurent_dvd`.
2. If `p ∤ a`, then `IsCoprime p a` (`ℚ(M)[L]` is Euclidean, `p` irreducible); map the Bézout
   identity to `ℂ(M)[L]` along `ι : ℚ(M) → ℂ(M)` (`RatFunc.liftRingHom`, as in the private
   `toComparison_dvd_of_mapC_dvd_twCClauses` of `AJTwist.Classical.TwCClauses`): the image of
   `g` divides `1`, but it has the positive degree of `g` (`algebraMap ℂ[M] ℂ(M)` is
   injective).
3. So `p ∣ a`, and `toLaurent` is a ring homomorphism.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A polynomial over a field with nonzero constant coefficient whose image in the Laurent
polynomial ring is prime is irreducible. -/
theorem ppa_irreducible_of_prime_toLaurent {K : Type*} [Field K] {p : K[X]}
    (hp : Prime (toLaurent p)) (h0 : p.coeff 0 ≠ 0) : Irreducible p := by
  have key : ∀ u v : K[X], p = u * v → IsUnit (toLaurent u) → IsUnit u := by
    intro u v huv hu
    have hu0 : u.coeff 0 ≠ 0 := by
      intro h
      apply h0
      rw [huv, mul_coeff_zero, h, zero_mul]
    have hdvd : toLaurent u ∣ toLaurent (1 : K[X]) := hu.dvd
    exact isUnit_of_dvd_one (dvd_of_toLaurent_dvd hu0 hdvd)
  refine ⟨fun hu ↦ hp.not_isUnit (hu.map toLaurent), fun u v huv ↦ ?_⟩
  have hL : toLaurent p = toLaurent u * toLaurent v := by rw [huv, map_mul]
  rcases hp.irreducible.isUnit_or_isUnit hL with h | h
  · exact Or.inl (key u v huv h)
  · exact Or.inr (key v u (by rw [huv, mul_comm]) h)

/-- The inclusion `ℚ(M) → ℂ(M)`, compatible with the coefficient maps from `ℤ[M]`. -/
private theorem exists_ratFunc_hom_ppaDescent : ∃ ι : RatFunc ℚ →+* RatFunc ℂ,
    ∀ P : ℤ[X][X], (mapC P).map (algebraMap ℂ[X] (RatFunc ℂ)) =
      (P.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ)))).map ι := by
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
  refine ⟨ι, fun P ↦ ?_⟩
  rw [mapC, Polynomial.map_map, Polynomial.map_map, hcomm]

/-- A prime of the comparison ring with nonzero constant coefficient divides every integer
polynomial with which it shares a factor of positive `L`-degree over `ℂ`. -/
theorem ppa_toComparison_dvd_of_common_factor {P A : ℤ[X][X]} (hP : Prime (toComparison P))
    (hP0 : P.coeff 0 ≠ 0) {g : ℂ[X][X]} (hdeg : 0 < g.natDegree) (hgP : g ∣ mapC P)
    (hgA : g ∣ mapC A) : toComparison P ∣ toComparison A := by
  obtain ⟨ι, hι⟩ := exists_ratFunc_hom_ppaDescent
  set ψ : ℤ[X] →+* RatFunc ℚ :=
    (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) with hψ
  have hp0 : (P.map ψ).coeff 0 ≠ 0 := by
    rw [coeff_map]
    exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr hP0
  have hirr : Irreducible (P.map ψ) := ppa_irreducible_of_prime_toLaurent hP hp0
  rcases EuclideanDomain.dvd_or_coprime (P.map ψ) (A.map ψ) hirr with hdvd | hcop
  · exact map_dvd Polynomial.toLaurent hdvd
  · exfalso
    obtain ⟨u, v, huv⟩ := hcop
    have h1 := congrArg (Polynomial.map ι) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one,
      ← hι, ← hι] at h1
    have hg1 : g.map (algebraMap ℂ[X] (RatFunc ℂ)) ∣ 1 := by
      rw [← h1]
      exact dvd_add (Dvd.dvd.mul_left (Polynomial.map_dvd _ hgP) _)
        (Dvd.dvd.mul_left (Polynomial.map_dvd _ hgA) _)
    have hd0 := Polynomial.natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hg1)
    rw [Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective ℂ)] at hd0
    omega

end AJConjecture
