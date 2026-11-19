import Mathlib
import AJTwist.Classical.TwCFourFamilies
import AJPaper.Finger.PpFReverse

/-!
# The A-polynomial of the mirror image (Unit PpF, node `PpF_APolyInv`)

Source: Section 8.2 of the paper: "the same meridian inversion on the full boundary eigenvalue
set gives `A_{S^*}(M, L) ≐ A_S(M⁻¹, L)`". In the library the mirror image is the closure of the
inverse braid `K.inv`, with `eigenvalueSet K.inv = {(M, L⁻¹)}` (`eigenvalueSet_inv`); the
statement is `A_{K.inv}(M, L) ≐ A_K(M, L⁻¹)` in `R = ℚ(M)[L, L⁻¹]` (the two forms agree since
eigenvalue sets are invariant under the simultaneous inversion).

* `ppf_toComparison_dvd_invert`: let `L ≠ 0` on `S` and `(M, L⁻¹) ∈ S'` for `(M, L) ∈ S`; for
  A-polynomials `A` of `S` and `A'` of `S'`, `A(M, L)` divides `A'(M, L⁻¹)` in `R`. Route: over
  `ℂ`, `mapC A` is square-free and every irreducible factor `h` of it divides
  `L · (mapC A').reverse`: either `h ≐ L`, or `h.coeff 0 ≠ 0`, the zero set of `h.reverse` lies
  in the closure of `S'` (`ppf_zeroSet_reverse_subset`), so `h.reverse ∣ mapC A'`
  (`ppf_irreducible_reverse`) and `h = h.reverse.reverse ∣ (mapC A').reverse`. Descend to `R`
  (restate the private `toComparison_dvd_of_mapC_dvd` and
  `squarefree_dvd_of_forall_irreducible_dvd` of the library) and use `toComparison_reverse`.
* `ppf_aPolynomial_inv`: `A_{K.inv} ≐ A_K(M, L⁻¹)`, by the first statement in both directions
  (`eigenvalueSet_inv`, `isEigenMirrorOf_inv`, `snd_ne_zero_of_mem_eigenvalueSet`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- In a unique factorization monoid, a squarefree element all of whose irreducible divisors
divide `b` divides `b`. -/
private theorem squarefree_dvd_of_forall_irreducible_dvd_ppfAPolyInv {α : Type*}
    [CommMonoidWithZero α] [Nontrivial α] [UniqueFactorizationMonoid α] (b a : α) :
    Squarefree a → (∀ g : α, Irreducible g → g ∣ a → g ∣ b) → a ∣ b := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun hsq _ ↦ absurd hsq not_squarefree_zero
  | h₂ x hx => exact fun _ _ ↦ hx.dvd
  | h₃ a p _ hp ih =>
    intro hsq hdiv
    have hpa : ¬ p ∣ a := fun hpa ↦ hp.not_isUnit (hsq p (mul_dvd_mul_left p hpa))
    obtain ⟨c, rfl⟩ := ih hsq.of_mul_right fun g hg hga ↦ hdiv g hg (hga.mul_left p)
    have hpc : p ∣ c :=
      (hp.dvd_or_dvd (hdiv p hp.irreducible (dvd_mul_right p a))).resolve_left hpa
    rw [mul_comm p a]
    exact mul_dvd_mul_left a hpc

/-- Divisibility over `ℂ` of two integer polynomials descends to the comparison ring
`ℚ(M)[L, L⁻¹]`: polynomial division over the field `ℚ(M)` is unchanged in `ℂ(M)`. -/
private theorem toComparison_dvd_of_mapC_dvd_ppfAPolyInv {A B : ℤ[X][X]}
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

/-- `mapC` commutes with the reverse. -/
private theorem mapC_reverse_ppfAPolyInv (P : ℤ[X][X]) :
    mapC P.reverse = (mapC P).reverse := by
  rw [mapC, reverse, reverse, reflect_map,
    natDegree_map_eq_of_injective (Polynomial.map_injective _ Int.cast_injective)]

/-- An irreducible curve of the closure of `S` divides `L` times the reverse of an A-polynomial
of a set containing the image of `S` under `(M, L) ↦ (M, L⁻¹)`. -/
private theorem irreducible_dvd_X_mul_reverse_ppfAPolyInv {S S' : Set (ℂ × ℂ)}
    (hSS' : ∀ p ∈ S, p.2 ≠ 0 ∧ (p.1, p.2⁻¹) ∈ S') {A' : ℤ[X][X]}
    (hA' : IsAPolynomialOf S' A') {g : ℂ[X][X]} (hg : Irreducible g)
    (hz : ∀ p : ℂ × ℂ, evalPoint g p = 0 → p ∈ zariskiClosure S) :
    g ∣ X * (mapC A').reverse := by
  by_cases h0 : g.coeff 0 = 0
  · exact (Polynomial.irreducible_X.dvd_symm hg (X_dvd_iff.mpr h0)).mul_right _
  · obtain ⟨c, hc⟩ := (hA'.2 g.reverse (ppf_irreducible_reverse hg h0)).mpr
      (ppf_zeroSet_reverse_subset hSS' hg h0 hz)
    refine Dvd.dvd.mul_left ⟨c.reverse, ?_⟩ _
    rw [mapC, hc, reverse_mul_of_domain, ppf_reverse_reverse h0]

/-- The image of `L` in the comparison ring. -/
private theorem toComparison_X_ppfAPolyInv :
    toComparison (X : ℤ[X][X]) = LaurentPolynomial.T 1 := by
  rw [toComparison, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X,
    Polynomial.toLaurent_X]

/-- An A-polynomial of `S` divides, in `ℚ(M)[L, L⁻¹]`, the image under `L ↦ L⁻¹` of an
A-polynomial of a set containing the image of `S` under `(M, L) ↦ (M, L⁻¹)`. -/
theorem ppf_toComparison_dvd_invert {S S' : Set (ℂ × ℂ)}
    (hSS' : ∀ p ∈ S, p.2 ≠ 0 ∧ (p.1, p.2⁻¹) ∈ S') {A A' : ℤ[X][X]}
    (hA : IsAPolynomialOf S A) (hA' : IsAPolynomialOf S' A') :
    toComparison A ∣ LaurentPolynomial.invert (toComparison A') := by
  have h1 : mapC A ∣ mapC (X * A'.reverse) := by
    have hX : mapC (X * A'.reverse) = X * (mapC A').reverse := by
      rw [← mapC_reverse_ppfAPolyInv, mapC, Polynomial.map_mul, Polynomial.map_X]
    rw [hX]
    exact squarefree_dvd_of_forall_irreducible_dvd_ppfAPolyInv _ _ hA.1 fun g hg hgA ↦
      irreducible_dvd_X_mul_reverse_ppfAPolyInv hSS' hA' hg ((hA.2 g hg).mp hgA)
  have h2 := toComparison_dvd_of_mapC_dvd_ppfAPolyInv h1
  rw [map_mul, toComparison_reverse, toComparison_X_ppfAPolyInv] at h2
  exact (LaurentPolynomial.isUnit_T _).dvd_mul_right.mp
    ((LaurentPolynomial.isUnit_T 1).dvd_mul_left.mp h2)

/-- **The A-polynomial of the mirror image**: every A-polynomial of the closure of the inverse
braid is associated, in `ℚ(M)[L, L⁻¹]`, to the image under `L ↦ L⁻¹` of every A-polynomial of
the knot. -/
theorem ppf_aPolynomial_inv {K : BraidKnot} {A A' : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet K) A)
    (hA' : IsAPolynomialOf (eigenvalueSet K.inv) A') :
    Associated (toComparison A') (LaurentPolynomial.invert (toComparison A)) := by
  have h1 : toComparison A' ∣ LaurentPolynomial.invert (toComparison A) :=
    ppf_toComparison_dvd_invert
      (fun p hp ↦ ⟨snd_ne_zero_of_mem_eigenvalueSet hp, isEigenMirrorOf_inv K p hp⟩) hA' hA
  have h2 : toComparison A ∣ LaurentPolynomial.invert (toComparison A') :=
    ppf_toComparison_dvd_invert (fun p hp ↦ ⟨snd_ne_zero_of_mem_eigenvalueSet hp, by
      rw [eigenvalueSet_inv]
      exact ⟨p, hp, rfl⟩⟩) hA hA'
  have h3 := map_dvd LaurentPolynomial.invert h2
  rw [LaurentPolynomial.involutive_invert] at h3
  exact associated_of_dvd_dvd h1 h3

end AJConjecture
