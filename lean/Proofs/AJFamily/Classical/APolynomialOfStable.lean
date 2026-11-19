import Mathlib
import AJConjecture.ZeroSetDvd
import AJFamily.Classical.GaloisDescent

/-!
# A-polynomials of automorphism-stable sets

A nonzero integer polynomial vanishing on a set `S ⊆ ℂ²` that is stable under the field
automorphisms of `ℂ` is divisible over `ℂ` by an A-polynomial of `S` with integer coefficients.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A zero of a polynomial is a zero of each of its multiples. -/
private theorem evalPoint_eq_zero_of_dvd_of_autStable {g h : ℂ[X][X]} (hgh : g ∣ h)
    {p : ℂ × ℂ} (hp : evalPoint g p = 0) : evalPoint h p = 0 := by
  obtain ⟨k, rfl⟩ := hgh
  simp only [evalPoint, eval₂_mul] at hp ⊢
  rw [hp, zero_mul]

/-- Mapping coefficients by a field automorphism fixes the complexification of an integer
polynomial. -/
private theorem map_ringEquiv_mapC_eq (σ : ℂ ≃+* ℂ) (P : ℤ[X][X]) :
    (mapC P).map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) = mapC P := by
  rw [mapC, Polynomial.map_map, Polynomial.mapRingHom_comp,
    show (σ : ℂ →+* ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ from RingHom.ext_int _ _]

/-- Mapping coefficients by `σ⁻¹` undoes mapping them by `σ`. -/
private theorem map_symm_map_ringEquiv (σ : ℂ ≃+* ℂ) (g : ℂ[X][X]) :
    (g.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ))).map
      (Polynomial.mapRingHom (σ.symm : ℂ →+* ℂ)) = g := by
  rw [Polynomial.map_map, Polynomial.mapRingHom_comp]
  simp

/-- Mapping coefficients by a field automorphism sends a normalised irreducible factor of an
automorphism-fixed polynomial, whose zero set lies in the closure of a stable set, to another
such factor. -/
private theorem map_ringEquiv_mem_normalizedFactors_closure {S : Set (ℂ × ℂ)}
    (hS : IsAutStable S) {Q g : ℂ[X][X]} (hQ : Q ≠ 0)
    (hQσ : ∀ σ : ℂ ≃+* ℂ, Q.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) = Q) (σ : ℂ ≃+* ℂ)
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hgS : ∀ p : ℂ × ℂ, evalPoint g p = 0 → p ∈ zariskiClosure S) :
    g.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) ∈
        UniqueFactorizationMonoid.normalizedFactors Q ∧
      ∀ p : ℂ × ℂ, evalPoint (g.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ))) p = 0 →
        p ∈ zariskiClosure S := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hQ] at hg ⊢
  obtain ⟨hirr, hnorm, hdvd⟩ := hg
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv (Polynomial.mapEquiv σ))).2 hirr
  · rw [normalize_map_ringEquiv, hnorm]
  · rw [← hQσ σ]
    exact Polynomial.map_dvd _ hdvd
  · intro p hp
    have hpq : p = (σ (σ.symm p.1), σ (σ.symm p.2)) := by simp
    rw [hpq] at hp ⊢
    have hev := evalPoint_map_ringEquiv σ g (σ.symm p.1, σ.symm p.2)
    dsimp only at hev
    rw [hev] at hp
    exact zariskiClosure_isAutStable hS σ (σ.symm p.1, σ.symm p.2)
      (hgS _ ((map_eq_zero_iff σ σ.injective).1 hp))

/-- A nonzero integer polynomial vanishing on an automorphism-stable set `S` is divisible, over
`ℂ`, by an A-polynomial of `S`: the product of its normalised irreducible factors whose zero set
lies in the Zariski closure of `S`, rescaled to have integer coefficients. -/
theorem exists_isAPolynomialOf_of_isAutStable {S : Set (ℂ × ℂ)} {P : ℤ[X][X]} (hP : P ≠ 0)
    (hSP : ∀ p ∈ S, evalPoint (mapC P) p = 0) (hS : IsAutStable S) :
    ∃ A : ℤ[X][X], IsAPolynomialOf S A ∧ mapC A ∣ mapC P := by
  classical
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℂ[X][X], Q = mapC P := ⟨_, rfl⟩
  rw [← hQdef] at hSP ⊢
  have hQ : Q ≠ 0 := hQdef ▸ (Polynomial.map_ne_zero_iff
    (Polynomial.map_injective _ (Int.castRingHom ℂ).injective_int)).2 hP
  have hQσ : ∀ σ : ℂ ≃+* ℂ, Q.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) = Q :=
    fun σ ↦ hQdef ▸ map_ringEquiv_mapC_eq σ P
  obtain ⟨T, hT⟩ : ∃ T : Finset ℂ[X][X],
      T = (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun g ↦ ∀ p : ℂ × ℂ, evalPoint g p = 0 → p ∈ zariskiClosure S) := ⟨_, rfl⟩
  have hmemT : ∀ g, g ∈ T ↔ g ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
      ∀ p : ℂ × ℂ, evalPoint g p = 0 → p ∈ zariskiClosure S := by
    intro g
    rw [hT, Finset.mem_filter, Multiset.mem_toFinset]
  have hTσ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ T, g.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) ∈ T := by
    intro σ g hg
    rw [hmemT] at hg ⊢
    exact map_ringEquiv_mem_normalizedFactors_closure hS hQ hQσ σ hg.1 hg.2
  have hfix : ∀ σ : ℂ ≃+* ℂ,
      (∏ g ∈ T, g).map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) = ∏ g ∈ T, g := by
    intro σ
    rw [Polynomial.map_prod]
    refine Finset.prod_nbij' (fun g ↦ g.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)))
      (fun g ↦ g.map (Polynomial.mapRingHom (σ.symm : ℂ →+* ℂ))) (hTσ σ) (hTσ σ.symm)
      (fun g _ ↦ map_symm_map_ringEquiv σ g) (fun g _ ↦ ?_) (fun g _ ↦ rfl)
    simpa using map_symm_map_ringEquiv σ.symm g
  obtain ⟨A, c, hc, hA⟩ := exists_int_poly_of_forall_ringEquiv_fixed _ hfix
  have hassoc : Associated (mapC A) (∏ g ∈ T, g) := by
    rw [hA]
    exact associated_unit_mul_left _ _ (Polynomial.isUnit_C.2 (Polynomial.isUnit_C.2 hc.isUnit))
  refine ⟨A, ⟨?_, fun g hg ↦ ?_⟩, ?_⟩
  · refine hassoc.squarefree_iff.2 (Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_)
    · intro t ht u hu htu
      have ht' := ((hmemT t).1 ht).1
      have hu' := ((hmemT u).1 hu).1
      have hti := UniqueFactorizationMonoid.irreducible_of_normalized_factor t ht'
      have hui := UniqueFactorizationMonoid.irreducible_of_normalized_factor u hu'
      exact hti.isRelPrime_iff_not_dvd.2 fun hd ↦ htu
        (UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated ht' hu'
          (hti.associated_of_dvd hui hd))
    · intro t ht
      exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor t
        ((hmemT t).1 ht).1).squarefree
  · change g ∣ mapC A ↔ _
    rw [hassoc.dvd_iff_dvd_right]
    constructor
    · intro hd p hp
      obtain ⟨t, ht, hgt⟩ := (hg.prime.dvd_finsetProd_iff _).1 hd
      exact ((hmemT t).1 ht).2 p (evalPoint_eq_zero_of_dvd_of_autStable hgt hp)
    · intro hcl
      have hdvd : g ∣ Q := dvd_of_forall_evalPoint_eq_zero hg fun p hp ↦ hcl p hp _ hSP
      obtain ⟨q, hq, hgq⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hQ hg hdvd
      have hqT : q ∈ T := (hmemT q).2
        ⟨hq, fun p hp ↦ hcl p (evalPoint_eq_zero_of_dvd_of_autStable hgq.symm.dvd hp)⟩
      exact hgq.dvd.trans (Finset.dvd_prod_of_mem _ hqT)
  · rw [hassoc.dvd_iff_dvd_left, Finset.prod_eq_multiset_prod, Multiset.map_id']
    refine (Multiset.prod_dvd_prod_of_le ?_).trans
      (UniqueFactorizationMonoid.prod_normalizedFactors hQ).dvd
    exact (Multiset.le_iff_subset T.nodup).2 fun g hg ↦ ((hmemT g).1 hg).1

end AJConjecture
