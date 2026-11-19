import Mathlib
import AJConjecture.APolynomialUnique
import AJConjecture.ExtraFactorPrime
import AJHandoff.TorusKnot.PairKClassical

/-!
# T-AEX, second half: the horizontal part of the formal A-polynomial

The source theorem (classical note §§4–5) is stated for "the full square-free `SL₂` boundary
polynomial `A_K` including `L - 1`", conventionally defined through the character variety of the
knot exterior (Cooper–Culler–Gillet–Long–Shalen). The library has no character variety; its
A-polynomial is `IsAPolynomialOf (eigenvalueSet K)`. The faithful formal content of the
comparison is:

* uniqueness: any two formal A-polynomials are associated in `R = ℚ(M)[L, L⁻¹]`
  (`isAPolynomialOf_toComparison_associated`, restated here as `aPolynomial_pair_associated`);
* the two properties the source proves for `A_K`, now for every formal A-polynomial:
  `A ∣ (L - 1) B_m` in `R` (`toComparison_dvd_famBound_pair`) and `gcd_R(E, A) = 1`
  (`isCoprime_extraFactor_pair`), with the abelian line retained (`L - 1` divides `A`,
  `sub_one_dvd_aPolynomial`).

What stays interpretation: that the eigenvalue-set definition (all representations, common
eigenvector, Zariski closure, curve components only) defines the same horizontal divisor as the
character-variety definition with the preferred longitude. Both use the zero-framed longitude;
reducible representations contribute only `L = 1`; components with zero-dimensional boundary
image and isolated points contribute no curve in either definition; vertical factors are units
of `R`.
-/

open Polynomial

namespace AJConjecture

/-- Two A-polynomials of `Wh⁻₀(T(r, s))` agree up to a unit of `ℚ(M)[L, L⁻¹]`. -/
theorem aPolynomial_pair_associated {r s : ℕ} (h : IsTorusPair r s) {A A' : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A)
    (hA' : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A') :
    Associated (toComparison A) (toComparison A') :=
  isAPolynomialOf_toComparison_associated hA hA'

/-- Divisibility over `ℂ` of two integer polynomials descends to the comparison ring
`ℚ(M)[L, L⁻¹]`: polynomial division over the field `ℚ(M)` is unchanged in `ℂ(M)`. -/
private theorem toComparison_dvd_of_mapC_dvd {A B : ℤ[X][X]} (h : mapC A ∣ mapC B) :
    toComparison A ∣ toComparison B := by
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

/-- T-CLASS (divisibility): every A-polynomial of `Wh⁻₀(T(r, s))` divides `(L - 1) B_(rs)` in
`ℚ(M)[L, L⁻¹]`. Route: each irreducible factor of `A` over `ℂ` has its zero set in the closure of
the eigenvalue set, hence in the zero set of `(L - 1) B_(rs)` (`evalPoint_famBound_pair`), so it
divides it (`dvd_of_forall_evalPoint_eq_zero`); `A` is square-free over `ℂ`, so `A` divides it
over `ℂ`; descend to `ℚ[M][L]` (coefficients fixed by `Aut ℂ`, as in `GaloisDescent`) and map to
the comparison ring. -/
theorem toComparison_dvd_famBound_pair {r s : ℕ} (h : IsTorusPair r s) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A) :
    toComparison A ∣ toComparison (famBound (r * s)) := by
  obtain ⟨A₀, hA₀, hdvd, -⟩ := exists_aPolynomial_pair h
  exact (isAPolynomialOf_toComparison_associated hA hA₀).dvd_iff_dvd_left.2
    (toComparison_dvd_of_mapC_dvd hdvd)

/-- The Laurent polynomial ring over a field is a principal ideal ring: it is the localisation
of the principal ideal domain `F[X]` at the powers of `X`. -/
private theorem isPrincipalIdealRing_laurentPolynomial_apoly (F : Type) [Field F] :
    IsPrincipalIdealRing (LaurentPolynomial F) := by
  refine ⟨fun J ↦ ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (X : F[X])) (LaurentPolynomial F) J]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (J.under F[X])
  refine ⟨algebraMap F[X] (LaurentPolynomial F) g, ?_⟩
  rw [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

/-- T-CLASS (exclusion): `gcd_R(E, A) = 1` for every A-polynomial of `Wh⁻₀(T(r, s))`, for both
parities of `rs`. Route: `E` is prime in `R` (`prime_toComparison_extraFactor`); if `E ∣ A` then
the zero set of `E` lies in the closure of the eigenvalue set, contradicting
`exists_extraFactor_zero_not_famBound_pair` (as in `conditional_counterexample`). -/
theorem isCoprime_extraFactor_pair {r s : ℕ} (h : IsTorusPair r s) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A) :
    IsCoprime (toComparison extraFactor) (toComparison A) := by
  have hEA : ¬ toComparison extraFactor ∣ toComparison A := by
    intro hdvd
    have h1 : extraFactor ∣ A := extraFactor_dvd_of_toComparison_dvd hdvd
    have h2 : extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) ∣
        A.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) := Polynomial.map_dvd _ h1
    have h3 := (hA.2 _ irreducible_extraFactor_map).mp h2
    obtain ⟨p, hp0, hpne⟩ := exists_extraFactor_zero_not_famBound_pair h
    exact hpne (h3 p hp0 _ fun q hq ↦ evalPoint_famBound_pair h hq)
  have := isPrincipalIdealRing_laurentPolynomial_apoly (RatFunc ℚ)
  exact (prime_toComparison_extraFactor.coprime_iff_not_dvd).mpr hEA

/-- The exponent sum of a word of the free group, as an element of `Multiplicative ℤ`. -/
private def pairExpSum (m : ℕ) : FreeGroup (Fin m) →* Multiplicative ℤ :=
  FreeGroup.lift fun _ ↦ Multiplicative.ofAdd 1

/-- Artin's action of a generator preserves the exponent sum. -/
private theorem pairExpSum_artinHom (m : ℕ) (g : ℕ × Bool) (x : FreeGroup (Fin m)) :
    pairExpSum m (artinHom m g x) = pairExpSum m x := by
  have h : (pairExpSum m).comp (artinHom m g) = pairExpSum m := by
    refine FreeGroup.ext_hom _ _ fun k ↦ ?_
    simp only [MonoidHom.comp_apply, artinHom, FreeGroup.lift_apply_of, map_mul, map_inv,
      pairExpSum]
    exact mul_inv_cancel_comm _ _
  exact DFunLike.congr_fun h x

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_apoly (m : ℕ) (w : BraidWord) (k : Fin m) :
    (artinWord m w k).1 = strandPerm m w k := by
  induction w with
  | nil => simp [artinWord, strandPerm]
  | cons g w ih =>
    rw [strandPerm, List.map_cons, List.prod_cons, ← strandPerm, Equiv.Perm.mul_apply, ← ih]
    simp only [artinWord]
    generalize (artinWord m w k).1 = l
    by_cases h : g.1 + 1 < m
    · simp only [artinGen, strandSwap, h, dite_true, Equiv.swap_apply_def]
      split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
    · simp [artinGen, strandSwap, h]

/-- The conjugators of one generator have total exponent sum its sign. -/
private theorem prod_pairExpSum_artinGen (m : ℕ) (g : ℕ × Bool) (hg : g.1 + 1 < m) :
    ∏ p : Fin m, pairExpSum m (artinGen m g p).2 =
      Multiplicative.ofAdd (if g.2 then (1 : ℤ) else -1) := by
  obtain ⟨i, b⟩ := g
  dsimp only at hg ⊢
  cases b with
  | true =>
    rw [Finset.prod_eq_single (⟨i, by omega⟩ : Fin m)]
    · simp [artinGen, hg, pairExpSum]
    · intro p _ hp
      have hp' : (p : ℕ) ≠ i := fun h ↦ hp (Fin.ext h)
      simp only [artinGen, hg, dite_true, hp', ite_false]
      split_ifs <;> simp_all
    · simp
  | false =>
    rw [Finset.prod_eq_single (⟨i + 1, hg⟩ : Fin m)]
    · simp [artinGen, hg, pairExpSum]
    · intro p _ hp
      have hp' : (p : ℕ) ≠ i + 1 := fun h ↦ hp (Fin.ext h)
      simp only [artinGen, hg, dite_true, hp', ite_false]
      split_ifs <;> simp_all
    · simp

/-- The conjugators of Artin's action of a braid word have total exponent sum its writhe. -/
private theorem prod_pairExpSum_artinWord (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) :
    ∏ k : Fin m, pairExpSum m (artinWord m w k).2 = Multiplicative.ofAdd (writhe w) := by
  induction w with
  | nil => simp [artinWord, writhe]
  | cons g w ih =>
    have hg : g.1 + 1 < m := hw g List.mem_cons_self
    simp only [artinWord, map_mul, pairExpSum_artinHom, Finset.prod_mul_distrib]
    rw [ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg')]
    have hperm : ∏ k : Fin m, pairExpSum m (artinGen m g (artinWord m w k).1).2 =
        ∏ p : Fin m, pairExpSum m (artinGen m g p).2 := by
      simp only [artinWord_fst_eq_strandPerm_apoly]
      exact Equiv.prod_comp (strandPerm m w) (fun p ↦ pairExpSum m (artinGen m g p).2)
    rw [hperm, prod_pairExpSum_artinGen m g hg, ← ofAdd_add]
    simp only [writhe, List.map_cons, List.sum_cons]
    rw [add_comm]

/-- A permutation of `Fin m` whose powers move `x` everywhere has minimal period `m` at `x`. -/
private theorem minimalPeriod_eq_of_transitive_apoly {m : ℕ} (σ : Equiv.Perm (Fin m))
    (x : Fin m) (h : ∀ j, ∃ k : ℕ, (σ ^ k) x = j) : Function.minimalPeriod σ x = m := by
  have hx : x ∈ Function.periodicPts σ := σ.injective.mem_periodicPts x
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts hx
  refine le_antisymm (by simpa using Function.minimalPeriod_le_card (f := σ) (x := x)) ?_
  have hs : Function.Surjective fun i : Fin (Function.minimalPeriod σ x) ↦ σ^[i] x := by
    intro j
    obtain ⟨k, hk⟩ := h j
    refine ⟨⟨k % Function.minimalPeriod σ x, Nat.mod_lt _ hp⟩, ?_⟩
    simp only
    rw [Function.iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hk]
  simpa using Fintype.card_le_of_surjective _ hs

/-- Along the orbit of a transitive permutation a product runs over all points. -/
private theorem prod_iterate_of_transitive_apoly {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin m)
    (h : ∀ j, ∃ k : ℕ, (σ ^ k) x = j) (F : Fin m → Multiplicative ℤ) :
    ((List.range m).map fun j ↦ F (σ^[j] x)).prod = ∏ t : Fin m, F t := by
  have hp := minimalPeriod_eq_of_transitive_apoly σ x h
  have hinj : Function.Injective fun j : Fin m ↦ σ^[j] x := by
    intro i j hij
    have := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x)
      (by rw [hp]; exact Set.mem_Iio.2 i.2) (by rw [hp]; exact Set.mem_Iio.2 j.2) hij
    exact Fin.ext this
  have hbij : Function.Bijective fun j : Fin m ↦ σ^[j] x :=
    (Finite.injective_iff_bijective).1 hinj
  rw [← Equiv.prod_comp (Equiv.ofBijective _ hbij) F, ← List.prod_ofFn]
  congr 1
  exact List.ext_getElem (by simp) fun i _ _ ↦ by simp

/-- The word of the preferred longitude has exponent sum zero. -/
private theorem pairExpSum_longitude_word (K : BraidKnot) :
    pairExpSum K.strands (((List.range K.strands).map fun j ↦
        (artinWord K.strands K.word
          ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod *
      (FreeGroup.of ⟨0, K.strands_pos⟩) ^ (-(writhe K.word))) = 1 := by
  have hπ : (fun k ↦ (artinWord K.strands K.word k).1) =
      ⇑(strandPerm K.strands K.word) := funext (artinWord_fst_eq_strandPerm_apoly _ _)
  have horb := prod_iterate_of_transitive_apoly (strandPerm K.strands K.word)
    ⟨0, K.strands_pos⟩ (K.connected _)
    (fun t ↦ pairExpSum K.strands (artinWord K.strands K.word t).2)
  rw [map_mul, map_list_prod, List.map_map, map_zpow, hπ]
  simp only [Function.comp_def] at horb ⊢
  rw [horb, prod_pairExpSum_artinWord _ _ K.isOnStrands, pairExpSum, FreeGroup.lift_apply_of,
    ← ofAdd_zsmul, ← ofAdd_add, smul_eq_mul, mul_one, add_neg_cancel, ofAdd_zero]

/-- The abelian representation: every generator goes to `diag(M, M⁻¹)`. -/
private noncomputable def pairDiagonal (M : ℂ) (hM : M ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![M, 0; 0, M⁻¹], by simp [Matrix.det_fin_two, hM]⟩

/-- The abelian line: every point `(M, 1)` with `M ≠ 0` is in the eigenvalue set of any knot
(abelian representation `x_j ↦ diag(M, M⁻¹)`, longitude `↦ 1`). -/
theorem mem_eigenvalueSet_of_L_eq_one (K : BraidKnot) {M : ℂ} (hM : M ≠ 0) :
    (M, (1 : ℂ)) ∈ eigenvalueSet K := by
  have hlift : FreeGroup.lift (fun _ : Fin K.strands ↦ pairDiagonal M hM) =
      (zpowersHom _ (pairDiagonal M hM)).comp (pairExpSum K.strands) :=
    FreeGroup.ext_hom _ _ fun k ↦ by simp [pairExpSum]
  have hrels : ∀ r ∈ artinRels K,
      FreeGroup.lift (fun _ : Fin K.strands ↦ pairDiagonal M hM) r = 1 := by
    rintro r ⟨k, rfl⟩
    rw [hlift, MonoidHom.comp_apply]
    have he : pairExpSum K.strands ((FreeGroup.of k)⁻¹ *
        ((artinWord K.strands K.word k).2 * FreeGroup.of (artinWord K.strands K.word k).1 *
          ((artinWord K.strands K.word k).2)⁻¹)) = 1 := by
      simp only [map_mul, map_inv, pairExpSum, FreeGroup.lift_apply_of]
      rw [mul_inv_cancel_comm, inv_mul_cancel]
    rw [he, map_one]
  have hl : PresentedGroup.toGroup hrels (longitude K) = 1 := by
    change FreeGroup.lift (fun _ : Fin K.strands ↦ pairDiagonal M hM) _ = 1
    rw [hlift, MonoidHom.comp_apply, pairExpSum_longitude_word, map_one]
  refine ⟨PresentedGroup.toGroup hrels, ?_, ?_, ?_, ?_⟩
  · rw [meridian, PresentedGroup.toGroup.of]
    simp [pairDiagonal]
  · rw [hl]
    simp
  · rw [meridian, PresentedGroup.toGroup.of]
    simp [pairDiagonal]
  · rw [hl]
    simp

/-- The value of `L - 1` at a point. -/
private theorem evalPoint_X_sub_one_apoly (p : ℂ × ℂ) :
    evalPoint (X - 1 : ℂ[X][X]) p = p.2 - 1 := by
  simp [evalPoint]

/-- Every point of the line `L = 1` is in the Zariski closure of the eigenvalue set. -/
private theorem mem_zariskiClosure_of_L_eq_one (K : BraidKnot) (z : ℂ) :
    (z, (1 : ℂ)) ∈ zariskiClosure (eigenvalueSet K) := by
  intro P hP
  have hval : ∀ m : ℂ, evalPoint P (m, 1) = (P.eval 1).eval m := fun m ↦ by simp [evalPoint]
  have hzero : P.eval 1 * X = 0 := Polynomial.funext fun x ↦ by
    rw [eval_mul, eval_X, eval_zero]
    rcases eq_or_ne x 0 with rfl | hx
    · exact mul_zero _
    · rw [← hval, hP _ (mem_eigenvalueSet_of_L_eq_one K hx), zero_mul]
  have hQ : P.eval 1 = 0 := (mul_eq_zero.1 hzero).resolve_right X_ne_zero
  rw [hval, hQ, eval_zero]

/-- The abelian line is retained: `L - 1` divides every A-polynomial over `ℂ`. -/
theorem sub_one_dvd_aPolynomial (K : BraidKnot) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet K) A) : (X - 1 : ℂ[X][X]) ∣ mapC A := by
  have hirr : Irreducible (X - 1 : ℂ[X][X]) := by
    simpa using irreducible_X_sub_C (1 : ℂ[X])
  refine (hA.2 _ hirr).2 fun p hp ↦ ?_
  rw [evalPoint_X_sub_one_apoly, sub_eq_zero] at hp
  obtain ⟨z, l⟩ := p
  dsimp only at hp
  rw [hp]
  exact mem_zariskiClosure_of_L_eq_one K z

end AJConjecture
