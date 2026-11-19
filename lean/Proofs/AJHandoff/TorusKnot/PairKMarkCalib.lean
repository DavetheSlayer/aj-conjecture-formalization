import Mathlib
import AJHandoff.TorusKnot.PairKTorusGroup
import AJHandoff.TorusKnot.PairKCoprodTorsion
import AJHandoff.TorusKnot.PairKAPolyHorizontal
import AJFamily.Classical.JonesMarkov
import AJFamily.Classical.TorusCompanionSL2

/-!
# Calibration of the peripheral pair and of the chirality conventions

The formal invariants are defined from a braid word: the coloured Jones function from the Kauffman
bracket of the cabled closed braid, the knot group as Artin's presentation with
`meridian K = x_0` and `longitude K` the word read along the strand, corrected by
`x_0 ^ (-writhe)`. This file records the facts that tie these definitions to the conventional
marked knot, for every braid knot and on the calibration knot (the closure of `σ_0³`).

* `commute_meridian_longitude`, `map_longitude_eq_one_of_commGroup`: for every braid knot the
  longitude commutes with the meridian and dies in every commutative quotient (it is
  null-homologous): the algebraic characterisation of a zero-framed longitude.
* `exists_hom_meridian_ofAdd_one`: the abelianisation sends the meridian to a generator of `ℤ`.
* `longitude_mul_meridian_pow_torusPairKnot`, `torusFullProd_pow_mem_center`: for the closure of
  the positive braid `(σ_0 ⋯ σ_(r-2))^s` the element `λ μ^(rs)` is the central element `Π^s`. In
  the standard marking this relation holds for the right-handed torus knot `T(r, s)`; the
  left-handed one has `λ μ^(-rs)` central.
* `coloredJones_two_trefoil`: the colour-2 invariant of the closure of `σ_0³` is
  `[2] · V(T⁻⁴)` with `V(t) = t + t³ - t⁴`, the Jones polynomial of the right-handed trefoil.
* `eigenvalueSet_trefoil_subset`, `mem_eigenvalueSet_trefoil`: the eigenvalue pairs of the closure
  of `σ_0³` lie on `(L - 1)(L M⁶ + 1) = 0`, and every point of `L M⁶ + 1 = 0` with `M ≠ 0` occurs.

So the same letter `(i, true)` is a positive crossing for the coloured Jones side and for the
peripheral side.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The pair `(2, 3)` is admissible. -/
theorem isTorusPair_two_three : IsTorusPair 2 3 :=
  ⟨le_refl 2, by norm_num, by decide⟩

/-- The exponent sum of a word of the free group, as an element of `Multiplicative ℤ`. -/
private def wordExpSum_calib (m : ℕ) : FreeGroup (Fin m) →* Multiplicative ℤ :=
  FreeGroup.lift fun _ ↦ Multiplicative.ofAdd 1

/-- Artin's action of a generator preserves the exponent sum. -/
private theorem wordExpSum_artinHom_calib (m : ℕ) (g : ℕ × Bool) (x : FreeGroup (Fin m)) :
    wordExpSum_calib m (artinHom m g x) = wordExpSum_calib m x := by
  have h : (wordExpSum_calib m).comp (artinHom m g) = wordExpSum_calib m := by
    refine FreeGroup.ext_hom _ _ fun k ↦ ?_
    simp only [MonoidHom.comp_apply, artinHom, FreeGroup.lift_apply_of, map_mul, map_inv,
      wordExpSum_calib]
    exact mul_inv_cancel_comm _ _
  exact DFunLike.congr_fun h x

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_calib (m : ℕ) (w : BraidWord) (k : Fin m) :
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
private theorem prod_wordExpSum_artinGen_calib (m : ℕ) (g : ℕ × Bool) (hg : g.1 + 1 < m) :
    ∏ p : Fin m, wordExpSum_calib m (artinGen m g p).2 =
      Multiplicative.ofAdd (if g.2 then (1 : ℤ) else -1) := by
  obtain ⟨i, b⟩ := g
  dsimp only at hg ⊢
  cases b with
  | true =>
    rw [Finset.prod_eq_single (⟨i, by omega⟩ : Fin m)]
    · simp [artinGen, hg, wordExpSum_calib]
    · intro p _ hp
      have hp' : (p : ℕ) ≠ i := fun h ↦ hp (Fin.ext h)
      simp only [artinGen, hg, dite_true, hp', ite_false]
      split_ifs <;> simp_all
    · simp
  | false =>
    rw [Finset.prod_eq_single (⟨i + 1, hg⟩ : Fin m)]
    · simp [artinGen, hg, wordExpSum_calib]
    · intro p _ hp
      have hp' : (p : ℕ) ≠ i + 1 := fun h ↦ hp (Fin.ext h)
      simp only [artinGen, hg, dite_true, hp', ite_false]
      split_ifs <;> simp_all
    · simp

/-- The conjugators of Artin's action of a braid word have total exponent sum its writhe. -/
private theorem prod_wordExpSum_artinWord_calib (m : ℕ) (w : BraidWord)
    (hw : IsOnStrands m w) :
    ∏ k : Fin m, wordExpSum_calib m (artinWord m w k).2 = Multiplicative.ofAdd (writhe w) := by
  induction w with
  | nil => simp [artinWord, writhe]
  | cons g w ih =>
    have hg : g.1 + 1 < m := hw g List.mem_cons_self
    simp only [artinWord, map_mul, wordExpSum_artinHom_calib, Finset.prod_mul_distrib]
    rw [ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg')]
    have hperm : ∏ k : Fin m, wordExpSum_calib m (artinGen m g (artinWord m w k).1).2 =
        ∏ p : Fin m, wordExpSum_calib m (artinGen m g p).2 := by
      simp only [artinWord_fst_eq_strandPerm_calib]
      exact Equiv.prod_comp (strandPerm m w) (fun p ↦ wordExpSum_calib m (artinGen m g p).2)
    rw [hperm, prod_wordExpSum_artinGen_calib m g hg, ← ofAdd_add]
    simp only [writhe, List.map_cons, List.sum_cons]
    rw [add_comm]

/-- A permutation of `Fin m` whose powers move `x` everywhere has minimal period `m` at `x`. -/
private theorem minimalPeriod_eq_of_transitive_calib {m : ℕ} (σ : Equiv.Perm (Fin m))
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
private theorem prod_iterate_of_transitive_calib {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin m)
    (h : ∀ j, ∃ k : ℕ, (σ ^ k) x = j) (F : Fin m → Multiplicative ℤ) :
    ((List.range m).map fun j ↦ F (σ^[j] x)).prod = ∏ t : Fin m, F t := by
  have hp := minimalPeriod_eq_of_transitive_calib σ x h
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

/-- The strand map of Artin's action, as a function, is the strand permutation. -/
private theorem artinWord_fst_fun_eq_calib (K : BraidKnot) :
    (fun k ↦ (artinWord K.strands K.word k).1) = ⇑(strandPerm K.strands K.word) :=
  funext (artinWord_fst_eq_strandPerm_calib _ _)

/-- The word of the preferred longitude has exponent sum zero. -/
private theorem wordExpSum_longitude_word_calib (K : BraidKnot) :
    wordExpSum_calib K.strands (((List.range K.strands).map fun j ↦
        (artinWord K.strands K.word
          ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod *
      (FreeGroup.of ⟨0, K.strands_pos⟩) ^ (-(writhe K.word))) = 1 := by
  have horb := prod_iterate_of_transitive_calib (strandPerm K.strands K.word)
    ⟨0, K.strands_pos⟩ (K.connected _)
    (fun t ↦ wordExpSum_calib K.strands (artinWord K.strands K.word t).2)
  rw [map_mul, map_list_prod, List.map_map, map_zpow, artinWord_fst_fun_eq_calib]
  simp only [Function.comp_def] at horb ⊢
  rw [horb, prod_wordExpSum_artinWord_calib _ _ K.isOnStrands, wordExpSum_calib,
    FreeGroup.lift_apply_of, ← ofAdd_zsmul, ← ofAdd_add, smul_eq_mul, mul_one, add_neg_cancel,
    ofAdd_zero]

/-- Each relator of Artin's presentation has exponent sum zero. -/
private theorem wordExpSum_artinRels_calib (K : BraidKnot) (r : FreeGroup (Fin K.strands))
    (hr : r ∈ artinRels K) : wordExpSum_calib K.strands r = 1 := by
  obtain ⟨k, rfl⟩ := hr
  simp only [map_mul, map_inv, wordExpSum_calib, FreeGroup.lift_apply_of]
  rw [mul_inv_cancel_comm, inv_mul_cancel]

/-- A homomorphism of the knot group that takes the same value on all the Artin generators sends
the longitude to `1`. -/
private theorem map_longitude_eq_one_of_const_calib (K : BraidKnot) {G : Type*} [Group G]
    (f : KnotGroup K →* G) (hf : ∀ k, f (PresentedGroup.of k) = f (meridian K)) :
    f (longitude K) = 1 := by
  have h : f (longitude K) = FreeGroup.lift (fun k ↦ f (PresentedGroup.of k))
      (((List.range K.strands).map fun j ↦
          (artinWord K.strands K.word
            ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod *
        (FreeGroup.of ⟨0, K.strands_pos⟩) ^ (-(writhe K.word))) :=
    map_presentedGroup_mk_eq_lift_of_braidRun f _
  have hlift : FreeGroup.lift (fun k : Fin K.strands ↦ f (PresentedGroup.of k)) =
      (zpowersHom G (f (meridian K))).comp (wordExpSum_calib K.strands) :=
    FreeGroup.ext_hom _ _ fun k ↦ by simp [wordExpSum_calib, hf]
  rw [h, hlift, MonoidHom.comp_apply, wordExpSum_longitude_word_calib, map_one]

/-- In the knot group, the generator of a strand is moved across its conjugating word to the
generator of the image strand. -/
private theorem knotGroup_of_mul_conj_calib (K : BraidKnot) (k : Fin K.strands) :
    (PresentedGroup.of k : KnotGroup K) *
        PresentedGroup.mk (artinRels K) (artinWord K.strands K.word k).2 =
      PresentedGroup.mk (artinRels K) (artinWord K.strands K.word k).2 *
        PresentedGroup.of (artinWord K.strands K.word k).1 := by
  have hmem : (FreeGroup.of k)⁻¹ *
      ((artinWord K.strands K.word k).2 * FreeGroup.of (artinWord K.strands K.word k).1 *
        ((artinWord K.strands K.word k).2)⁻¹) ∈ artinRels K := ⟨k, rfl⟩
  have h := PresentedGroup.one_of_mem hmem
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv, eq_mul_inv_iff_mul_eq] at h
  exact h

/-- The meridian is moved across the product of the first `j` conjugating words along the knot
to the generator of the `j`-th strand met. -/
private theorem meridian_mul_prod_conj_calib (K : BraidKnot) (j : ℕ) :
    meridian K * ((List.range j).map fun i ↦ PresentedGroup.mk (artinRels K)
        (artinWord K.strands K.word
          ((fun k ↦ (artinWord K.strands K.word k).1)^[i] ⟨0, K.strands_pos⟩)).2).prod =
      ((List.range j).map fun i ↦ PresentedGroup.mk (artinRels K)
        (artinWord K.strands K.word
          ((fun k ↦ (artinWord K.strands K.word k).1)^[i] ⟨0, K.strands_pos⟩)).2).prod *
        PresentedGroup.of ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩) := by
  induction j with
  | zero => simp [meridian]
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ← mul_assoc, ih, mul_assoc, knotGroup_of_mul_conj_calib, ← mul_assoc,
      Function.iterate_succ_apply']

/-- Following the knot once around returns to the strand `0`. -/
private theorem iterate_strands_zero_calib (K : BraidKnot) :
    (fun k ↦ (artinWord K.strands K.word k).1)^[K.strands] ⟨0, K.strands_pos⟩ =
      ⟨0, K.strands_pos⟩ := by
  rw [artinWord_fst_fun_eq_calib]
  have hp := minimalPeriod_eq_of_transitive_calib (strandPerm K.strands K.word)
    ⟨0, K.strands_pos⟩ (K.connected _)
  have h := Function.iterate_minimalPeriod (f := ⇑(strandPerm K.strands K.word))
    (x := ⟨0, K.strands_pos⟩)
  rwa [hp] at h

/-- The longitude commutes with the meridian. -/
theorem commute_meridian_longitude (K : BraidKnot) : Commute (meridian K) (longitude K) := by
  have hL : longitude K = ((List.range K.strands).map fun i ↦ PresentedGroup.mk (artinRels K)
      (artinWord K.strands K.word
        ((fun k ↦ (artinWord K.strands K.word k).1)^[i] ⟨0, K.strands_pos⟩)).2).prod *
      meridian K ^ (-(writhe K.word)) := by
    change PresentedGroup.mk (artinRels K) _ = _
    rw [map_mul, map_list_prod, List.map_map, map_zpow]
    rfl
  have h := meridian_mul_prod_conj_calib K K.strands
  rw [iterate_strands_zero_calib] at h
  rw [hL]
  exact Commute.mul_right h ((Commute.refl _).zpow_right _)

/-- The longitude is null-homologous: every homomorphism of the knot group to a commutative group
sends it to `1`. -/
theorem map_longitude_eq_one_of_commGroup (K : BraidKnot) {A : Type*} [CommGroup A]
    (f : KnotGroup K →* A) : f (longitude K) = 1 := by
  refine map_longitude_eq_one_of_const_calib K f fun k ↦ ?_
  obtain ⟨g, hg⟩ := exists_conj_meridian K k
  rw [hg, map_mul, map_mul, map_inv, mul_comm (f g), mul_inv_cancel_right]

/-- The abelianisation: a homomorphism of the knot group to `ℤ` sending the meridian to `1`. -/
theorem exists_hom_meridian_ofAdd_one (K : BraidKnot) :
    ∃ f : KnotGroup K →* Multiplicative ℤ, f (meridian K) = Multiplicative.ofAdd 1 := by
  have hrels : ∀ r ∈ artinRels K,
      FreeGroup.lift (fun _ : Fin K.strands ↦ Multiplicative.ofAdd (1 : ℤ)) r = 1 :=
    wordExpSum_artinRels_calib K
  refine ⟨PresentedGroup.toGroup hrels, ?_⟩
  rw [meridian, PresentedGroup.toGroup.of]

/-- Classical calibration: for the closure of the positive braid `(σ_0 ⋯ σ_(r-2))^s`,
`λ μ^(rs) = Π^s`. -/
theorem longitude_mul_meridian_pow_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    longitude (torusPairKnot r s h) * meridian (torusPairKnot r s h) ^ (r * s) =
      torusFullProd h ^ s := by
  rw [longitude_torusPairKnot, mul_assoc, ← zpow_natCast (meridian _) (r * s), ← zpow_add,
    neg_add_cancel, zpow_zero, mul_one]

/-- `Π^s` is central in the group of `T(r, s)`. -/
theorem torusFullProd_pow_mem_center {r s : ℕ} (h : IsTorusPair r s) :
    torusFullProd h ^ s ∈ Subgroup.center (KnotGroup (torusPairKnot r s h)) :=
  Subgroup.mem_center_iff.2 fun g ↦ (torusFullProd_pow_comm h g).symm

/-- The quantum trace of the identity on `m` strands is `δ^m`, with `δ = -t² - t⁻²`. -/
private theorem qtr_one_calib (m : ℕ) :
    qtr m (1 : SkMat m m) =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) ^ m := by
  rw [qtr, mul_one, skWeight, Matrix.trace_diagonal, ← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum]
  simp only [Fintype.sum_bool, skWeightEntry, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ite_true, Bool.false_eq_true, ite_false]
  ring

/-- The quantum trace is linear. -/
private theorem qtr_smul_add_smul_calib (n : ℕ) (x y : RatFunc ℚ) (A B : SkMat n n) :
    qtr n (x • A + y • B) = x * qtr n A + y * qtr n B := by
  simp only [qtr, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul]

/-- The cube of `a + b e` when `e² = δ e`. -/
private theorem kauffman_cube_calib {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (e : A) (δ a b : R) (he : e * e = δ • e) :
    (a • (1 : A) + b • e) * ((a • (1 : A) + b • e) * (a • (1 : A) + b • e)) =
      (a ^ 3) • (1 : A) + (3 * a ^ 2 * b + 3 * a * b ^ 2 * δ + b ^ 3 * δ ^ 2) • e := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, he, smul_smul,
    smul_add]
  module

/-- The cube of the positive crossing on two strands, by Kauffman's skein relation. -/
private theorem braidMatrix_cube_calib :
    braidMatrix 2 [(0, true), (0, true), (0, true)] =
      ((RatFunc.X : RatFunc ℚ) ^ 2 - (RatFunc.X⁻¹) ^ 2 + (RatFunc.X⁻¹) ^ 6) •
          crossingF 2 (0, true) +
        ((RatFunc.X : RatFunc ℚ)⁻¹ - (RatFunc.X⁻¹) ^ 5) • (1 : SkMat 2 2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hb : braidMatrix 2 [(0, true), (0, true), (0, true)] =
      crossingF 2 (0, true) * (crossingF 2 (0, true) * crossingF 2 (0, true)) := by
    simp [braidMatrix]
  rw [hb, crossingF_pos, kauffman_cube_calib _ _ _ _ (tlGenF_mul_self 2 0), smul_add, smul_smul,
    smul_smul, add_right_comm (_ • (1 : SkMat 2 2)), ← add_smul]
  congr 2
  · field_simp
    ring
  · simp only [zpow_neg, zpow_ofNat]
    field_simp
    ring

/-- The Kauffman bracket of the closure of `σ_0³`. -/
private theorem bracket_two_cube_calib :
    bracket 2 [(0, true), (0, true), (0, true)] =
      (T 7 : ℤ[T;T⁻¹]) + T 3 + T (-1) - T (-9) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : qtr 2 (crossingF 2 (0, true)) = -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) *
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) := by
    have h := qtr_braidMatrix_stabilise 1 [] true (fun g hg ↦ by simp at hg) one_pos
    simpa [braidMatrix, qtr_one_calib] using h
  apply laurentToField_injective
  rw [laurentToField_bracket, braidMatrix_cube_calib, qtr_smul_add_smul_calib, h1, qtr_one_calib]
  simp only [map_add, map_sub, laurentToField_T, zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- Quantum calibration: the colour-2 invariant of the closure of `σ_0³` is `[2] · V(T⁻⁴)` with
`V(t) = t + t³ - t⁴`, the Jones polynomial of the right-handed trefoil. -/
theorem coloredJones_two_trefoil :
    coloredJones (torusPairKnot 2 3 isTorusPair_two_three) 2 =
      ((T 2 : ℤ[T;T⁻¹]) + T (-2)) * (T (-4) + T (-12) - T (-16)) := by
  have hw : (torusPairKnot 2 3 isTorusPair_two_three).word =
      [(0, true), (0, true), (0, true)] := by
    simp [torusPairKnot, torusPairWord]
  have hwr : writhe [(0, true), (0, true), (0, true)] = 3 := by
    simp [writhe]
  rw [coloredJones_two_eq_jones2, jones2]
  simp only [hw, hwr]
  rw [show (torusPairKnot 2 3 isTorusPair_two_three).strands = 2 from rfl,
    bracket_two_cube_calib]
  simp only [mul_add, add_mul, mul_sub, ← T_add]
  norm_num
  ring

/-- A tuple fixed by the run of the braid word satisfies the relators of Artin's presentation. -/
private theorem lift_artinRels_of_fixed_calib (K : BraidKnot) {G : Type*} [Group G]
    (f : Fin K.strands → G) (hfix : (braidRun K.strands K.word f).1 = f) :
    ∀ r ∈ artinRels K, FreeGroup.lift f r = 1 := by
  rintro r ⟨k, rfl⟩
  have h := braidRun_fst_apply K.strands K.word f k
  rw [hfix] at h
  rw [map_mul, map_inv, map_mul, map_mul, map_inv, FreeGroup.lift_apply_of,
    FreeGroup.lift_apply_of, lift_artinWord_snd, ← h, inv_mul_cancel]

/-- Artin's action of `σ_0³` on a pair: conjugation of the swapped pair by `f_0 f_1 f_0`. -/
private theorem braidRun_trefoil_fst_calib {G : Type*} [Group G] (f : Fin 2 → G) (k : Fin 2) :
    (braidRun 2 (torusPairWord 2 3) f).1 k =
      f 0 * f 1 * f 0 * f (k + 1) * (f 0 * f 1 * f 0)⁻¹ := by
  rw [braidRun_torusPairWord_fst two_pos]
  fin_cases k <;> simp [List.range_succ, mul_assoc]

/-- Powers of an upper triangular `2 × 2` matrix are upper triangular, with the powers of the
top-left entry in the top-left corner. -/
private theorem upperTriangular_pow_calib (U : Matrix (Fin 2) (Fin 2) ℂ) (h : U 1 0 = 0)
    (n : ℕ) : (U ^ n) 1 0 = 0 ∧ (U ^ n) 0 0 = U 0 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, ih.1,
      ih.2, h, pow_succ]
    simp

/-- Classical calibration on the predicate itself: every eigenvalue pair of the closure of `σ_0³`
lies on `(L - 1)(L M⁶ + 1) = 0`. -/
theorem eigenvalueSet_trefoil_subset {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet (torusPairKnot 2 3 isTorusPair_two_three)) :
    p.2 = 1 ∨ p.2 * p.1 ^ 6 = -1 := by
  obtain ⟨ρ, hm, -, hM, hL⟩ := hp
  set f : Fin 2 → Matrix.SpecialLinearGroup (Fin 2) ℂ := fun k ↦ ρ (PresentedGroup.of k)
  have hfix : (braidRun 2 (torusPairWord 2 3) f).1 = f :=
    braidRun_fst_of_hom (torusPairKnot 2 3 isTorusPair_two_three) ρ
  have hrel : (f 0 * f 1) ^ 1 * f 0 = f 1 * (f 0 * f 1) ^ 1 := by
    have h0 := congrFun hfix 0
    rw [braidRun_trefoil_fst_calib, mul_inv_eq_iff_eq_mul] at h0
    simp only [mul_assoc, zero_add, pow_one] at h0 ⊢
    exact (mul_left_cancel h0).symm
  rcases torus_rel_eq_or_center_eq_neg_one 1 (f 0) (f 1) hrel with heq | hneg
  · left
    have hone : ρ (longitude (torusPairKnot 2 3 isTorusPair_two_three)) = 1 := by
      refine map_longitude_eq_one_of_const_calib _ ρ ?_
      change ∀ k : Fin 2, f k = f 0
      intro k
      fin_cases k
      · rfl
      · exact heq.symm
    rw [← hL, hone]
    simp
  · right
    have hprod : ρ (torusFullProd isTorusPair_two_three) = f 0 * f 1 := by
      rw [torusFullProd, map_list_prod]
      refine (congrArg List.prod List.map_map).trans ?_
      change ((List.finRange 2).map f).prod = _
      simp [List.finRange_succ]
    have h1 := congrArg ρ (longitude_mul_meridian_pow_torusPairKnot isTorusPair_two_three)
    rw [map_mul, map_pow, map_pow, hprod] at h1
    have h2 := congrArg Subtype.val h1
    have hneg3 : ((f 0 * f 1) ^ 3).1 = -1 := hneg
    rw [hneg3, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] at h2
    obtain ⟨hU10, hU00⟩ := upperTriangular_pow_calib _ hm (2 * 3)
    have h00 := congrFun (congrFun h2 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hU10, hU00, hM, hL, mul_zero, add_zero] at h00
    simpa using h00

/-- The meridian matrix `!![M, 1; 0, M⁻¹]` of the irreducible representations of the group of the
closure of `σ_0³`. -/
private def trefoilUpper_calib (M : ℂ) (hM : M ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![M, 1; 0, M⁻¹], by simp [Matrix.det_fin_two, hM]⟩

/-- The image `!![M, 0; -(M² - 1 + M⁻²), M⁻¹]` of the second generator. -/
private def trefoilLower_calib (M : ℂ) (hM : M ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![M, 0; -(M ^ 2 - 1 + M⁻¹ ^ 2), M⁻¹], by simp [Matrix.det_fin_two, hM]⟩

/-- The two matrices satisfy the braid relation. -/
private theorem trefoilUpper_mul_trefoilLower_calib (M : ℂ) (hM : M ≠ 0) :
    trefoilUpper_calib M hM * trefoilLower_calib M hM * trefoilUpper_calib M hM =
      trefoilLower_calib M hM * trefoilUpper_calib M hM * trefoilLower_calib M hM := by
  have hA : (trefoilUpper_calib M hM).1 = !![M, 1; 0, M⁻¹] := rfl
  have hB : (trefoilLower_calib M hM).1 = !![M, 0; -(M ^ 2 - 1 + M⁻¹ ^ 2), M⁻¹] := rfl
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hA, hB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    ring

/-- Every point of `L M⁶ + 1 = 0` with `M ≠ 0` is an eigenvalue pair of the closure of `σ_0³`. -/
theorem mem_eigenvalueSet_trefoil {M : ℂ} (hM : M ≠ 0) :
    (M, -(M ^ 6)⁻¹) ∈ eigenvalueSet (torusPairKnot 2 3 isTorusPair_two_three) := by
  have hAc : (trefoilUpper_calib M hM).1 = !![M, 1; 0, M⁻¹] := rfl
  have hBc : (trefoilLower_calib M hM).1 = !![M, 0; -(M ^ 2 - 1 + M⁻¹ ^ 2), M⁻¹] := rfl
  set A := trefoilUpper_calib M hM
  set B := trefoilLower_calib M hM
  have hbr : A * B * A = B * A * B := trefoilUpper_mul_trefoilLower_calib M hM
  have h0 : A * B * A * B = A * (A * B * A) :=
    calc A * B * A * B = A * (B * A * B) := by simp only [mul_assoc]
      _ = A * (A * B * A) := by rw [hbr]
  have h1 : A * B * A * A = B * (A * B * A) :=
    calc A * B * A * A = B * A * B * A := by rw [hbr]
      _ = B * (A * B * A) := by simp only [mul_assoc]
  have hfix : (braidRun 2 (torusPairWord 2 3) ![A, B]).1 = ![A, B] := by
    funext k
    rw [braidRun_trefoil_fst_calib, mul_inv_eq_iff_eq_mul]
    fin_cases k
    · simpa using h0
    · simpa using h1
  have hrels := lift_artinRels_of_fixed_calib (torusPairKnot 2 3 isTorusPair_two_three)
    ![A, B] hfix
  set ρ := PresentedGroup.toGroup hrels
  have hgen : (fun k : Fin 2 ↦ ρ (PresentedGroup.of k)) = ![A, B] :=
    funext fun k ↦ PresentedGroup.toGroup.of hrels
  have hmer : ρ (meridian (torusPairKnot 2 3 isTorusPair_two_three)) = A :=
    congrFun hgen 0
  have hprod : ρ (torusFullProd isTorusPair_two_three) = A * B := by
    rw [torusFullProd, map_list_prod]
    refine (congrArg List.prod List.map_map).trans ?_
    change ((List.finRange 2).map fun k : Fin 2 ↦ ρ (PresentedGroup.of k)).prod = _
    rw [hgen]
    simp [List.finRange_succ]
  have h2 := congrArg ρ (longitude_mul_meridian_pow_torusPairKnot isTorusPair_two_three)
  rw [map_mul, map_pow, map_pow, hprod, hmer] at h2
  have hne : A ≠ B := by
    intro h
    have h' := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℂ ↦ X.1 0 1) h
    simp [hAc, hBc] at h'
  have hneg : ((A * B) ^ 3).1 = -1 :=
    (torus_rel_eq_or_center_eq_neg_one 1 A B (by rw [pow_one, hbr, mul_assoc])).resolve_left hne
  have hlam : (ρ (longitude (torusPairKnot 2 3 isTorusPair_two_three))).1 =
      -((A⁻¹).1 ^ (2 * 3)) := by
    have h3 : ρ (longitude (torusPairKnot 2 3 isTorusPair_two_three)) =
        (A * B) ^ 3 * A⁻¹ ^ (2 * 3) := by
      rw [← h2, inv_pow, mul_inv_cancel_right]
    rw [h3, Matrix.SpecialLinearGroup.coe_mul, hneg, Matrix.SpecialLinearGroup.coe_pow,
      neg_one_mul]
  have hAi : (A⁻¹).1 = !![M⁻¹, -1; 0, M] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hAc, Matrix.adjugate_fin_two_of, neg_zero]
  obtain ⟨h10, h00⟩ := upperTriangular_pow_calib (A⁻¹).1 (by rw [hAi]; rfl) (2 * 3)
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · rw [hmer, hAc]
    rfl
  · rw [hlam, Matrix.neg_apply, h10, neg_zero]
  · rw [hmer, hAc]
    rfl
  · rw [hlam, Matrix.neg_apply, h00, hAi]
    simp

end AJConjecture
