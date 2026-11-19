import Mathlib
import AJTwist.Knot.TwKMirrorJones
import AJConjecture.APolynomial
import AJHandoff.TorusKnot.PairKMarkCalib
import AJConjecture.SkeinThickGenReverse
import AJConjecture.SkeinBracketTrace
import AJConjecture.SkeinThickCableBasic

/-!
# The knot group and the eigenvalue set of the mirror image

Two closed braids represent the mirror image of the closure of `w`: the mirror word
`mirrorWord w` (every crossing reversed; `BraidKnot.mirror`) and the inverse word
`invWord w = (mirrorWord w).reverse` (`BraidKnot.inv`). Their closures differ by a rotation that
reverses the orientation of the knot.

* For the **inverse word** everything is immediate from Artin's presentation: the relators
  `x_k = β⁻¹ · x_k` generate the same normal subgroup as `x_k = β · x_k`, so the knot group is the
  same quotient of the same free group; the meridian is the same generator, and the conjugating
  words met along the knot are the inverses in the opposite order, so the longitude is inverted
  (`exists_knotGroup_inv_equiv`). Hence `eigenvalueSet K.inv = {(M, L⁻¹)}`.
* Every eigenvalue set is invariant under `(M, L) ↦ (M⁻¹, L⁻¹)` (`eigenvalueSet_symm`: the
  meridian and the longitude commute, `commute_meridian_longitude`; take the other common
  eigenvector, or the same one in the parabolic case). So `eigenvalueSet K.inv = {(M⁻¹, L)}`,
  the form used in the paper.
* For the **mirror word** the same description holds, but its proof would need the invariance of
  the eigenvalue set under reversal of the braid word (a change of base point of the Wirtinger
  generators). It is not needed: the mirror families are defined with `BraidKnot.inv`
  (`twFamilyKnot`).

Tested with the library's formulas (`SCR/K/tools/chk_group.py`, `chk_group2.py`): for `T(2,3)` on
two and three strands and for the knot `5_2` on three strands, the pairs of `K.mirror` and of
`K.inv` are the pairs `(M, L⁻¹)` of `K`, and the pairs of `K` at `M⁻¹` are the `L⁻¹` at `M`.
-/

open LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The matrix of the cable of the reversed word is the transpose of the matrix of the cable. -/
private theorem braidMatrix_cable_reverse_mirrorGroup (n c : ℕ) (w : BraidWord) :
    braidMatrix n (cable c w.reverse) = (braidMatrix n (cable c w)).transpose := by
  induction w with
  | nil => exact (Matrix.transpose_one).symm
  | cons g w ih =>
    have h1 : cable c (g :: w).reverse = cable c w.reverse ++ cableGen c g := by
      simp [cable]
    have h2 : cable c (g :: w) = cableGen c g ++ cable c w := by
      simp [cable]
    have h3 : (braidMatrix n (cableGen c g)).transpose = braidMatrix n (cableGen c g) := by
      rw [cableGen_eq_thickCross, braidMatrix_thickCross_transpose]
    rw [h1, h2, braidMatrix_append, braidMatrix_append, Matrix.transpose_mul, ih, h3]

/-- The bracket of a cable does not change when the word is reversed. -/
private theorem bracket_cable_reverse_mirrorGroup (n c : ℕ) (w : BraidWord) :
    bracket n (cable c w.reverse) = bracket n (cable c w) := by
  rw [← bracket_reverse n (cable c w)]
  apply laurentToField_injective
  rw [laurentToField_bracket, laurentToField_bracket, braidMatrix_cable_reverse_mirrorGroup,
    braidMatrix_transpose]

/-- The coloured Jones polynomials of the two mirror braids agree. -/
private theorem coloredJonesPos_inv_mirrorGroup (K : BraidKnot) (k : ℕ) :
    coloredJonesPos K.inv k = coloredJonesPos K.mirror k := by
  have hw : K.inv.word = (mirrorWord K.word).reverse := rfl
  have hw' : K.mirror.word = mirrorWord K.word := rfl
  have hs : K.inv.strands = K.strands := rfl
  have hs' : K.mirror.strands = K.strands := rfl
  have hwr : writhe (mirrorWord K.word).reverse = writhe (mirrorWord K.word) := by
    simp only [writhe, List.map_reverse, List.sum_reverse]
  have hch : chebyshevBracket K.strands (mirrorWord K.word).reverse k =
      chebyshevBracket K.strands (mirrorWord K.word) k := by
    simp only [chebyshevBracket, bracket_cable_reverse_mirrorGroup]
  rw [coloredJonesPos, coloredJonesPos, hw, hw', hs, hs', hwr, hch]

/-- The coloured Jones functions of the two mirror braids agree. -/
theorem coloredJones_inv (K : BraidKnot) (n : ℤ) :
    coloredJones K.inv n = laurentBar (coloredJones K n) := by
  rw [← coloredJones_mirror]
  simp only [coloredJones, coloredJonesPos_inv_mirrorGroup]

/-- Artin's action of a braid word, as an endomorphism of the free group. -/
private def artinWordHom_mirrorGroup (m : ℕ) :
    BraidWord → (FreeGroup (Fin m) →* FreeGroup (Fin m))
  | [] => MonoidHom.id _
  | g :: w => (artinHom m g).comp (artinWordHom_mirrorGroup m w)

/-- Artin's action of a word on a generator is the conjugate recorded by `artinWord`. -/
private theorem artinWordHom_of_mirrorGroup (m : ℕ) (w : BraidWord) (k : Fin m) :
    artinWordHom_mirrorGroup m w (FreeGroup.of k) =
      (artinWord m w k).2 * FreeGroup.of (artinWord m w k).1 * ((artinWord m w k).2)⁻¹ := by
  induction w with
  | nil => simp [artinWordHom_mirrorGroup, artinWord]
  | cons g w ih =>
    rw [artinWordHom_mirrorGroup, MonoidHom.comp_apply, ih]
    simp only [artinWord, map_mul, map_inv, artinHom, FreeGroup.lift_apply_of, mul_inv_rev,
      mul_assoc]

/-- Artin's action is multiplicative on words. -/
private theorem artinWordHom_append_mirrorGroup (m : ℕ) (u v : BraidWord) :
    artinWordHom_mirrorGroup m (u ++ v) =
      (artinWordHom_mirrorGroup m u).comp (artinWordHom_mirrorGroup m v) := by
  induction u with
  | nil => rfl
  | cons g u ih =>
    rw [List.cons_append, artinWordHom_mirrorGroup, ih, artinWordHom_mirrorGroup,
      MonoidHom.comp_assoc]

/-- The strand and the conjugating word of a concatenation. -/
private theorem artinWord_append_mirrorGroup (m : ℕ) (u v : BraidWord) (k : Fin m) :
    artinWord m (u ++ v) k = ((artinWord m u (artinWord m v k).1).1,
      artinWordHom_mirrorGroup m u (artinWord m v k).2 *
        (artinWord m u (artinWord m v k).1).2) := by
  induction u with
  | nil => simp [artinWord, artinWordHom_mirrorGroup]
  | cons g u ih =>
    rw [List.cons_append, artinWord, ih]
    simp only [artinWord, artinWordHom_mirrorGroup, MonoidHom.comp_apply, map_mul, mul_assoc]

/-- The strand maps of a letter and of its inverse are inverse to each other. -/
private theorem artinGen_not_fst_mirrorGroup (m : ℕ) (g : ℕ × Bool) (k : Fin m) :
    (artinGen m (g.1, !g.2) (artinGen m g k).1).1 = k := by
  obtain ⟨i, s⟩ := g
  by_cases h : i + 1 < m
  · by_cases h1 : (k : ℕ) = i
    · simp [artinGen, h, h1, Fin.ext_iff]
    · by_cases h2 : (k : ℕ) = i + 1
      · simp [artinGen, h, h2, Fin.ext_iff]
      · simp [artinGen, h, h1, h2]
  · simp [artinGen, h]

/-- The conjugating words of a letter and of its inverse cancel. -/
private theorem artinGen_not_snd_mirrorGroup (m : ℕ) (g : ℕ × Bool) (k : Fin m) :
    artinHom m (g.1, !g.2) (artinGen m g k).2 * (artinGen m (g.1, !g.2) (artinGen m g k).1).2 =
      1 := by
  obtain ⟨i, s⟩ := g
  by_cases h : i + 1 < m
  · by_cases h1 : (k : ℕ) = i
    · cases s <;> simp [artinGen, artinHom, h, h1]
    · by_cases h2 : (k : ℕ) = i + 1
      · cases s <;> simp [artinGen, artinHom, h, h2]
      · simp [artinGen, h, h1, h2]
  · simp [artinGen, h]

/-- Artin's actions of a letter and of its inverse are inverse to each other. -/
private theorem artinHom_not_comp_mirrorGroup (m : ℕ) (g : ℕ × Bool) :
    (artinHom m (g.1, !g.2)).comp (artinHom m g) = MonoidHom.id _ := by
  refine FreeGroup.ext_hom _ _ fun k ↦ ?_
  have h1 := artinGen_not_fst_mirrorGroup m g k
  have h2 := artinGen_not_snd_mirrorGroup m g k
  have h3 : artinHom m (g.1, !g.2) (FreeGroup.of (artinGen m g k).1) =
      (artinGen m (g.1, !g.2) (artinGen m g k).1).2 * FreeGroup.of k *
        ((artinGen m (g.1, !g.2) (artinGen m g k).1).2)⁻¹ := by
    conv_lhs => rw [artinHom, FreeGroup.lift_apply_of]
    rw [h1]
  have h4 : artinHom m g (FreeGroup.of k) =
      (artinGen m g k).2 * FreeGroup.of (artinGen m g k).1 * ((artinGen m g k).2)⁻¹ := by
    rw [artinHom, FreeGroup.lift_apply_of]
  rw [MonoidHom.comp_apply, MonoidHom.id_apply, h4, map_mul, map_mul, map_inv, h3,
    ← mul_assoc, ← mul_assoc, h2, one_mul, mul_assoc, ← mul_inv_rev, h2, inv_one, mul_one]

/-- The inverse word of a word with a first letter. -/
private theorem invWord_cons_mirrorGroup (g : ℕ × Bool) (w : BraidWord) :
    invWord (g :: w) = invWord w ++ [(g.1, !g.2)] := by
  simp [invWord, mirrorWord]

/-- The inverse word of the inverse word is the word. -/
private theorem invWord_invWord_mirrorGroup (w : BraidWord) : invWord (invWord w) = w := by
  simp [invWord, mirrorWord, List.map_reverse, Function.comp_def]

/-- The strand and the conjugating word of a single letter. -/
private theorem artinWord_singleton_mirrorGroup (m : ℕ) (g : ℕ × Bool) (k : Fin m) :
    artinWord m [g] k = artinGen m g k := by
  simp [artinWord]

/-- The strand maps of a word and of its inverse word are inverse to each other. -/
private theorem artinWord_invWord_fst_mirrorGroup (m : ℕ) (w : BraidWord) (k : Fin m) :
    (artinWord m (invWord w) (artinWord m w k).1).1 = k := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    rw [invWord_cons_mirrorGroup, artinWord_append_mirrorGroup, artinWord_singleton_mirrorGroup]
    simp only [artinWord]
    rw [artinGen_not_fst_mirrorGroup, ih]

/-- The conjugating words of a word and of its inverse word cancel, exactly in the free group. -/
private theorem artinWordHom_invWord_snd_mirrorGroup (m : ℕ) (w : BraidWord) (k : Fin m) :
    artinWordHom_mirrorGroup m (invWord w) (artinWord m w k).2 *
      (artinWord m (invWord w) (artinWord m w k).1).2 = 1 := by
  induction w with
  | nil => simp [invWord, mirrorWord, artinWord, artinWordHom_mirrorGroup]
  | cons g w ih =>
    have hg := artinGen_not_snd_mirrorGroup m g (artinWord m w k).1
    have hc := DFunLike.congr_fun (artinHom_not_comp_mirrorGroup m g) (artinWord m w k).2
    rw [MonoidHom.comp_apply, MonoidHom.id_apply] at hc
    rw [invWord_cons_mirrorGroup, artinWord_append_mirrorGroup, artinWordHom_append_mirrorGroup,
      artinWord_singleton_mirrorGroup]
    simp only [artinWord, MonoidHom.comp_apply, artinWordHom_mirrorGroup, MonoidHom.id_apply,
      map_mul]
    rw [hc, artinGen_not_fst_mirrorGroup, mul_assoc,
      ← mul_assoc (artinWordHom_mirrorGroup m (invWord w) (artinHom m (g.1, !g.2) _)),
      ← map_mul, hg, map_one, one_mul, ih]

/-- Artin's actions of a word and of its inverse word are inverse to each other. -/
private theorem artinWordHom_invWord_comp_mirrorGroup (m : ℕ) (w : BraidWord) :
    (artinWordHom_mirrorGroup m (invWord w)).comp (artinWordHom_mirrorGroup m w) =
      MonoidHom.id _ := by
  refine FreeGroup.ext_hom _ _ fun k ↦ ?_
  have h1 := artinWord_invWord_fst_mirrorGroup m w k
  have h2 := artinWordHom_invWord_snd_mirrorGroup m w k
  have h3 := artinWordHom_of_mirrorGroup m (invWord w) (artinWord m w k).1
  rw [h1] at h3
  rw [MonoidHom.comp_apply, MonoidHom.id_apply, artinWordHom_of_mirrorGroup, map_mul, map_mul,
    map_inv, h3, ← mul_assoc, ← mul_assoc, h2, one_mul, mul_assoc, ← mul_inv_rev, h2, inv_one,
    mul_one]

/-- In the group of the closed braid, Artin's action of the braid word is trivial. -/
private theorem mk_comp_artinWordHom_mirrorGroup (K : BraidKnot) :
    (PresentedGroup.mk (artinRels K)).comp (artinWordHom_mirrorGroup K.strands K.word) =
      PresentedGroup.mk (artinRels K) := by
  refine FreeGroup.ext_hom _ _ fun k ↦ ?_
  have hmem : (FreeGroup.of k)⁻¹ *
      ((artinWord K.strands K.word k).2 * FreeGroup.of (artinWord K.strands K.word k).1 *
        ((artinWord K.strands K.word k).2)⁻¹) ∈ artinRels K := ⟨k, rfl⟩
  have h := PresentedGroup.one_of_mem hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  rw [MonoidHom.comp_apply, artinWordHom_of_mirrorGroup]
  exact h.symm

/-- In the group of the closed braid, Artin's action of a right inverse of the braid is
trivial. -/
private theorem mk_comp_artinWordHom_of_comp_mirrorGroup (K : BraidKnot) (w' : BraidWord)
    (h : (artinWordHom_mirrorGroup K.strands K.word).comp (artinWordHom_mirrorGroup K.strands w') =
      MonoidHom.id _) :
    (PresentedGroup.mk (artinRels K)).comp (artinWordHom_mirrorGroup K.strands w') =
      PresentedGroup.mk (artinRels K) := by
  conv_lhs => rw [← mk_comp_artinWordHom_mirrorGroup K, MonoidHom.comp_assoc, h, MonoidHom.comp_id]

/-- The Artin relators of a right inverse of the braid lie in the normal closure of the Artin
relators of the braid. -/
private theorem artinRel_mem_normalClosure_mirrorGroup (K : BraidKnot) (w' : BraidWord)
    (h : (artinWordHom_mirrorGroup K.strands K.word).comp (artinWordHom_mirrorGroup K.strands w') =
      MonoidHom.id _) (k : Fin K.strands) :
    (FreeGroup.of k)⁻¹ * ((artinWord K.strands w' k).2 * FreeGroup.of (artinWord K.strands w' k).1 *
      ((artinWord K.strands w' k).2)⁻¹) ∈ Subgroup.normalClosure (artinRels K) := by
  have h1 := DFunLike.congr_fun (mk_comp_artinWordHom_of_comp_mirrorGroup K w' h) (FreeGroup.of k)
  rw [MonoidHom.comp_apply, artinWordHom_of_mirrorGroup] at h1
  refine (QuotientGroup.eq_one_iff _).1 ?_
  change PresentedGroup.mk (artinRels K) _ = 1
  rw [map_mul, map_inv, h1, inv_mul_cancel]

/-- Two sets of relators, each in the normal closure of the other, have the same normal
closure. -/
private theorem normalClosure_eq_of_subset_mirrorGroup {α : Type*} (R R' : Set (FreeGroup α))
    (h : R ⊆ Subgroup.normalClosure R') (h' : R' ⊆ Subgroup.normalClosure R) :
    Subgroup.normalClosure R = Subgroup.normalClosure R' :=
  le_antisymm (Subgroup.normalClosure_le_normal h) (Subgroup.normalClosure_le_normal h')

/-- The Artin relators of the inverse braid and of the braid have the same normal closure. -/
private theorem normalClosure_artinRels_inv_mirrorGroup (K : BraidKnot) :
    Subgroup.normalClosure (artinRels K.inv) = Subgroup.normalClosure (artinRels K) := by
  have h1 := artinWordHom_invWord_comp_mirrorGroup K.strands (invWord K.word)
  rw [invWord_invWord_mirrorGroup] at h1
  have h2 := artinWordHom_invWord_comp_mirrorGroup K.strands K.word
  refine normalClosure_eq_of_subset_mirrorGroup (α := Fin K.strands) (artinRels K.inv)
    (artinRels K) ?_ ?_
  · rintro r ⟨k, rfl⟩
    exact artinRel_mem_normalClosure_mirrorGroup K (invWord K.word) h1 k
  · rintro r ⟨k, rfl⟩
    exact artinRel_mem_normalClosure_mirrorGroup K.inv K.word h2 k

/-- Presented groups whose relators have the same normal closure are the same quotient. -/
private theorem exists_presentedGroup_equiv_mirrorGroup {α : Type*} (R R' : Set (FreeGroup α))
    (h : Subgroup.normalClosure R' = Subgroup.normalClosure R) :
    ∃ φ : PresentedGroup R' ≃* PresentedGroup R,
      ∀ x : FreeGroup α, φ (PresentedGroup.mk R' x) = PresentedGroup.mk R x :=
  ⟨QuotientGroup.quotientMulEquivOfEq h, fun _ ↦ rfl⟩

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_mirrorGroup (m : ℕ) (w : BraidWord) (k : Fin m) :
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

/-- A permutation of `Fin m` whose powers move `x` everywhere has minimal period `m` at `x`. -/
private theorem minimalPeriod_eq_of_transitive_mirrorGroup {m : ℕ} (σ : Equiv.Perm (Fin m))
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

/-- Following the knot once around returns to the strand `0`. -/
private theorem iterate_strands_zero_mirrorGroup (K : BraidKnot) :
    (fun k ↦ (artinWord K.strands K.word k).1)^[K.strands] ⟨0, K.strands_pos⟩ =
      ⟨0, K.strands_pos⟩ := by
  have hfun : (fun k ↦ (artinWord K.strands K.word k).1) = ⇑(strandPerm K.strands K.word) :=
    funext (artinWord_fst_eq_strandPerm_mirrorGroup _ _)
  rw [hfun]
  have hp := minimalPeriod_eq_of_transitive_mirrorGroup (strandPerm K.strands K.word)
    ⟨0, K.strands_pos⟩ (K.connected _)
  have h := Function.iterate_minimalPeriod (f := ⇑(strandPerm K.strands K.word))
    (x := ⟨0, K.strands_pos⟩)
  rwa [hp] at h

/-- Following the inverse braid from the strand `0` runs through the orbit backwards. -/
private theorem iterate_invWord_zero_mirrorGroup (K : BraidKnot) (j : ℕ) (hj : j ≤ K.strands) :
    (fun k ↦ (artinWord K.strands (invWord K.word) k).1)^[j] ⟨0, K.strands_pos⟩ =
      (fun k ↦ (artinWord K.strands K.word k).1)^[K.strands - j] ⟨0, K.strands_pos⟩ := by
  induction j with
  | zero => rw [Function.iterate_zero, id, Nat.sub_zero, iterate_strands_zero_mirrorGroup]
  | succ j ih =>
    obtain ⟨n, hn⟩ : ∃ n, K.strands - j = n + 1 := ⟨K.strands - j - 1, by omega⟩
    have hn' : K.strands - (j + 1) = n := by omega
    rw [Function.iterate_succ_apply', ih (by omega), hn, hn', Function.iterate_succ_apply']
    exact artinWord_invWord_fst_mirrorGroup _ _ _

/-- In the group of the closed braid, the conjugating word of the inverse braid at the image
strand is the inverse of the conjugating word of the braid. -/
private theorem mk_artinWord_invWord_snd_mirrorGroup (K : BraidKnot) (k : Fin K.strands) :
    PresentedGroup.mk (artinRels K)
        (artinWord K.strands (invWord K.word) (artinWord K.strands K.word k).1).2 =
      (PresentedGroup.mk (artinRels K) (artinWord K.strands K.word k).2)⁻¹ := by
  have h1 := artinWordHom_invWord_comp_mirrorGroup K.strands (invWord K.word)
  rw [invWord_invWord_mirrorGroup] at h1
  have h := congrArg (PresentedGroup.mk (artinRels K))
    (artinWordHom_invWord_snd_mirrorGroup K.strands K.word k)
  rw [map_mul, map_one, ← MonoidHom.comp_apply,
    mk_comp_artinWordHom_of_comp_mirrorGroup K _ h1] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The product of the inverses in the opposite order is the inverse of the product. -/
private theorem prod_range_inv_reverse_mirrorGroup {G : Type*} [Group G] (f : ℕ → G) (n : ℕ) :
    ((List.range n).map fun j ↦ (f (n - 1 - j))⁻¹).prod = ((List.range n).map f).prod⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : ((List.range (n + 1)).map fun j ↦ (f (n + 1 - 1 - j))⁻¹) =
        (f n)⁻¹ :: (List.range n).map fun j ↦ (f (n - 1 - j))⁻¹ := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ ↦ ?_
      simp only [Function.comp_apply]
      congr 2
      omega
    have hR : (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [hL, hR, List.prod_cons, ih, List.prod_append, List.prod_singleton, mul_inv_rev]

/-- In the group of the closed braid, the longitude word of the inverse braid is the inverse of
the longitude. -/
private theorem mk_longitude_word_invWord_mirrorGroup (K : BraidKnot) :
    PresentedGroup.mk (artinRels K)
      (((List.range K.strands).map fun j ↦
        (artinWord K.strands (invWord K.word)
          ((fun k ↦ (artinWord K.strands (invWord K.word) k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod *
        (FreeGroup.of ⟨0, K.strands_pos⟩) ^ (-(writhe (invWord K.word)))) = (longitude K)⁻¹ := by
  have hL : longitude K = ((List.range K.strands).map fun i ↦ PresentedGroup.mk (artinRels K)
      (artinWord K.strands K.word
        ((fun k ↦ (artinWord K.strands K.word k).1)^[i] ⟨0, K.strands_pos⟩)).2).prod *
      meridian K ^ (-(writhe K.word)) := by
    change PresentedGroup.mk (artinRels K) _ = _
    rw [map_mul, map_list_prod, List.map_map, map_zpow]
    rfl
  have hΛ : ((List.range K.strands).map fun i ↦ PresentedGroup.mk (artinRels K)
      (artinWord K.strands K.word
        ((fun k ↦ (artinWord K.strands K.word k).1)^[i] ⟨0, K.strands_pos⟩)).2).prod =
      longitude K * meridian K ^ writhe K.word := by
    rw [hL, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hprod : ((List.range K.strands).map fun j ↦ PresentedGroup.mk (artinRels K)
      (artinWord K.strands (invWord K.word)
        ((fun k ↦ (artinWord K.strands (invWord K.word) k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod =
      (longitude K * meridian K ^ writhe K.word)⁻¹ := by
    rw [← hΛ, ← prod_range_inv_reverse_mirrorGroup]
    congr 1
    refine List.map_congr_left fun j hj ↦ ?_
    have hj' : j < K.strands := List.mem_range.1 hj
    obtain ⟨n, hn⟩ : ∃ n, K.strands - j = n + 1 := ⟨K.strands - j - 1, by omega⟩
    have hn' : K.strands - 1 - j = n := by omega
    rw [iterate_invWord_zero_mirrorGroup K j hj'.le, hn, hn', Function.iterate_succ_apply']
    exact mk_artinWord_invWord_snd_mirrorGroup K _
  have hcomm := commute_meridian_longitude K
  rw [map_mul, map_list_prod, List.map_map, map_zpow]
  change ((List.range K.strands).map fun j ↦ PresentedGroup.mk (artinRels K)
      (artinWord K.strands (invWord K.word)
        ((fun k ↦ (artinWord K.strands (invWord K.word) k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod *
      meridian K ^ (-(writhe (invWord K.word))) = _
  rw [hprod, writhe_invWord, neg_neg, mul_inv_rev, mul_assoc, ← zpow_neg]
  have h2 : Commute ((longitude K)⁻¹) (meridian K ^ writhe K.word) :=
    (hcomm.symm.inv_left).zpow_right _
  rw [h2.eq, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

/-- The knot group of the inverse braid is the knot group of the braid, with the same meridian
and the inverse longitude. -/
theorem exists_knotGroup_inv_equiv (K : BraidKnot) :
    ∃ φ : KnotGroup K.inv ≃* KnotGroup K,
      φ (meridian K.inv) = meridian K ∧ φ (longitude K.inv) = (longitude K)⁻¹ := by
  obtain ⟨φ, hφ⟩ := exists_presentedGroup_equiv_mirrorGroup (α := Fin K.strands) (artinRels K)
    (artinRels K.inv) (normalClosure_artinRels_inv_mirrorGroup K)
  refine ⟨φ, hφ _, ?_⟩
  exact (hφ _).trans (mk_longitude_word_invWord_mirrorGroup K)

/-- The inverse of an upper triangular matrix of `SL₂(ℂ)` is upper triangular, with the inverse
eigenvalue on the first basis vector. -/
private theorem specialLinear_inv_upper_mirrorGroup (X : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h : X.1 1 0 = 0) : (X⁻¹).1 1 0 = 0 ∧ (X⁻¹).1 0 0 = (X.1 0 0)⁻¹ := by
  have hdet := X.2
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  have hinv : (X⁻¹).1 = Matrix.adjugate X.1 := Matrix.SpecialLinearGroup.coe_inv X
  rw [hinv, Matrix.adjugate_fin_two]
  refine ⟨by simp [h], ?_⟩
  simpa using eq_inv_of_mul_eq_one_right hdet

/-- The second diagonal entry of an upper triangular matrix of `SL₂(ℂ)`. -/
private theorem specialLinear_upper_one_one_mirrorGroup
    (X : Matrix.SpecialLinearGroup (Fin 2) ℂ) (h : X.1 1 0 = 0) : X.1 1 1 = (X.1 0 0)⁻¹ := by
  have hdet := X.2
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  exact eq_inv_of_mul_eq_one_right hdet

/-- An isomorphism of knot groups that preserves the meridian and inverts the longitude sends
the eigenvalue pairs `(M, L)` to `(M, L⁻¹)`. -/
private theorem mem_eigenvalueSet_of_equiv_mirrorGroup {K K' : BraidKnot}
    (φ : KnotGroup K' ≃* KnotGroup K) (hm : φ (meridian K') = meridian K)
    (hl : φ (longitude K') = (longitude K)⁻¹) {p : ℂ × ℂ} (hp : p ∈ eigenvalueSet K) :
    (p.1, p.2⁻¹) ∈ eigenvalueSet K' := by
  obtain ⟨ρ, h1, h2, h3, h4⟩ := hp
  obtain ⟨h5, h6⟩ := specialLinear_inv_upper_mirrorGroup (ρ (longitude K)) h2
  refine ⟨ρ.comp φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hm]
    exact h1
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hl, map_inv]
    exact h5
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hm]
    exact h3
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hl, map_inv, h6, h4]

/-- The eigenvalue set of the inverse braid. -/
theorem eigenvalueSet_inv (K : BraidKnot) :
    eigenvalueSet K.inv = (fun p : ℂ × ℂ ↦ (p.1, p.2⁻¹)) '' eigenvalueSet K := by
  obtain ⟨φ, hm, hl⟩ := exists_knotGroup_inv_equiv K
  have hm' : φ.symm (meridian K) = meridian K.inv := by
    rw [MulEquiv.symm_apply_eq, hm]
  have hl' : φ.symm (longitude K) = (longitude K.inv)⁻¹ := by
    rw [MulEquiv.symm_apply_eq, map_inv, hl, inv_inv]
  ext p
  constructor
  · intro hp
    refine ⟨(p.1, p.2⁻¹), mem_eigenvalueSet_of_equiv_mirrorGroup φ.symm hm' hl' hp, ?_⟩
    simp only [inv_inv]
  · rintro ⟨q, hq, rfl⟩
    exact mem_eigenvalueSet_of_equiv_mirrorGroup φ hm hl hq

/-- The first column of the conjugate of an upper triangular matrix by the matrix that
exchanges its two eigenvectors. -/
private theorem conj_upper_entries_mirrorGroup (u b : ℂ) (hu : u ≠ 0)
    (Z : Matrix (Fin 2) (Fin 2) ℂ) (hZ : Z 1 0 = 0) :
    (!![0, u⁻¹; -u, b] * Z * !![b, -u⁻¹; u, 0]) 1 0 =
        u * (-(Z 0 0 * b) - u * Z 0 1 + b * Z 1 1) ∧
      (!![0, u⁻¹; -u, b] * Z * !![b, -u⁻¹; u, 0]) 0 0 = Z 1 1 := by
  constructor
  · simp only [Fin.isValue, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.symm_of,
      Matrix.empty_mul, Matrix.coe_rowEquiv, Matrix.row_of, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_mul, hZ, mul_zero, add_zero]
    ring
  · simp only [Fin.isValue, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.symm_of,
      Matrix.empty_mul, Matrix.coe_rowEquiv, Matrix.row_of, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      zero_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add, hZ, mul_zero]
    field_simp

/-- Two commuting upper triangular matrices of `SL₂(ℂ)`, the first with two different
eigenvalues, are conjugate by one element to upper triangular matrices with the other
eigenvalues on the first basis vector. -/
private theorem exists_conj_swap_eigen_mirrorGroup (X Y : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hc : Commute X Y) (hX : X.1 1 0 = 0) (hY : Y.1 1 0 = 0) (hne : X.1 0 0 ≠ X.1 1 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℂ,
      (g * X * g⁻¹).1 1 0 = 0 ∧ (g * Y * g⁻¹).1 1 0 = 0 ∧
        (g * X * g⁻¹).1 0 0 = X.1 1 1 ∧ (g * Y * g⁻¹).1 0 0 = Y.1 1 1 := by
  have hu : X.1 1 1 - X.1 0 0 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hcomm : X.1 0 0 * Y.1 0 1 + X.1 0 1 * Y.1 1 1 = Y.1 0 0 * X.1 0 1 + Y.1 0 1 * X.1 1 1 := by
    have h := congrArg (fun Z : Matrix.SpecialLinearGroup (Fin 2) ℂ ↦ Z.1 0 1) hc.eq
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  obtain ⟨u, hu'⟩ : ∃ u : ℂ, u = X.1 1 1 - X.1 0 0 := ⟨_, rfl⟩
  rw [← hu'] at hu
  have hdet : Matrix.det !![0, u⁻¹; -u, X.1 0 1] = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring
  obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, g.1 = !![0, u⁻¹; -u, X.1 0 1] :=
    ⟨⟨_, hdet⟩, rfl⟩
  have hgi : (g⁻¹).1 = !![X.1 0 1, -u⁻¹; u, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hg, Matrix.adjugate_fin_two_of, neg_neg]
  have hmul : ∀ Z : Matrix.SpecialLinearGroup (Fin 2) ℂ, (g * Z * g⁻¹).1 =
      !![0, u⁻¹; -u, X.1 0 1] * Z.1 * !![X.1 0 1, -u⁻¹; u, 0] := fun Z ↦ by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgi, hg]
  obtain ⟨hX1, hX2⟩ := conj_upper_entries_mirrorGroup u (X.1 0 1) hu X.1 hX
  obtain ⟨hY1, hY2⟩ := conj_upper_entries_mirrorGroup u (X.1 0 1) hu Y.1 hY
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [hmul, hX1]
    linear_combination (-(u * X.1 0 1)) * hu'
  · rw [hmul, hY1]
    linear_combination u * hcomm + (-(u * Y.1 0 1)) * hu'
  · rw [hmul, hX2]
  · rw [hmul, hY2]

/-- Every eigenvalue set is invariant under `(M, L) ↦ (M⁻¹, L⁻¹)`. -/
theorem eigenvalueSet_symm (K : BraidKnot) {p : ℂ × ℂ} (hp : p ∈ eigenvalueSet K) :
    (p.1⁻¹, p.2⁻¹) ∈ eigenvalueSet K := by
  obtain ⟨ρ, h1, h2, h3, h4⟩ := hp
  have hM := specialLinear_upper_one_one_mirrorGroup _ h1
  have hL := specialLinear_upper_one_one_mirrorGroup _ h2
  have hc : Commute (ρ (meridian K)) (ρ (longitude K)) := (commute_meridian_longitude K).map ρ
  rw [h3] at hM
  rw [h4] at hL
  by_cases hA : (ρ (meridian K)).1 0 0 = (ρ (meridian K)).1 1 1
  · by_cases hB : (ρ (longitude K)).1 0 0 = (ρ (longitude K)).1 1 1
    · have e1 : p.1⁻¹ = p.1 := by rw [← hM, ← hA, h3]
      have e2 : p.2⁻¹ = p.2 := by rw [← hL, ← hB, h4]
      rw [e1, e2]
      exact ⟨ρ, h1, h2, h3, h4⟩
    · obtain ⟨g, g1, g2, g3, g4⟩ := exists_conj_swap_eigen_mirrorGroup _ _ hc.symm h2 h1 hB
      exact ⟨(MulAut.conj g).toMonoidHom.comp ρ, g2, g1, g4.trans hM, g3.trans hL⟩
  · obtain ⟨g, g1, g2, g3, g4⟩ := exists_conj_swap_eigen_mirrorGroup _ _ hc h1 h2 hA
    exact ⟨(MulAut.conj g).toMonoidHom.comp ρ, g1, g2, g3.trans hM, g4.trans hL⟩

/-- The eigenvalue set of the inverse braid in the form of the paper. -/
theorem eigenvalueSet_inv' (K : BraidKnot) :
    eigenvalueSet K.inv = (fun p : ℂ × ℂ ↦ (p.1⁻¹, p.2)) '' eigenvalueSet K := by
  rw [eigenvalueSet_inv]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1⁻¹, p.2⁻¹), eigenvalueSet_symm K hp, by simp only [inv_inv]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1⁻¹, p.2⁻¹), eigenvalueSet_symm K hp, by simp only [inv_inv]⟩

end AJConjecture
