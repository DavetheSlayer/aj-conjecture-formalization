import Mathlib
import AJFamily.Classical.FamilyPeripheralLongitude

/-!
# Generic facts about the run of a block word

For an arbitrary list of blocks:

* `gapProd_eq_prod_range`: the gap factor of level `n` is the product, from the last block to
  the first, of the loops `loopAt` of the blocks whose gap interval contains `n`;
* `stLoop_eq_prod_range`: the strand loop of the strand at top position `t` is the product, from
  the last block to the first, of the loops of the blocks that the strand carries;
* `map_longitude_eq_orbitLoop`: for a knot whose word is the block word, the image of the
  preferred longitude under any representation is the orbit loop of the strand `0` (the meridian
  count along the orbit is the writhe, and the orbit loop commutes with the meridian).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The default block used to read a list of blocks with `List.getD`. -/
private abbrev periDefault : SBlock := SBlock.neg 0

theorem gapProd_eq_prod_range (m : ℕ) (bs : List SBlock) (f : Fin m → G) (n : ℕ) :
    gapProd m bs f n = ((List.range bs.length).reverse.map fun q ↦
      if (bs.getD q periDefault).lo ≤ n ∧ n ≤ (bs.getD q periDefault).hi then loopAt m bs f q
      else 1).prod := by
  induction bs generalizing f with
  | nil => simp [gapProd]
  | cons b bs ih =>
    rw [gapProd, ih, List.length_cons, List.range_succ_eq_map, List.reverse_cons,
      List.map_append, List.prod_append, List.map_reverse, List.map_reverse, List.map_map]
    congr 1
    · refine congrArg List.prod (congrArg List.reverse (List.map_congr_left fun q _ ↦ ?_))
      simp only [Function.comp_apply, List.getD_cons_succ, loopAt, List.take_succ_cons,
        runTop_cons]
    · simp [SBlock.gapLoop, loopAt, runTop_nil]

theorem stLoop_eq_prod_range (m : ℕ) (bs : List SBlock) (f : Fin m → G) (t : ℕ) :
    stLoop m bs f t = ((List.range bs.length).reverse.map fun q ↦
      if (bs.getD q periDefault).carries (stPerm (bs.drop (q + 1)) t) then loopAt m bs f q
      else 1).prod := by
  induction bs generalizing f with
  | nil => simp [stLoop]
  | cons b bs ih =>
    rw [stLoop, ih, List.length_cons, List.range_succ_eq_map, List.reverse_cons,
      List.map_append, List.prod_append, List.map_reverse, List.map_reverse, List.map_map]
    congr 1
    · refine congrArg List.prod (congrArg List.reverse (List.map_congr_left fun q _ ↦ ?_))
      simp only [Function.comp_apply, List.getD_cons_succ, loopAt, List.take_succ_cons,
        runTop_cons, List.drop_succ_cons]
    · simp [SBlock.strandLoop, loopAt, runTop_nil]

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_peri (m : ℕ) (w : BraidWord) (k : Fin m) :
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

/-- `stPerm` of a valid block list is the strand permutation of its word. -/
private theorem strandPerm_blocksWord_val {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m)
    (t : Fin m) : ((strandPerm m (blocksWord bs) t : Fin m) : ℕ) = stPerm bs t := by
  rw [← artinWord_fst_eq_strandPerm_peri, artinWord_blocksWord_fst bs hv]

/-- The iterates of the strand permutation are the iterates of `stPerm`. -/
private theorem iterate_strandPerm_blocksWord_val {m : ℕ} (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (t : Fin m) (j : ℕ) :
    (((strandPerm m (blocksWord bs))^[j] t : Fin m) : ℕ) = (stPerm bs)^[j] t := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', strandPerm_blocksWord_val bs hv,
      ih]

/-- A permutation of `Fin m` whose powers move `x` everywhere has minimal period `m` at `x`. -/
private theorem minimalPeriod_eq_of_transitive {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin m)
    (h : ∀ j, ∃ k : ℕ, (σ ^ k) x = j) : Function.minimalPeriod σ x = m := by
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

/-- The sum of a function along the orbit of `0` of a transitive permutation is its sum over
all points. -/
private theorem sum_orbit_eq_sum {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin m)
    (h : ∀ j, ∃ k : ℕ, (σ ^ k) x = j) (F : Fin m → ℤ) :
    ∑ j : Fin m, F (σ^[j] x) = ∑ t : Fin m, F t := by
  have hp := minimalPeriod_eq_of_transitive σ x h
  have hinj : Function.Injective fun j : Fin m ↦ σ^[j] x := by
    intro i j hij
    have := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x)
      (by rw [hp]; exact Set.mem_Iio.2 i.2) (by rw [hp]; exact Set.mem_Iio.2 j.2) hij
    exact Fin.ext this
  have hbij : Function.Bijective fun j : Fin m ↦ σ^[j] x :=
    (Finite.injective_iff_bijective).1 hinj
  exact Equiv.sum_comp (Equiv.ofBijective _ hbij) F

/-- The writhe of a block word is the sum of the writhes of its blocks. -/
private theorem writhe_blocksWord_cons (b : SBlock) (bs : List SBlock) :
    writhe (blocksWord (b :: bs)) = writhe b.word + writhe (blocksWord bs) := by
  simp [blocksWord, writhe, List.map_append, List.sum_append]

/-- The sum over all strands of the meridian count of one block is the writhe of the block. -/
private theorem sum_count_eq_writhe {m : ℕ} (b : SBlock) (hb : b.Valid m) :
    ∑ t : Fin m, b.count t = writhe b.word := by
  cases b with
  | band i j =>
    obtain ⟨-, hj⟩ := hb
    have h1 : writhe (SBlock.band i j).word = 1 := by
      simp [SBlock.word, bandWord, writhe, List.map_append, List.sum_append, Function.comp_def]
    rw [h1]
    simp only [SBlock.count]
    rw [Finset.sum_eq_single ⟨j, hj⟩ (fun t _ ht ↦ by
      simp only [ite_eq_right_iff]; exact fun h ↦ absurd (Fin.ext h) ht) (by simp)]
    simp
  | neg i =>
    have hi : i < m := by simp only [SBlock.Valid] at hb; omega
    have h1 : writhe (SBlock.neg i).word = -1 := by simp [SBlock.word, writhe]
    rw [h1]
    simp only [SBlock.count]
    rw [Finset.sum_eq_single ⟨i, hi⟩ (fun t _ ht ↦ by
      simp only [ite_eq_right_iff]; exact fun h ↦ absurd (Fin.ext h) ht) (by simp)]
    simp

/-- The sum over all strands of the meridian counts is the writhe of the block word. -/
private theorem sum_stCount_eq_writhe {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m) :
    ∑ t : Fin m, stCount bs t = writhe (blocksWord bs) := by
  induction bs with
  | nil => simp [stCount, blocksWord, writhe]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    simp only [stCount, Finset.sum_add_distrib]
    rw [ih hv.2, writhe_blocksWord_cons, add_comm]
    congr 1
    rw [← sum_count_eq_writhe b hv.1]
    have h := Equiv.sum_comp (strandPerm m (blocksWord bs)) (fun t : Fin m ↦ b.count t)
    simp only [strandPerm_blocksWord_val bs hv.2] at h
    exact h

/-- For a knot given by a block word, the meridian count along the orbit of `0` is the
writhe. -/
theorem orbitCount_eq_writhe (K : BraidKnot) (bs : List SBlock) (hw : K.word = blocksWord bs)
    (hv : ∀ b ∈ bs, b.Valid K.strands) : orbitCount K.strands bs = writhe K.word := by
  have hc := K.connected ⟨0, K.strands_pos⟩
  rw [hw] at hc
  rw [orbitCount, hw, ← sum_stCount_eq_writhe bs hv,
    ← sum_orbit_eq_sum (strandPerm K.strands (blocksWord bs)) ⟨0, K.strands_pos⟩ hc]
  have hsum : ∀ F : ℕ → ℤ, ((List.range K.strands).map F).sum = ∑ j : Fin K.strands, F j :=
    fun F ↦ by rw [Fin.sum_univ_eq_sum_range]; rfl
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [iterate_strandPerm_blocksWord_val bs hv]

/-- For a knot given by a block word, the strand `0` returns after one full turn of its orbit. -/
theorem iterate_stPerm_strands (K : BraidKnot) (bs : List SBlock) (hw : K.word = blocksWord bs)
    (hv : ∀ b ∈ bs, b.Valid K.strands) : (stPerm bs)^[K.strands] 0 = 0 := by
  have hc := K.connected ⟨0, K.strands_pos⟩
  rw [hw] at hc
  have hp := minimalPeriod_eq_of_transitive _ _ hc
  have h := Function.iterate_minimalPeriod (f := strandPerm K.strands (blocksWord bs))
    (x := ⟨0, K.strands_pos⟩)
  rw [hp] at h
  have h' := congrArg Fin.val h
  rwa [iterate_strandPerm_blocksWord_val bs hv] at h'

/-- For a knot given by a block word and a representation of its group, the image of the
preferred longitude is the orbit loop of the strand `0`, and the orbit loop commutes with the
image of the meridian. -/
theorem map_longitude_eq_orbitLoop (K : BraidKnot) (bs : List SBlock)
    (hw : K.word = blocksWord bs) (hv : ∀ b ∈ bs, b.Valid K.strands) (ρ : KnotGroup K →* G) :
    ρ (longitude K) = orbitLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) ∧
      orbitLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) * ρ (meridian K) =
        ρ (meridian K) * orbitLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) := by
  obtain ⟨hl, hc⟩ := map_longitude_blocks K bs hw hv (iterate_stPerm_strands K bs hw hv) ρ
  refine ⟨?_, hc⟩
  rw [hl, orbitCount_eq_writhe K bs hw hv]
  have hc' : Commute (orbitLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)))
      (ρ (meridian K)) := hc
  rw [mul_assoc, (hc'.zpow_right (-(writhe K.word))).eq, ← mul_assoc, ← zpow_add,
    add_neg_cancel, zpow_zero, one_mul]

end AJConjecture
