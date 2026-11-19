import Mathlib
import AJConjecture.BraidRunOfHom
import AJConjecture.MapLongitude
import AJFamily.Classical.FamilyPeripheralRun

/-!
# The longitude of a block word

For a knot whose braid word is a list of blocks and a representation `ρ` of its group, the
images of the generators form a tuple fixed by the run. Hence every gap factor is trivial
(`gapProd_fixed`), the edge meridians are permuted by conjugation with the strand loops
(`edgeMer_fixed`), and the image of the longitude is `a ^ orbitCount * orbitLoop * a ^ (-writhe)`,
where the product `orbitLoop` of the strand loops along the orbit of `0` commutes with the
meridian `a` (`map_longitude_blocks`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The product of the strand loops along the orbit of `0`. -/
def orbitLoop (m : ℕ) (bs : List SBlock) (f : Fin m → G) : G :=
  ((List.range m).map fun j ↦ stLoop m bs f ((stPerm bs)^[j] 0)).prod

/-- The sum of the meridian counts along the orbit of `0`. -/
def orbitCount (m : ℕ) (bs : List SBlock) : ℤ :=
  ((List.range m).map fun j ↦ stCount bs ((stPerm bs)^[j] 0)).sum

/-- For a representation, the tuple of the images of the generators is fixed by the run of the
blocks. -/
private theorem runTop_fixed_of_hom (K : BraidKnot) (bs : List SBlock)
    (hw : K.word = blocksWord bs) (ρ : KnotGroup K →* G) :
    runTop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) = fun t ↦ ρ (PresentedGroup.of t) := by
  rw [runTop, ← hw]
  exact braidRun_fst_of_hom K ρ

theorem gapProd_fixed (K : BraidKnot) (bs : List SBlock) (hw : K.word = blocksWord bs)
    (hv : ∀ b ∈ bs, b.Valid K.strands) (ρ : KnotGroup K →* G) (n : ℕ) :
    gapProd K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) n = 1 := by
  have h := prePr_runTop bs hv (fun t ↦ ρ (PresentedGroup.of t)) n
  rw [runTop_fixed_of_hom K bs hw ρ] at h
  exact (mul_eq_right.mp h.symm)

theorem edgeMer_fixed (K : BraidKnot) (bs : List SBlock) (hw : K.word = blocksWord bs)
    (hv : ∀ b ∈ bs, b.Valid K.strands) (ρ : KnotGroup K →* G) (t : ℕ) (ht : t < K.strands) :
    edgeMer (fun t ↦ ρ (PresentedGroup.of t)) t =
      stLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) t *
        edgeMer (fun t ↦ ρ (PresentedGroup.of t)) (stPerm bs t) *
        (stLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) t)⁻¹ := by
  have h := edgeMer_runTop bs hv (fun t ↦ ρ (PresentedGroup.of t)) t ht
  rwa [runTop_fixed_of_hom K bs hw ρ] at h

/-- The iterates of the strand map of a block word are the iterates of `stPerm`. -/
private theorem iterate_artinWord_blocksWord {m : ℕ} (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (k : Fin m) (j : ℕ) :
    (((fun k ↦ (artinWord m (blocksWord bs) k).1)^[j] k : Fin m) : ℕ) = (stPerm bs)^[j] k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', artinWord_blocksWord_fst bs hv,
      ih]

/-- The partial products of the conjugators along the orbit of `0`, for a fixed tuple. -/
private theorem orbit_partial_prod {m : ℕ} (bs : List SBlock) (f : Fin m → G) (hm : 0 < m)
    (hv : ∀ b ∈ bs, b.Valid m)
    (hfix : ∀ t < m, edgeMer f t = stLoop m bs f t * edgeMer f (stPerm bs t) *
      (stLoop m bs f t)⁻¹) (r : ℕ) :
    ((List.range r).map fun j ↦ (prePr f ((stPerm bs)^[j] 0))⁻¹ *
        edgeMer f ((stPerm bs)^[j] 0) ^ stCount bs ((stPerm bs)^[j] 0) *
        stLoop m bs f ((stPerm bs)^[j] 0) * prePr f (stPerm bs ((stPerm bs)^[j] 0))).prod =
      f ⟨0, hm⟩ ^ ((List.range r).map fun j ↦ stCount bs ((stPerm bs)^[j] 0)).sum *
        ((List.range r).map fun j ↦ stLoop m bs f ((stPerm bs)^[j] 0)).prod *
        prePr f ((stPerm bs)^[r] 0) ∧
    edgeMer f ((stPerm bs)^[r] 0) =
      (((List.range r).map fun j ↦ stLoop m bs f ((stPerm bs)^[j] 0)).prod)⁻¹ * f ⟨0, hm⟩ *
        ((List.range r).map fun j ↦ stLoop m bs f ((stPerm bs)^[j] 0)).prod := by
  induction r with
  | zero => simp [prePr_zero, edgeMer_zero f hm]
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    have hlt : (stPerm bs)^[r] 0 < m := by
      clear h1 h2
      induction r with
      | zero => exact hm
      | succ r ihr => rw [Function.iterate_succ_apply']; exact stPerm_lt bs hv _ ihr
    have he := hfix _ hlt
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, List.sum_append, List.sum_cons, List.sum_nil, mul_one,
      add_zero, Function.iterate_succ_apply']
    set L := ((List.range r).map fun j ↦ stLoop m bs f ((stPerm bs)^[j] 0)).prod
    set t := (stPerm bs)^[r] 0
    set Λ := stLoop m bs f t
    constructor
    · have hc : (L⁻¹ * f ⟨0, hm⟩ * L) ^ stCount bs t = L⁻¹ * f ⟨0, hm⟩ ^ stCount bs t * L := by
        simpa using conj_zpow (a := L⁻¹) (b := f ⟨0, hm⟩) (i := stCount bs t)
      rw [h1, h2, hc, zpow_add]
      group
    · have : edgeMer f (stPerm bs t) = Λ⁻¹ * edgeMer f t * Λ := by rw [he]; group
      rw [this, h2]
      group

theorem map_longitude_blocks (K : BraidKnot) (bs : List SBlock) (hw : K.word = blocksWord bs)
    (hv : ∀ b ∈ bs, b.Valid K.strands) (horb : (stPerm bs)^[K.strands] 0 = 0)
    (ρ : KnotGroup K →* G) :
    ρ (longitude K) = ρ (meridian K) ^ orbitCount K.strands bs *
        orbitLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) *
        ρ (meridian K) ^ (-(writhe K.word)) ∧
      orbitLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) * ρ (meridian K) =
        ρ (meridian K) * orbitLoop K.strands bs (fun t ↦ ρ (PresentedGroup.of t)) := by
  set f : Fin K.strands → G := fun t ↦ ρ (PresentedGroup.of t)
  have hfix := runTop_fixed_of_hom K bs hw ρ
  have hlist : ((List.range K.strands).map fun j ↦
      (braidRun K.strands K.word f).2
        ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩)) =
      (List.range K.strands).map fun j ↦ (prePr f ((stPerm bs)^[j] 0))⁻¹ *
        edgeMer f ((stPerm bs)^[j] 0) ^ stCount bs ((stPerm bs)^[j] 0) *
        stLoop K.strands bs f ((stPerm bs)^[j] 0) *
        prePr f (stPerm bs ((stPerm bs)^[j] 0)) := by
    refine List.map_congr_left fun j _ ↦ ?_
    rw [hw, braidRun_blocksWord_snd bs hv, hfix, iterate_artinWord_blocksWord bs hv]
  obtain ⟨h1, h2⟩ := orbit_partial_prod bs f K.strands_pos hv
    (fun t ht ↦ edgeMer_fixed K bs hw hv ρ t ht) K.strands
  rw [horb, prePr_zero, mul_one] at h1
  rw [horb, edgeMer_zero f K.strands_pos] at h2
  have hmer : ρ (meridian K) = f ⟨0, K.strands_pos⟩ := rfl
  refine ⟨?_, ?_⟩
  · rw [map_longitude, hlist, h1, hmer, orbitCount, orbitLoop]
  · rw [hmer, orbitLoop]
    set L := ((List.range K.strands).map fun j ↦ stLoop K.strands bs f ((stPerm bs)^[j] 0)).prod
    calc L * f ⟨0, K.strands_pos⟩ = L * (L⁻¹ * f ⟨0, K.strands_pos⟩ * L) := by rw [← h2]
      _ = f ⟨0, K.strands_pos⟩ * L := by group

end AJConjecture
