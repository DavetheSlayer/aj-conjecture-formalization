import Mathlib
import AJHandoff.TorusKnot.PairKPeriGapRel

/-!
# The Hopf loops of `pairBlocks r s`

The two negative Hopf letters `σ_T⁻¹` (`T = 2c - 1`) of `pairBlocks r s` are the only blocks
besides the round `R_0 = b(T - r, T)` and the top-right climb `C = b(T - s, T)` that touch the
edges `T` and `T + 1`. Reading the edge meridians `β = e_T`, `α = e_(T+1)` of the bottom tuple
through these four blocks gives the loops of the Hopf letters:
`H₁ = R_0 β⁻¹ α` and `H₂ = C H₁ α⁻¹ H₁⁻¹ β R_0⁻¹`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The arithmetic of an admissible pair used for the positions of the Hopf blocks. -/
private theorem pairHopf_arith {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
  simp only [pairC, pairRunDown, Nat.add_sub_cancel]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [show a + 2 - 1 = a + 1 by omega]
    nlinarith
  · rw [show a + 2 - 1 = a + 1 by omega]
    ring

/-- A block that neither moves nor carries the strand `t` leaves the edge meridian of `t`
unchanged. -/
private theorem edgeMer_step_of_untouched {m : ℕ} (b : SBlock) (hb : b.Valid m) (f : Fin m → G)
    (t : ℕ) (ht : t < m) (hp : b.perm t = t) (hc : b.carries t = false) :
    edgeMer (b.step m f) t = edgeMer f t := by
  rw [SBlock.edgeMer_step b hb f t ht, SBlock.strandLoop, hc, hp]
  simp

/-- Blocks that neither move nor carry the strand `t` leave the edge meridian of `t`
unchanged. -/
private theorem edgeMer_runTop_of_untouched {m : ℕ} (bs : List SBlock) (f : Fin m → G) (t : ℕ)
    (ht : t < m) (hu : ∀ b ∈ bs, b.Valid m ∧ b.perm t = t ∧ b.carries t = false) :
    edgeMer (runTop m bs f) t = edgeMer f t := by
  induction bs generalizing f with
  | nil => rw [runTop_nil]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hu
    rw [runTop_cons, ih _ hu.2, edgeMer_step_of_untouched b hu.1.1 f t ht hu.1.2.1 hu.1.2.2]

/-- The loop of a band in terms of the edge meridians of its ends. -/
private theorem loop_band_edgeMer {m : ℕ} (f : Fin m → G) (i j : ℕ) :
    (SBlock.band i j).loop f = edgeMer f j * (edgeMer f i)⁻¹ := by
  simp only [SBlock.loop, edgeMer]
  group

/-- The loop of a negative letter in terms of edge meridians. -/
private theorem loop_neg_edgeMer {m : ℕ} (f : Fin m → G) (i : ℕ) :
    (SBlock.neg i).loop f = (edgeMer f i)⁻¹ * edgeMer f (i + 1) := by
  simp only [SBlock.loop, edgeMer]
  group

/-- The edge meridian of the upper end `j` above a band `b(i, j)`. -/
private theorem edgeMer_step_band_top {m : ℕ} (i j : ℕ) (hij : i < j) (hj : j < m)
    (f : Fin m → G) :
    edgeMer ((SBlock.band i j).step m f) j = edgeMer f j * ((SBlock.band i j).loop f)⁻¹ := by
  rw [SBlock.edgeMer_step (SBlock.band i j) (show i < j ∧ j < m from ⟨hij, hj⟩) f j hj]
  simp only [SBlock.strandLoop, SBlock.carries, SBlock.perm, true_or, decide_true, ite_true,
    show j ≠ i by omega, ite_false, loop_band_edgeMer]
  group

/-- The block list split around the Hopf letters. -/
private theorem pairBlocks_split (r s : ℕ) :
    pairBlocks r s =
      ((List.range (r - 2)).map (fun i ↦ SBlock.band i (pairTop r s - 1 - i)) ++
        (List.range (pairRunDown r s)).map (fun j ↦ SBlock.band (r + pairRunDown r s - 3 - j)
          (r + pairRunDown r s - 2 - j)) ++
        (List.range (pairRunUp r s)).map (fun j ↦ SBlock.band (r - 2 + pairRunDown r s + j)
          (r - 1 + pairRunDown r s + j)) ++
        [SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r)]) ++
      ([SBlock.band (pairTop r s - r) (pairTop r s), SBlock.neg (pairTop r s)] ++
      (((List.range (s - 2)).map (fun j ↦ SBlock.band (pairTop r s - r - 1 - j)
          (pairTop r s - 1 - j)) ++ [SBlock.band (r - 2) (pairTop r s + 1 - s)]) ++
      ([SBlock.band (pairTop r s - s) (pairTop r s)] ++
      ((List.range (r - 2)).map (fun j ↦ SBlock.band (r - 3 - j)
          (pairTop r s + 2 - s - r + j)) ++ [SBlock.neg (pairTop r s)])))) := by
  simp only [pairBlocks, List.append_assoc, List.cons_append, List.nil_append]

/-- The loops of the two Hopf letters of `pairBlocks r s` in terms of the edge meridians of the
levels `T` and `T + 1` of the bottom tuple. -/
theorem pairHopf_loops {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G) :
    loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH1 r s) =
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0) *
          (edgeMer f (pairTop r s))⁻¹ * edgeMer f (pairTop r s + 1) ∧
      loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s) =
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxC r s) *
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH1 r s) *
          (edgeMer f (pairTop r s + 1))⁻¹ *
          (loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH1 r s))⁻¹ *
          edgeMer f (pairTop r s) *
          (loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairHopf_arith h
  -- the four pieces of the block list between the Hopf blocks
  set T := pairTop r s with hT
  set pre : List SBlock := (List.range (r - 2)).map (fun i ↦ SBlock.band i (T - 1 - i)) ++
      (List.range (pairRunDown r s)).map (fun j ↦ SBlock.band (r + pairRunDown r s - 3 - j)
        (r + pairRunDown r s - 2 - j)) ++
      (List.range (pairRunUp r s)).map (fun j ↦ SBlock.band (r - 2 + pairRunDown r s + j)
        (r - 1 + pairRunDown r s + j)) ++
      [SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (T + 1 - r)] with hpre
  set mid : List SBlock := (List.range (s - 2)).map (fun j ↦ SBlock.band (T - r - 1 - j)
      (T - 1 - j)) ++ [SBlock.band (r - 2) (T + 1 - s)] with hmid
  set post : List SBlock := (List.range (r - 2)).map (fun j ↦ SBlock.band (r - 3 - j)
      (T + 2 - s - r + j)) with hpost
  have hsplit : pairBlocks r s = pre ++ ([SBlock.band (T - r) T, SBlock.neg T] ++
      (mid ++ ([SBlock.band (T - s) T] ++ (post ++ [SBlock.neg T])))) := pairBlocks_split r s
  have hTm : T + 1 < (pairStrands r s) := by simp only [hT, pairTop, pairStrands]; omega
  have hlpre : pre.length = pairIdxB r s + 1 := by
    simp only [hpre, List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil, pairIdxB, pairRunUp]
    omega
  have hlmid : mid.length = s - 1 := by
    simp only [hmid, List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega
  have hlpost : post.length = r - 2 := by simp [hpost]
  -- the blocks of the pieces do not touch the edges `T` and `T + 1`
  have hu : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ pre ++ mid ++ post,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := by
    intro t ht1 ht2 b hb
    simp only [hpre, hmid, hpost, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    simp only [hT, pairTop, pairStrands, pairRunUp] at ht1 ht2 hb ⊢
    rcases hb with (((((⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) |
      (⟨j, hj, rfl⟩ | rfl)) | ⟨j, hj, rfl⟩) <;>
      simp only [SBlock.Valid, SBlock.perm, SBlock.carries, decide_eq_false_iff_not] <;>
      refine ⟨by omega, by split_ifs <;> omega, by omega⟩
  have hupre : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ pre,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := fun t h1 h2 b hb ↦
    hu t h1 h2 b (List.mem_append_left _ (List.mem_append_left _ hb))
  have humid : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ mid,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := fun t h1 h2 b hb ↦
    hu t h1 h2 b (List.mem_append_left _ (List.mem_append_right _ hb))
  have hupost : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ post,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := fun t h1 h2 b hb ↦
    hu t h1 h2 b (List.mem_append_right _ hb)
  -- the tuples between the blocks
  set g := runTop (pairStrands r s) pre f with hg
  set R := (SBlock.band (T - r) T).loop g with hR
  set g1 := (SBlock.band (T - r) T).step (pairStrands r s) g with hg1
  set H := (SBlock.neg T).loop g1 with hH
  set g2 := (SBlock.neg T).step (pairStrands r s) g1 with hg2
  set g3 := runTop (pairStrands r s) mid g2 with hg3
  set Cl := (SBlock.band (T - s) T).loop g3 with hCl
  set g4 := (SBlock.band (T - s) T).step (pairStrands r s) g3 with hg4
  set g5 := runTop (pairStrands r s) post g4 with hg5
  -- the loops at the four positions
  have hLR : loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0) = R := by
    rw [hsplit, show pairIdxR r s 0 = pre.length + 0 by simp [pairIdxR, hlpre],
      loopAt_append_right, loopAt_append_left _ _ _ _ _ (by simp)]
    simp [loopAt, runTop_nil, hR, hg]
  have hLH1 : loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH1 r s) = H := by
    rw [hsplit, show pairIdxH1 r s = pre.length + 1 by simp [pairIdxH1, hlpre],
      loopAt_append_right, loopAt_append_left _ _ _ _ _ (by simp)]
    simp [loopAt, runTop_cons, runTop_nil, hH, hg1, hg]
  have hLC : loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxC r s) = Cl := by
    rw [hsplit, show pairIdxC r s = pre.length + ([SBlock.band (T - r) T, SBlock.neg T].length +
      (mid.length + 0)) by
        simp only [pairIdxC, hlpre, hlmid, List.length_cons, List.length_nil]; omega,
      loopAt_append_right, loopAt_append_right, loopAt_append_right,
      loopAt_append_left _ _ _ _ _ (by simp)]
    simp [loopAt, runTop_cons, runTop_nil, hCl, hg3, hg2, hg1, hg]
  have hLH2 : loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s) =
      (SBlock.neg T).loop g5 := by
    rw [hsplit, show pairIdxH2 r s = pre.length + ([SBlock.band (T - r) T, SBlock.neg T].length +
      (mid.length + ([SBlock.band (T - s) T].length + (post.length + 0)))) by
        simp only [pairIdxH2, hlpre, hlmid, hlpost, List.length_cons, List.length_nil, pairIdxB]
        omega,
      loopAt_append_right, loopAt_append_right, loopAt_append_right, loopAt_append_right,
      loopAt_append_right]
    simp [loopAt, runTop_cons, runTop_nil, hg5, hg4, hg3, hg2, hg1, hg]
  -- the edge meridians
  have hTr : T - r < T := by simp only [hT, pairTop]; omega
  have hTs : T - s < T := by simp only [hT, pairTop]; omega
  have e0 : edgeMer g T = edgeMer f T :=
    edgeMer_runTop_of_untouched pre f T (by omega) (hupre T le_rfl (by omega))
  have e0' : edgeMer g (T + 1) = edgeMer f (T + 1) :=
    edgeMer_runTop_of_untouched pre f (T + 1) hTm (hupre (T + 1) (by omega) le_rfl)
  have e1 : edgeMer g1 T = edgeMer g T * R⁻¹ :=
    edgeMer_step_band_top (T - r) T hTr (by omega) g
  have e1' : edgeMer g1 (T + 1) = edgeMer g (T + 1) :=
    edgeMer_step_of_untouched (SBlock.band (T - r) T)
      (show (SBlock.band (T - r) T).Valid (pairStrands r s) from ⟨hTr, by omega⟩) g (T + 1) hTm
      (by simp only [SBlock.perm]; split_ifs <;> omega)
      (by simp only [SBlock.carries, decide_eq_false_iff_not]; omega)
  have hH1 : H = R * (edgeMer f T)⁻¹ * edgeMer f (T + 1) := by
    rw [hH, loop_neg_edgeMer, e1, e1', e0, e0']
    group
  have e2 : edgeMer g2 T = H * edgeMer g1 (T + 1) * H⁻¹ := by
    rw [hg2, SBlock.edgeMer_step (SBlock.neg T)
      (show (SBlock.neg T).Valid (pairStrands r s) from hTm) g1 T (by omega)]
    simp [SBlock.strandLoop, SBlock.carries, SBlock.perm, hH]
  have e2' : edgeMer g2 (T + 1) = edgeMer g1 T := by
    rw [hg2, SBlock.edgeMer_step (SBlock.neg T)
      (show (SBlock.neg T).Valid (pairStrands r s) from hTm) g1 (T + 1) hTm]
    simp [SBlock.strandLoop, SBlock.carries, SBlock.perm]
  have e3 : edgeMer g3 T = edgeMer g2 T :=
    edgeMer_runTop_of_untouched mid g2 T (by omega) (humid T le_rfl (by omega))
  have e3' : edgeMer g3 (T + 1) = edgeMer g2 (T + 1) :=
    edgeMer_runTop_of_untouched mid g2 (T + 1) hTm (humid (T + 1) (by omega) le_rfl)
  have e4 : edgeMer g4 T = edgeMer g3 T * Cl⁻¹ :=
    edgeMer_step_band_top (T - s) T hTs (by omega) g3
  have e4' : edgeMer g4 (T + 1) = edgeMer g3 (T + 1) :=
    edgeMer_step_of_untouched (SBlock.band (T - s) T)
      (show (SBlock.band (T - s) T).Valid (pairStrands r s) from ⟨hTs, by omega⟩) g3 (T + 1) hTm
      (by simp only [SBlock.perm]; split_ifs <;> omega)
      (by simp only [SBlock.carries, decide_eq_false_iff_not]; omega)
  have e5 : edgeMer g5 T = edgeMer g4 T :=
    edgeMer_runTop_of_untouched post g4 T (by omega) (hupost T le_rfl (by omega))
  have e5' : edgeMer g5 (T + 1) = edgeMer g4 (T + 1) :=
    edgeMer_runTop_of_untouched post g4 (T + 1) hTm (hupost (T + 1) (by omega) le_rfl)
  rw [hLR, hLH1, hLC, hLH2]
  refine ⟨hH1, ?_⟩
  rw [loop_neg_edgeMer, e5, e5', e4, e4', e3, e3', e2, e2', e1, e1', e0, e0', hH1]
  group

end AJConjecture
