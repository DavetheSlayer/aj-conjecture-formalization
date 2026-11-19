import Mathlib
import AJFamily.Classical.FamilyPeripheralPhaseOuter
import AJFamily.Classical.FamilyPeripheralPhaseStair

/-!
# The gap relations and the Hopf loops of the family word

With `L r = loopAt (4k+3) (famBlocks k) f r`, the gap factors of the family block list at the
levels used in `isSatelliteData_of_famRelations` are computed in terms of the loops `L r`, phase
by phase. The two Hopf loops `L (2k+1)` and `L (4k+3)` are expressed through the edge meridians
`e_{4k+1}`, `e_{4k+2}` of the bottom tuple.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The gap factor of the family block list splits into the four phases. -/
private theorem gapProd_famBlocks_phases (k : ℕ) (f : Fin (4 * k + 3) → G) (n : ℕ) :
    gapProd (4 * k + 3) (famBlocks k) f n =
      gapProd (4 * k + 3) (famTop k)
          (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f) n *
        gapProd (4 * k + 3) (famStair k) (runTop (4 * k + 3) (famClimbs k ++ famMid k) f) n *
        gapProd (4 * k + 3) (famMid k) (runTop (4 * k + 3) (famClimbs k) f) n *
        gapProd (4 * k + 3) (famClimbs k) f n := by
  rw [famBlocks, gapProd_append, gapProd_append, gapProd_append]
  simp only [mul_assoc]

/-- The loops of the climbs as loops of the family block list. -/
private theorem famGaps_climbLoop (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (r : ℕ)
    (hr : r < 2 * k - 1) :
    loopAt (4 * k + 3) (famClimbs k) f r = loopAt (4 * k + 3) (famBlocks k) f r :=
  (loopAt_famBlocks_climb k hk f r hr).symm

/-- The loop of the big climb as a loop of the family block list. -/
private theorem famGaps_midLoop0 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famMid k) (runTop (4 * k + 3) (famClimbs k) f) 0 =
      loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1) := by
  rw [← loopAt_famBlocks_mid k hk f 0 (by norm_num), Nat.add_zero (2 * k - 1)]

/-- The loop of the first staircase step of the middle as a loop of the family block list. -/
private theorem famGaps_midLoop1 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famMid k) (runTop (4 * k + 3) (famClimbs k) f) 1 =
      loopAt (4 * k + 3) (famBlocks k) f (2 * k) := by
  rw [← loopAt_famBlocks_mid k hk f 1 (by norm_num), show 2 * k - 1 + 1 = 2 * k by omega]

/-- The loop of the first Hopf letter as a loop of the family block list. -/
private theorem famGaps_midLoop2 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famMid k) (runTop (4 * k + 3) (famClimbs k) f) 2 =
      loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1) := by
  rw [← loopAt_famBlocks_mid k hk f 2 (by norm_num), show 2 * k - 1 + 2 = 2 * k + 1 by omega]

/-- The loops of the staircase as loops of the family block list. -/
private theorem famGaps_stairLoop (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (s : ℕ)
    (hs : s < 2 * k - 1) :
    loopAt (4 * k + 3) (famStair k) (runTop (4 * k + 3) (famClimbs k ++ famMid k) f) s =
      loopAt (4 * k + 3) (famBlocks k) f (2 * k + 2 + s) :=
  (loopAt_famBlocks_stair k hk f s hs).symm

/-- The loop of the last crossing as a loop of the family block list. -/
private theorem famGaps_topLoop0 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famTop k)
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f) 0 =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 1) :=
  (loopAt_famBlocks_top k hk f 0).symm

/-- The loop of the final climb as a loop of the family block list. -/
private theorem famGaps_topLoop1 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famTop k)
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f) 1 =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) :=
  (loopAt_famBlocks_top k hk f 1).symm

/-- The loop of the second Hopf letter as a loop of the family block list. -/
private theorem famGaps_topLoop2 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famTop k)
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f) 2 =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 3) :=
  (loopAt_famBlocks_top k hk f 2).symm

/-- The validity of the climbs. -/
private theorem famGaps_climbs_valid (k : ℕ) (hk : 1 ≤ k) :
    ∀ b ∈ famClimbs k, b.Valid (4 * k + 3) := fun b hb ↦
  famBlocks_valid k hk b (by simp [famBlocks, hb])

/-- The chamber products above the climbs and the first two blocks of the middle, at the levels
of the first Hopf letter. -/
private theorem famGaps_prePr_hopf1 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (n : ℕ)
    (hn : 4 * k + 1 ≤ n) :
    prePr (runTop (4 * k + 3) [SBlock.band (2 * k - 1) (4 * k), SBlock.band (4 * k - 1) (4 * k + 1)]
        (runTop (4 * k + 3) (famClimbs k) f)) n =
      (if n = 4 * k + 1 then loopAt (4 * k + 3) (famBlocks k) f (2 * k) else 1) * prePr f n := by
  have hv2 : ∀ b ∈ [SBlock.band (2 * k - 1) (4 * k), SBlock.band (4 * k - 1) (4 * k + 1)],
      b.Valid (4 * k + 3) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      SBlock.Valid]
    omega
  have hl : loopAt (4 * k + 3) (famMid k) (runTop (4 * k + 3) (famClimbs k) f) 1 =
      (SBlock.band (4 * k - 1) (4 * k + 1)).loop
        ((SBlock.band (2 * k - 1) (4 * k)).step (4 * k + 3)
          (runTop (4 * k + 3) (famClimbs k) f)) := by
    simp [loopAt, famMid, runTop_cons, runTop_nil]
  rw [prePr_runTop _ hv2, prePr_runTop _ (famGaps_climbs_valid k hk), gapProd_famClimbs k hk,
    ← famGaps_midLoop1 k hk, hl]
  simp only [gapProd, gapLoop_band_eq, one_mul]
  split_ifs <;> first | omega | simp

/-- The chamber products above the first `4k+3` blocks, at the levels of the second Hopf
letter. -/
private theorem famGaps_prePr_hopf2 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (n : ℕ)
    (hn : 4 * k + 1 ≤ n) (hn' : n ≤ 4 * k + 3) :
    prePr (runTop (4 * k + 3) [SBlock.band 0 (2 * k + 1), SBlock.band (2 * k) (4 * k + 1)]
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f)) n =
      (if n = 4 * k + 1 then
          loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) *
            loopAt (4 * k + 3) (famBlocks k) f (2 * k)
        else if n = 4 * k + 2 then loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1) else 1) *
        prePr f n := by
  have hv2 : ∀ b ∈ [SBlock.band 0 (2 * k + 1), SBlock.band (2 * k) (4 * k + 1)],
      b.Valid (4 * k + 3) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      SBlock.Valid]
    omega
  have hv : ∀ b ∈ famClimbs k ++ famMid k ++ famStair k, b.Valid (4 * k + 3) := fun b hb ↦
    famBlocks_valid k hk b (by rw [famBlocks]; exact List.mem_append_left _ hb)
  have hl : loopAt (4 * k + 3) (famTop k)
      (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f) 1 =
      (SBlock.band (2 * k) (4 * k + 1)).loop ((SBlock.band 0 (2 * k + 1)).step (4 * k + 3)
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f)) := by
    simp [loopAt, famTop, runTop_cons, runTop_nil]
  rw [prePr_runTop _ hv2, prePr_runTop _ hv, gapProd_append, gapProd_append,
    gapProd_famStair k hk, gapProd_famMid k hk, gapProd_famClimbs k hk, famGaps_midLoop1 k hk,
    famGaps_midLoop2 k hk, ← famGaps_topLoop1 k hk, hl]
  simp only [gapProd, gapLoop_band_eq, one_mul]
  split_ifs <;> first | omega | simp only [one_mul, mul_one, mul_assoc]

theorem gapProd_famBlocks_climb (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (n : ℕ)
    (h1 : 1 ≤ n) (h2 : n ≤ 2 * k - 1) :
    gapProd (4 * k + 3) (famBlocks k) f n =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 1) * loopAt (4 * k + 3) (famBlocks k) f (n - 1) := by
  rw [gapProd_famBlocks_phases, gapProd_famTop k hk, gapProd_famStair k hk, gapProd_famMid k hk,
    gapProd_famClimbs k hk]
  split_ifs <;> try omega
  rw [famGaps_topLoop0 k hk, famGaps_climbLoop k hk f _ (by omega), mul_one, mul_one]

theorem gapProd_famBlocks_bigClimb (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    gapProd (4 * k + 3) (famBlocks k) f (2 * k) =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 1) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1) := by
  rw [gapProd_famBlocks_phases, gapProd_famTop k hk, gapProd_famStair k hk, gapProd_famMid k hk,
    gapProd_famClimbs k hk]
  split_ifs <;> try omega
  rw [famGaps_topLoop0 k hk, famGaps_midLoop0 k hk, mul_one, mul_one]

theorem gapProd_famBlocks_close (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    gapProd (4 * k + 3) (famBlocks k) f (2 * k + 1) =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) * loopAt (4 * k + 3) (famBlocks k) f (4 * k + 1) *
        loopAt (4 * k + 3) (famBlocks k) f (4 * k) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1) := by
  rw [gapProd_famBlocks_phases, gapProd_famTop k hk, gapProd_famStair k hk, gapProd_famMid k hk,
    gapProd_famClimbs k hk]
  split_ifs <;> try omega
  rw [famGaps_topLoop0 k hk, famGaps_topLoop1 k hk, famGaps_midLoop0 k hk,
    famGaps_stairLoop k hk f _ (by omega), show 2 * k + 2 + (2 * k - 2) = 4 * k by omega, mul_one]

theorem gapProd_famBlocks_stair (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (n : ℕ)
    (h1 : 2 * k + 2 ≤ n) (h2 : n ≤ 4 * k - 1) :
    gapProd (4 * k + 3) (famBlocks k) f n =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k + 2 + (4 * k - n)) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k + 2 + (4 * k - 1 - n)) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1) := by
  rw [gapProd_famBlocks_phases, gapProd_famTop k hk, gapProd_famStair k hk, gapProd_famMid k hk,
    gapProd_famClimbs k hk]
  split_ifs <;> try omega
  rw [famGaps_topLoop1 k hk, famGaps_midLoop0 k hk, famGaps_stairLoop k hk f _ (by omega),
    famGaps_stairLoop k hk f _ (by omega), mul_one]
  simp only [mul_assoc]

theorem gapProd_famBlocks_firstStep (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    gapProd (4 * k + 3) (famBlocks k) f (4 * k) =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k + 2) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1) := by
  rw [gapProd_famBlocks_phases, gapProd_famTop k hk, gapProd_famStair k hk, gapProd_famMid k hk,
    gapProd_famClimbs k hk]
  split_ifs <;> try omega
  rw [famGaps_topLoop1 k hk, famGaps_midLoop0 k hk, famGaps_midLoop1 k hk,
    famGaps_stairLoop k hk f _ (by omega), Nat.add_zero (2 * k + 2), mul_one]
  simp only [mul_assoc]

theorem gapProd_famBlocks_clasp (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    gapProd (4 * k + 3) (famBlocks k) f (4 * k + 1) =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) * loopAt (4 * k + 3) (famBlocks k) f (2 * k) := by
  rw [gapProd_famBlocks_phases, gapProd_famTop k hk, gapProd_famStair k hk, gapProd_famMid k hk,
    gapProd_famClimbs k hk]
  split_ifs <;> try omega
  rw [famGaps_topLoop1 k hk, famGaps_midLoop1 k hk, mul_one, mul_one]

theorem gapProd_famBlocks_hopf (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    gapProd (4 * k + 3) (famBlocks k) f (4 * k + 2) =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 3) *
        loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1) := by
  rw [gapProd_famBlocks_phases, gapProd_famTop k hk, gapProd_famStair k hk, gapProd_famMid k hk,
    gapProd_famClimbs k hk]
  split_ifs <;> try omega
  rw [famGaps_topLoop2 k hk, famGaps_midLoop2 k hk, mul_one, mul_one]

theorem loopAt_famBlocks_hopf1 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1) =
      loopAt (4 * k + 3) (famBlocks k) f (2 * k) * (edgeMer f (4 * k + 1))⁻¹ *
        edgeMer f (4 * k + 2) := by
  have hl : loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1) = (SBlock.neg (4 * k + 1)).loop
      (runTop (4 * k + 3) [SBlock.band (2 * k - 1) (4 * k), SBlock.band (4 * k - 1) (4 * k + 1)]
        (runTop (4 * k + 3) (famClimbs k) f)) := by
    rw [← famGaps_midLoop2 k hk]
    simp [loopAt, famMid]
  have h1 := famGaps_prePr_hopf1 k hk f (4 * k + 1) le_rfl
  have h2 := famGaps_prePr_hopf1 k hk f (4 * k + 2) (by omega)
  have h3 := famGaps_prePr_hopf1 k hk f (4 * k + 3) (by omega)
  simp only [ite_true, show ¬4 * k + 2 = 4 * k + 1 by omega, show ¬4 * k + 3 = 4 * k + 1 by omega,
    ite_false, one_mul] at h1 h2 h3
  rw [hl]
  simp only [SBlock.loop, edgeMer, Nat.add_assoc]
  rw [h1, h2, h3]
  group

theorem loopAt_famBlocks_hopf2 (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    loopAt (4 * k + 3) (famBlocks k) f (4 * k + 3) =
      loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) * loopAt (4 * k + 3) (famBlocks k) f (2 * k) *
        (edgeMer f (4 * k + 1))⁻¹ * (loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1))⁻¹ *
        edgeMer f (4 * k + 2) * (loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1))⁻¹ := by
  have hl : loopAt (4 * k + 3) (famBlocks k) f (4 * k + 3) = (SBlock.neg (4 * k + 1)).loop
      (runTop (4 * k + 3) [SBlock.band 0 (2 * k + 1), SBlock.band (2 * k) (4 * k + 1)]
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f)) := by
    rw [← famGaps_topLoop2 k hk]
    simp [loopAt, famTop]
  have h1 := famGaps_prePr_hopf2 k hk f (4 * k + 1) le_rfl (by omega)
  have h2 := famGaps_prePr_hopf2 k hk f (4 * k + 2) (by omega) (by omega)
  have h3 := famGaps_prePr_hopf2 k hk f (4 * k + 3) (by omega) le_rfl
  simp only [ite_true, show ¬4 * k + 2 = 4 * k + 1 by omega, show ¬4 * k + 3 = 4 * k + 1 by omega,
    show ¬4 * k + 3 = 4 * k + 2 by omega, ite_false, one_mul] at h1 h2 h3
  rw [hl]
  simp only [SBlock.loop, edgeMer, Nat.add_assoc]
  rw [h1, h2, h3]
  group

end AJConjecture
