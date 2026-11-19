import Mathlib
import AJFamily.Classical.FamilyPeripheralWord

/-!
# The outer phases of the family word

The strand permutation, meridian counts, strand loops and gap factors of the three outer phases
of the family block list (the climbs `famClimbs k`, the middle `famMid k` and the top
`famTop k`), read on an arbitrary tuple `g` below the phase and expressed through the phase's
own block loops `loopAt … g r`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The climb `b(l, l+1)`. -/
private def famClimbStep (l : ℕ) : SBlock := SBlock.band l (l + 1)

/-- The partial climbs made of the first `r` climbs. -/
private def famClimbPart (r : ℕ) : List SBlock := (List.range r).map famClimbStep

/-- The climbs are the partial climbs of `2k-1` blocks. -/
private theorem famClimbs_eq_part (k : ℕ) : famClimbs k = famClimbPart (2 * k - 1) := rfl

/-- Splitting off the top climb of the partial climbs. -/
private theorem famClimbPart_succ (r : ℕ) :
    famClimbPart (r + 1) = famClimbPart r ++ [famClimbStep r] := by
  simp [famClimbPart, List.range_succ]

/-- The length of the partial climbs. -/
private theorem famClimbPart_length (r : ℕ) : (famClimbPart r).length = r := by
  simp [famClimbPart]

/-- The loops of the earlier climbs do not see the top climb. -/
private theorem loopAt_famClimbPart_succ_lt {m : ℕ} (r : ℕ) (g : Fin m → G) (j : ℕ)
    (hj : j < r) : loopAt m (famClimbPart (r + 1)) g j = loopAt m (famClimbPart r) g j := by
  rw [famClimbPart_succ, loopAt_append_left _ _ _ _ _ (by rw [famClimbPart_length]; exact hj)]

/-- The loop of the top climb. -/
private theorem loopAt_famClimbPart_succ_top {m : ℕ} (r : ℕ) (g : Fin m → G) :
    loopAt m (famClimbPart (r + 1)) g r =
      (famClimbStep r).loop (runTop m (famClimbPart r) g) := by
  have h := loopAt_append_right m (famClimbPart r) [famClimbStep r] g 0
  rw [famClimbPart_length, Nat.add_zero] at h
  rw [famClimbPart_succ, h]
  simp [loopAt, List.take, runTop_nil]

/-- The gap factor of a climb. -/
private theorem famClimbStep_gapLoop {m : ℕ} (r n : ℕ) (f : Fin m → G) :
    (famClimbStep r).gapLoop f n = if n = r + 1 then (famClimbStep r).loop f else 1 := by
  simp only [famClimbStep, SBlock.gapLoop, SBlock.lo, SBlock.hi]
  congr 1
  simp only [eq_iff_iff]
  omega

/-- The strand permutation of the partial climbs. -/
private theorem stPerm_famClimbPart (r t : ℕ) :
    stPerm (famClimbPart r) t = if t = r then 0 else if t < r then t + 1 else t := by
  induction r generalizing t with
  | zero =>
    simp only [famClimbPart, List.range_zero, List.map_nil, stPerm]
    split_ifs <;> omega
  | succ r ih =>
    rw [famClimbPart_succ, stPerm_append]
    simp only [stPerm, famClimbStep, SBlock.perm]
    split_ifs <;> rw [ih] <;> split_ifs <;> omega

/-- The meridian counts of the partial climbs. -/
private theorem stCount_famClimbPart (r t : ℕ) :
    stCount (famClimbPart r) t = if t = r then (r : ℤ) else 0 := by
  induction r generalizing t with
  | zero =>
    simp only [famClimbPart, List.range_zero, List.map_nil, stCount]
    split_ifs <;> simp
  | succ r ih =>
    rw [famClimbPart_succ, stCount_append]
    simp only [stCount, stPerm, famClimbStep, SBlock.perm, SBlock.count]
    split_ifs <;> rw [ih] <;> split_ifs <;> omega

/-- The strand loops of the partial climbs. -/
private theorem stLoop_famClimbPart {m : ℕ} (r : ℕ) (g : Fin m → G) (t : ℕ) :
    stLoop m (famClimbPart r) g t =
      if t = r then ((List.range r).reverse.map (loopAt m (famClimbPart r) g)).prod else 1 := by
  induction r generalizing t with
  | zero =>
    simp only [famClimbPart, List.range_zero, List.map_nil, stLoop]
    split_ifs <;> simp
  | succ r ih =>
    have hmap : (List.range r).reverse.map (loopAt m (famClimbPart (r + 1)) g) =
        (List.range r).reverse.map (loopAt m (famClimbPart r) g) := by
      refine List.map_congr_left fun j hj ↦ ?_
      rw [List.mem_reverse, List.mem_range] at hj
      exact loopAt_famClimbPart_succ_lt r g j hj
    rw [List.range_succ, List.reverse_append, List.map_append, List.prod_append, hmap]
    conv_lhs => rw [famClimbPart_succ, stLoop_append]
    simp only [List.reverse_singleton, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, loopAt_famClimbPart_succ_top]
    simp only [stLoop, stPerm, famClimbStep, SBlock.perm, SBlock.strandLoop, SBlock.carries,
      decide_eq_true_eq]
    split_ifs <;> rw [ih] <;> split_ifs <;> first | omega | simp

/-- The gap factors of the partial climbs. -/
private theorem gapProd_famClimbPart {m : ℕ} (r : ℕ) (g : Fin m → G) (n : ℕ) :
    gapProd m (famClimbPart r) g n =
      if 1 ≤ n ∧ n ≤ r then loopAt m (famClimbPart r) g (n - 1) else 1 := by
  induction r with
  | zero =>
    simp only [famClimbPart, List.range_zero, List.map_nil, gapProd]
    split_ifs <;> first | rfl | omega
  | succ r ih =>
    conv_lhs => rw [famClimbPart_succ, gapProd_append, ih]
    simp only [gapProd, famClimbStep_gapLoop, one_mul]
    by_cases hn : n = r + 1
    · subst hn
      rw [Nat.add_sub_cancel, loopAt_famClimbPart_succ_top]
      simp
    · simp only [hn, ite_false, one_mul]
      split_ifs <;> first | omega | rfl | rw [loopAt_famClimbPart_succ_lt r g _ (by omega)]

theorem stPerm_famClimbs (k t : ℕ) :
    stPerm (famClimbs k) t = if t = 2 * k - 1 then 0 else if t < 2 * k - 1 then t + 1 else t := by
  rw [famClimbs_eq_part, stPerm_famClimbPart]

theorem stCount_famClimbs (k t : ℕ) :
    stCount (famClimbs k) t = if t = 2 * k - 1 then ((2 * k - 1 : ℕ) : ℤ) else 0 := by
  rw [famClimbs_eq_part, stCount_famClimbPart]

set_option linter.unusedVariables false in
theorem stLoop_famClimbs (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (t : ℕ) :
    stLoop (4 * k + 3) (famClimbs k) g t =
      if t = 2 * k - 1 then
        ((List.range (2 * k - 1)).reverse.map (loopAt (4 * k + 3) (famClimbs k) g)).prod
      else 1 := by
  rw [famClimbs_eq_part, stLoop_famClimbPart]

set_option linter.unusedVariables false in
theorem gapProd_famClimbs (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (n : ℕ) :
    gapProd (4 * k + 3) (famClimbs k) g n =
      if 1 ≤ n ∧ n ≤ 2 * k - 1 then loopAt (4 * k + 3) (famClimbs k) g (n - 1) else 1 := by
  rw [famClimbs_eq_part, gapProd_famClimbPart]

/-- The gap factor of a band. -/
theorem gapLoop_band_eq {m : ℕ} (f : Fin m → G) (i j n : ℕ) :
    (SBlock.band i j).gapLoop f n =
      if i + 1 ≤ n ∧ n ≤ j then (SBlock.band i j).loop f else 1 :=
  rfl

/-- The gap factor of a negative letter. -/
private theorem gapLoop_neg_eq {m : ℕ} (f : Fin m → G) (i n : ℕ) :
    (SBlock.neg i).gapLoop f n = if n = i + 1 then (SBlock.neg i).loop f else 1 := by
  simp only [SBlock.gapLoop, SBlock.lo, SBlock.hi]
  congr 1
  simp only [eq_iff_iff]
  omega

/-- The strand loop of a band. -/
private theorem strandLoop_band_eq {m : ℕ} (f : Fin m → G) (i j t : ℕ) :
    (SBlock.band i j).strandLoop f t =
      if t = j ∨ (i < t ∧ t < j) then (SBlock.band i j).loop f else 1 := by
  simp only [SBlock.strandLoop, SBlock.carries, decide_eq_true_eq]

/-- The strand loop of a negative letter. -/
private theorem strandLoop_neg_eq {m : ℕ} (f : Fin m → G) (i t : ℕ) :
    (SBlock.neg i).strandLoop f t = if t = i then (SBlock.neg i).loop f else 1 := by
  simp only [SBlock.strandLoop, SBlock.carries, decide_eq_true_eq]

/-- The loop of the first block of a three-block list. -/
private theorem loopAt_three_zero {m : ℕ} (b₀ b₁ b₂ : SBlock) (g : Fin m → G) :
    loopAt m [b₀, b₁, b₂] g 0 = b₀.loop g := by
  simp [loopAt, runTop_nil]

/-- The loop of the second block of a three-block list. -/
private theorem loopAt_three_one {m : ℕ} (b₀ b₁ b₂ : SBlock) (g : Fin m → G) :
    loopAt m [b₀, b₁, b₂] g 1 = b₁.loop (b₀.step m g) := by
  simp [loopAt, runTop_cons, runTop_nil]

/-- The loop of the third block of a three-block list. -/
private theorem loopAt_three_two {m : ℕ} (b₀ b₁ b₂ : SBlock) (g : Fin m → G) :
    loopAt m [b₀, b₁, b₂] g 2 = b₂.loop (b₁.step m (b₀.step m g)) := by
  simp [loopAt, runTop_cons, runTop_nil]

/-- The strand permutation of a three-block list. -/
private theorem stPerm_three (b₀ b₁ b₂ : SBlock) (t : ℕ) :
    stPerm [b₀, b₁, b₂] t = b₀.perm (b₁.perm (b₂.perm t)) := rfl

/-- The meridian counts of a three-block list. -/
private theorem stCount_three (b₀ b₁ b₂ : SBlock) (t : ℕ) :
    stCount [b₀, b₁, b₂] t =
      b₂.count t + b₁.count (b₂.perm t) + b₀.count (b₁.perm (b₂.perm t)) := by
  simp [stCount, stPerm]

/-- The strand loops of a three-block list. -/
private theorem stLoop_three {m : ℕ} (b₀ b₁ b₂ : SBlock) (g : Fin m → G) (t : ℕ) :
    stLoop m [b₀, b₁, b₂] g t =
      b₂.strandLoop (b₁.step m (b₀.step m g)) t *
        b₁.strandLoop (b₀.step m g) (b₂.perm t) * b₀.strandLoop g (b₁.perm (b₂.perm t)) := by
  simp [stLoop, stPerm]

/-- The gap factors of a three-block list. -/
private theorem gapProd_three {m : ℕ} (b₀ b₁ b₂ : SBlock) (g : Fin m → G) (n : ℕ) :
    gapProd m [b₀, b₁, b₂] g n = b₂.gapLoop (b₁.step m (b₀.step m g)) n *
      b₁.gapLoop (b₀.step m g) n * b₀.gapLoop g n := by
  simp [gapProd]

theorem stPerm_famMid (k t : ℕ) (hk : 1 ≤ k) :
    stPerm (famMid k) t =
      if t = 4 * k + 1 then 4 * k + 2 else if t = 4 * k + 2 then 4 * k - 1
      else if t = 4 * k then 2 * k - 1 else if t = 4 * k - 1 then 4 * k + 1
      else if t = 2 * k - 1 then 4 * k else t := by
  simp only [famMid, stPerm_three, SBlock.perm]
  split_ifs <;> omega

theorem stCount_famMid (k t : ℕ) (hk : 1 ≤ k) :
    stCount (famMid k) t =
      if t = 4 * k + 1 then -1 else if t = 4 * k + 2 ∨ t = 4 * k then 1 else 0 := by
  simp only [famMid, stCount_three, SBlock.perm, SBlock.count]
  split_ifs <;> omega

theorem stLoop_famMid (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (t : ℕ) :
    stLoop (4 * k + 3) (famMid k) g t =
      if t = 4 * k + 1 then loopAt (4 * k + 3) (famMid k) g 2
      else if t = 4 * k + 2 ∨ t = 4 * k then
        loopAt (4 * k + 3) (famMid k) g 1 * loopAt (4 * k + 3) (famMid k) g 0
      else if 2 * k ≤ t ∧ t ≤ 4 * k - 2 then loopAt (4 * k + 3) (famMid k) g 0
      else 1 := by
  simp only [famMid, stLoop_three, loopAt_three_zero, loopAt_three_one,
    loopAt_three_two, SBlock.perm, strandLoop_band_eq, strandLoop_neg_eq]
  split_ifs <;> first | omega | simp

theorem gapProd_famMid (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (n : ℕ) :
    gapProd (4 * k + 3) (famMid k) g n =
      if 2 * k ≤ n ∧ n ≤ 4 * k - 1 then loopAt (4 * k + 3) (famMid k) g 0
      else if n = 4 * k then
        loopAt (4 * k + 3) (famMid k) g 1 * loopAt (4 * k + 3) (famMid k) g 0
      else if n = 4 * k + 1 then loopAt (4 * k + 3) (famMid k) g 1
      else if n = 4 * k + 2 then loopAt (4 * k + 3) (famMid k) g 2
      else 1 := by
  simp only [famMid, gapProd_three, loopAt_three_zero, loopAt_three_one,
    loopAt_three_two, gapLoop_band_eq, gapLoop_neg_eq]
  split_ifs <;> first | omega | simp

theorem stPerm_famTop (k t : ℕ) (hk : 1 ≤ k) :
    stPerm (famTop k) t =
      if t = 4 * k + 1 then 4 * k + 2 else if t = 4 * k + 2 then 2 * k
      else if t = 2 * k + 1 then 0 else if t = 2 * k then 4 * k + 1
      else if t = 0 then 2 * k + 1 else t := by
  simp only [famTop, stPerm_three, SBlock.perm]
  split_ifs <;> first | omega | contradiction

theorem stCount_famTop (k t : ℕ) (hk : 1 ≤ k) :
    stCount (famTop k) t =
      if t = 4 * k + 1 then -1 else if t = 4 * k + 2 ∨ t = 2 * k + 1 then 1 else 0 := by
  simp only [famTop, stCount_three, SBlock.perm, SBlock.count]
  split_ifs <;> omega

theorem stLoop_famTop (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (t : ℕ) :
    stLoop (4 * k + 3) (famTop k) g t =
      if t = 4 * k + 1 then loopAt (4 * k + 3) (famTop k) g 2
      else if t = 4 * k + 2 ∨ t = 2 * k + 1 then
        loopAt (4 * k + 3) (famTop k) g 1 * loopAt (4 * k + 3) (famTop k) g 0
      else if 2 * k + 2 ≤ t ∧ t ≤ 4 * k then loopAt (4 * k + 3) (famTop k) g 1
      else if 1 ≤ t ∧ t ≤ 2 * k - 1 then loopAt (4 * k + 3) (famTop k) g 0
      else 1 := by
  simp only [famTop, stLoop_three, loopAt_three_zero, loopAt_three_one,
    loopAt_three_two, SBlock.perm, strandLoop_band_eq, strandLoop_neg_eq]
  split_ifs <;> first | omega | simp

set_option linter.unusedVariables false in
theorem gapProd_famTop (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (n : ℕ) :
    gapProd (4 * k + 3) (famTop k) g n =
      if 1 ≤ n ∧ n ≤ 2 * k then loopAt (4 * k + 3) (famTop k) g 0
      else if n = 2 * k + 1 then
        loopAt (4 * k + 3) (famTop k) g 1 * loopAt (4 * k + 3) (famTop k) g 0
      else if 2 * k + 2 ≤ n ∧ n ≤ 4 * k + 1 then loopAt (4 * k + 3) (famTop k) g 1
      else if n = 4 * k + 2 then loopAt (4 * k + 3) (famTop k) g 2
      else 1 := by
  simp only [famTop, gapProd_three, loopAt_three_zero, loopAt_three_one,
    loopAt_three_two, gapLoop_band_eq, gapLoop_neg_eq]
  split_ifs <;> first | omega | simp

end AJConjecture
