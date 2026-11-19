import Mathlib
import AJFamily.Classical.FamilyPeripheralWord

/-!
# The staircase phase of the family word

The strand permutation, meridian counts, strand loops and gap factors of the staircase
`famStair k`, the bands `b(4k-2-s, 4k-s)` for `s < 2k-1`, read on an arbitrary tuple `g` below
it and expressed through its own block loops `loopAt … (famStair k) g s`. The strands at the
top positions `2k` and `2k+1` collect the odd and the even steps' loops in descending order.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The `s`-th step `b(4k-2-s, 4k-s)` of the staircase. -/
private def famStairStep (k s : ℕ) : SBlock := SBlock.band (4 * k - 2 - s) (4 * k - s)

/-- The partial staircase made of its first `r` steps. -/
private def famStairPart (k r : ℕ) : List SBlock := (List.range r).map (famStairStep k)

/-- The staircase is the partial staircase of `2k-1` steps. -/
private theorem famStair_eq_part (k : ℕ) : famStair k = famStairPart k (2 * k - 1) := rfl

/-- Splitting off the top step of a partial staircase. -/
private theorem famStairPart_succ (k r : ℕ) :
    famStairPart k (r + 1) = famStairPart k r ++ [famStairStep k r] := by
  simp [famStairPart, List.range_succ]

/-- The strand permutation of a single block. -/
private theorem stPerm_singleton_block (b : SBlock) (t : ℕ) : stPerm [b] t = b.perm t := rfl

/-- The meridian count of a single block. -/
private theorem stCount_singleton_block (b : SBlock) (t : ℕ) : stCount [b] t = b.count t := by
  simp [stCount, stPerm]

/-- The strand loop of a single block. -/
private theorem stLoop_singleton_block (m : ℕ) (b : SBlock) (f : Fin m → G) (t : ℕ) :
    stLoop m [b] f t = b.strandLoop f t := by
  simp [stLoop, stPerm]

/-- The gap factor of a single block. -/
private theorem gapProd_singleton_block (m : ℕ) (b : SBlock) (f : Fin m → G) (n : ℕ) :
    gapProd m [b] f n = b.gapLoop f n := by
  simp [gapProd]

/-- The loop of the `s`-th staircase step is its loop read above the first `s` steps. -/
private theorem loopAt_famStair_eq (k : ℕ) (g : Fin (4 * k + 3) → G) (s : ℕ)
    (hs : s < 2 * k - 1) :
    loopAt (4 * k + 3) (famStair k) g s =
      (famStairStep k s).loop (runTop (4 * k + 3) (famStairPart k s) g) := by
  simp [loopAt, famStair_eq_part, famStairPart, ← List.map_take, List.take_range, hs.le,
    List.getElem?_range hs]

/-- The pair of alternating products `(T (r-1) T (r-3) ⋯, T (r-2) T (r-4) ⋯)`. -/
private def famStairAlt (T : ℕ → G) : ℕ → G × G
  | 0 => (1, 1)
  | r + 1 => (T r * (famStairAlt T r).2, (famStairAlt T r).1)

/-- Closed form of the alternating products. -/
private theorem famStairAlt_closed (T : ℕ → G) (m : ℕ) :
    famStairAlt T (2 * m + 1) =
      (((List.range (m + 1)).reverse.map fun j ↦ T (2 * j)).prod,
        ((List.range m).reverse.map fun j ↦ T (2 * j + 1)).prod) ∧
    famStairAlt T (2 * m) =
      (((List.range m).reverse.map fun j ↦ T (2 * j + 1)).prod,
        ((List.range m).reverse.map fun j ↦ T (2 * j)).prod) := by
  induction m with
  | zero => simp [famStairAlt]
  | succ m ih =>
    have h2 : famStairAlt T (2 * (m + 1)) = (T (2 * m + 1) * (famStairAlt T (2 * m + 1)).2,
        (famStairAlt T (2 * m + 1)).1) := rfl
    have h3 : famStairAlt T (2 * (m + 1) + 1) =
        (T (2 * (m + 1)) * (famStairAlt T (2 * (m + 1))).2, (famStairAlt T (2 * (m + 1))).1) :=
      rfl
    rw [h3, h2, ih.1]
    simp [List.range_succ]

/-- The strand permutation of the staircase step. -/
private theorem famStairStep_perm (k s t : ℕ) : (famStairStep k s).perm t =
    if t = 4 * k - 2 - s then 4 * k - s else if t = 4 * k - s then 4 * k - 2 - s else t := rfl

/-- The meridian count of the staircase step. -/
private theorem famStairStep_count (k s t : ℕ) :
    (famStairStep k s).count t = if t = 4 * k - s then 1 else 0 := rfl

/-- The strand loop of the staircase step. -/
private theorem famStairStep_strandLoop {m : ℕ} (k s t : ℕ) (hs : s + 2 ≤ 4 * k)
    (f : Fin m → G) : (famStairStep k s).strandLoop f t =
      if t = 4 * k - s ∨ t = 4 * k - 1 - s then (famStairStep k s).loop f else 1 := by
  simp only [famStairStep, SBlock.strandLoop, SBlock.carries]
  congr 1
  simp only [decide_eq_true_eq, eq_iff_iff]
  omega

/-- The gap factor of the staircase step. -/
private theorem famStairStep_gapLoop {m : ℕ} (k s n : ℕ) (hs : s + 2 ≤ 4 * k)
    (f : Fin m → G) : (famStairStep k s).gapLoop f n =
      if 4 * k - 1 - s ≤ n ∧ n ≤ 4 * k - s then (famStairStep k s).loop f else 1 := by
  simp only [famStairStep, SBlock.gapLoop, SBlock.lo, SBlock.hi]
  congr 1
  simp only [eq_iff_iff]
  omega

/-- The strand permutation of the partial staircase of `r` steps. -/
private theorem stPerm_famStairPart (k r t : ℕ) (hk : 1 ≤ k) (hr : r ≤ 2 * k - 1) :
    stPerm (famStairPart k r) t =
      if t = 4 * k - 1 - r then (if r % 2 = 1 then 4 * k else 4 * k - 1)
      else if t = 4 * k - r then (if r % 2 = 1 then 4 * k - 1 else 4 * k)
      else if 4 * k + 1 - r ≤ t ∧ t ≤ 4 * k then t - 2 else t := by
  induction r generalizing t with
  | zero =>
    simp only [famStairPart, List.range_zero, List.map_nil, stPerm]
    split_ifs <;> first | omega | simp_all
  | succ r ih =>
    rw [famStairPart_succ, stPerm_append, stPerm_singleton_block, famStairStep_perm]
    split_ifs <;> rw [ih _ (by omega)] <;> split_ifs <;> omega

/-- The meridian counts of the partial staircase of `r` steps. -/
private theorem stCount_famStairPart (k r t : ℕ) (hk : 1 ≤ k) (hr : r ≤ 2 * k - 1) :
    stCount (famStairPart k r) t = if 4 * k + 1 - r ≤ t ∧ t ≤ 4 * k then 1 else 0 := by
  induction r generalizing t with
  | zero =>
    simp only [famStairPart, List.range_zero, List.map_nil, stCount]
    split_ifs <;> first | rfl | omega
  | succ r ih =>
    rw [famStairPart_succ, stCount_append, stCount_singleton_block, famStairStep_count,
      stPerm_singleton_block, famStairStep_perm]
    split_ifs <;> rw [ih _ (by omega)] <;> split_ifs <;> omega

/-- The strand loops of the partial staircase of `r` steps, in terms of the loops of the
staircase. -/
private theorem stLoop_famStairPart (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 2 * k - 1)
    (g : Fin (4 * k + 3) → G) (t : ℕ) :
    stLoop (4 * k + 3) (famStairPart k r) g t =
      if t = 4 * k - 1 - r then (famStairAlt (loopAt (4 * k + 3) (famStair k) g) r).2
      else if t = 4 * k - r then (famStairAlt (loopAt (4 * k + 3) (famStair k) g) r).1
      else if 4 * k + 1 - r ≤ t ∧ t ≤ 4 * k then loopAt (4 * k + 3) (famStair k) g (4 * k - t)
      else 1 := by
  induction r generalizing t with
  | zero =>
    simp only [famStairPart, List.range_zero, List.map_nil, stLoop, famStairAlt]
    split_ifs <;> first | rfl | omega
  | succ r ih =>
    have e1 : (famStairAlt (loopAt (4 * k + 3) (famStair k) g) (r + 1)).1 =
        loopAt (4 * k + 3) (famStair k) g r *
          (famStairAlt (loopAt (4 * k + 3) (famStair k) g) r).2 := rfl
    have e2 : (famStairAlt (loopAt (4 * k + 3) (famStair k) g) (r + 1)).2 =
        (famStairAlt (loopAt (4 * k + 3) (famStair k) g) r).1 := rfl
    rw [famStairPart_succ, stLoop_append, stLoop_singleton_block,
      famStairStep_strandLoop _ _ _ (by omega), ← loopAt_famStair_eq k g r (by omega),
      stPerm_singleton_block, famStairStep_perm, e1, e2]
    split_ifs <;> rw [ih (by omega)] <;> split_ifs <;>
      first | rfl | omega | simp only [one_mul] | (simp only [mul_one]; congr 1; omega)

/-- The gap factors of the partial staircase of `r` steps, in terms of the loops of the
staircase. -/
private theorem gapProd_famStairPart (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 2 * k - 1)
    (g : Fin (4 * k + 3) → G) (n : ℕ) :
    gapProd (4 * k + 3) (famStairPart k r) g n =
      if n = 4 * k ∧ 1 ≤ r then loopAt (4 * k + 3) (famStair k) g 0
      else if 4 * k - r < n ∧ n ≤ 4 * k - 1 then
        loopAt (4 * k + 3) (famStair k) g (4 * k - n) *
          loopAt (4 * k + 3) (famStair k) g (4 * k - 1 - n)
      else if n = 4 * k - r ∧ 1 ≤ r then loopAt (4 * k + 3) (famStair k) g (r - 1)
      else 1 := by
  induction r with
  | zero =>
    simp only [famStairPart, List.range_zero, List.map_nil, gapProd]
    split_ifs <;> first | rfl | omega
  | succ r ih =>
    rw [famStairPart_succ, gapProd_append, gapProd_singleton_block,
      famStairStep_gapLoop _ _ _ (by omega), ← loopAt_famStair_eq k g r (by omega),
      ih (by omega)]
    split_ifs <;>
      first | omega | simp only [one_mul] | (simp only [mul_one]; congr 1; omega) |
        (congr 1 <;> congr 1 <;> omega) | simp_all

theorem stPerm_famStair (k t : ℕ) (hk : 1 ≤ k) :
    stPerm (famStair k) t =
      if t = 2 * k then 4 * k else if t = 2 * k + 1 then 4 * k - 1
      else if 2 * k + 2 ≤ t ∧ t ≤ 4 * k then t - 2 else t := by
  rw [famStair_eq_part, stPerm_famStairPart k _ t hk le_rfl]
  split_ifs <;> omega

theorem stCount_famStair (k t : ℕ) (hk : 1 ≤ k) :
    stCount (famStair k) t = if 2 * k + 2 ≤ t ∧ t ≤ 4 * k then 1 else 0 := by
  rw [famStair_eq_part, stCount_famStairPart k _ t hk le_rfl]
  split_ifs <;> first | rfl | omega

theorem stLoop_famStair (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (t : ℕ) :
    stLoop (4 * k + 3) (famStair k) g t =
      if t = 2 * k then
        ((List.range (k - 1)).reverse.map fun r ↦ loopAt (4 * k + 3) (famStair k) g (2 * r + 1)).prod
      else if t = 2 * k + 1 then
        ((List.range k).reverse.map fun r ↦ loopAt (4 * k + 3) (famStair k) g (2 * r)).prod
      else if 2 * k + 2 ≤ t ∧ t ≤ 4 * k then loopAt (4 * k + 3) (famStair k) g (4 * k - t)
      else 1 := by
  conv_lhs => rw [famStair_eq_part]
  rw [stLoop_famStairPart k _ hk le_rfl]
  obtain ⟨h1, -⟩ := famStairAlt_closed (loopAt (4 * k + 3) (famStair k) g) (k - 1)
  rw [show 2 * (k - 1) + 1 = 2 * k - 1 by omega, Nat.sub_add_cancel hk] at h1
  rw [h1]
  split_ifs <;> first | rfl | omega

theorem gapProd_famStair (k : ℕ) (hk : 1 ≤ k) (g : Fin (4 * k + 3) → G) (n : ℕ) :
    gapProd (4 * k + 3) (famStair k) g n =
      if n = 4 * k then loopAt (4 * k + 3) (famStair k) g 0
      else if 2 * k + 2 ≤ n ∧ n ≤ 4 * k - 1 then
        loopAt (4 * k + 3) (famStair k) g (4 * k - n) *
          loopAt (4 * k + 3) (famStair k) g (4 * k - 1 - n)
      else if n = 2 * k + 1 then loopAt (4 * k + 3) (famStair k) g (2 * k - 2)
      else 1 := by
  conv_lhs => rw [famStair_eq_part]
  rw [gapProd_famStairPart k _ hk le_rfl]
  split_ifs <;> first | rfl | omega

end AJConjecture
