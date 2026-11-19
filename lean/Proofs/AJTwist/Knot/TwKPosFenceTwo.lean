import Mathlib
import AJTwist.Knot.TwKPosFence

/-!
# The fence word for the companion `T(2, s)` in closed form, both clasp signs

`twStripTail_two`: the fence word of `twBlocks 2 s 0 σ` is `u1 +0 · twkStrip2Tail s σ`. This is
a new computation: for `r = 2` the library reaches the older `stripWord` of `AJFamily`, not the
generic fence word. The blocks of `pairBlocks 2 s` (`T = 2s - 1`) are `band 0 1`, the `s - 2`
blocks `band j (j+1)` of the increasing run, the big climb `band (s-2) (2s-2)`, round `0`
`band (2s-3) (2s-1)`, `neg (2s-1)`, the `s - 2` rounds `band (2s-4-j) (2s-2-j)`, `band 0 s`,
`band (s-1) (2s-1)`, `neg (2s-1)`.

Route: as `isoFenceWord_pairBlocks` (`AJHandoff.TorusKnot.PairKIsoStrip`) with `q = 0`: the first
and the last block of every disc, the open discs and the positions at every block
(`isoFirst`, `isoLast`, `isoPos`), then the fence block of every block. In the fence word the big
climb is the last block `isoStInc 0` of the increasing run (the disc `s - 1` closes, the disc
`2s - 2` opens). The sign `σ` enters only through `isoFenceWord_map_twClaspBlock`: the two Hopf
blocks are bands of span two between the positions of the discs `2s - 1` and `2s`.

Checked by evaluating the Lean definitions (`SCR/KP/leancheck/EvalFence.lean`): the statement
holds for `s = 3, 5, 7`, both signs.
-/

namespace AJConjecture

/-! ### The blocks of `pairBlocks 2 (a + 3)` -/

/-- The lower disc of the block `k` of `pairBlocks 2 (a + 3)`. -/
private def twoLo (a k : ℕ) : ℕ :=
  if k ≤ a then k else if k = a + 1 then a + 1 else if k = a + 2 then 2 * a + 3
  else if k = a + 3 then 2 * a + 5 else if k ≤ 2 * a + 4 then 3 * a + 6 - k
  else if k = 2 * a + 5 then 0 else if k = 2 * a + 6 then a + 2 else 2 * a + 5

/-- The upper disc of the block `k` of `pairBlocks 2 (a + 3)`. -/
private def twoHi (a k : ℕ) : ℕ :=
  if k ≤ a then k + 1 else if k = a + 1 then 2 * a + 4 else if k = a + 2 then 2 * a + 5
  else if k = a + 3 then 2 * a + 6 else if k ≤ 2 * a + 4 then 3 * a + 8 - k
  else if k = 2 * a + 5 then a + 3 else if k = 2 * a + 6 then 2 * a + 5 else 2 * a + 6

/-- The block `k` of `pairBlocks 2 (a + 3)`. -/
private def twoBlk (a k : ℕ) : SBlock :=
  if k = a + 3 ∨ k = 2 * a + 7 then SBlock.neg (2 * a + 5)
  else SBlock.band (twoLo a k) (twoHi a k)

/-- The first block of the disc `m` of `pairBlocks 2 (a + 3)`. -/
private def twoF (a m : ℕ) : ℕ :=
  if m ≤ a + 1 then m - 1 else if m = a + 2 then 2 * a + 4 else if m = 2 * a + 3 then a + 2
  else if m ≤ 2 * a + 3 then 3 * a + 6 - m else if m = 2 * a + 4 then a + 1
  else if m = 2 * a + 5 then a + 2 else a + 3

/-- The last block of the disc `m` of `pairBlocks 2 (a + 3)`. -/
private def twoL (a m : ℕ) : ℕ :=
  if m ≤ a + 1 then m else if m = a + 2 then 2 * a + 6 else if m = a + 3 then 2 * a + 5
  else if m ≤ 2 * a + 3 then 3 * a + 8 - m else if m = 2 * a + 4 then a + 4 else 2 * a + 7

/-- Chooses the case of a case-by-case description. -/
local macro "two_pick" : tactic =>
  `(tactic| first
    | (left; omega) | (right; left; omega) | (right; right; left; omega)
    | (right; right; right; left; omega) | (right; right; right; right; left; omega)
    | (right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; left; omega)
    | (right; right; right; right; right; right; right; omega)
    | (right; right; right; right; right; right; omega)
    | (right; right; right; right; right; omega))

/-- The discs of the block `k`, case by case. -/
private theorem twoEnds_spec (a k : ℕ) :
    (k ≤ a ∧ twoLo a k = k ∧ twoHi a k = k + 1) ∨
    (k = a + 1 ∧ twoLo a k = a + 1 ∧ twoHi a k = 2 * a + 4) ∨
    (k = a + 2 ∧ twoLo a k = 2 * a + 3 ∧ twoHi a k = 2 * a + 5) ∨
    (k = a + 3 ∧ twoLo a k = 2 * a + 5 ∧ twoHi a k = 2 * a + 6) ∨
    (a + 4 ≤ k ∧ k ≤ 2 * a + 4 ∧ twoLo a k = 3 * a + 6 - k ∧ twoHi a k = 3 * a + 8 - k) ∨
    (k = 2 * a + 5 ∧ twoLo a k = 0 ∧ twoHi a k = a + 3) ∨
    (k = 2 * a + 6 ∧ twoLo a k = a + 2 ∧ twoHi a k = 2 * a + 5) ∨
    (2 * a + 7 ≤ k ∧ twoLo a k = 2 * a + 5 ∧ twoHi a k = 2 * a + 6) := by
  unfold twoLo twoHi
  split_ifs <;> two_pick

/-- The first block of the disc `m`, case by case. -/
private theorem twoF_spec (a m : ℕ) :
    (m ≤ a + 1 ∧ twoF a m = m - 1) ∨ (m = a + 2 ∧ twoF a m = 2 * a + 4) ∨
    (a + 3 ≤ m ∧ m = 2 * a + 3 ∧ twoF a m = a + 2) ∨
    (a + 3 ≤ m ∧ m < 2 * a + 3 ∧ twoF a m = 3 * a + 6 - m) ∨
    (m = 2 * a + 4 ∧ twoF a m = a + 1) ∨ (m = 2 * a + 5 ∧ twoF a m = a + 2) ∨
    (2 * a + 6 ≤ m ∧ twoF a m = a + 3) := by
  unfold twoF
  split_ifs <;> two_pick

/-- The last block of the disc `m`, case by case. -/
private theorem twoL_spec (a m : ℕ) :
    (m ≤ a + 1 ∧ twoL a m = m) ∨ (m = a + 2 ∧ twoL a m = 2 * a + 6) ∨
    (m = a + 3 ∧ twoL a m = 2 * a + 5) ∨
    (a + 4 ≤ m ∧ m ≤ 2 * a + 3 ∧ twoL a m = 3 * a + 8 - m) ∨
    (m = 2 * a + 4 ∧ twoL a m = a + 4) ∨ (2 * a + 5 ≤ m ∧ twoL a m = 2 * a + 7) := by
  unfold twoL
  split_ifs <;> two_pick

/-- The discs joined by the block `k`. -/
private theorem isoEnds_twoBlk (a k : ℕ) : isoEnds (twoBlk a k) = (twoLo a k, twoHi a k) := by
  unfold twoBlk
  split_ifs with h
  · simp only [isoEnds, twoLo, twoHi]
    rcases h with rfl | rfl <;> split_ifs <;> first | rfl | omega
  · rfl

/-- The blocks of `pairBlocks 2 (a + 3)`, one by one. -/
private theorem pairBlocks_two_getElem? (a k : ℕ) (hk : k < 2 * a + 8) :
    (pairBlocks 2 (a + 3))[k]? = some (twoBlk a k) := by
  have hE : pairRunDown 2 (a + 3) = 1 := by simp [pairRunDown]
  have hz : pairRunUp 2 (a + 3) = a := by simp [pairRunUp, pairC]
  have hT : pairTop 2 (a + 3) = 2 * a + 5 := by simp [pairTop, pairC]; omega
  by_cases h0 : k = 0
  · have := pairBlocks_getElem?_runDown (r := 2) (s := a + 3) (j := 0) (by rw [hE]; omega)
    rw [hE] at this
    rw [h0, twoBlk, twoLo, twoHi, ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega)]
    exact this
  by_cases h1 : k ≤ a
  · have := pairBlocks_getElem?_runUp (r := 2) (s := a + 3) (j := k - 1) (by rw [hz]; omega)
    rw [hE, show 2 - 2 + 1 + (k - 1) = k by omega, show 2 - 1 + 1 + (k - 1) = k + 1 by omega]
      at this
    rw [twoBlk, twoLo, twoHi, ite_eq_right (by omega), ite_eq_left h1, ite_eq_left h1]
    exact this
  by_cases h2 : k = a + 1
  · have := pairBlocks_getElem?_bigClimb (r := 2) (s := a + 3)
    rw [hE, hz, hT, show 2 - 2 + 1 + a = a + 1 by omega,
      show 2 * a + 5 + 1 - 2 = 2 * a + 4 by omega] at this
    rw [h2, twoBlk, twoLo, twoHi, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl]
    exact this
  by_cases h3 : k = a + 2
  · have := pairBlocks_getElem?_roundZero (r := 2) (s := a + 3)
    rw [hE, hz, hT, show 2 - 2 + 1 + a + 1 = a + 2 by omega,
      show 2 * a + 5 - 2 = 2 * a + 3 by omega] at this
    rw [h3, twoBlk, twoLo, twoHi, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left rfl]
    exact this
  by_cases h4 : k = a + 3
  · have := pairBlocks_getElem?_hopfFirst (r := 2) (s := a + 3)
    rw [hE, hz, hT, show 2 - 2 + 1 + a + 2 = a + 3 by omega] at this
    rw [h4, twoBlk, ite_eq_left (Or.inl rfl)]
    exact this
  by_cases h5 : k ≤ 2 * a + 4
  · have := pairBlocks_getElem?_round (r := 2) (s := a + 3) (j := k - (a + 4)) (by omega)
    rw [hE, hz, hT, show 2 - 2 + 1 + a + 3 + (k - (a + 4)) = k by omega,
      show 2 * a + 5 - 2 - 1 - (k - (a + 4)) = 3 * a + 6 - k by omega,
      show 2 * a + 5 - 1 - (k - (a + 4)) = 3 * a + 8 - k by omega] at this
    rw [twoBlk, twoLo, twoHi, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h5, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left h5]
    exact this
  by_cases h6 : k = 2 * a + 5
  · have := pairBlocks_getElem?_lastRound (r := 2) (s := a + 3)
    rw [hE, hz, hT, show 2 - 2 + 1 + a + 3 + (a + 3 - 2) = 2 * a + 5 by omega,
      show 2 - 2 = 0 by omega, show 2 * a + 5 + 1 - (a + 3) = a + 3 by omega] at this
    rw [h6, twoBlk, twoLo, twoHi, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    exact this
  by_cases h7 : k = 2 * a + 6
  · have := pairBlocks_getElem?_topRight (r := 2) (s := a + 3)
    rw [hE, hz, hT, show 2 - 2 + 1 + a + 3 + (a + 3 - 2) + 1 = 2 * a + 6 by omega,
      show 2 * a + 5 - (a + 3) = a + 2 by omega] at this
    rw [h7, twoBlk, twoLo, twoHi, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    exact this
  · obtain rfl : k = 2 * a + 7 := by omega
    have := pairBlocks_getElem?_hopfSecond (r := 2) (s := a + 3) le_rfl
    rw [hE, hz, hT, show 2 - 2 + 1 + a + 3 + (a + 3 - 2) + 2 + (2 - 2) = 2 * a + 7 by omega]
      at this
    rw [twoBlk, ite_eq_left (Or.inr rfl)]
    exact this

/-- `pairBlocks 2 (a + 3)` as a list of `2a + 8` blocks. -/
private theorem pairBlocks_two_eq (a : ℕ) :
    pairBlocks 2 (a + 3) = (List.range (2 * a + 8)).map (twoBlk a) := by
  have hlen : (pairBlocks 2 (a + 3)).length = 2 * a + 8 := by
    rw [pairBlocks_length]
    simp only [pairRunDown, pairRunUp, pairC]
    omega
  refine List.ext_getElem? fun k ↦ ?_
  by_cases hk : k < 2 * a + 8
  · rw [pairBlocks_two_getElem? a k hk, List.getElem?_map, List.getElem?_range hk]
    rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- The block `k` is attached to the discs `twoLo a k` and `twoHi a k`. -/
private theorem isoAttached_twoBlk (a k m : ℕ) :
    isoAttached m (twoBlk a k) = decide (twoLo a k = m ∨ twoHi a k = m) := by
  rw [isoAttached, isoEnds_twoBlk]

/-- The first block of every disc. -/
private theorem isoFirst_two (a m : ℕ) (h1 : 1 ≤ m) (hm : m ≤ 2 * a + 6) :
    isoFirst (pairBlocks 2 (a + 3)) m = twoF a m := by
  rw [pairBlocks_two_eq]
  have hF : twoF a m < 2 * a + 8 := by have := twoF_spec a m; omega
  refine (List.findIdx_eq (by simpa using hF)).2 ⟨?_, fun j hj ↦ ?_⟩
  · rw [List.getElem_map, List.getElem_range, isoAttached_twoBlk, decide_eq_true_eq]
    have h2 := twoF_spec a m
    have h3 := twoEnds_spec a (twoF a m)
    omega
  · rw [List.getElem_map, List.getElem_range, isoAttached_twoBlk, decide_eq_false_iff_not]
    have h2 := twoF_spec a m
    have h3 := twoEnds_spec a j
    omega

/-- The last block attached to a disc, from its index. -/
private theorem isoLast_eq_twKFenceTwo {B : List SBlock} {m j : ℕ} (hj : j < B.length)
    (ha : isoAttached m B[j] = true)
    (hno : ∀ j' (h' : j' < B.length), j < j' → isoAttached m B[j'] = false) :
    isoLast B m = j := by
  have hlen : B.length - 1 - j < B.reverse.length := by
    rw [List.length_reverse]
    omega
  have key : B.reverse.findIdx (isoAttached m) = B.length - 1 - j := by
    refine (List.findIdx_eq hlen).2 ⟨?_, fun i hi ↦ ?_⟩
    · rw [List.getElem_reverse,
        getElem_congr_idx (show B.length - 1 - (B.length - 1 - j) = j by omega)]
      exact ha
    · rw [List.getElem_reverse]
      exact hno _ _ (by omega)
  unfold isoLast
  rw [key]
  omega

/-- The last block of every disc. -/
private theorem isoLast_two (a m : ℕ) (h1 : 1 ≤ m) (hm : m ≤ 2 * a + 6) :
    isoLast (pairBlocks 2 (a + 3)) m = twoL a m := by
  rw [pairBlocks_two_eq]
  have hL : twoL a m < 2 * a + 8 := by have := twoL_spec a m; omega
  refine isoLast_eq_twKFenceTwo (by simpa using hL) ?_ fun j' h' hj' ↦ ?_
  · rw [List.getElem_map, List.getElem_range, isoAttached_twoBlk, decide_eq_true_eq]
    have h2 := twoL_spec a m
    have h3 := twoEnds_spec a (twoL a m)
    omega
  · rw [List.length_map, List.length_range] at h'
    rw [List.getElem_map, List.getElem_range, isoAttached_twoBlk, decide_eq_false_iff_not]
    have h2 := twoL_spec a m
    have h3 := twoEnds_spec a j'
    omega

/-! ### Cups, caps and positions from the list of open discs -/

/-- A filtered range is the increasing list of its elements. -/
private theorem filter_range_eq_of_pairwise (p : ℕ → Bool) (N : ℕ) (S : List ℕ)
    (hS : S.Pairwise (· < ·)) (h : ∀ x, (x < N ∧ p x = true) ↔ x ∈ S) :
    (List.range N).filter p = S := by
  refine List.Perm.eq_of_pairwise' (r := (· < ·)) (List.pairwise_lt_range.filter p) hS ?_
  refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _)
    (hS.imp fun hab ↦ Nat.ne_of_lt hab)).2 fun x ↦ ?_
  rw [List.mem_filter, List.mem_range]
  exact h x

/-- The position of a disc from the increasing list of the open discs below it. -/
private theorem isoPos_two (a k m : ℕ) (S : List ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 2 * a + 7)
    (hS : S.Pairwise (· < ·))
    (h : ∀ x, (x < m ∧ 1 ≤ x ∧ twoF a x ≤ k ∧ k ≤ twoL a x) ↔ x ∈ S) :
    isoPos (pairBlocks 2 (a + 3)) 0 k m = 1 + 2 * S.length := by
  rw [isoPos, ite_eq_right (by omega), filter_range_eq_of_pairwise _ m S hS]
  intro x
  rw [← h x]
  refine and_congr_right fun hx ↦ ?_
  simp only [isoOpen, decide_eq_true_eq]
  refine and_congr_right fun hx1 ↦ ?_
  rw [isoFirst_two a x hx1 (by omega), isoLast_two a x hx1 (by omega)]
  omega

/-- The cups of a block from the increasing list of the discs it opens. -/
private theorem isoFenceCups_two (a k : ℕ) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (h : ∀ x, (x < 2 * a + 7 ∧ 0 < x ∧ twoF a x = k) ↔ x ∈ C) :
    isoFenceCups (2 * a + 6) (pairBlocks 2 (a + 3)) 0 k =
      C.map fun m ↦ isoU (isoPos (pairBlocks 2 (a + 3)) 0 k m) := by
  rw [isoFenceCups, filter_range_eq_of_pairwise _ _ C hC]
  intro x
  rw [← h x]
  refine and_congr_right fun hx ↦ ?_
  simp only [decide_eq_true_eq]
  refine and_congr_right fun hx1 ↦ ?_
  rw [isoFirst_two a x hx1 (by omega)]

/-- The caps of a block from the increasing list of the discs it closes. -/
private theorem isoFenceCaps_two (a k : ℕ) (D : List ℕ) (hD : D.Pairwise (· < ·))
    (h : ∀ x, (x < 2 * a + 7 ∧ 0 < x ∧ twoL a x = k) ↔ x ∈ D) :
    isoFenceCaps (2 * a + 6) (pairBlocks 2 (a + 3)) 0 k =
      D.reverse.map fun m ↦ isoN (isoPos (pairBlocks 2 (a + 3)) 0 k m) := by
  rw [isoFenceCaps, filter_range_eq_of_pairwise _ _ D hD]
  intro x
  rw [← h x]
  refine and_congr_right fun hx ↦ ?_
  simp only [decide_eq_true_eq]
  refine and_congr_right fun hx1 ↦ ?_
  rw [isoLast_two a x hx1 (by omega)]

/-! ### The fence blocks -/

/-- The fence block of the block `k` of `pairBlocks 2 (a + 3)` with the clasp sign `σ`. -/
private def twoW (a : ℕ) (σ : Bool) (k : ℕ) : MorseWord :=
  isoFenceCups (2 * a + 6) (pairBlocks 2 (a + 3)) 0 k ++
    isoBlockWord (isoPos (pairBlocks 2 (a + 3)) 0 k) (twClaspBlock σ (twoBlk a k)) ++
    isoFenceCaps (2 * a + 6) (pairBlocks 2 (a + 3)) 0 k

/-- The fence block of a band from the discs it opens and closes. -/
private theorem twoW_band (a : ℕ) (σ : Bool) (k lo hi : ℕ) (C D : List ℕ)
    (hb : twoBlk a k = SBlock.band lo hi) (hC : C.Pairwise (· < ·))
    (hCm : ∀ x, (x < 2 * a + 7 ∧ 0 < x ∧ twoF a x = k) ↔ x ∈ C) (hD : D.Pairwise (· < ·))
    (hDm : ∀ x, (x < 2 * a + 7 ∧ 0 < x ∧ twoL a x = k) ↔ x ∈ D) :
    twoW a σ k = (C.map fun m ↦ isoU (isoPos (pairBlocks 2 (a + 3)) 0 k m)) ++
      isoBand (isoPos (pairBlocks 2 (a + 3)) 0 k lo) (isoPos (pairBlocks 2 (a + 3)) 0 k hi) true ++
      D.reverse.map fun m ↦ isoN (isoPos (pairBlocks 2 (a + 3)) 0 k m) := by
  rw [twoW, hb, isoFenceCups_two a k C hC hCm, isoFenceCaps_two a k D hD hDm]
  rfl

/-- The fence block of a Hopf letter from the discs it opens and closes. -/
private theorem twoW_neg (a : ℕ) (σ : Bool) (k i : ℕ) (C D : List ℕ)
    (hb : twoBlk a k = SBlock.neg i) (hC : C.Pairwise (· < ·))
    (hCm : ∀ x, (x < 2 * a + 7 ∧ 0 < x ∧ twoF a x = k) ↔ x ∈ C) (hD : D.Pairwise (· < ·))
    (hDm : ∀ x, (x < 2 * a + 7 ∧ 0 < x ∧ twoL a x = k) ↔ x ∈ D) :
    twoW a σ k = (C.map fun m ↦ isoU (isoPos (pairBlocks 2 (a + 3)) 0 k m)) ++
      isoBand (isoPos (pairBlocks 2 (a + 3)) 0 k i) (isoPos (pairBlocks 2 (a + 3)) 0 k (i + 1))
        (!σ) ++
      D.reverse.map fun m ↦ isoN (isoPos (pairBlocks 2 (a + 3)) 0 k m) := by
  rw [twoW, hb, isoFenceCups_two a k C hC hCm, isoFenceCaps_two a k D hD hDm]
  cases σ <;> rfl

/-- The block `k` is a band. -/
private theorem twoBlk_band (a k lo hi : ℕ) (hk : k ≠ a + 3 ∧ k ≠ 2 * a + 7)
    (hlo : twoLo a k = lo) (hhi : twoHi a k = hi) : twoBlk a k = SBlock.band lo hi := by
  rw [twoBlk, ite_eq_right (by omega), hlo, hhi]

/-- Closes the description of the discs opened by, closed by or open at a block. -/
local macro "two_arith" a:term:max : tactic =>
  `(tactic| (
    intro x
    have hF := twoF_spec $a x
    have hL := twoL_spec $a x
    first
      | (simp only [List.not_mem_nil, iff_false]; omega)
      | (simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))

/-- Unfolds the cups and caps of a fence block. -/
local macro "two_lists" : tactic =>
  `(tactic| simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_nil])

/-- An increasing list of two discs. -/
private theorem two_pw2 {d₁ d₂ : ℕ} (h : d₁ < d₂) : [d₁, d₂].Pairwise (· < ·) :=
  List.pairwise_pair.2 h

/-- An increasing list of three discs. -/
private theorem two_pw3 {d₁ d₂ d₃ : ℕ} (h₁ : d₁ < d₂) (h₂ : d₂ < d₃) :
    [d₁, d₂, d₃].Pairwise (· < ·) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
  omega

/-- The head block: `u1 +0`. -/
private theorem twoW_zero (a : ℕ) (σ : Bool) : twoW a σ 0 = [isoU 1, isoX true 0] := by
  have hE := twoEnds_spec a 0
  rw [twoW_band a σ 0 0 1 [1] [] (twoBlk_band a 0 0 1 (by omega) (by omega) (by omega))
    (List.pairwise_singleton _ _) (by two_arith a) List.Pairwise.nil (by two_arith a)]
  two_lists
  rw [isoPos_two a 0 1 [] (by omega) (by omega) List.Pairwise.nil (by two_arith a)]
  rfl

/-- The blocks of the increasing run. -/
private theorem twoW_inc (a : ℕ) (σ : Bool) (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ a) :
    twoW a σ k = isoStInc 0 := by
  have hE := twoEnds_spec a k
  rw [twoW_band a σ k k (k + 1) [k + 1] [k]
    (twoBlk_band a k k (k + 1) (by omega) (by omega) (by omega))
    (List.pairwise_singleton _ _) (by two_arith a) (List.pairwise_singleton _ _)
    (by two_arith a)]
  two_lists
  rw [isoPos_two a k k [] (by omega) (by omega) List.Pairwise.nil (by two_arith a),
    isoPos_two a k (k + 1) [k] (by omega) (by omega) (List.pairwise_singleton _ _)
      (by two_arith a)]
  rfl

/-- The big climb: the last block of the increasing run. -/
private theorem twoW_climb (a : ℕ) (σ : Bool) (k : ℕ) (hk : k = a + 1) :
    twoW a σ k = isoStInc 0 := by
  have hE := twoEnds_spec a k
  rw [twoW_band a σ k (a + 1) (2 * a + 4) [2 * a + 4] [a + 1]
    (twoBlk_band a k _ _ (by omega) (by omega) (by omega))
    (List.pairwise_singleton _ _) (by two_arith a) (List.pairwise_singleton _ _)
    (by two_arith a)]
  two_lists
  rw [isoPos_two a k (a + 1) [] (by omega) (by omega) List.Pairwise.nil (by two_arith a),
    isoPos_two a k (2 * a + 4) [a + 1] (by omega) (by omega) (List.pairwise_singleton _ _)
      (by two_arith a)]
  rfl

/-- Round `0`. -/
private theorem twoW_r0 (a : ℕ) (σ : Bool) (k : ℕ) (hk : k = a + 2) :
    twoW a σ k = isoStR0 0 2 := by
  have hE := twoEnds_spec a k
  rw [twoW_band a σ k (2 * a + 3) (2 * a + 5) [2 * a + 3, 2 * a + 5] []
    (twoBlk_band a k _ _ (by omega) (by omega) (by omega))
    (two_pw2 (by omega)) (by two_arith a) List.Pairwise.nil (by two_arith a)]
  two_lists
  rw [isoPos_two a k (2 * a + 3) [] (by omega) (by omega) List.Pairwise.nil (by two_arith a),
    isoPos_two a k (2 * a + 5) [2 * a + 3, 2 * a + 4] (by omega) (by omega)
      (two_pw2 (by omega)) (by two_arith a)]
  rfl

/-- The first Hopf letter. -/
private theorem twoW_hopf (a : ℕ) (σ : Bool) (k : ℕ) (hk : k = a + 3) :
    twoW a σ k = twkStHopf 0 2 σ := by
  rw [twoW_neg a σ k (2 * a + 5) [2 * a + 6] []
    (by rw [twoBlk, ite_eq_left (Or.inl hk)])
    (List.pairwise_singleton _ _) (by two_arith a) List.Pairwise.nil (by two_arith a)]
  two_lists
  rw [isoPos_two a k (2 * a + 5) [2 * a + 3, 2 * a + 4] (by omega) (by omega)
      (two_pw2 (by omega)) (by two_arith a),
    isoPos_two a k (2 * a + 5 + 1) [2 * a + 3, 2 * a + 4, 2 * a + 5] (by omega) (by omega)
      (two_pw3 (by omega) (by omega)) (by two_arith a)]
  rfl

/-- The rounds. -/
private theorem twoW_round (a : ℕ) (σ : Bool) (k : ℕ) (h1 : a + 4 ≤ k) (h2 : k ≤ 2 * a + 4) :
    twoW a σ k = isoStRound 0 2 := by
  have hE := twoEnds_spec a k
  obtain ⟨l, rfl⟩ : ∃ l, k = 3 * a + 6 - l := ⟨3 * a + 6 - k, by omega⟩
  rw [twoW_band a σ _ l (l + 2) [l] [l + 2]
    (twoBlk_band a _ _ _ (by omega) (by omega) (by omega))
    (List.pairwise_singleton _ _) (by two_arith a) (List.pairwise_singleton _ _)
    (by two_arith a)]
  two_lists
  rw [isoPos_two a _ l [] (by omega) (by omega) List.Pairwise.nil (by two_arith a),
    isoPos_two a _ (l + 2) [l, l + 1] (by omega) (by omega) (two_pw2 (by omega))
      (by two_arith a)]
  rfl

/-- The descent to the disc `0`. -/
private theorem twoW_desc (a : ℕ) (σ : Bool) (k : ℕ) (hk : k = 2 * a + 5) :
    twoW a σ k = isoBand 0 3 true ++ [isoN 3] := by
  have hE := twoEnds_spec a k
  rw [twoW_band a σ k 0 (a + 3) [] [a + 3]
    (twoBlk_band a k _ _ (by omega) (by omega) (by omega))
    List.Pairwise.nil (by two_arith a) (List.pairwise_singleton _ _) (by two_arith a)]
  two_lists
  rw [isoPos_two a k (a + 3) [a + 2] (by omega) (by omega) (List.pairwise_singleton _ _)
      (by two_arith a)]
  rfl

/-- The top-right climb. -/
private theorem twoW_top (a : ℕ) (σ : Bool) (k : ℕ) (hk : k = 2 * a + 6) :
    twoW a σ k = isoBand 1 3 true ++ [isoN 1] := by
  have hE := twoEnds_spec a k
  rw [twoW_band a σ k (a + 2) (2 * a + 5) [] [a + 2]
    (twoBlk_band a k _ _ (by omega) (by omega) (by omega))
    List.Pairwise.nil (by two_arith a) (List.pairwise_singleton _ _) (by two_arith a)]
  two_lists
  rw [isoPos_two a k (a + 2) [] (by omega) (by omega) List.Pairwise.nil (by two_arith a),
    isoPos_two a k (2 * a + 5) [a + 2] (by omega) (by omega) (List.pairwise_singleton _ _)
      (by two_arith a)]
  rfl

/-- The second Hopf letter. -/
private theorem twoW_final (a : ℕ) (σ : Bool) (k : ℕ) (hk : k = 2 * a + 7) :
    twoW a σ k = twkStFinal σ := by
  rw [twoW_neg a σ k (2 * a + 5) [] [2 * a + 5, 2 * a + 6]
    (by rw [twoBlk, ite_eq_left (Or.inr hk)])
    List.Pairwise.nil (by two_arith a) (two_pw2 (by omega)) (by two_arith a)]
  two_lists
  rw [isoPos_two a k (2 * a + 5) [] (by omega) (by omega) List.Pairwise.nil (by two_arith a),
    isoPos_two a k (2 * a + 5 + 1) [2 * a + 5] (by omega) (by omega)
      (List.pairwise_singleton _ _) (by two_arith a)]
  rfl

/-! ### Assembly -/

/-- Blocks listed by a function of the index, with their indices. -/
private theorem flatMap_zipIdx_two {β : Type} (a : ℕ) (g : SBlock × ℕ → List β) :
    (pairBlocks 2 (a + 3)).zipIdx.flatMap g =
      (List.range (2 * a + 8)).flatMap fun k ↦ g (twoBlk a k, k) := by
  rw [pairBlocks_two_eq]
  generalize 2 * a + 8 = N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.zipIdx_append, List.flatMap_append,
      List.flatMap_append, ih]
    simp

/-- A concatenation over a range, split in two. -/
private theorem flatMap_range_add_two {β : Type} (m n : ℕ) (g : ℕ → List β) :
    (List.range (m + n)).flatMap g =
      (List.range m).flatMap g ++ (List.range n).flatMap fun i ↦ g (m + i) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

/-- A run of equal fence blocks. -/
private theorem flatMap_range_const_two (g : ℕ → MorseWord) (X : MorseWord) (n : ℕ)
    (h : ∀ i, i < n → g i = X) : (List.range n).flatMap g = phaseTwoBlk X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih fun i hi ↦ h i (by omega), List.flatMap_cons,
      List.flatMap_nil, List.append_nil, h n (by omega)]
    simp only [phaseTwoBlk, List.replicate_succ', List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]

/-- The fence blocks of `pairBlocks 2 (a + 3)` with clasp sign `σ`, concatenated. -/
private theorem flatMap_twoW (a : ℕ) (σ : Bool) :
    (List.range (2 * a + 8)).flatMap (twoW a σ) =
      [isoU 1, isoX true 0] ++ twkStrip2Tail (a + 3) σ := by
  rw [show 2 * a + 8 = 1 + (a + 1) + 2 + (a + 1) + 3 by omega, flatMap_range_add_two,
    flatMap_range_add_two, flatMap_range_add_two, flatMap_range_add_two,
    flatMap_range_const_two (fun i ↦ twoW a σ (1 + i)) (isoStInc 0) (a + 1) fun i hi ↦ by
      rcases Nat.lt_or_ge i a with h | h
      · exact twoW_inc a σ _ (by omega) (by omega)
      · exact twoW_climb a σ _ (by omega),
    flatMap_range_const_two (fun i ↦ twoW a σ (1 + (a + 1) + 2 + i)) (isoStRound 0 2) (a + 1)
      fun i hi ↦ twoW_round a σ _ (by omega) (by omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
  rw [twoW_zero, twoW_r0 a σ _ (by omega), twoW_hopf a σ _ (by omega),
    twoW_desc a σ _ (by omega), twoW_top a σ _ (by omega), twoW_final a σ _ (by omega),
    twkStrip2Tail, show a + 3 - 2 = a + 1 by omega]
  simp only [List.append_assoc]

/-- With the clasp sign `σ` and no twist the blocks are those of `pairBlocks` with the Hopf
letters of sign `σ`. -/
private theorem twBlocks_zero_eq_map_twKFenceTwo {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    twBlocks r s 0 σ = (pairBlocks r s).map (twClaspBlock σ) := by
  conv_rhs => rw [pairBlocks_eq_head_cons h]
  rw [twBlocks, twChain, ite_eq_left rfl]
  rfl

/-- The fence word of the untwisted list with clasp sign `σ` in closed form, `r = 2`. -/
theorem twStripTail_two {s : ℕ} (h : IsTorusPair 2 s) (σ : Bool) :
    twStripTail 2 s σ = twkStrip2Tail s σ := by
  obtain ⟨a, rfl⟩ : ∃ a, s = a + 3 := ⟨s - 3, by have := h.2.1; omega⟩
  have hn : pairStrands 2 (a + 3) - 1 = 2 * a + 6 := by
    simp only [pairStrands, pairC]
    omega
  rw [twStripTail, twBlocks_zero_eq_map_twKFenceTwo h, hn, isoFenceWord_map_twClaspBlock,
    flatMap_zipIdx_two]
  change ((List.range (2 * a + 8)).flatMap (twoW a σ)).drop 2 = _
  rw [flatMap_twoW]
  rfl

end AJConjecture
