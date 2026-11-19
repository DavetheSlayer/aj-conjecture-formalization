import Mathlib
import AJHandoff.TorusKnot.PairKIsoWords

/-!
# Thin words: the discs of a braided surface pulled out of the long closure

For a list `B` of blocks on `n + 1` strands (discs `0, …, n`; disc `0` carries the base point),
the long closure `morseLongClosure (n + 1) (blocksWord B)` draws disc `d ≥ 1` as the loop formed
by the strand `d` and its closing arc. *Thinning* the disc `d` moves its closing arc next to the
strand `d` (a flip of the return strand over everything inside the loop): the disc becomes a thin
vertical pair of strands, and every band that passed in front of it now passes in front of both
of its edges.

`isoThinPartial n B j` is the long closure with the discs `j + 1, …, n` thinned: the discs
`1, …, j` are still nested closing arcs, the discs above `j` are side by side inside the innermost
arc, disc `d > j` occupies the positions `2d - j - 1, 2d - j`, and a block joining the discs `a`,
`b` is the signed band between the positions of `a` and `b` (`isoThinIndex j`). For `j = n` this
is the long closure (`isoThinPartial_top`), for `j = 0` the thin word `isoThinWord n B`, in which
all discs are side by side (cups `u₁ u₃ ⋯ u_{2n-1}`, bands `b(t a, t b)` with `t 0 = 0`,
`t d = 2d - 1`, caps `n_{2n-1} ⋯ n₃ n₁`).

Checked outside Lean for the blocks `pairBlocks r s`, `(r, s) ∈ {(2,3), (2,5), (3,4), (3,5),
(4,5)}` and every `j`: one component, the writhe and the rotation number of the source, the same
Jones polynomial (`SCR/ISO/tools/phase1.py`).
-/

namespace AJConjecture

/-- The position of the disc `d` when the discs above `j` are thin: `d` for `d ≤ j`, and the left
edge `2d - j - 1` of the thin disc for `d > j`. -/
def isoThinIndex (j d : ℕ) : ℕ := if d ≤ j then d else 2 * d - j - 1

/-- The long closure of the block word with the discs `j + 1, …, n` thinned. -/
def isoThinPartial (n : ℕ) (B : List SBlock) (j : ℕ) : MorseWord :=
  (List.range j).map (fun i ↦ isoU (i + 1)) ++
    ((List.range (n - j)).map fun t ↦ isoU (j + 1 + 2 * t)) ++
    B.flatMap (isoBlockWord (isoThinIndex j)) ++
    ((List.range (n - j)).reverse.map fun t ↦ isoN (j + 1 + 2 * t)) ++
    (List.range j).reverse.map (fun i ↦ isoN (i + 1))

/-- The thin word: every disc `1, …, n` thinned. -/
def isoThinWord (n : ℕ) (B : List SBlock) : MorseWord := isoThinPartial n B 0

/-- With no disc thinned, the partial thin word is the long closure. -/
theorem isoThinPartial_top {n : ℕ} {B : List SBlock} (hB : ∀ b ∈ B, b.Valid (n + 1)) :
    isoThinPartial n B n = morseLongClosure (n + 1) (blocksWord B) := by
  have hb : B.flatMap (isoBlockWord (isoThinIndex n)) = B.flatMap (isoBlockWord id) := by
    refine List.flatMap_congr fun b hb' ↦ ?_
    have := isoEnds_lt (hB b hb')
    simp only [isoBlockWord, isoThinIndex, id]
    split_ifs <;> first | rfl | omega
  simp only [isoThinPartial, morseLongClosure, Nat.sub_self, List.range_zero, List.map_nil,
    List.reverse_nil, List.append_nil, hb, flatMap_isoBlockWord_id, Nat.add_sub_cancel]
  rfl

/-- Every partial thin word is a diagram from one strand to one strand. -/
theorem morseFits_isoThinPartial {n j : ℕ} {B : List SBlock} (hB : ∀ b ∈ B, b.Valid (n + 1))
    (hj : j ≤ n) : morseFits 1 (isoThinPartial n B j) = true ∧
      morseOut 1 (isoThinPartial n B j) = 1 := by
  have hcross := isoBlockWords_cross (isoThinIndex j) B
  have h1 : morseOut 1 ((List.range j).map fun i ↦ isoU (i + 1)) = 2 * j + 1 := by
    rw [morseOut_of_cups _ _ (by simp [isoU])]
    simp only [List.length_map, List.length_range]
    omega
  have h2 : morseOut (2 * j + 1) ((List.range (n - j)).map fun t ↦ isoU (j + 1 + 2 * t)) =
      2 * n + 1 := by
    rw [morseOut_of_cups _ _ (by simp [isoU])]
    simp only [List.length_map, List.length_range]
    omega
  have h4 : morseOut (2 * n + 1)
      ((List.range (n - j)).reverse.map fun t ↦ isoN (j + 1 + 2 * t)) = 2 * j + 1 := by
    rw [morseOut_of_caps _ _ (by simp [isoN])]
    simp only [List.length_map, List.length_reverse, List.length_range]
    omega
  have h5 : morseOut (2 * j + 1) ((List.range j).reverse.map fun i ↦ isoN (i + 1)) = 1 := by
    rw [morseOut_of_caps _ _ (by simp [isoN])]
    simp only [List.length_map, List.length_reverse, List.length_range]
    omega
  refine ⟨?_, ?_⟩
  · simp only [isoThinPartial, morseFits_append, morseOut_append, h1, h2,
      morseOut_isoBlockWords, h4, Bool.and_eq_true]
    refine ⟨⟨⟨⟨morseFits_isoCups _ _ _ fun t _ ↦ by omega,
      morseFits_isoCups _ _ _ fun t _ ↦ by omega⟩, ?_⟩,
      morseFits_isoCaps _ _ _ fun t _ ↦ by omega⟩, morseFits_isoCaps _ _ _ fun t _ ↦ by omega⟩
    refine morseFits_of_cross _ _ hcross fun l hl ↦ ?_
    obtain ⟨b, hb', hl⟩ := List.mem_flatMap.mp hl
    have hv := isoEnds_lt (hB b hb')
    have hm := (mem_isoBand hl).2
    simp only [isoThinIndex] at hm
    split_ifs at hm <;> omega
  · simp only [isoThinPartial, morseOut_append, h1, h2, morseOut_isoBlockWords, h4, h5]

end AJConjecture
