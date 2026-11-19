import Mathlib
import AJHandoff.TorusKnot.PairKConnected
import AJFamily.Skein.WhiteheadTorusKnot
import AJFamily.Classical.FamilyPeripheralWord

/-!
# The knots `Wh⁻₀(T(r, s))`

`pairWhiteheadKnot r s h`: the closure of `pairWhiteheadWord r s` on `2(r - 1)s + 1` strands,
the boundary of a braided annulus around the right-handed torus knot `T(r, s)` with framing `0`,
plumbed with a negative Hopf band. That it is the untwisted negative-clasp Whitehead double of
`T(r, s)` is expressed formally by the long-knot identity `longKnotOp_pairWhiteheadKnot` and by
the satellite structure of its knot group `isWhSatellite_pairWhiteheadKnot`; the identification
with the named geometric satellite is interpretation (MARK).

For `r = 2` the word is the library's `whiteheadTorusWord k` (`pairWhiteheadWord_two`), so
Theorem F is about the same knots as `AJFamily.FamilyMain`.
-/

namespace AJConjecture

/-- The untwisted negative-clasp Whitehead double of `T(r, s)` as a closed braid. -/
def pairWhiteheadKnot (r s : ℕ) (h : IsTorusPair r s) : BraidKnot where
  strands := pairStrands r s
  word := pairWhiteheadWord r s
  strands_pos := Nat.succ_pos _
  isOnStrands := isOnStrands_pairWhiteheadWord h
  connected := connected_pairWhiteheadWord h

/-- For `r = 2`, `s = 2k + 1` the blocks are the family blocks. -/
private theorem pairBlocks_two (k : ℕ) (hk : 1 ≤ k) :
    pairBlocks 2 (2 * k + 1) = famBlocks k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hc : pairC 2 (2 * (n + 1) + 1) = 2 * n + 3 := by simp only [pairC]; omega
  have hE : pairRunDown 2 (2 * (n + 1) + 1) = 1 := by simp only [pairRunDown]; omega
  have hz : pairRunUp 2 (2 * (n + 1) + 1) = 2 * n := by simp only [pairRunUp, hc]; omega
  have hT : pairTop 2 (2 * (n + 1) + 1) = 4 * n + 5 := by simp only [pairTop, hc]; omega
  simp only [pairBlocks, hT, hE, hz, famBlocks, famClimbs, famMid, famStair, famTop]
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, show 2 * (n + 1) + 1 - 2 = 2 * n + 1 by omega,
    show 2 - 2 = 0 by rfl]
  simp only [List.range_zero, List.map_nil, List.nil_append, List.append_nil, List.append_assoc]
  have h1 : (List.range 1).map (fun j ↦ SBlock.band (0 - j) (2 + 1 - 2 - j)) ++
      (List.range (2 * n)).map (fun j ↦ SBlock.band (0 + 1 + j) (2 - 1 + 1 + j)) =
      (List.range (2 * n + 1)).map (fun l ↦ SBlock.band l (l + 1)) := by
    rw [List.range_succ_eq_map (n := 2 * n), List.map_cons, List.map_map, List.range_one,
      List.map_singleton, List.singleton_append]
    refine List.cons_eq_cons.2 ⟨rfl, List.map_congr_left fun j _ ↦ ?_⟩
    simp only [Function.comp_apply, SBlock.band.injEq]
    omega
  have h2 : (List.range (2 * n + 1)).map
      (fun j ↦ SBlock.band (4 * n + 5 - 2 - 1 - j) (4 * n + 5 - 1 - j)) =
      (List.range (2 * n + 1)).map
        (fun s ↦ SBlock.band (4 * (n + 1) - 2 - s) (4 * (n + 1) - s)) := by
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [SBlock.band.injEq]
    omega
  rw [← List.append_assoc, h1, h2]
  simp only [List.cons_append, List.nil_append, List.append_cancel_left_eq, List.cons.injEq,
    SBlock.band.injEq, SBlock.neg.injEq, true_and, and_true]
  omega

/-- For `r = 2`, `s = 2k + 1` the braided-surface word is the family word of the library. -/
theorem pairWhiteheadWord_two (k : ℕ) (hk : 1 ≤ k) :
    pairWhiteheadWord 2 (2 * k + 1) = whiteheadTorusWord k := by
  rw [pairWhiteheadWord, pairBlocks_two k hk, blocksWord_famBlocks]

/-- For `r = 2`, `s = 2k + 1` the number of strands is `4k + 3`. -/
theorem pairStrands_two (k : ℕ) : pairStrands 2 (2 * k + 1) = 4 * k + 3 := by
  simp only [pairStrands, pairC]
  omega

end AJConjecture
