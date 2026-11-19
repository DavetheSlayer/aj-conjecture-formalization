import Mathlib
import AJFamily.Classical.FamilyPeripheralRun
import AJFamily.Skein.TorusWord

/-!
# The family word as a list of blocks

The braid word `whiteheadTorusWord k` is the word of the list `famBlocks k` of `4k+4` blocks in
four phases: the climbs `b(l, l+1)` (`l < 2k-1`); the middle `b(2k-1, 4k)`, `b(4k-1, 4k+1)`,
`σ_{4k+1}⁻¹`; the staircase `b(4k-2-s, 4k-s)` (`s < 2k-1`); and the top `b(0, 2k+1)`,
`b(2k, 4k+1)`, `σ_{4k+1}⁻¹`. The loop of each block of `famBlocks k` is the loop of the
corresponding block of its phase, read on the tuple produced by the earlier phases.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The climbs `b(l, l+1)`, `l < 2k-1`. -/
def famClimbs (k : ℕ) : List SBlock := (List.range (2 * k - 1)).map fun l ↦ SBlock.band l (l + 1)

/-- The big climb, the first staircase step and the first Hopf letter. -/
def famMid (k : ℕ) : List SBlock :=
  [SBlock.band (2 * k - 1) (4 * k), SBlock.band (4 * k - 1) (4 * k + 1), SBlock.neg (4 * k + 1)]

/-- The staircase `b(4k-2-s, 4k-s)`, `s < 2k-1`. -/
def famStair (k : ℕ) : List SBlock :=
  (List.range (2 * k - 1)).map fun s ↦ SBlock.band (4 * k - 2 - s) (4 * k - s)

/-- The last crossing, the final climb and the second Hopf letter. -/
def famTop (k : ℕ) : List SBlock :=
  [SBlock.band 0 (2 * k + 1), SBlock.band (2 * k) (4 * k + 1), SBlock.neg (4 * k + 1)]

/-- The family word as a list of blocks. -/
def famBlocks (k : ℕ) : List SBlock := famClimbs k ++ famMid k ++ famStair k ++ famTop k

/-- A surface band is the positive band word. -/
private theorem surfaceBand_eq_bandWord (i j : ℕ) : surfaceBand i j = bandWord i j true := by
  have h : j - i - 1 = j - 1 - i := by omega
  simp only [surfaceBand, bandWord, h]

theorem blocksWord_famBlocks (k : ℕ) : blocksWord (famBlocks k) = whiteheadTorusWord k := by
  simp only [blocksWord, famBlocks, famClimbs, famMid, famStair, famTop, whiteheadTorusWord,
    List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil, SBlock.word,
    surfaceBand_eq_bandWord, List.append_nil, List.append_assoc]
  congr 1
  have h : (fun a : ℕ ↦ bandWord a (a + 1) true) = fun a ↦ [(a, true)] := by
    funext a
    simp [bandWord]
  rw [h]
  induction List.range (2 * k - 1) with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]

theorem famBlocks_valid (k : ℕ) (hk : 1 ≤ k) : ∀ b ∈ famBlocks k, b.Valid (4 * k + 3) := by
  intro b hb
  simp only [famBlocks, famClimbs, famMid, famStair, famTop, List.mem_append, List.mem_map,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with ((⟨l, hl, rfl⟩ | rfl | rfl | rfl) | ⟨s, hs, rfl⟩) | rfl | rfl | rfl <;>
    simp only [SBlock.Valid] <;> omega

set_option linter.unusedVariables false in
theorem loopAt_famBlocks_climb (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (r : ℕ)
    (hr : r < 2 * k - 1) :
    loopAt (4 * k + 3) (famBlocks k) f r = loopAt (4 * k + 3) (famClimbs k) f r := by
  rw [famBlocks, List.append_assoc, List.append_assoc, loopAt_append_left]
  simpa [famClimbs] using hr

set_option linter.unusedVariables false in
theorem loopAt_famBlocks_mid (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (r : ℕ) (hr : r < 3) :
    loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1 + r) =
      loopAt (4 * k + 3) (famMid k) (runTop (4 * k + 3) (famClimbs k) f) r := by
  have hl : (famClimbs k).length = 2 * k - 1 := by simp [famClimbs]
  rw [famBlocks, List.append_assoc, List.append_assoc, ← hl, loopAt_append_right,
    loopAt_append_left _ (famMid k)]
  simpa [famMid] using hr

theorem loopAt_famBlocks_stair (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (s : ℕ)
    (hs : s < 2 * k - 1) :
    loopAt (4 * k + 3) (famBlocks k) f (2 * k + 2 + s) =
      loopAt (4 * k + 3) (famStair k) (runTop (4 * k + 3) (famClimbs k ++ famMid k) f) s := by
  have hl : (famClimbs k ++ famMid k).length = 2 * k + 2 := by
    simp only [famClimbs, famMid, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil]
    omega
  rw [famBlocks, List.append_assoc, ← hl, loopAt_append_right, loopAt_append_left]
  simpa [famStair] using hs

theorem loopAt_famBlocks_top (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (r : ℕ) :
    loopAt (4 * k + 3) (famBlocks k) f (4 * k + 1 + r) =
      loopAt (4 * k + 3) (famTop k)
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f) r := by
  have hl : (famClimbs k ++ famMid k ++ famStair k).length = 4 * k + 1 := by
    simp only [famClimbs, famMid, famStair, List.length_append, List.length_map,
      List.length_range, List.length_cons, List.length_nil]
    omega
  rw [famBlocks, ← hl, loopAt_append_right]

end AJConjecture
