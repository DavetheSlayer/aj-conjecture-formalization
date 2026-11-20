import Mathlib
import AJConjecture.KnotGroup
import AJTwist.Classical.TwCChain

/-!
# The braid words of the twist knots (PpA, Section 7.6, claim 1: the knots)

Source: arXiv:2611.24826v1, Section 2 (`marking.tex`): "Write `Z_ℓ = Z_ℓ(U)` for the pure
closure, where `U` is the unknot and the patterned solid torus is embedded with zero framing",
i.e. `Z_ℓ = W_(-,ℓ)(U)`, the twist knot with `ℓ` full twists and a negative clasp.

The library has no braid for these knots. `ppaTwistBlocks ℓ` is a braided surface in the style
of `twBlocks`: two discs on the levels `0`, `1` joined by the chain `twChain 3 1 ℓ` (through new
discs on the levels `3, 4, …`) and by the negative letter `σ_0⁻¹` form an unknotted annulus with
`ℓ` full twists (for `ℓ = 0` the chain is the band `σ_0`, and `σ_0 σ_0⁻¹` bounds the untwisted
annulus), and the disc on the level `2` with the two letters `σ_1⁻¹` is the negative Hopf band
plumbed on it, as in `pairBlocks`:

  `ppaTwistBlocks ℓ = twChain 3 1 ℓ ++ [σ_1⁻¹, σ_0⁻¹, σ_1⁻¹]` on `3 + twExtra ℓ` strands.

The closure `ppaTwistKnot ℓ` is defined in `AJPaper.Filling.PpATwistKnot`. For `ℓ = 0` the word
is `σ_0 σ_1⁻¹ σ_0⁻¹ σ_1⁻¹`, an unknot; `ℓ = -1` is the figure-eight knot and `ℓ = 1` a trefoil (5
and 9 strands).

Checked outside Lean (`SCR/A/py/twistknot2.py`, with the routines of
`scripts/four_families/tw_audit_lib.py` of the repository): for `-4 ≤ ℓ ≤ 4` the closure has
one component, writhe `-2 - 2ℓ`, and Alexander polynomial `ℓ t² + (1 - 2ℓ) t + ℓ` (Burau
representation, exact); for `-4 ≤ ℓ ≤ 3` the colour-2 value of the library's coloured Jones
function equals the paper's finite sum for `W_(-,ℓ)` with companion input `[2n + 1]` (the
unknot), at two points modulo a prime, and it matches no other twist with `|ℓ'| ≤ 5` and clasp
sign except the amphichiral coincidences `(−, −1) = (+, 1)` and `ℓ = 0`; colour 3 for
`-2 ≤ ℓ ≤ 0`. The Lean words for `|ℓ| ≤ 2` were compared with the words used by the scripts
(`SCR/A/lean/TestTwist.lean`).

`ppaTwistBlocks_valid`, `isOnStrands_ppaTwistWord`: the word lives on `3 + twExtra ℓ` strands
(`twChain_valid` with `M = 3`, `j₀ = 1`; the word of a valid block is on the strands, as the
private `isOnStrands_sBlock_word_twKBlocks` of `AJTwist.Knot.TwKBlocks`).
-/

namespace AJConjecture

/-- The clasp and the second band of the annulus: `σ_1⁻¹, σ_0⁻¹, σ_1⁻¹`. -/
def ppaTwistTail : List SBlock := [SBlock.neg 1, SBlock.neg 0, SBlock.neg 1]

/-- The blocks of the braided surface of the twist knot `Z_ℓ = W_(-,ℓ)(U)`. -/
def ppaTwistBlocks (ℓ : ℤ) : List SBlock := twChain 3 1 ℓ ++ ppaTwistTail

/-- The braid word of the twist knot `Z_ℓ` on `3 + twExtra ℓ` strands. -/
def ppaTwistWord (ℓ : ℤ) : BraidWord := blocksWord (ppaTwistBlocks ℓ)

/-- Every block lives on `3 + twExtra ℓ` strands. -/
theorem ppaTwistBlocks_valid (ℓ : ℤ) : ∀ b ∈ ppaTwistBlocks ℓ, b.Valid (3 + twExtra ℓ) := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact twChain_valid (by norm_num) (by norm_num) ℓ b hb
  · simp only [ppaTwistTail, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [SBlock.Valid] <;> omega

/-- The braid word lives on `3 + twExtra ℓ` strands. -/
theorem isOnStrands_ppaTwistWord (ℓ : ℤ) : IsOnStrands (3 + twExtra ℓ) (ppaTwistWord ℓ) := by
  intro g hg
  obtain ⟨b, hb, hg⟩ := List.mem_flatMap.1 hg
  have hv := ppaTwistBlocks_valid ℓ b hb
  cases b with
  | band i j =>
    simp only [SBlock.Valid] at hv
    simp only [SBlock.word, bandWord, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton] at hg
    rcases hg with (⟨x, hx, rfl⟩ | rfl) | ⟨x, hx, rfl⟩ <;> dsimp only <;> omega
  | neg i =>
    simp only [SBlock.Valid] at hv
    simp only [SBlock.word, List.mem_singleton] at hg
    rw [hg]
    exact hv

end AJConjecture
