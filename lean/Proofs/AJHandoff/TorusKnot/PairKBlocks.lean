import Mathlib
import AJHandoff.PairDefs
import AJFamily.Classical.FamilyPeripheralRun

/-!
# The braided-surface word of `Wh⁻₀(T(r, s))`

For an admissible pair `(r, s)` put `c = (r - 1) s` (the number of crossings of `T(r, s)` as the
closure of `(σ_0 ⋯ σ_(r-2))^s`), `T = 2c - 1`, `E = (r - 2)(s - 1) + 1` and `z = c - r - 1`.
`pairBlocks r s` is a list of `2c` positive bands and two negative letters on `2c + 1` levels: a
braided annulus around `T(r, s)` (levels `0, …, 2c - 1`, one band per column of a grid
diagram of the companion with Thurston–Bennequin number `0`) plumbed with a negative Hopf band
on the top level `2c`. Reading the blocks in order:

* the left climbs `b(i, T - 1 - i)`, `i < r - 2`, of the `r - 2` closure arcs that pass below
  the diagram;
* a decreasing run `σ_(r+E-3), …, σ_(r-2)` and an increasing run `σ_(r-2+E), …, σ_(2c-r-s-1)`
  (stabilisations of the remaining closure arc), and the big climb `b(2c - r - s, T + 1 - r)`;
* the rounds of the staircase: round `0` is `b(T - r, T)`, followed by the first Hopf letter
  `σ_T⁻¹`; round `t` (`1 ≤ t ≤ s - 2`) is `b(T - r - t, T - t)`: the top strand of the
  conveyor drops below the other `r - 1`; the last round `b(r - 2, T - s + 1)` drops to the
  bottom wire;
* the top-right climb `b(T - s, T)`, the right descents `b(r - 3 - j, T - s - r + 2 + j)`,
  `j < r - 2`, and the second Hopf letter.

For `r = 2` this is the library's `whiteheadTorusWord k` (`s = 2k + 1`), see
`AJHandoff.TorusKnot.PairKKnot`. Checked by computer outside the formal development (Regina 7.4)
for `(2,3), (2,5), (3,4), (3,5), (3,7), (3,8), (4,5), (4,7)`: one component, writhe `2c - 2`,
annulus framing `0`, core the right-handed `T(r, s)`, Jones polynomial equal to that of the
band-and-clasp satellite diagram `pairTargetWord r s`.
-/

namespace AJConjecture

/-- The number `c = (r - 1) s` of crossings of the companion braid `(σ_0 ⋯ σ_(r-2))^s`. -/
def pairC (r s : ℕ) : ℕ := (r - 1) * s

/-- The top level `T = 2c - 1` of the braided annulus. -/
def pairTop (r s : ℕ) : ℕ := 2 * pairC r s - 1

/-- The number of strands `2c + 1` of the braided-surface word. -/
def pairStrands (r s : ℕ) : ℕ := 2 * pairC r s + 1

/-- The length `E = (r - 2)(s - 1) + 1` of the decreasing run of stabilisations. -/
def pairRunDown (r s : ℕ) : ℕ := (r - 2) * (s - 1) + 1

/-- The length `z = c - r - 1` of the increasing run of stabilisations. -/
def pairRunUp (r s : ℕ) : ℕ := pairC r s - r - 1

/-- The blocks of the braided Seifert surface (annulus plus negative Hopf band) of
`Wh⁻₀(T(r, s))`, in the order of the braid word. -/
def pairBlocks (r s : ℕ) : List SBlock :=
  let T := pairTop r s
  let E := pairRunDown r s
  let z := pairRunUp r s
  (List.range (r - 2)).map (fun i ↦ SBlock.band i (T - 1 - i)) ++
    (List.range E).map (fun j ↦ SBlock.band (r + E - 3 - j) (r + E - 2 - j)) ++
    (List.range z).map (fun j ↦ SBlock.band (r - 2 + E + j) (r - 1 + E + j)) ++
    [SBlock.band (r - 2 + E + z) (T + 1 - r), SBlock.band (T - r) T, SBlock.neg T] ++
    (List.range (s - 2)).map (fun j ↦ SBlock.band (T - r - 1 - j) (T - 1 - j)) ++
    [SBlock.band (r - 2) (T + 1 - s), SBlock.band (T - s) T] ++
    (List.range (r - 2)).map (fun j ↦ SBlock.band (r - 3 - j) (T + 2 - s - r + j)) ++
    [SBlock.neg T]

/-- The braid word of `Wh⁻₀(T(r, s))` on `2(r - 1)s + 1` strands. -/
def pairWhiteheadWord (r s : ℕ) : BraidWord := blocksWord (pairBlocks r s)

/-- The arithmetic of an admissible pair used to place the blocks: `s ≤ c`, `r + 1 ≤ s` and
`E + s + r = c + 3`. -/
private theorem pairBlocks_arith {r s : ℕ} (h : IsTorusPair r s) :
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

/-- Every block of `pairBlocks r s` lives on `2c + 1` strands. -/
theorem pairBlocks_valid {r s : ℕ} (h : IsTorusPair r s) :
    ∀ b ∈ pairBlocks r s, b.Valid (pairStrands r s) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairBlocks_arith h
  intro b hb
  simp only [pairBlocks, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hb
  simp only [pairStrands, pairTop, pairRunUp] at hb ⊢
  rcases hb with (((((((⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl | rfl | rfl) |
    ⟨j, hj, rfl⟩) | rfl | rfl) | ⟨j, hj, rfl⟩) | rfl) <;>
    simp only [SBlock.Valid] <;> omega

/-- The word of a valid block only uses generators on `m` strands. -/
private theorem isOnStrands_sBlock_word {m : ℕ} (b : SBlock) (hb : b.Valid m) :
    IsOnStrands m b.word := by
  intro g hg
  cases b with
  | band i j =>
    simp only [SBlock.Valid] at hb
    simp only [SBlock.word, bandWord, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton] at hg
    rcases hg with (⟨x, hx, rfl⟩ | rfl) | ⟨x, hx, rfl⟩ <;> dsimp only <;> omega
  | neg i =>
    simp only [SBlock.Valid] at hb
    simp only [SBlock.word, List.mem_singleton] at hg
    rw [hg]
    exact hb

/-- The braid word lives on `2c + 1` strands. -/
theorem isOnStrands_pairWhiteheadWord {r s : ℕ} (h : IsTorusPair r s) :
    IsOnStrands (pairStrands r s) (pairWhiteheadWord r s) := by
  intro g hg
  obtain ⟨b, hb, hg⟩ := List.mem_flatMap.1 hg
  exact isOnStrands_sBlock_word b (pairBlocks_valid h b hb) g hg

/-- The writhe of the braided-surface word is `2c - 2`: `2c` positive bands, each of writhe
`1`, and two negative Hopf letters. -/
theorem writhe_pairWhiteheadWord {r s : ℕ} (h : IsTorusPair r s) :
    writhe (pairWhiteheadWord r s) = 2 * (((r - 1) * s : ℕ) : ℤ) - 2 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairBlocks_arith h
  have hw : ∀ bs : List SBlock, writhe (blocksWord bs) = (bs.map fun b ↦ writhe b.word).sum := by
    intro bs
    induction bs with
    | nil => simp [blocksWord, writhe]
    | cons b bs ih =>
      simp only [blocksWord, List.flatMap_cons, List.map_cons, List.sum_cons] at ih ⊢
      rw [← ih]
      simp [writhe, List.map_append, List.sum_append]
  have hband : ∀ i j : ℕ, writhe (SBlock.band i j).word = 1 := by
    intro i j
    simp [SBlock.word, bandWord, writhe, List.map_append, List.sum_append, Function.comp_def]
  have hneg : ∀ i : ℕ, writhe (SBlock.neg i).word = -1 := by
    intro i
    simp [SBlock.word, writhe]
  rw [pairWhiteheadWord, hw, pairBlocks]
  simp only [List.map_append, List.map_map, Function.comp_def, hband, hneg, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_const',
    List.sum_replicate, List.length_range, nsmul_eq_mul, mul_one]
  simp only [pairRunUp, pairC] at hE hc ⊢
  generalize (r - 1) * s = c at *
  omega

end AJConjecture
