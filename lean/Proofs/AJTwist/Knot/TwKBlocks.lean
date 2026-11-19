import Mathlib
import AJTwist.TwDefs
import AJHandoff.TorusKnot.PairKKnot

/-!
# The braided-surface words of the twisted Whitehead doubles of `T(r, s)`

Source: *Whitehead doubles and the failure of the square-free AJ conjecture*, revision 5, §2
(the marked satellites `W_{ε,ℓ}(T_η)`).

`twBlocks r s ℓ σ` is `pairBlocks r s` with two changes.

* **Twist.** The head block `band 0 j₀` of `pairBlocks r s` (`j₀ = twHeadTop r s`: `2c - 2` for
  `r ≥ 3`, `1` for `r = 2`, `c = (r - 1) s`) is replaced by the chain `twChain M j₀ ℓ` through new
  discs on the new top levels `M, M + 1, …`, `M = pairStrands r s = 2c + 1`. All other blocks and
  all old levels are unchanged. In the thin picture every block of the chain between two new
  discs is a stabilisation of the annulus: an ascending positive block adds a negative full twist
  and a negative curl, a descending positive block a positive curl, an ascending negative block a
  negative curl, a descending negative block a positive full twist and a positive curl. The
  chains are balanced: the curls cancel, so the band of the annulus gets `ℓ` full twists and the
  writhe of the word changes by exactly `-2ℓ`:
  * `ℓ = -n < 0` (`2n` new discs): `band 0 (M+n-1)`, `n - 1` descending positive blocks down to
    the disc `M`, the jump `band M (M+n)`, `n - 1` ascending positive blocks up to the disc
    `M + 2n - 1`, `band j₀ (M+2n-1)`;
  * `ℓ = n > 0` (`2n + 4` new discs): `band 0 (M+n+1)`, `n + 2` ascending negative letters up to
    the disc `M + 2n + 3`, the jump `band (M+n) (M+2n+3)`, `n` descending negative letters down to
    the disc `M`, `band j₀ M`.
* **Clasp.** For `σ = false` (positive clasp) the two Hopf letters `neg (2c - 1)` become the
  positive letters `band (2c - 1) (2c)`; `σ = true` is the negative clasp of `pairBlocks`.

`twBlocks r s 0 true = pairBlocks r s`. A run of `|1 - 2ℓ|` letters on one level is *not* a band
with `1 - 2ℓ` half twists (it is the twisted double only for `ℓ ∈ {0, 1}`), which is why the
twist is realised by a chain.

Checked outside Lean (`SCR/K/tools/twk3.py`, thickness-one Kauffman-bracket operators of the
fence words mod `p`): for `(r, s) ∈ {(2,3), (2,5), (3,4), (3,5), (4,5)}`, `|ℓ| ≤ 3` (resp. `≤ 2`)
and both `σ`, the word is a knot of writhe `2c - 2ℓ ∓ 2` with the operator of the band-and-clasp
diagram with `2ℓ - 2c` half twists and clasp sign `σ`.
-/

namespace AJConjecture

/-- The upper disc of the head block `band 0 j₀` of `pairBlocks r s`: the first left climb
`band 0 (2c - 2)` for `r ≥ 3`, the first run letter `band 0 1` for `r = 2`. -/
def twHeadTop (r s : ℕ) : ℕ := if r = 2 then 1 else pairTop r s - 1

/-- The chain that replaces the block `band 0 j₀`: `ℓ` full twists of the band through new discs
on the levels `M, M + 1, …` (`2|ℓ|` discs for `ℓ ≤ 0`, `2ℓ + 4` discs for `ℓ > 0`). -/
def twChain (M j₀ : ℕ) (ℓ : ℤ) : List SBlock :=
  if ℓ = 0 then [SBlock.band 0 j₀]
  else if ℓ < 0 then
    [SBlock.band 0 (M + ℓ.natAbs - 1)] ++
      (List.range (ℓ.natAbs - 1)).map
        (fun i ↦ SBlock.band (M + ℓ.natAbs - 2 - i) (M + ℓ.natAbs - 1 - i)) ++
      [SBlock.band M (M + ℓ.natAbs)] ++
      (List.range (ℓ.natAbs - 1)).map
        (fun i ↦ SBlock.band (M + ℓ.natAbs + i) (M + ℓ.natAbs + 1 + i)) ++
      [SBlock.band j₀ (M + 2 * ℓ.natAbs - 1)]
  else
    [SBlock.band 0 (M + ℓ.natAbs + 1)] ++
      (List.range (ℓ.natAbs + 2)).map (fun i ↦ SBlock.neg (M + ℓ.natAbs + 1 + i)) ++
      [SBlock.band (M + ℓ.natAbs) (M + 2 * ℓ.natAbs + 3)] ++
      (List.range ℓ.natAbs).map (fun i ↦ SBlock.neg (M + ℓ.natAbs - 1 - i)) ++
      [SBlock.band j₀ M]

/-- The number of new discs of the chain. -/
def twExtra (ℓ : ℤ) : ℕ := if ℓ ≤ 0 then 2 * ℓ.natAbs else 2 * ℓ.natAbs + 4

/-- A Hopf letter with the clasp sign `σ`: unchanged for `σ = true` (negative clasp), the
positive letter on the same level for `σ = false`. Bands are unchanged. -/
def twClaspBlock (σ : Bool) : SBlock → SBlock
  | .band i j => .band i j
  | .neg i => if σ then .neg i else .band i (i + 1)

/-- The blocks of the braided surface of `W_{ε,ℓ}(T(r, s))` (`σ = true`: negative clasp). -/
def twBlocks (r s : ℕ) (ℓ : ℤ) (σ : Bool) : List SBlock :=
  twChain (pairStrands r s) (twHeadTop r s) ℓ ++ (pairBlocks r s).tail.map (twClaspBlock σ)

/-- The number of strands `2c + 1 + twExtra ℓ`. -/
def twStrands (r s : ℕ) (ℓ : ℤ) : ℕ := pairStrands r s + twExtra ℓ

/-- The braid word of `W_{ε,ℓ}(T(r, s))`. -/
def twWhiteheadWord (r s : ℕ) (ℓ : ℤ) (σ : Bool) : BraidWord := blocksWord (twBlocks r s ℓ σ)

/-- The head block of `pairBlocks r s` is `band 0 (twHeadTop r s)`. -/
theorem pairBlocks_eq_head_cons {r s : ℕ} (h : IsTorusPair r s) :
    pairBlocks r s = SBlock.band 0 (twHeadTop r s) :: (pairBlocks r s).tail := by
  obtain ⟨hr, hrs, -⟩ := h
  have key : (pairBlocks r s).head? = some (SBlock.band 0 (twHeadTop r s)) := by
    by_cases h2 : r = 2
    · subst h2
      simp [pairBlocks, twHeadTop, pairRunDown, List.range_succ_eq_map]
    · obtain ⟨a, rfl⟩ : ∃ a, r = a + 3 := ⟨r - 3, by omega⟩
      simp [pairBlocks, twHeadTop, List.range_succ_eq_map]
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.1 key
  rw [hys, List.tail_cons]

/-- Without twist and with the negative clasp the blocks are those of `pairBlocks`. -/
theorem twBlocks_zero_true {r s : ℕ} (h : IsTorusPair r s) :
    twBlocks r s 0 true = pairBlocks r s := by
  have hid : ∀ bs : List SBlock, bs.map (twClaspBlock true) = bs := by
    intro bs
    refine (List.map_congr_left fun b _ ↦ ?_).trans (List.map_id bs)
    cases b <;> rfl
  rw [twBlocks, twChain, ite_eq_left rfl, hid, List.singleton_append, ← pairBlocks_eq_head_cons h]

/-- Without twist and with the negative clasp the word is `pairWhiteheadWord r s`. -/
theorem twWhiteheadWord_zero_true {r s : ℕ} (h : IsTorusPair r s) :
    twWhiteheadWord r s 0 true = pairWhiteheadWord r s := by
  rw [twWhiteheadWord, twBlocks_zero_true h, pairWhiteheadWord]

/-- A block that lives on `m` strands lives on more strands. -/
private theorem valid_mono_twKBlocks {m m' : ℕ} (hm : m ≤ m') (b : SBlock) (hb : b.Valid m) :
    b.Valid m' := by
  cases b <;> simp only [SBlock.Valid] at hb ⊢ <;> omega

/-- Changing the sign of a Hopf letter keeps the block on `m` strands. -/
private theorem valid_twClaspBlock_twKBlocks (σ : Bool) {m : ℕ} (b : SBlock) (hb : b.Valid m) :
    (twClaspBlock σ b).Valid m := by
  cases b with
  | band i j => exact hb
  | neg i =>
    cases σ
    · simp only [SBlock.Valid, twClaspBlock, Bool.false_eq_true, ite_false] at hb ⊢
      omega
    · exact hb

/-- The blocks of the chain live on `M + twExtra ℓ` strands. -/
private theorem twChain_valid_twKBlocks {M j₀ : ℕ} (h0 : 0 < j₀) (hj : j₀ < M) (ℓ : ℤ) :
    ∀ b ∈ twChain M j₀ ℓ, b.Valid (M + twExtra ℓ) := by
  intro b hb
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne
    rw [twChain, ite_eq_right hl.ne, ite_eq_left hl] at hb
    rw [twExtra, ite_eq_left hl.le]
    generalize ℓ.natAbs = n at hb hn ⊢
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hb
    rcases hb with (((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | rfl <;>
      simp only [SBlock.Valid] <;> omega
  · rw [twChain, ite_eq_left rfl, List.mem_singleton] at hb
    subst hb
    simp only [SBlock.Valid]
    omega
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne'
    rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt] at hb
    rw [twExtra, ite_eq_right hl.not_ge]
    generalize ℓ.natAbs = n at hb hn ⊢
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hb
    rcases hb with (((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | rfl <;>
      simp only [SBlock.Valid] <;> omega

/-- Every block lives on `twStrands r s ℓ` strands. -/
theorem twBlocks_valid {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    ∀ b ∈ twBlocks r s ℓ σ, b.Valid (twStrands r s ℓ) := by
  have hv := pairBlocks_valid h
  have hhead : (SBlock.band 0 (twHeadTop r s)).Valid (pairStrands r s) :=
    hv _ (by rw [pairBlocks_eq_head_cons h]; exact List.mem_cons_self)
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact twChain_valid_twKBlocks hhead.1 hhead.2 ℓ b hb
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    exact valid_twClaspBlock_twKBlocks σ _
      (valid_mono_twKBlocks (Nat.le_add_right _ _) b' (hv b' (List.mem_of_mem_tail hb')))

/-- The word of a valid block only uses generators on `m` strands. -/
private theorem isOnStrands_sBlock_word_twKBlocks {m : ℕ} (b : SBlock) (hb : b.Valid m) :
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

/-- The braid word lives on `twStrands r s ℓ` strands. -/
theorem isOnStrands_twWhiteheadWord {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    IsOnStrands (twStrands r s ℓ) (twWhiteheadWord r s ℓ σ) := by
  intro g hg
  obtain ⟨b, hb, hg⟩ := List.mem_flatMap.1 hg
  exact isOnStrands_sBlock_word_twKBlocks b (twBlocks_valid h ℓ σ b hb) g hg

/-- The writhe of a block word is the sum of the writhes of its blocks. -/
private theorem writhe_blocksWord_twKBlocks (bs : List SBlock) :
    writhe (blocksWord bs) = (bs.map fun b ↦ writhe b.word).sum := by
  induction bs with
  | nil => simp [blocksWord, writhe]
  | cons b bs ih =>
    simp only [blocksWord, List.flatMap_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    simp [writhe, List.map_append, List.sum_append]

/-- A positive band has writhe `1`. -/
private theorem writhe_band_word_twKBlocks (i j : ℕ) : writhe (SBlock.band i j).word = 1 := by
  simp [SBlock.word, bandWord, writhe, List.map_append, List.sum_append, Function.comp_def]

/-- A negative letter has writhe `-1`. -/
private theorem writhe_neg_word_twKBlocks (i : ℕ) : writhe (SBlock.neg i).word = -1 := by
  simp [SBlock.word, writhe]

/-- The chain has writhe `1 - 2ℓ`. -/
private theorem writhe_twChain_twKBlocks (M j₀ : ℕ) (ℓ : ℤ) :
    ((twChain M j₀ ℓ).map fun b ↦ writhe b.word).sum = 1 - 2 * ℓ := by
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne
    rw [twChain, ite_eq_right hl.ne, ite_eq_left hl]
    simp only [List.map_append, List.map_map, Function.comp_def, writhe_band_word_twKBlocks,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.map_const', List.sum_replicate, List.length_range, nsmul_eq_mul, mul_one]
    omega
  · simp [twChain, writhe_band_word_twKBlocks]
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne'
    rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt]
    simp only [List.map_append, List.map_map, Function.comp_def, writhe_band_word_twKBlocks,
      writhe_neg_word_twKBlocks, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.map_const', List.sum_replicate, List.length_range, nsmul_eq_mul]
    omega

/-- The writhe of the blocks of `pairBlocks r s` with the clasp of sign `σ`. -/
private theorem writhe_pairBlocks_clasp_twKBlocks {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    (((pairBlocks r s).map (twClaspBlock σ)).map fun b ↦ writhe b.word).sum =
      2 * (((r - 1) * s : ℕ) : ℤ) + (if σ then -2 else 2) := by
  obtain ⟨hr, hrs, -⟩ := h
  have hc : s ≤ pairC r s := Nat.le_mul_of_pos_left s (by omega)
  have hE : pairRunDown r s + s + r = pairC r s + 3 := by
    obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
    simp only [pairC, pairRunDown, Nat.add_sub_cancel]
    rw [show a + 2 - 1 = a + 1 by omega]
    ring
  have hnegσ : ∀ i : ℕ, writhe (twClaspBlock σ (SBlock.neg i)).word = if σ then -1 else 1 := by
    intro i
    cases σ
    · exact writhe_band_word_twKBlocks i (i + 1)
    · exact writhe_neg_word_twKBlocks i
  have hbandσ : ∀ i j : ℕ, writhe (twClaspBlock σ (SBlock.band i j)).word = 1 :=
    writhe_band_word_twKBlocks
  rw [pairBlocks]
  simp only [List.map_append, List.map_map, Function.comp_def, hbandσ, hnegσ, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_const',
    List.sum_replicate, List.length_range, nsmul_eq_mul, mul_one]
  simp only [pairRunUp, pairC] at hE hc ⊢
  generalize (r - 1) * s = c at *
  cases σ <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- The writhe of the word is `2c - 2ℓ - 2` for the negative clasp and `2c - 2ℓ + 2` for the
positive clasp: it is the writhe of the band-and-clasp diagram with `2ℓ - 2c` half twists. -/
theorem writhe_twWhiteheadWord {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    writhe (twWhiteheadWord r s ℓ σ) =
      2 * (((r - 1) * s : ℕ) : ℤ) - 2 * ℓ + (if σ then -2 else 2) := by
  have htail := writhe_pairBlocks_clasp_twKBlocks h σ
  rw [pairBlocks_eq_head_cons h, List.map_cons, List.map_cons, List.sum_cons,
    show twClaspBlock σ (SBlock.band 0 (twHeadTop r s)) = SBlock.band 0 (twHeadTop r s) from rfl,
    writhe_band_word_twKBlocks] at htail
  rw [twWhiteheadWord, writhe_blocksWord_twKBlocks, twBlocks, List.map_append, List.sum_append,
    writhe_twChain_twKBlocks]
  linarith

end AJConjecture
