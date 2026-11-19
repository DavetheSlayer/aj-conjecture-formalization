import Mathlib
import AJHandoff.TorusKnot.PairKTargetWord
import AJFamily.Classical.BandWord
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusPhaseTwoPass
import AJFamily.Skein.TorusPhaseTwoWords

/-!
# Word families of the isotopy of Theorem T

Small Morse-word families shared by the files `PairKIso*`: single letters, signed bands as Morse
words, the discs joined by a block of a braided surface, and the relabelling of a block word by a
map on discs (used by the thinning of `PairKIsoThinDefs` and the fence words of
`PairKIsoFenceDefs`). See `SCR/ISO/DESIGN.md` for the plan of the isotopy.
-/

namespace AJConjecture

/-- A cup at position `i`. -/
def isoU (i : ℕ) : MorseLetter := (.cup, i)

/-- A cap at position `i`. -/
def isoN (i : ℕ) : MorseLetter := (.cap, i)

/-- A crossing of sign `s` at position `i`. -/
def isoX (s : Bool) (i : ℕ) : MorseLetter := (.cross s, i)

/-- The signed band `b(i, j)` (`σ_{j-1} ⋯ σ_{i+1} σ_i^{±1} σ_{i+1}⁻¹ ⋯ σ_{j-1}⁻¹`) as a Morse
word. -/
def isoBand (i j : ℕ) (b : Bool) : MorseWord := morseOfBraid (bandWord i j b)

/-- The two discs joined by a block: `band i j` joins `i` and `j`, `neg i` (a negative band of span
one) joins `i` and `i + 1`. -/
def isoEnds : SBlock → ℕ × ℕ
  | .band i j => (i, j)
  | .neg i => (i, i + 1)

/-- The sign of the half twist of a block. -/
def isoSign : SBlock → Bool
  | .band _ _ => true
  | .neg _ => false

/-- The Morse word of a block whose discs are relabelled by `f` (disc `d` sits at position
`f d`): the signed band between the positions of its two discs. -/
def isoBlockWord (f : ℕ → ℕ) (b : SBlock) : MorseWord :=
  isoBand (f (isoEnds b).1) (f (isoEnds b).2) (isoSign b)

/-- A left curl of sign `s` on the strand `i`: `u_i x^s_{i+1} n_i`. -/
def isoCurlL (s : Bool) (i : ℕ) : MorseWord := [isoU i, isoX s (i + 1), isoN i]

/-- A right curl of sign `s` on the strand `i`: `u_{i+1} x^s_i n_{i+1}` (the pattern of `kink`). -/
def isoCurlR (s : Bool) (i : ℕ) : MorseWord := [isoU (i + 1), isoX s i, isoN (i + 1)]

/-- With the identity relabelling, the block words of a block list are its braid word. -/
theorem flatMap_isoBlockWord_id (B : List SBlock) :
    B.flatMap (isoBlockWord id) = morseOfBraid (blocksWord B) := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    simp only [List.flatMap_cons, ih, blocksWord, morseOfBraid, List.map_append]
    congr 1
    cases b with
    | band i j => rfl
    | neg i => simp [isoBlockWord, isoBand, isoEnds, isoSign, bandWord, SBlock.word, morseOfBraid]

/-- A rule applied forward at the junction of `u` and `v`. -/
theorem morseReach_isoRule (n₀ : ℕ) (u v : MorseWord) (r : MorseRule)
    (hok : morseRuleOk r = true)
    (hl : morseFits (morseOut n₀ u) (morseRuleLhs r) = true)
    (hr : morseFits (morseOut n₀ u) (morseRuleRhs r) = true) :
    MorseReach n₀ (u ++ morseRuleLhs r ++ v) (u ++ morseRuleRhs r ++ v) :=
  ⟨[(u.length, r, false)], by
    simpa [morseApplyAll] using morseApply_junction n₀ u v r false hok hl hr⟩

/-- A word of cups adds two strands per letter. -/
theorem morseOut_of_cups (n : ℕ) (w : MorseWord) (hw : ∀ l ∈ w, l.1 = MorseKind.cup) :
    morseOut n w = n + 2 * w.length := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    rw [morseOut, ih _ fun x hx ↦ hw x (List.mem_cons_of_mem _ hx), morseLetterOut,
      hw l List.mem_cons_self]
    simp only [morseKindOut, morseKindIn, List.length_cons]
    omega

/-- A word of caps removes two strands per letter. -/
theorem morseOut_of_caps (n : ℕ) (w : MorseWord) (hw : ∀ l ∈ w, l.1 = MorseKind.cap) :
    morseOut n w = n - 2 * w.length := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    rw [morseOut, ih _ fun x hx ↦ hw x (List.mem_cons_of_mem _ hx), morseLetterOut,
      hw l List.mem_cons_self]
    simp only [morseKindOut, morseKindIn, List.length_cons]
    omega

/-- A row of cups fits when the cup of index `t` fits on the `n + 2 t` strands before it. -/
theorem morseFits_isoCups (n k : ℕ) (f : ℕ → ℕ) (hf : ∀ t < k, f t ≤ n + 2 * t) :
    morseFits n ((List.range k).map fun t ↦ isoU (f t)) = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, morseFits_append, ih fun t ht ↦ hf t (by omega),
      Bool.true_and, morseOut_of_cups _ _ (by simp [isoU])]
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil, morseFits_cons,
      isoU, morseKindIn, morseFits_nil, and_true]
    have := hf k (by omega)
    omega

/-- A row of caps (read from the index `k - 1` down to `0`) fits when the cap of index `t` fits on
the strands left before it. -/
theorem morseFits_isoCaps (n k : ℕ) (f : ℕ → ℕ)
    (hf : ∀ t < k, f t + 2 + 2 * (k - 1 - t) ≤ n) :
    morseFits n ((List.range k).reverse.map fun t ↦ isoN (f t)) = true := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_cons, morseFits_cons, isoN, morseKindIn]
    refine ⟨by have := hf k (by omega); omega, ?_⟩
    apply ih
    intro t ht
    have := hf t (by omega)
    simp only [morseLetterOut, morseKindOut, morseKindIn]
    omega

/-- The letters of a band are crossings at the positions `i … j - 1` (or at `i` when `j ≤ i`). -/
theorem mem_isoBand {i j : ℕ} {b : Bool} {l : MorseLetter} (hl : l ∈ isoBand i j b) :
    (∃ s, l.1 = MorseKind.cross s) ∧ i ≤ l.2 ∧ (l.2 = i ∨ l.2 + 1 ≤ j) := by
  simp only [isoBand, morseOfBraid, bandWord, List.mem_map, List.mem_append, List.mem_range,
    List.mem_singleton] at hl
  obtain ⟨g, hg, rfl⟩ := hl
  rcases hg with (⟨x, hx, rfl⟩ | rfl) | ⟨x, hx, rfl⟩ <;>
    refine ⟨⟨_, rfl⟩, ?_, ?_⟩ <;> dsimp only <;> omega

/-- A band does not change the number of strands. -/
theorem morseOut_isoBand (n i j : ℕ) (b : Bool) : morseOut n (isoBand i j b) = n :=
  morseOut_of_cross n _ fun _ hl ↦ (mem_isoBand hl).1

/-- The letters of the block words of a block list are crossings. -/
theorem isoBlockWords_cross (f : ℕ → ℕ) (B : List SBlock) :
    ∀ l ∈ B.flatMap (isoBlockWord f), ∃ s, l.1 = MorseKind.cross s := by
  intro l hl
  obtain ⟨b, -, hl⟩ := List.mem_flatMap.mp hl
  exact (mem_isoBand hl).1

/-- The block words of a block list do not change the number of strands. -/
theorem morseOut_isoBlockWords (n : ℕ) (f : ℕ → ℕ) (B : List SBlock) :
    morseOut n (B.flatMap (isoBlockWord f)) = n :=
  morseOut_of_cross n _ (isoBlockWords_cross f B)

/-- The two discs of a valid block are ordered and lie below `m`. -/
theorem isoEnds_lt {m : ℕ} {b : SBlock} (hb : b.Valid m) :
    (isoEnds b).1 < (isoEnds b).2 ∧ (isoEnds b).2 < m := by
  cases b with
  | band i j => exact hb
  | neg i => exact ⟨Nat.lt_succ_self i, hb⟩

end AJConjecture
