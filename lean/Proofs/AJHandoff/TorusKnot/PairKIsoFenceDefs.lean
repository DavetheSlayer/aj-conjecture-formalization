import Mathlib
import AJHandoff.TorusKnot.PairKIsoThinDefs

/-!
# Fence words: thin discs with their dead ends retracted

In the thin word every disc runs from the bottom of the word to its top. Disc `m` is needed only
between its first and its last block (`isoFirst`, `isoLast`); below and above it is a dead end,
crossed only by bands passing in front of it. Retracting the dead ends (the cup of the disc slides
up to its first block, the cap down to its last block) gives the *fence word*: a disc is *open* at
the block `k` when `isoFirst ≤ k ≤ isoLast`, its left edge sits at `isoPos`, one plus twice the
number of open discs of smaller index, and every block is preceded by the cups of the discs it
opens and followed by the caps of the discs it closes.

`isoFenceAux n B j` keeps the discs `1, …, j` open everywhere (their cups at the bottom, their caps
at the top); `isoFenceAux n B n` is the thin word (`isoFenceAux_top`) and `isoFenceWord n B :=
isoFenceAux n B 0` is the fence word. For the blocks `pairBlocks r s` the fence word is the strip
word `pairStrip r s` (`AJHandoff.TorusKnot.PairKIsoStrip`). Checked outside Lean for every `j` and
`(r, s) ∈ {(2,3), (2,5), (3,4), (3,5), (4,5)}` (`SCR/ISO/tools/phase1.py`).
-/

namespace AJConjecture

/-- The block `b` is attached to the disc `m`. -/
def isoAttached (m : ℕ) (b : SBlock) : Bool := decide ((isoEnds b).1 = m ∨ (isoEnds b).2 = m)

/-- The index of the first block attached to the disc `m`. -/
def isoFirst (B : List SBlock) (m : ℕ) : ℕ := B.findIdx (isoAttached m)

/-- The index of the last block attached to the disc `m`. -/
def isoLast (B : List SBlock) (m : ℕ) : ℕ := B.length - 1 - B.reverse.findIdx (isoAttached m)

/-- The disc `m ≥ 1` is open at the block `k`: kept open (`m ≤ j`) or between its first and last
block. -/
def isoOpen (B : List SBlock) (j m k : ℕ) : Bool :=
  decide (1 ≤ m ∧ (m ≤ j ∨ (isoFirst B m ≤ k ∧ k ≤ isoLast B m)))

/-- The position of the left edge of the disc `m` at the block `k` (`0` for the base disc). -/
def isoPos (B : List SBlock) (j k m : ℕ) : ℕ :=
  if m = 0 then 0 else 1 + 2 * ((List.range m).filter fun x ↦ isoOpen B j x k).length

/-- The fence word of the block `k`: cups of the discs it opens, its band, caps of the discs it
closes. -/
def isoFenceBlock (n : ℕ) (B : List SBlock) (j k : ℕ) (b : SBlock) : MorseWord :=
  (((List.range (n + 1)).filter fun m ↦
      decide (j < m ∧ isoFirst B m = k)).map fun m ↦ isoU (isoPos B j k m)) ++
    isoBlockWord (isoPos B j k) b ++
    (((List.range (n + 1)).filter fun m ↦
      decide (j < m ∧ isoLast B m = k)).reverse.map fun m ↦ isoN (isoPos B j k m))

/-- The fence word with the discs `1, …, j` kept open everywhere. -/
def isoFenceAux (n : ℕ) (B : List SBlock) (j : ℕ) : MorseWord :=
  ((List.range (min j n)).map fun t ↦ isoU (2 * t + 1)) ++
    (B.zipIdx.flatMap fun bk ↦ isoFenceBlock n B j bk.2 bk.1) ++
    ((List.range (min j n)).reverse.map fun t ↦ isoN (2 * t + 1))

/-- The fence word of a block list. -/
def isoFenceWord (n : ℕ) (B : List SBlock) : MorseWord := isoFenceAux n B 0

/-- A filtered range grows by its last element. -/
private theorem length_filter_range_succ_fence (p : ℕ → Bool) (m : ℕ) :
    ((List.range (m + 1)).filter p).length =
      ((List.range m).filter p).length + if p m then 1 else 0 := by
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : p m <;> simp [h]

/-- With every disc kept open, the disc `m ≥ 1` sits at `2m - 1`. -/
private theorem isoPos_top_fence (n : ℕ) (B : List SBlock) (k m : ℕ) (hm : m ≤ n) :
    isoPos B n k m = isoThinIndex 0 m := by
  have hc : ∀ m', m' ≤ n + 1 →
      ((List.range m').filter fun x ↦ isoOpen B n x k).length = m' - 1 := by
    intro m'
    induction m' with
    | zero => intro _; rfl
    | succ m' ih =>
      intro hm'
      rw [length_filter_range_succ_fence, ih (by omega)]
      by_cases h0 : m' = 0
      · subst h0
        simp [isoOpen]
      · have : isoOpen B n m' k = true := by
          simp only [isoOpen, decide_eq_true_eq]
          omega
        simp only [this, ↓reduceIte]
        omega
  simp only [isoPos, isoThinIndex]
  split_ifs with h1 h2 <;> first | omega | (rw [hc m (by omega)]; omega)

/-- With every disc kept open, a fence block is the thin block word. -/
private theorem isoFenceBlock_top_fence (n : ℕ) (B : List SBlock) (k : ℕ) (b : SBlock)
    (hb : b.Valid (n + 1)) : isoFenceBlock n B n k b = isoBlockWord (isoThinIndex 0) b := by
  have hv := isoEnds_lt hb
  have e1 : ((List.range (n + 1)).filter fun m ↦ decide (n < m ∧ isoFirst B m = k)) = [] :=
    List.filter_eq_nil_iff.mpr fun a ha ↦ by
      simp only [List.mem_range] at ha
      simp only [decide_eq_true_eq, not_and]
      omega
  have e2 : ((List.range (n + 1)).filter fun m ↦ decide (n < m ∧ isoLast B m = k)) = [] :=
    List.filter_eq_nil_iff.mpr fun a ha ↦ by
      simp only [List.mem_range] at ha
      simp only [decide_eq_true_eq, not_and]
      omega
  simp only [isoFenceBlock, e1, e2, List.map_nil, List.reverse_nil, List.nil_append,
    List.append_nil, isoBlockWord]
  rw [isoPos_top_fence n B k _ (by omega), isoPos_top_fence n B k _ (by omega)]

/-- The fence blocks with every disc kept open, from any start index. -/
private theorem flatMap_isoFenceBlock_top_fence (n : ℕ) (B' : List SBlock) :
    ∀ (B : List SBlock) (i : ℕ), (∀ b ∈ B, b.Valid (n + 1)) →
      (B.zipIdx i).flatMap (fun bk ↦ isoFenceBlock n B' n bk.2 bk.1) =
        B.flatMap (isoBlockWord (isoThinIndex 0)) := by
  intro B
  induction B with
  | nil => intro _ _; rfl
  | cons b B ih =>
    intro i hB
    rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons,
      isoFenceBlock_top_fence n B' i b (hB b List.mem_cons_self),
      ih (i + 1) fun x hx ↦ hB x (List.mem_cons_of_mem _ hx)]

/-- With every disc kept open, the fence word is the thin word. -/
theorem isoFenceAux_top {n : ℕ} {B : List SBlock} (hB : ∀ b ∈ B, b.Valid (n + 1)) :
    isoFenceAux n B n = isoThinWord n B := by
  have hu : (fun t ↦ isoU (0 + 1 + 2 * t)) = fun t ↦ isoU (2 * t + 1) :=
    funext fun t ↦ by rw [Nat.zero_add, Nat.add_comm]
  have hn : (fun t ↦ isoN (0 + 1 + 2 * t)) = fun t ↦ isoN (2 * t + 1) :=
    funext fun t ↦ by rw [Nat.zero_add, Nat.add_comm]
  simp only [isoFenceAux, isoThinWord, isoThinPartial, min_self, List.range_zero, List.map_nil,
    List.reverse_nil, List.nil_append, List.append_nil, Nat.sub_zero,
    flatMap_isoFenceBlock_top_fence n B B 0 hB, hu, hn]

/-! ### Positions of the discs in the fence words -/

/-- The number of open discs below `m + 1`. -/
theorem length_filter_isoOpen_succ (B : List SBlock) (j k m : ℕ) :
    ((List.range (m + 1)).filter fun x ↦ isoOpen B j x k).length =
      ((List.range m).filter fun x ↦ isoOpen B j x k).length +
        if isoOpen B j m k then 1 else 0 :=
  length_filter_range_succ_fence _ m

/-- Bounds on the number of open discs below `m`: at most `m - 1`, at least `min (m - 1) j`. -/
theorem length_filter_isoOpen_bounds (B : List SBlock) (j k m : ℕ) :
    min (m - 1) j ≤ ((List.range m).filter fun x ↦ isoOpen B j x k).length ∧
      ((List.range m).filter fun x ↦ isoOpen B j x k).length ≤ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [length_filter_isoOpen_succ]
    by_cases h0 : m = 0
    · subst h0
      simp [isoOpen]
    by_cases h1 : m ≤ j
    · have : isoOpen B j m k = true := by
        simp only [isoOpen, decide_eq_true_eq]
        omega
      simp only [this, ↓reduceIte]
      omega
    · split_ifs <;> omega

/-- A disc above the kept discs sits right of them. -/
theorem le_isoPos_of_lt (B : List SBlock) {j k m : ℕ} (hm : j < m) :
    2 * j + 1 ≤ isoPos B j k m := by
  have := (length_filter_isoOpen_bounds B j k m).1
  simp only [isoPos, show m ≠ 0 by omega, ↓reduceIte]
  omega

/-- The disc `m ≥ 1` sits at most at `2m - 1`. -/
theorem isoPos_lt_two_mul (B : List SBlock) (j k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    isoPos B j k m + 1 ≤ 2 * m := by
  have := (length_filter_isoOpen_bounds B j k m).2
  simp only [isoPos, show m ≠ 0 by omega, ↓reduceIte]
  omega

/-- The disc `j + 1` sits right of the kept discs `1, …, j`. -/
theorem isoPos_succ_self (B : List SBlock) (j k : ℕ) : isoPos B j k (j + 1) = 2 * j + 1 := by
  have := length_filter_isoOpen_bounds B j k (j + 1)
  simp only [isoPos, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, min_self] at this ⊢
  omega

/-- Keeping the disc `j + 1` open where it is closed moves the discs above it two places right. -/
theorem isoPos_succ_of_not_open (B : List SBlock) (j k m : ℕ)
    (h : ¬(isoFirst B (j + 1) ≤ k ∧ k ≤ isoLast B (j + 1))) :
    isoPos B (j + 1) k m = isoPos B j k m + if j + 1 < m then 2 else 0 := by
  have hc : ∀ m', ((List.range m').filter fun x ↦ isoOpen B (j + 1) x k).length =
      ((List.range m').filter fun x ↦ isoOpen B j x k).length + if j + 1 < m' then 1 else 0 := by
    intro m'
    induction m' with
    | zero => simp
    | succ m' ih =>
      rw [length_filter_isoOpen_succ, length_filter_isoOpen_succ, ih]
      by_cases h1 : m' = j + 1
      · subst h1
        have e1 : isoOpen B (j + 1) (j + 1) k = true := by
          simp only [isoOpen, decide_eq_true_eq]
          omega
        have e2 : isoOpen B j (j + 1) k = false := by
          simp only [isoOpen, decide_eq_false_iff_not]
          omega
        simp only [e1, e2, ↓reduceIte, Bool.false_eq_true]
        split_ifs <;> omega
      · have e : isoOpen B (j + 1) m' k = isoOpen B j m' k := by
          simp only [isoOpen]
          congr 1
          apply propext
          omega
        rw [e]
        split_ifs <;> omega
  simp only [isoPos, hc m]
  split_ifs <;> omega

/-- Where the disc `j + 1` is open anyway, keeping it open changes no position. -/
theorem isoPos_succ_of_open (B : List SBlock) (j k : ℕ)
    (h : isoFirst B (j + 1) ≤ k ∧ k ≤ isoLast B (j + 1)) :
    isoPos B (j + 1) k = isoPos B j k := by
  have e : (fun x ↦ isoOpen B (j + 1) x k) = fun x ↦ isoOpen B j x k := by
    funext x
    simp only [isoOpen]
    congr 1
    apply propext
    by_cases hx : x = j + 1
    · subst hx
      omega
    · omega
  funext m
  simp only [isoPos, e]

/-- When the disc `j + 1` is not concerned, the discs above `j + 1` and above `j` agree. -/
theorem filter_isoDisc_succ (N j k : ℕ) (f : ℕ → ℕ) (hf : f (j + 1) ≠ k) :
    (List.range N).filter (fun m ↦ decide (j + 1 < m ∧ f m = k)) =
      (List.range N).filter (fun m ↦ decide (j < m ∧ f m = k)) := by
  refine List.filter_congr fun m _ ↦ ?_
  by_cases hm : m = j + 1
  · subst hm
    simp [hf]
  · simp only [decide_eq_decide]
    omega

/-- When the disc `j + 1` is concerned, it is the first of the discs above `j`. -/
theorem filter_isoDisc_cons (n j k : ℕ) (f : ℕ → ℕ) (hf : f (j + 1) = k) (hj : j < n) :
    (List.range (n + 1)).filter (fun m ↦ decide (j < m ∧ f m = k)) =
      (j + 1) :: (List.range (n + 1)).filter (fun m ↦ decide (j + 1 < m ∧ f m = k)) := by
  have key : ∀ N, j + 2 ≤ N → (List.range N).filter (fun m ↦ decide (j < m ∧ f m = k)) =
      (j + 1) :: (List.range N).filter (fun m ↦ decide (j + 1 < m ∧ f m = k)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have e1 : (List.range (j + 1)).filter (fun m ↦ decide (j < m ∧ f m = k)) = [] :=
        List.filter_eq_nil_iff.mpr fun a ha ↦ by
          simp only [List.mem_range] at ha
          simp only [decide_eq_true_eq, not_and]
          omega
      have e2 : (List.range (j + 2)).filter (fun m ↦ decide (j + 1 < m ∧ f m = k)) = [] :=
        List.filter_eq_nil_iff.mpr fun a ha ↦ by
          simp only [List.mem_range] at ha
          simp only [decide_eq_true_eq, not_and]
          omega
      rw [e2, show j + 2 = j + 1 + 1 by rfl, List.range_succ, List.filter_append, e1]
      simp [hf]
    | succ N hN ih =>
      rw [List.range_succ, List.filter_append, List.filter_append, ih]
      have : decide (j < N ∧ f N = k) = decide (j + 1 < N ∧ f N = k) := by
        simp only [decide_eq_decide]
        omega
      simp only [List.filter_singleton, this, List.cons_append]
  exact key (n + 1) (by omega)

/-- A block below the first block of the disc `m` is not attached to it. -/
theorem isoAttached_of_lt_isoFirst {B : List SBlock} {m k : ℕ} {b : SBlock}
    (hk : k < isoFirst B m) (hbk : B[k]? = some b) : isoAttached m b = false := by
  have h := List.not_of_lt_findIdx hk
  obtain ⟨_, hb⟩ := List.getElem?_eq_some_iff.mp hbk
  rw [← hb]
  exact h

/-- A block above the last block of the disc `m` is not attached to it. -/
theorem isoAttached_of_isoLast_lt {B : List SBlock} {m k : ℕ} {b : SBlock}
    (hk : isoLast B m < k) (hbk : B[k]? = some b) : isoAttached m b = false := by
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hbk
  have h1 : B.length - 1 - k < B.reverse.findIdx (isoAttached m) := by
    simp only [isoLast] at hk
    omega
  have h := List.not_of_lt_findIdx h1
  have e : B.reverse[B.length - 1 - k]'(by simp; omega) = b := by
    have := List.getElem?_reverse (l := B) (i := B.length - 1 - k) (by omega)
    rw [show B.length - 1 - (B.length - 1 - k) = k by omega, hbk] at this
    obtain ⟨_, h2⟩ := List.getElem?_eq_some_iff.mp this
    exact h2
  rw [← e]
  exact h

/-- The discs of a block not attached to `m` differ from `m`. -/
theorem isoEnds_ne_of_not_attached {m : ℕ} {b : SBlock} (h : isoAttached m b = false) :
    (isoEnds b).1 ≠ m ∧ (isoEnds b).2 ≠ m := by
  simp only [isoAttached, decide_eq_false_iff_not, not_or] at h
  exact h

/-! ### Moves of a dead-end cup or cap -/

/-- A band of span one is a single crossing. -/
theorem isoBand_span_one (c : ℕ) (s : Bool) : isoBand c (c + 1) s = [isoX s c] := by
  simp [isoBand, bandWord, morseOfBraid, isoX]

/-- A band peels: `b(c, d + 1) = σ_d b(c, d) σ_d⁻¹` for `c < d`. -/
theorem isoBand_peel_right (c d : ℕ) (hcd : c < d) (s : Bool) :
    isoBand c (d + 1) s = isoX true d :: (isoBand c d s ++ [isoX false d]) := by
  obtain ⟨k, hk⟩ : ∃ k, d - 1 - c = k := ⟨_, rfl⟩
  have hk' : d + 1 - 1 - c = k + 1 := by omega
  have h1 : (List.range (k + 1)).map (fun t ↦ (d + 1 - 1 - t, true)) =
      (d, true) :: (List.range k).map (fun t ↦ (d - 1 - t, true)) := by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.cons.injEq]
    refine ⟨by simp, List.map_congr_left fun t _ ↦ ?_⟩
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    omega
  have h2 : (List.range (k + 1)).map (fun t ↦ (c + 1 + t, false)) =
      (List.range k).map (fun t ↦ (c + 1 + t, false)) ++ [(d, false)] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    congr 3
    omega
  simp only [isoBand, bandWord, hk, hk', h1, h2, morseOfBraid, isoX]
  simp

/-- The letters of a fitting word of crossings fit. -/
theorem le_of_morseFits_cross {N : ℕ} {x : MorseWord}
    (hx : ∀ l ∈ x, ∃ s, l.1 = MorseKind.cross s) (h : morseFits N x = true) :
    ∀ l ∈ x, l.2 + 2 ≤ N := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [morseFits_cons] at h
    obtain ⟨s, hs⟩ := hx a List.mem_cons_self
    have hN : morseLetterOut N a = N := by
      simp only [morseLetterOut, hs, morseKindOut, morseKindIn]
      omega
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · have := h.1
      rw [hs] at this
      simpa [morseKindIn] using this
    · rw [hN] at h
      exact ih (fun l hl ↦ hx l (List.mem_cons_of_mem _ hl)) h.2 l hl

/-- A fitting band `b(c, e)`, `c < e`, lives on at least `e + 1` strands. -/
theorem le_of_morseFits_isoBand {N c e : ℕ} {s : Bool} (hce : c < e)
    (h : morseFits N (isoBand c e s) = true) : e + 1 ≤ N := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  have hb := le_of_morseFits_cross (fun l hl ↦ (mem_isoBand hl).1) h
  by_cases hd : c = d
  · subst hd
    have := hb (isoX s c) (by rw [isoBand_span_one]; simp)
    simp only [isoX] at this
    omega
  · have := hb (isoX true d) (by rw [isoBand_peel_right c d (by omega)]; simp)
    simp only [isoX] at this
    omega

/-- A band fits on the strands right of its right end. -/
theorem morseFits_isoBand_of_le {N c e : ℕ} {s : Bool} (hce : c < e) (h : e + 1 ≤ N) :
    morseFits N (isoBand c e s) = true :=
  morseFits_of_cross _ _ (fun _ hl ↦ (mem_isoBand hl).1) fun _ hl ↦ by
    have := mem_isoBand hl
    omega

/-- The arities of a cup. -/
private theorem morseKind_cup_fence : morseKindIn .cup = 0 ∧ morseKindOut .cup = 2 := ⟨rfl, rfl⟩

/-- The arities of a cap. -/
private theorem morseKind_cap_fence : morseKindIn .cap = 2 ∧ morseKindOut .cap = 0 := ⟨rfl, rfl⟩

/-- The arities of any letter are at most two. -/
private theorem morseKind_le_fence (κ : MorseKind) : morseKindIn κ ≤ 2 ∧ morseKindOut κ ≤ 2 := by
  cases κ <;> simp [morseKindIn, morseKindOut]

/-- A cup rises past letters standing right of it (exchanges); they move two places left. -/
theorem morseReach_isoCupSweep (n₀ q : ℕ) (u x v : MorseWord) (hx : ∀ l ∈ x, q ≤ l.2)
    (hfit : morseFits (morseOut n₀ u) (isoU q :: morseShiftWord 2 x) = true) :
    MorseReach n₀ (u ++ [isoU q] ++ morseShiftWord 2 x ++ v) (u ++ x ++ [isoU q] ++ v) := by
  induction x generalizing u with
  | nil => exact ⟨[], by simp [morseApplyAll, morseShiftWord]⟩
  | cons l x ih =>
    obtain ⟨κ, i⟩ := l
    have hl : q ≤ i := hx (κ, i) List.mem_cons_self
    have hk := morseKind_le_fence κ
    simp only [morseShiftWord, List.map_cons, shiftLetter, morseFits_cons, isoU,
      morseKind_cup_fence, morseLetterOut] at hfit
    obtain ⟨h1, h2, h3⟩ := hfit
    have e1 := morseReach_isoRule n₀ u (morseShiftWord 2 x ++ v) (.exch (MorseKind.cup, q) (κ, i))
      (by simp only [morseRuleOk, morseKind_cup_fence, decide_eq_true_eq]; omega)
      (by
        simp only [morseRuleLhs, morseFits_cons, morseKind_cup_fence, morseLetterOut,
          morseFits_nil, and_true]
        omega)
      (by
        simp only [morseRuleRhs, morseFits_cons, morseKind_cup_fence, morseLetterOut,
          morseFits_nil, and_true]
        omega)
    have e2 := ih (u ++ [(κ, i)]) (fun l' hl' ↦ hx l' (List.mem_cons_of_mem _ hl')) (by
      rw [morseOut_append]
      simp only [morseOut, morseLetterOut, morseFits_cons, isoU, morseKind_cup_fence]
      refine ⟨by omega, ?_⟩
      rw [show morseOut n₀ u + morseKindOut κ - morseKindIn κ + 2 - 0 =
        morseOut n₀ u + 2 - 0 + morseKindOut κ - morseKindIn κ by omega]
      exact h3)
    simp only [morseRuleLhs, morseRuleRhs, morseKind_cup_fence, Nat.sub_zero] at e1
    simp only [morseShiftWord, shiftLetter, isoU, List.map_cons, List.append_assoc,
      List.cons_append] at e1 e2 ⊢
    exact morseReach_trans e1 e2

/-- A cap falls past letters standing right of it (exchanges); they move two places right. -/
theorem morseReach_isoCapSweep (n₀ q : ℕ) (u x v : MorseWord) (hx : ∀ l ∈ x, q ≤ l.2)
    (hfit : morseFits (morseOut n₀ u) (morseShiftWord 2 x ++ [isoN q]) = true) :
    MorseReach n₀ (u ++ morseShiftWord 2 x ++ [isoN q] ++ v) (u ++ [isoN q] ++ x ++ v) := by
  induction x using List.reverseRecOn generalizing v with
  | nil => exact ⟨[], by simp [morseApplyAll, morseShiftWord]⟩
  | append_singleton x l ih =>
    obtain ⟨κ, i⟩ := l
    have hl : q ≤ i := hx (κ, i) (by simp)
    have hk := morseKind_le_fence κ
    rw [morseShiftWord_append, morseFits_append, morseFits_append, Bool.and_eq_true,
      Bool.and_eq_true] at hfit
    obtain ⟨⟨h1, h2⟩, h3⟩ := hfit
    set N := morseOut n₀ (u ++ morseShiftWord 2 x) with hN
    have hN' : morseOut (morseOut n₀ u) (morseShiftWord 2 x) = N := by rw [hN, morseOut_append]
    rw [hN'] at h2
    rw [morseOut_append, hN'] at h3
    simp only [morseShiftWord, shiftLetter, List.map_cons, List.map_nil, morseFits_cons,
      morseLetterOut, morseOut, isoN, morseKind_cap_fence, morseFits_nil, and_true] at h2 h3
    have e1 := morseReach_symm (morseReach_isoRule n₀ (u ++ morseShiftWord 2 x) v
      (.exch (MorseKind.cap, q) (κ, i + 2))
      (by simp only [morseRuleOk, morseKind_cap_fence, decide_eq_true_eq]; omega)
      (by
        rw [← hN]
        simp only [morseRuleLhs, morseFits_cons, morseKind_cap_fence, morseLetterOut,
          morseFits_nil, and_true]
        omega)
      (by
        rw [← hN]
        simp only [morseRuleRhs, morseFits_cons, morseKind_cap_fence, morseLetterOut,
          morseFits_nil, and_true]
        omega))
    have e2 := ih ([(κ, i)] ++ v) (fun l' hl' ↦ hx l' (by simp [hl'])) (by
      rw [morseFits_append, h1, Bool.true_and, hN']
      simp only [isoN, morseFits_cons, morseKind_cap_fence, morseFits_nil, and_true]
      omega)
    simp only [morseRuleLhs, morseRuleRhs, morseKind_cap_fence,
      show i + 2 + 0 - 2 = i by omega] at e1
    rw [morseShiftWord_append]
    simp only [morseShiftWord, shiftLetter, isoN, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append] at e1 e2 ⊢
    exact morseReach_trans e1 e2

/-- A cup rises past a band whose left end lies left of it and whose right end lies right of it:
`cupSlide` at the two edges, exchanges elsewhere. -/
theorem morseReach_isoCupBand (n₀ q c : ℕ) (s : Bool) (hc : c < q) :
    ∀ e, q + 2 ≤ e → ∀ u v : MorseWord, q ≤ morseOut n₀ u → e ≤ morseOut n₀ u + 1 →
      MorseReach n₀ (u ++ [isoU q] ++ isoBand c e s ++ v)
        (u ++ isoBand c (e - 2) s ++ [isoU q] ++ v) := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    intro u v hq he
    have hcr : ∀ l ∈ isoBand c q s, ∃ t, l.1 = MorseKind.cross t := fun _ hl ↦ (mem_isoBand hl).1
    have h1 := morseReach_isoRule n₀ u
      (isoBand c q s ++ [isoX false q, isoX false (q + 1)] ++ v) (.cupSlide q true false) rfl
      (by
        simp only [morseRuleLhs, Bool.false_eq_true, ↓reduceIte, morseFits_cons,
          morseLetterOut, morseKindIn, morseKindOut, morseFits_nil,
          and_true]
        omega)
      (by
        simp only [morseRuleRhs, Bool.false_eq_true, ↓reduceIte, morseFits_cons,
          morseKind_cup_fence, morseFits_nil, and_true]
        omega)
    have h2 := morseReach_comm n₀ u (isoBand c q s) [isoU (q + 1)]
      ([isoX false q, isoX false (q + 1)] ++ v) hcr
      (fun b hb a ha ↦ by
        rw [List.mem_singleton.mp ha]
        have := mem_isoBand hb
        simp only [isoU]
        omega)
      (by
        simp only [List.singleton_append, morseFits_cons, isoU, morseKind_cup_fence,
          morseLetterOut]
        exact ⟨by omega, morseFits_isoBand_of_le hc (by omega)⟩)
    have h3 := morseReach_isoRule n₀ (u ++ isoBand c q s) v (.cupSlide q false true) rfl
      (by
        rw [morseOut_append, morseOut_isoBand]
        simp only [morseRuleLhs, ↓reduceIte, morseFits_cons, 
          morseLetterOut, morseKindIn, morseKindOut, morseFits_nil, and_true]
        omega)
      (by
        rw [morseOut_append, morseOut_isoBand]
        simp only [morseRuleRhs, ↓reduceIte, morseFits_cons, morseKind_cup_fence,
          morseFits_nil, and_true]
        omega)
    rw [show q + 2 - 2 = q by omega, show q + 2 = q + 1 + 1 by rfl,
      isoBand_peel_right c (q + 1) (by omega), isoBand_peel_right c q hc]
    simp only [morseRuleLhs, morseRuleRhs, ↓reduceIte, Bool.false_eq_true] at h1 h3
    simp only [isoU, isoX, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)
  | succ e he ih =>
    intro u v hq he'
    have h1 := morseReach_isoCupSweep n₀ q u [isoX true (e - 2)]
      (isoBand c e s ++ [isoX false e] ++ v)
      (fun l hl ↦ by rw [List.mem_singleton.mp hl]; simp only [isoX]; omega)
      (by
        simp only [morseShiftWord, shiftLetter, isoX, isoU, List.map_cons, List.map_nil,
          morseFits_cons, morseKind_cup_fence, morseLetterOut, morseKindIn, morseFits_nil,
          and_true]
        omega)
    have h2 := ih (u ++ [isoX true (e - 2)]) ([isoX false e] ++ v)
      (by rw [morseOut_append]; simp only [isoX, morseOut, morseLetterOut, morseKindOut,
        morseKindIn]; omega)
      (by rw [morseOut_append]; simp only [isoX, morseOut, morseLetterOut, morseKindOut,
        morseKindIn]; omega)
    have h3 := morseReach_isoCupSweep n₀ q (u ++ [isoX true (e - 2)] ++ isoBand c (e - 2) s)
      [isoX false (e - 2)] v
      (fun l hl ↦ by rw [List.mem_singleton.mp hl]; simp only [isoX]; omega)
      (by
        rw [morseOut_append, morseOut_isoBand, morseOut_append]
        simp only [morseShiftWord, shiftLetter, isoX, isoU, List.map_cons, List.map_nil,
          morseFits_cons, morseLetterOut, morseKindIn, morseKindOut,
          morseOut, morseFits_nil, and_true]
        omega)
    rw [isoBand_peel_right c e (by omega), show e + 1 - 2 = e - 2 + 1 by omega,
      isoBand_peel_right c (e - 2) (by omega)]
    have he2 : e - 2 + 2 = e := by omega
    simp only [morseShiftWord, shiftLetter, List.map_cons, List.map_nil] at h1 h3
    simp only [isoU, isoX, he2, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- A cap falls past a band whose left end lies left of it and whose right end lies right of it:
`capSlide` at the two edges, exchanges elsewhere. -/
theorem morseReach_isoCapBand (n₀ q c : ℕ) (s : Bool) (hc : c < q) :
    ∀ e, q + 2 ≤ e → ∀ u v : MorseWord, e + 1 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ isoBand c e s ++ [isoN q] ++ v)
        (u ++ [isoN q] ++ isoBand c (e - 2) s ++ v) := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    intro u v he
    have hcr : ∀ l ∈ isoBand c q s, ∃ t, l.1 = MorseKind.cross t := fun _ hl ↦ (mem_isoBand hl).1
    have hout : morseOut n₀ (u ++ [isoX true (q + 1), isoX true q] ++ isoBand c q s) =
        morseOut n₀ u := by
      rw [morseOut_append, morseOut_isoBand, morseOut_append]
      simp only [isoX, morseOut, morseLetterOut, morseKindOut, morseKindIn]
      omega
    have h1 := morseReach_isoRule n₀ (u ++ [isoX true (q + 1), isoX true q] ++ isoBand c q s) v
      (.capSlide q false true) rfl
      (by
        rw [hout]
        simp only [morseRuleLhs, ↓reduceIte, morseFits_cons, 
          morseLetterOut, morseKindIn, morseKindOut, morseFits_nil, and_true]
        omega)
      (by
        rw [hout]
        simp only [morseRuleRhs, ↓reduceIte, morseFits_cons, morseKind_cap_fence,
          morseFits_nil, and_true]
        omega)
    have h2 := morseReach_symm (morseReach_comm n₀ (u ++ [isoX true (q + 1), isoX true q])
      (isoBand c q s) [isoN (q + 1)] v hcr
      (fun b hb a ha ↦ by
        rw [List.mem_singleton.mp ha]
        have := mem_isoBand hb
        simp only [isoN]
        omega)
      (by
        rw [morseOut_append]
        simp only [isoX, morseOut, morseLetterOut, morseKindOut, morseKindIn,
          List.singleton_append, morseFits_cons, isoN]
        exact ⟨by omega, morseFits_isoBand_of_le hc (by omega)⟩))
    have h3 := morseReach_isoRule n₀ u (isoBand c q s ++ v) (.capSlide q true false) rfl
      (by
        simp only [morseRuleLhs, Bool.false_eq_true, ↓reduceIte, morseFits_cons,
          morseLetterOut, morseKindIn, morseKindOut, morseFits_nil,
          and_true]
        omega)
      (by
        simp only [morseRuleRhs, Bool.false_eq_true, ↓reduceIte, morseFits_cons,
          morseKind_cap_fence, morseFits_nil, and_true]
        omega)
    rw [show q + 2 - 2 = q by omega, show q + 2 = q + 1 + 1 by rfl,
      isoBand_peel_right c (q + 1) (by omega), isoBand_peel_right c q hc]
    simp only [morseRuleLhs, morseRuleRhs, ↓reduceIte, Bool.false_eq_true] at h1 h3
    simp only [isoN, isoX, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)
  | succ e he ih =>
    intro u v he'
    have h1 := morseReach_isoCapSweep n₀ q (u ++ [isoX true e] ++ isoBand c e s)
      [isoX false (e - 2)] v
      (fun l hl ↦ by rw [List.mem_singleton.mp hl]; simp only [isoX]; omega)
      (by
        rw [morseOut_append, morseOut_isoBand, morseOut_append]
        simp only [morseShiftWord, shiftLetter, isoX, isoN, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, morseFits_cons, 
          morseLetterOut, morseKindIn, morseKindOut, morseOut, morseFits_nil, and_true]
        omega)
    have h2 := ih (u ++ [isoX true e]) ([isoX false (e - 2)] ++ v)
      (by rw [morseOut_append]; simp only [isoX, morseOut, morseLetterOut, morseKindOut,
        morseKindIn]; omega)
    have h3 := morseReach_isoCapSweep n₀ q u [isoX true (e - 2)]
      (isoBand c (e - 2) s ++ [isoX false (e - 2)] ++ v)
      (fun l hl ↦ by rw [List.mem_singleton.mp hl]; simp only [isoX]; omega)
      (by
        simp only [morseShiftWord, shiftLetter, isoX, isoN, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, morseFits_cons, 
          morseLetterOut, morseKindIn, morseKindOut, morseFits_nil, and_true]
        omega)
    rw [isoBand_peel_right c e (by omega), show e + 1 - 2 = e - 2 + 1 by omega,
      isoBand_peel_right c (e - 2) (by omega)]
    have he2 : e - 2 + 2 = e := by omega
    simp only [morseShiftWord, shiftLetter, List.map_cons, List.map_nil] at h1 h3
    simp only [isoN, isoX, he2, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-! ### The three parts of a fence block -/

/-- The cups of a fence block: the discs opened by the block `k`. -/
def isoFenceCups (n : ℕ) (B : List SBlock) (j k : ℕ) : MorseWord :=
  ((List.range (n + 1)).filter fun m ↦ decide (j < m ∧ isoFirst B m = k)).map fun m ↦
    isoU (isoPos B j k m)

/-- The caps of a fence block: the discs closed by the block `k`. -/
def isoFenceCaps (n : ℕ) (B : List SBlock) (j k : ℕ) : MorseWord :=
  (((List.range (n + 1)).filter fun m ↦ decide (j < m ∧ isoLast B m = k)).reverse.map fun m ↦
    isoN (isoPos B j k m))

/-- A fence block is its cups, its band and its caps. -/
theorem isoFenceBlock_eq (n : ℕ) (B : List SBlock) (j k : ℕ) (b : SBlock) :
    isoFenceBlock n B j k b =
      isoFenceCups n B j k ++ isoBlockWord (isoPos B j k) b ++ isoFenceCaps n B j k := rfl

/-- The cups of a fence block are cups right of the kept discs. -/
theorem mem_isoFenceCups {n : ℕ} {B : List SBlock} {j k : ℕ} {l : MorseLetter}
    (hl : l ∈ isoFenceCups n B j k) : l.1 = MorseKind.cup ∧ 2 * j + 1 ≤ l.2 := by
  simp only [isoFenceCups, List.mem_map, List.mem_filter, decide_eq_true_eq] at hl
  obtain ⟨m, ⟨-, hm, -⟩, rfl⟩ := hl
  exact ⟨rfl, le_isoPos_of_lt B hm⟩

/-- The caps of a fence block are caps right of the kept discs. -/
theorem mem_isoFenceCaps {n : ℕ} {B : List SBlock} {j k : ℕ} {l : MorseLetter}
    (hl : l ∈ isoFenceCaps n B j k) : l.1 = MorseKind.cap ∧ 2 * j + 1 ≤ l.2 := by
  simp only [isoFenceCaps, List.mem_map, List.mem_reverse, List.mem_filter,
    decide_eq_true_eq] at hl
  obtain ⟨m, ⟨-, hm, -⟩, rfl⟩ := hl
  exact ⟨rfl, le_isoPos_of_lt B hm⟩

/-- Where the disc `j + 1` is closed and not opened, keeping it open shifts the cups. -/
theorem isoFenceCups_succ (n : ℕ) (B : List SBlock) (j k : ℕ)
    (hno : ¬(isoFirst B (j + 1) ≤ k ∧ k ≤ isoLast B (j + 1))) (hf : isoFirst B (j + 1) ≠ k) :
    isoFenceCups n B (j + 1) k = morseShiftWord 2 (isoFenceCups n B j k) := by
  simp only [isoFenceCups, filter_isoDisc_succ (n + 1) j k (isoFirst B) hf, morseShiftWord,
    List.map_map]
  refine List.map_congr_left fun m hm ↦ ?_
  simp only [List.mem_filter, decide_eq_true_eq] at hm
  have hm' : j + 1 < m := by
    rcases Nat.lt_or_ge (j + 1) m with h | h
    · exact h
    · obtain rfl : m = j + 1 := by omega
      exact absurd hm.2.2 hf
  simp only [Function.comp_apply, isoPos_succ_of_not_open B j k m hno, hm', ↓reduceIte, isoU,
    shiftLetter]

/-- Where the disc `j + 1` is closed and not closed here, keeping it open shifts the caps. -/
theorem isoFenceCaps_succ (n : ℕ) (B : List SBlock) (j k : ℕ)
    (hno : ¬(isoFirst B (j + 1) ≤ k ∧ k ≤ isoLast B (j + 1))) (hl : isoLast B (j + 1) ≠ k) :
    isoFenceCaps n B (j + 1) k = morseShiftWord 2 (isoFenceCaps n B j k) := by
  simp only [isoFenceCaps, filter_isoDisc_succ (n + 1) j k (isoLast B) hl, morseShiftWord,
    List.map_map]
  refine List.map_congr_left fun m hm ↦ ?_
  simp only [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hm
  have hm' : j + 1 < m := by
    rcases Nat.lt_or_ge (j + 1) m with h | h
    · exact h
    · obtain rfl : m = j + 1 := by omega
      exact absurd hm.2.2 hl
  simp only [Function.comp_apply, isoPos_succ_of_not_open B j k m hno, hm', ↓reduceIte, isoN,
    shiftLetter]

/-- A band shifted by `t` strands. -/
theorem isoBand_add (c d t : ℕ) (s : Bool) :
    isoBand (c + t) (d + t) s = morseShiftWord t (isoBand c d s) := by
  simp only [isoBand, bandWord, morseOfBraid, morseShiftWord, List.map_append, List.map_map,
    show d + t - 1 - (c + t) = d - 1 - c by omega]
  congr 1
  · congr 1
    refine List.map_congr_left fun x hx ↦ ?_
    simp only [List.mem_range] at hx
    simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
    omega
  · refine List.map_congr_left fun x _ ↦ ?_
    simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
    omega

end AJConjecture
