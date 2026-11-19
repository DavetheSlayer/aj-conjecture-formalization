import Mathlib
import AJTwist.Knot.TwKKnot
import AJHandoff.TorusKnot.PairKIsotopy

/-!
# Phase I for the twisted words: the fence word is a new prefix on the old fence word

The generic phase I of the library (`morseReach_isoPhaseOne`: thinning and dead-end retraction of
any `IsoFenceable` block list) applies to `twBlocks r s ℓ σ`. Because the new discs of the chain
lie on top levels and the chain replaces the head block, nothing else is open while the chain
runs, and the positions of the old discs are never changed by the new ones. So the fence word is

`twPrefix ℓ ++ twStripTail r s σ`,

where `twStripTail r s σ` is the fence word of the untwisted list without its first two letters
`u1 +0` (for `σ = true`, `r ≥ 3`: `(pairStrip r s).drop 2`), and `twPrefix ℓ` is `u1 +0` followed
by the fence blocks of the chain: every block between new discs is one of four words on three
strands (the return strand and a thin pair), `twIncP`, `twDecP` (the library's `isoStInc 0`,
`isoStDec 1`) and their versions with a negative band `twIncN`, `twDecN`.

Checked outside Lean (`SCR/K/tools/twk3.py`, column `tail==old` and the printed prefixes) for
`(2,3), (2,5), (3,4), (3,5), (4,5)`, `|ℓ| ≤ 3`, both clasp signs.
-/

namespace AJConjecture

/-- Ascending positive chain block: the new pair opens on the right, the old pair closes. -/
def twIncP : MorseWord := [isoU 3] ++ isoBand 1 3 true ++ [isoN 1]

/-- Descending positive chain block: the new pair opens on the left, the old pair closes. -/
def twDecP : MorseWord := [isoU 1] ++ isoBand 1 3 true ++ [isoN 3]

/-- Ascending negative chain block. -/
def twIncN : MorseWord := [isoU 3] ++ isoBand 1 3 false ++ [isoN 1]

/-- Descending negative chain block. -/
def twDecN : MorseWord := [isoU 1] ++ isoBand 1 3 false ++ [isoN 3]

/-- The fence word of the chain `twChain M j₀ ℓ` (a word from one strand to three strands). -/
def twPrefix (ℓ : ℤ) : MorseWord :=
  [isoU 1, isoX true 0] ++
    (if ℓ = 0 then []
    else if ℓ < 0 then
      phaseTwoBlk twDecP (ℓ.natAbs - 1) ++ phaseTwoBlk twIncP ℓ.natAbs ++ twDecP
    else phaseTwoBlk twIncN (ℓ.natAbs + 2) ++ twDecP ++ phaseTwoBlk twDecN ℓ.natAbs ++ twDecP)

/-- The fence word of the untwisted block list with clasp sign `σ`, without its first two
letters `u1 +0`: a word from three strands (the return strand and the first thin pair) to one. -/
def twStripTail (r s : ℕ) (σ : Bool) : MorseWord :=
  (isoFenceWord (pairStrands r s - 1) (twBlocks r s 0 σ)).drop 2

/-! ### Fence blocks of a schedule -/

/-- The position of the left edge of the disc `m` at the block `k`, when the disc `x` is first
used at the block `F x` and last used at the block `L x`. -/
private def twSchedPos (F L : ℕ → ℕ) (k m : ℕ) : ℕ :=
  if m = 0 then 0
  else 1 + 2 * ((List.range m).filter fun x ↦
    decide (1 ≤ x ∧ (x ≤ 0 ∨ (F x ≤ k ∧ k ≤ L x)))).length

/-- The fence block of the block `k` for the schedule `F`, `L`. -/
private def twSchedBlock (n : ℕ) (F L : ℕ → ℕ) (k : ℕ) (b : SBlock) : MorseWord :=
  (((List.range (n + 1)).filter fun m ↦ decide (0 < m ∧ F m = k)).map fun m ↦
      isoU (twSchedPos F L k m)) ++
    isoBlockWord (twSchedPos F L k) b ++
    (((List.range (n + 1)).filter fun m ↦ decide (0 < m ∧ L m = k)).reverse.map fun m ↦
      isoN (twSchedPos F L k m))

/-- A fence block depends on the block list only through the first and last blocks of the
discs. -/
private theorem isoFenceBlock_eq_twSchedBlock (n : ℕ) (B : List SBlock) (k : ℕ) (b : SBlock) :
    isoFenceBlock n B 0 k b = twSchedBlock n (isoFirst B) (isoLast B) k b := rfl

/-- Positions depend only on which discs are open. -/
private theorem twSchedPos_congr {n : ℕ} {F L F' L' : ℕ → ℕ} {k k' : ℕ}
    (h : ∀ m, 1 ≤ m → m ≤ n → ((F m ≤ k ∧ k ≤ L m) ↔ (F' m ≤ k' ∧ k' ≤ L' m))) {m : ℕ}
    (hm : m ≤ n + 1) : twSchedPos F L k m = twSchedPos F' L' k' m := by
  have hf : (List.range m).filter (fun x ↦ decide (1 ≤ x ∧ (x ≤ 0 ∨ (F x ≤ k ∧ k ≤ L x)))) =
      (List.range m).filter (fun x ↦ decide (1 ≤ x ∧ (x ≤ 0 ∨ (F' x ≤ k' ∧ k' ≤ L' x)))) := by
    refine List.filter_congr fun x hx ↦ ?_
    rw [List.mem_range] at hx
    by_cases hx1 : 1 ≤ x
    · simp only [h x hx1 (by omega)]
    · simp only [hx1, false_and]
  rw [twSchedPos, twSchedPos, hf]

/-- Two schedules with the same open, opening and closing discs have the same fence block. -/
private theorem twSchedBlock_congr {n : ℕ} {F L F' L' : ℕ → ℕ} {k k' : ℕ} (b : SBlock)
    (ho : ∀ m, 1 ≤ m → m ≤ n → ((F m ≤ k ∧ k ≤ L m) ↔ (F' m ≤ k' ∧ k' ≤ L' m)))
    (hf : ∀ m, 1 ≤ m → m ≤ n → (F m = k ↔ F' m = k'))
    (hl : ∀ m, 1 ≤ m → m ≤ n → (L m = k ↔ L' m = k'))
    (hb : (isoEnds b).1 ≤ n ∧ (isoEnds b).2 ≤ n) :
    twSchedBlock n F L k b = twSchedBlock n F' L' k' b := by
  have hp : ∀ m, m ≤ n + 1 → twSchedPos F L k m = twSchedPos F' L' k' m :=
    fun m hm ↦ twSchedPos_congr ho hm
  have hcup : (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ F m = k)) =
      (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ F' m = k')) := by
    refine List.filter_congr fun m hm ↦ ?_
    rw [List.mem_range] at hm
    by_cases hm0 : 0 < m
    · simp only [hf m hm0 (by omega)]
    · simp only [hm0, false_and]
  have hcap : (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ L m = k)) =
      (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ L' m = k')) := by
    refine List.filter_congr fun m hm ↦ ?_
    rw [List.mem_range] at hm
    by_cases hm0 : 0 < m
    · simp only [hl m hm0 (by omega)]
    · simp only [hm0, false_and]
  have e1 : ((List.range (n + 1)).filter fun m ↦ decide (0 < m ∧ F' m = k')).map
      (fun m ↦ isoU (twSchedPos F L k m)) =
      ((List.range (n + 1)).filter fun m ↦ decide (0 < m ∧ F' m = k')).map
      (fun m ↦ isoU (twSchedPos F' L' k' m)) :=
    List.map_congr_left fun m hm ↦ by
      rw [hp m (by have := List.mem_range.1 (List.mem_filter.1 hm).1; omega)]
  have e2 : ((List.range (n + 1)).filter fun m ↦ decide (0 < m ∧ L' m = k')).reverse.map
      (fun m ↦ isoN (twSchedPos F L k m)) =
      ((List.range (n + 1)).filter fun m ↦ decide (0 < m ∧ L' m = k')).reverse.map
      (fun m ↦ isoN (twSchedPos F' L' k' m)) :=
    List.map_congr_left fun m hm ↦ by
      rw [hp m (by
        have := List.mem_range.1 (List.mem_filter.1 (List.mem_reverse.1 hm)).1; omega)]
  rw [twSchedBlock, twSchedBlock, hcup, hcap, e1, e2, isoBlockWord, isoBlockWord,
    hp _ (by omega), hp _ (by omega)]

/-- Discs that neither open nor close at the block can be left out of the range. -/
private theorem twSchedBlock_shrink {n M : ℕ} {F L : ℕ → ℕ} {k : ℕ} (b : SBlock) (hM1 : 1 ≤ M)
    (hM : M ≤ n + 1) (h : ∀ m, M ≤ m → m ≤ n → F m ≠ k ∧ L m ≠ k) :
    twSchedBlock n F L k b = twSchedBlock (M - 1) F L k b := by
  have key : ∀ q : ℕ → Bool, (∀ m, M ≤ m → m ≤ n → q m = false) →
      (List.range (n + 1)).filter q = (List.range (M - 1 + 1)).filter q := by
    intro q hq
    have h0 : (List.map (fun x ↦ M - 1 + 1 + x) (List.range (n + 1 - M))).filter q = [] := by
      refine List.filter_eq_nil_iff.2 fun x hx ↦ ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [hq _ (by omega) (by have := List.mem_range.1 hy; omega)]
      exact Bool.false_ne_true
    rw [show n + 1 = (M - 1 + 1) + (n + 1 - M) by omega, List.range_add, List.filter_append, h0,
      List.append_nil]
  rw [twSchedBlock, twSchedBlock,
    key _ fun m h1 h2 ↦ decide_eq_false fun hc ↦ (h m h1 h2).1 hc.2,
    key _ fun m h1 h2 ↦ decide_eq_false fun hc ↦ (h m h1 h2).2 hc.2]

/-! ### First and last blocks in a concatenation -/

/-- The first block of a disc in a concatenation. -/
private theorem isoFirst_append_twKFence (C T : List SBlock) (m : ℕ) :
    isoFirst (C ++ T) m =
      if isoFirst C m < C.length then isoFirst C m else isoFirst T m + C.length :=
  List.findIdx_append

/-- The last block of a disc attached to the second list. -/
private theorem isoLast_append_of_attached_twKFence {C T : List SBlock} {m : ℕ}
    (h : isoFirst T m < T.length) :
    isoLast (C ++ T) m = C.length + isoLast T m ∧ isoLast T m < T.length := by
  have hr : T.reverse.findIdx (isoAttached m) < T.reverse.length := by
    obtain ⟨b, hb, hab⟩ := List.findIdx_lt_length.1 h
    exact List.findIdx_lt_length.2 ⟨b, List.mem_reverse.2 hb, hab⟩
  unfold isoLast
  rw [List.reverse_append, List.findIdx_append, ite_eq_left hr, List.length_append]
  rw [List.length_reverse] at hr
  omega

/-- The last block of a disc not attached to the second list. -/
private theorem isoLast_append_of_not_attached_twKFence {C T : List SBlock} {m : ℕ}
    (h : isoFirst T m = T.length) : isoLast (C ++ T) m = isoLast C m := by
  have hr : T.reverse.findIdx (isoAttached m) = T.reverse.length :=
    List.findIdx_eq_length.2 fun x hx ↦ List.findIdx_eq_length.1 h x (List.mem_reverse.1 hx)
  unfold isoLast
  rw [List.reverse_append, List.findIdx_append, hr, ite_eq_right (lt_irrefl _),
    List.length_append, List.length_reverse]
  omega

/-- A disc above the strands of a block list is attached to none of its blocks. -/
private theorem isoFirst_eq_length_of_valid_twKFence {M m : ℕ} {T : List SBlock}
    (hT : ∀ b ∈ T, b.Valid M) (hm : M ≤ m) : isoFirst T m = T.length := by
  refine List.findIdx_eq_length.2 fun b hb ↦ ?_
  have hv := hT b hb
  cases b <;> simp only [SBlock.Valid] at hv <;>
    exact decide_eq_false (by simp only [isoEnds]; omega)

/-- The ends of a valid block. -/
private theorem isoEnds_le_of_valid_twKFence {M : ℕ} {b : SBlock} (hb : b.Valid M) :
    (isoEnds b).1 ≤ M - 1 ∧ (isoEnds b).2 ≤ M - 1 := by
  cases b <;> simp only [SBlock.Valid] at hb <;> simp only [isoEnds] <;> omega

/-! ### The tail of the fence word does not see the head -/

/-- The hypotheses on the tail `T` of the block list: blocks on the old discs `0, …, M - 1`,
every old disc is attached to the tail, and every old disc except `j₀` carries two blocks of the
tail. -/
private def TwTailOK (M j₀ : ℕ) (T : List SBlock) : Prop :=
  1 ≤ j₀ ∧ j₀ < M ∧ (∀ b ∈ T, b.Valid M) ∧ (∀ m, 1 ≤ m → m < M → isoFirst T m < T.length) ∧
    ∀ m, 1 ≤ m → m < M → m ≠ j₀ → isoFirst T m < isoLast T m

/-- The fence block of the block `i` of the tail, when the head is attached to the old disc `j₀`
only: it does not depend on the head. -/
private theorem isoFenceBlock_tail_twKFence {M j₀ n : ℕ} {C T : List SBlock}
    (hT : TwTailOK M j₀ T) (hC : C ≠ []) (hM : M ≤ n + 1)
    (hCj : ∀ m, 1 ≤ m → m < M → (isoFirst C m < C.length ↔ m = j₀)) {i : ℕ}
    (hi : i < T.length) {b : SBlock} (hb : b.Valid M) :
    isoFenceBlock n (C ++ T) 0 (C.length + i) b =
      twSchedBlock (M - 1) (fun m ↦ if m = j₀ then 0 else isoFirst T m + 1)
        (fun m ↦ isoLast T m + 1) (i + 1) b := by
  obtain ⟨hj1, hjM, hTv, hTa, -⟩ := hT
  have hCl : 1 ≤ C.length := List.length_pos_iff.2 hC
  rw [isoFenceBlock_eq_twSchedBlock, twSchedBlock_shrink b (by omega) hM]
  · refine twSchedBlock_congr b (fun m h1 h2 ↦ ?_) (fun m h1 h2 ↦ ?_) (fun m h1 h2 ↦ ?_)
      (isoEnds_le_of_valid_twKFence hb)
    iterate 2
      obtain ⟨e, he⟩ := isoLast_append_of_attached_twKFence (C := C) (hTa m h1 (by omega))
      have hc := hCj m h1 (by omega)
      rw [isoFirst_append_twKFence]
      by_cases hmj : m = j₀
      · rw [ite_eq_left (hc.2 hmj), ite_eq_left hmj]
        have := hc.2 hmj
        omega
      · rw [ite_eq_right (fun hlt ↦ hmj (hc.1 hlt)), ite_eq_right hmj]
        omega
    · obtain ⟨e, he⟩ := isoLast_append_of_attached_twKFence (C := C) (hTa m h1 (by omega))
      omega
  · intro m h1 h2
    have hnot := isoFirst_eq_length_of_valid_twKFence hTv h1
    rw [isoFirst_append_twKFence, isoLast_append_of_not_attached_twKFence hnot, hnot]
    refine ⟨?_, ?_⟩
    · split_ifs <;> omega
    · unfold isoLast
      omega

/-- The fence word of a concatenation, block by block. -/
private theorem isoFenceWord_append_twKFence (n : ℕ) (C T : List SBlock) :
    isoFenceWord n (C ++ T) =
      (C.zipIdx.flatMap fun bk ↦ isoFenceBlock n (C ++ T) 0 bk.2 bk.1) ++
        (T.zipIdx.flatMap fun bk ↦ isoFenceBlock n (C ++ T) 0 (C.length + bk.2) bk.1) := by
  rw [isoFenceWord, isoFenceAux, Nat.zero_min, List.range_zero, List.map_nil, List.reverse_nil,
    List.map_nil, List.nil_append, List.append_nil, List.zipIdx_append, List.flatMap_append,
    Nat.zero_add, List.zipIdx_eq_map_add (i := C.length), List.flatMap_map]

/-- The part of the fence word that comes from the tail. -/
private def twTailWord (M j₀ : ℕ) (T : List SBlock) : MorseWord :=
  T.zipIdx.flatMap fun bk ↦
    twSchedBlock (M - 1) (fun m ↦ if m = j₀ then 0 else isoFirst T m + 1)
      (fun m ↦ isoLast T m + 1) (bk.2 + 1) bk.1

/-- The fence word of a head attached to the old disc `j₀` only, followed by the tail. -/
private theorem isoFenceWord_head_tail_twKFence {M j₀ n : ℕ} {C T : List SBlock}
    (hT : TwTailOK M j₀ T) (hC : C ≠ []) (hM : M ≤ n + 1)
    (hCj : ∀ m, 1 ≤ m → m < M → (isoFirst C m < C.length ↔ m = j₀)) :
    isoFenceWord n (C ++ T) =
      (C.zipIdx.flatMap fun bk ↦ isoFenceBlock n (C ++ T) 0 bk.2 bk.1) ++ twTailWord M j₀ T := by
  rw [isoFenceWord_append_twKFence, twTailWord]
  congr 1
  refine List.flatMap_congr fun bk hbk ↦ ?_
  obtain ⟨b, i⟩ := bk
  obtain ⟨hi, hbi⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hbk)
  exact isoFenceBlock_tail_twKFence hT hC hM hCj hi
    (hT.2.2.1 b (hbi ▸ List.getElem_mem hi))

/-! ### Fence blocks with one or two open discs -/

/-- The filter of a range by a predicate that holds nowhere. -/
private theorem filter_range_eq_nil_twKFence (q : ℕ → Bool) (N : ℕ)
    (hq : ∀ x, x < N → q x = false) : (List.range N).filter q = [] :=
  List.filter_eq_nil_iff.2 fun x hx ↦ by
    rw [hq x (List.mem_range.1 hx)]
    exact Bool.false_ne_true

/-- The filter of a range by a predicate that singles out `c`. -/
private theorem filter_range_eq_singleton_twKFence (q : ℕ → Bool) (N c : ℕ) (hc : c < N)
    (hq : ∀ x, x < N → (q x = true ↔ x = c)) : (List.range N).filter q = [c] := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_or_ge c N with h | h
    · have hN : q N = false := by
        rw [← Bool.not_eq_true]
        intro hN
        have := (hq N (by omega)).1 hN
        omega
      rw [ih h fun x hx ↦ hq x (by omega)]
      simp [hN]
    · obtain rfl : c = N := by omega
      have h0 : (List.range c).filter q = [] :=
        filter_range_eq_nil_twKFence q c fun x hx ↦ by
          rw [← Bool.not_eq_true]
          intro hqx
          have := (hq x (by omega)).1 hqx
          omega
      have hcc : q c = true := (hq c (by omega)).2 rfl
      simp [h0, hcc]

/-- The position of a disc with no open disc below it. -/
private theorem twSchedPos_eq_one_twKFence {F L : ℕ → ℕ} {k m : ℕ} (hm : 1 ≤ m)
    (h : ∀ x, 1 ≤ x → x < m → ¬ (F x ≤ k ∧ k ≤ L x)) : twSchedPos F L k m = 1 := by
  rw [twSchedPos, ite_eq_right (by omega), filter_range_eq_nil_twKFence _ _ fun x hx ↦
    decide_eq_false ?_]
  · rfl
  · rintro ⟨h1, h2 | h2⟩
    · omega
    · exact h x h1 hx h2

/-- The position of a disc with exactly one open disc below it. -/
private theorem twSchedPos_eq_three_twKFence {F L : ℕ → ℕ} {k m c : ℕ} (hc : 1 ≤ c)
    (hcm : c < m) (h : ∀ x, 1 ≤ x → x < m → ((F x ≤ k ∧ k ≤ L x) ↔ x = c)) :
    twSchedPos F L k m = 3 := by
  rw [twSchedPos, ite_eq_right (by omega), filter_range_eq_singleton_twKFence _ m c hcm
    fun x hx ↦ ?_]
  · rfl
  · rw [decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · omega
      · exact (h x h1 hx).1 h2
    · rintro rfl
      exact ⟨hc, Or.inr ((h x hc hx).2 rfl)⟩

/-- The fence block of a block joining the base disc to the only open disc, which it opens. -/
private theorem twSchedBlock_first_twKFence {n : ℕ} {F L : ℕ → ℕ} {k a : ℕ} {b : SBlock}
    (ha1 : 1 ≤ a) (han : a ≤ n) (hb : isoEnds b = (0, a)) (hs : isoSign b = true)
    (ho : ∀ m, 1 ≤ m → m ≤ n → ((F m ≤ k ∧ k ≤ L m) ↔ m = a))
    (hf : ∀ m, 1 ≤ m → m ≤ n → (F m = k ↔ m = a))
    (hl : ∀ m, 1 ≤ m → m ≤ n → L m ≠ k) :
    twSchedBlock n F L k b = [isoU 1, isoX true 0] := by
  have hpa : twSchedPos F L k a = 1 := twSchedPos_eq_one_twKFence ha1 fun x h1 hx hc ↦ by
    have := (ho x h1 (by omega)).1 hc
    omega
  have hcup : (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ F m = k)) = [a] :=
    filter_range_eq_singleton_twKFence _ _ a (by omega) fun x hx ↦ by
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact (hf x h1 (by omega)).1 h2
      · rintro rfl
        exact ⟨ha1, (hf x ha1 han).2 rfl⟩
  have hcap : (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ L m = k)) = [] :=
    filter_range_eq_nil_twKFence _ _ fun x hx ↦
      decide_eq_false fun hc ↦ hl x hc.1 (by omega) hc.2
  rw [twSchedBlock, hcup, hcap, isoBlockWord, hb, hs]
  change [isoU (twSchedPos F L k a)] ++ isoBand (twSchedPos F L k 0) (twSchedPos F L k a) true ++
    [] = _
  rw [hpa]
  rfl

/-- The fence block of a block joining the only two open discs `lo < hi`, opening `c` and
closing `d`. -/
private theorem twSchedBlock_pair_twKFence {n : ℕ} {F L : ℕ → ℕ} {k lo hi c d : ℕ} {b : SBlock}
    (hlo : 1 ≤ lo) (hlt : lo < hi) (hhi : hi ≤ n) (hb : isoEnds b = (lo, hi))
    (ho : ∀ m, 1 ≤ m → m ≤ n → ((F m ≤ k ∧ k ≤ L m) ↔ (m = lo ∨ m = hi)))
    (hc : 1 ≤ c ∧ c ≤ n) (hf : ∀ m, 1 ≤ m → m ≤ n → (F m = k ↔ m = c))
    (hd : 1 ≤ d ∧ d ≤ n) (hl : ∀ m, 1 ≤ m → m ≤ n → (L m = k ↔ m = d)) :
    twSchedPos F L k lo = 1 ∧ twSchedPos F L k hi = 3 ∧
      twSchedBlock n F L k b =
        [isoU (twSchedPos F L k c)] ++ isoBand 1 3 (isoSign b) ++ [isoN (twSchedPos F L k d)] := by
  have hplo : twSchedPos F L k lo = 1 := twSchedPos_eq_one_twKFence hlo fun x h1 hx hc ↦ by
    have := (ho x h1 (by omega)).1 hc
    omega
  have hphi : twSchedPos F L k hi = 3 := twSchedPos_eq_three_twKFence hlo hlt fun x h1 hx ↦ by
    constructor
    · intro hc
      have := (ho x h1 (by omega)).1 hc
      omega
    · rintro rfl
      exact (ho x h1 (by omega)).2 (Or.inl rfl)
  have hcup : (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ F m = k)) = [c] :=
    filter_range_eq_singleton_twKFence _ _ c (by omega) fun x hx ↦ by
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact (hf x h1 (by omega)).1 h2
      · rintro rfl
        exact ⟨hc.1, (hf x hc.1 hc.2).2 rfl⟩
  have hcap : (List.range (n + 1)).filter (fun m ↦ decide (0 < m ∧ L m = k)) = [d] :=
    filter_range_eq_singleton_twKFence _ _ d (by omega) fun x hx ↦ by
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact (hl x h1 (by omega)).1 h2
      · rintro rfl
        exact ⟨hd.1, (hl x hd.1 hd.2).2 rfl⟩
  refine ⟨hplo, hphi, ?_⟩
  rw [twSchedBlock, hcup, hcap, isoBlockWord, hb]
  change [isoU (twSchedPos F L k c)] ++
    isoBand (twSchedPos F L k lo) (twSchedPos F L k hi) (isoSign b) ++
      [isoN (twSchedPos F L k d)] = _
  rw [hplo, hphi]

/-! ### Chains: a path of discs from the base disc to `j₀` through the new discs -/

/-- The hypotheses on a chain of `L` blocks `blk 0, …, blk (L - 1)`: the block `k` joins the disc
`a (k - 1)` (the base disc `0` for `k = 0`) to the disc `a k`; the discs `a k` are distinct and
new (`M ≤ a k ≤ n`), except the last one, which is `j₀`; every new disc occurs. -/
private def TwPathOK (M j₀ n L : ℕ) (blk : ℕ → SBlock) (a : ℕ → ℕ) : Prop :=
  1 ≤ L ∧ M ≤ n + 1 ∧
    (∀ k, k < L → isoEnds (blk k) =
      (min (if k = 0 then 0 else a (k - 1)) (a k), max (if k = 0 then 0 else a (k - 1)) (a k))) ∧
    (∀ i j, i < L → j < L → a i = a j → i = j) ∧
    (∀ k, k + 1 < L → M ≤ a k ∧ a k ≤ n) ∧ a (L - 1) = j₀ ∧
    (∀ m, M ≤ m → m ≤ n → ∃ k, k + 1 < L ∧ a k = m) ∧ isoSign (blk 0) = true

section Path

variable {M j₀ n L : ℕ} {blk : ℕ → SBlock} {a : ℕ → ℕ} {T : List SBlock}

/-- The discs of a chain are discs `1, …, n`. -/
private theorem twPath_range_twKFence (hP : TwPathOK M j₀ n L blk a) (hj1 : 1 ≤ j₀)
    (hjM : j₀ < M) {i : ℕ} (hi : i < L) : 1 ≤ a i ∧ a i ≤ n := by
  obtain ⟨hL, hMn, -, -, hnew, hlast, -, -⟩ := hP
  by_cases hi' : i + 1 < L
  · have := hnew i hi'
    omega
  · rw [show i = L - 1 by omega, hlast]
    omega

/-- An old disc other than `j₀` is not a disc of the chain. -/
private theorem twPath_ne_twKFence (hP : TwPathOK M j₀ n L blk a) {m : ℕ} (hmM : m < M)
    (hmj : m ≠ j₀) {i : ℕ} (hi : i < L) : m ≠ a i := by
  obtain ⟨hL, hMn, -, -, hnew, hlast, -, -⟩ := hP
  intro hmi
  by_cases hi' : i + 1 < L
  · have := (hnew i hi').1
    omega
  · rw [show i = L - 1 by omega, hlast] at hmi
    exact hmj hmi

/-- The blocks of a chain attached to a disc `m ≥ 1`. -/
private theorem isoAttached_path_twKFence (hP : TwPathOK M j₀ n L blk a) {k m : ℕ} (hk : k < L)
    (hm : 1 ≤ m) : isoAttached m (blk k) = true ↔ (m = a k ∨ (1 ≤ k ∧ m = a (k - 1))) := by
  obtain ⟨-, -, hends, -⟩ := hP
  rw [isoAttached, decide_eq_true_eq, hends k hk]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte, Nat.zero_min, Nat.zero_max]
    omega
  · simp only [hk0, ↓reduceIte]
    omega

/-- The first block of the chain attached to its `i`th disc. -/
private theorem isoFirst_path_twKFence (hP : TwPathOK M j₀ n L blk a) {i : ℕ} (hi : i < L)
    (hai : 1 ≤ a i) : isoFirst ((List.range L).map blk) (a i) = i := by
  have hlen : i < ((List.range L).map blk).length := by
    rw [List.length_map, List.length_range]
    exact hi
  refine (List.findIdx_eq hlen).2 ⟨?_, fun j hji ↦ ?_⟩
  · rw [List.getElem_map, List.getElem_range]
    exact (isoAttached_path_twKFence hP hi hai).2 (Or.inl rfl)
  · rw [List.getElem_map, List.getElem_range, ← Bool.not_eq_true,
      isoAttached_path_twKFence hP (by omega) hai]
    rintro (h | ⟨h1, h⟩)
    · have := hP.2.2.2.1 i j hi (by omega) h
      omega
    · have := hP.2.2.2.1 i (j - 1) hi (by omega) h
      omega

/-- A disc `m ≥ 1` that is not a disc of the chain is attached to none of its blocks. -/
private theorem isoFirst_path_eq_length_twKFence (hP : TwPathOK M j₀ n L blk a) {m : ℕ}
    (hm : 1 ≤ m) (hno : ∀ i, i < L → m ≠ a i) :
    isoFirst ((List.range L).map blk) m = ((List.range L).map blk).length := by
  refine List.findIdx_eq_length.2 fun b hb ↦ ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb
  rw [List.mem_range] at hk
  rw [← Bool.not_eq_true, isoAttached_path_twKFence hP hk hm]
  rintro (h | ⟨h1, h⟩)
  · exact hno k hk h
  · exact hno (k - 1) (by omega) h

/-- The last block attached to a disc, from its index. -/
private theorem isoLast_eq_twKFence {B : List SBlock} {m j : ℕ} (hj : j < B.length)
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

/-- The last block of the chain attached to its `i`th disc, when it is not the last disc. -/
private theorem isoLast_path_twKFence (hP : TwPathOK M j₀ n L blk a) {i : ℕ} (hi : i + 1 < L)
    (hai : 1 ≤ a i) : isoLast ((List.range L).map blk) (a i) = i + 1 := by
  have hlen : i + 1 < ((List.range L).map blk).length := by
    rw [List.length_map, List.length_range]
    exact hi
  refine isoLast_eq_twKFence hlen ?_ fun j' h' hj' ↦ ?_
  · rw [List.getElem_map, List.getElem_range]
    exact (isoAttached_path_twKFence hP hi hai).2 (Or.inr ⟨by omega, rfl⟩)
  · rw [List.length_map, List.length_range] at h'
    rw [List.getElem_map, List.getElem_range, ← Bool.not_eq_true,
      isoAttached_path_twKFence hP h' hai]
    rintro (h | ⟨h1, h⟩)
    · have := hP.2.2.2.1 i j' (by omega) h' h
      omega
    · have := hP.2.2.2.1 i (j' - 1) (by omega) (by omega) h
      omega

/-- The first and last blocks of every disc `1, …, n` in the chain followed by the tail: a new
disc `a i` lives on the blocks `i`, `i + 1`; the disc `j₀` opens at the last block of the chain
and closes in the tail; the other old discs live in the tail. -/
private theorem twPath_sched_twKFence (hP : TwPathOK M j₀ n L blk a) (hT : TwTailOK M j₀ T)
    {m : ℕ} (h1 : 1 ≤ m) (hn : m ≤ n) :
    (∃ i, i + 1 < L ∧ m = a i ∧ isoFirst ((List.range L).map blk ++ T) m = i ∧
        isoLast ((List.range L).map blk ++ T) m = i + 1) ∨
      (m = a (L - 1) ∧ isoFirst ((List.range L).map blk ++ T) m = L - 1 ∧
        L ≤ isoLast ((List.range L).map blk ++ T) m ∧
          isoLast ((List.range L).map blk ++ T) m < L + T.length) ∨
      ((∀ i, i < L → m ≠ a i) ∧ L ≤ isoFirst ((List.range L).map blk ++ T) m ∧
        isoFirst ((List.range L).map blk ++ T) m < isoLast ((List.range L).map blk ++ T) m ∧
          isoLast ((List.range L).map blk ++ T) m < L + T.length) := by
  have hlen : ((List.range L).map blk).length = L := by rw [List.length_map, List.length_range]
  obtain ⟨hj1, hjM, hTv, hTa, hTt⟩ := hT
  have hL := hP.1
  have hlast := hP.2.2.2.2.2.1
  rcases Nat.lt_or_ge m M with hmM | hmM
  · obtain ⟨e, he⟩ := isoLast_append_of_attached_twKFence (C := (List.range L).map blk)
      (hTa m h1 hmM)
    rw [hlen] at e
    by_cases hmj : m = j₀
    · right; left
      have hF := isoFirst_path_twKFence hP (i := L - 1) (by omega) (by rw [hlast]; exact hj1)
      rw [hlast, ← hmj] at hF
      refine ⟨by rw [hlast, hmj], ?_, by omega, by omega⟩
      rw [isoFirst_append_twKFence, hF, hlen, ite_eq_left (by omega)]
    · right; right
      have hno : ∀ i, i < L → m ≠ a i := fun i hi ↦ twPath_ne_twKFence hP hmM hmj hi
      have hF := isoFirst_path_eq_length_twKFence hP h1 hno
      have ht := hTt m h1 hmM hmj
      have hFB : isoFirst ((List.range L).map blk ++ T) m = isoFirst T m + L := by
        rw [isoFirst_append_twKFence, hF, ite_eq_right (lt_irrefl _), hlen]
      exact ⟨hno, by omega, by omega, by omega⟩
  · left
    obtain ⟨i, hi, rfl⟩ := hP.2.2.2.2.2.2.1 m hmM hn
    have hF := isoFirst_path_twKFence hP (i := i) (by omega) h1
    have hLc := isoLast_path_twKFence hP hi h1
    have hnot := isoFirst_eq_length_of_valid_twKFence hTv hmM
    refine ⟨i, hi, rfl, ?_, ?_⟩
    · rw [isoFirst_append_twKFence, hF, hlen, ite_eq_left (by omega)]
    · rw [isoLast_append_of_not_attached_twKFence hnot, hLc]

/-- The discs open at, opened by and closed by the block `k` of the chain. -/
private theorem twPath_block_facts_twKFence (hP : TwPathOK M j₀ n L blk a)
    (hT : TwTailOK M j₀ T) {k : ℕ} (hk : k < L) {m : ℕ} (h1 : 1 ≤ m) (hn : m ≤ n) :
    ((isoFirst ((List.range L).map blk ++ T) m ≤ k ∧
        k ≤ isoLast ((List.range L).map blk ++ T) m) ↔ (m = a k ∨ (1 ≤ k ∧ m = a (k - 1)))) ∧
      (isoFirst ((List.range L).map blk ++ T) m = k ↔ m = a k) ∧
      (isoLast ((List.range L).map blk ++ T) m = k ↔ (1 ≤ k ∧ m = a (k - 1))) := by
  have hinj := hP.2.2.2.1
  rcases twPath_sched_twKFence hP hT h1 hn with
    ⟨i, hi, hmi, hF, hL⟩ | ⟨hmi, hF, hL, -⟩ | ⟨hno, hF, hlt, hL⟩
  · have e1 : m = a k ↔ i = k :=
      ⟨fun h ↦ hinj i k (by omega) hk (hmi.symm.trans h), fun h ↦ by rw [← h]; exact hmi⟩
    have e2 : (1 ≤ k ∧ m = a (k - 1)) ↔ i + 1 = k :=
      ⟨fun h ↦ by
        have := hinj i (k - 1) (by omega) (by omega) (hmi.symm.trans h.2)
        omega,
      fun h ↦ ⟨by omega, by rw [hmi, ← h, Nat.add_sub_cancel]⟩⟩
    rw [e1, e2, hF, hL]
    omega
  · have e1 : m = a k ↔ k = L - 1 :=
      ⟨fun h ↦ by
        have := hinj (L - 1) k (by omega) hk (hmi.symm.trans h)
        omega,
      fun h ↦ by rw [h]; exact hmi⟩
    have e2 : (1 ≤ k ∧ m = a (k - 1)) ↔ False :=
      ⟨fun h ↦ by
        have := hinj (L - 1) (k - 1) (by omega) (by omega) (hmi.symm.trans h.2)
        omega,
      False.elim⟩
    rw [e1, e2, hF, or_false, iff_false]
    omega
  · have e1 : m = a k ↔ False := ⟨fun h ↦ hno k hk h, False.elim⟩
    have e2 : (1 ≤ k ∧ m = a (k - 1)) ↔ False := ⟨fun h ↦ hno (k - 1) (by omega) h.2, False.elim⟩
    rw [e1, e2, or_false, iff_false, iff_false, iff_false]
    omega

/-- The fence block of the block `k` of a chain: `u1 +0` for the first block; afterwards the new
disc opens on the left (`a k < a (k - 1)`) or on the right of the disc that closes. -/
private def twPathBlockWord (blk : ℕ → SBlock) (a : ℕ → ℕ) (k : ℕ) : MorseWord :=
  if k = 0 then [isoU 1, isoX true 0]
  else if a k < a (k - 1) then [isoU 1] ++ isoBand 1 3 (isoSign (blk k)) ++ [isoN 3]
  else [isoU 3] ++ isoBand 1 3 (isoSign (blk k)) ++ [isoN 1]

/-- The fence blocks of a chain. -/
private theorem isoFenceBlock_path_twKFence (hP : TwPathOK M j₀ n L blk a)
    (hT : TwTailOK M j₀ T) {k : ℕ} (hk : k < L) :
    isoFenceBlock n ((List.range L).map blk ++ T) 0 k (blk k) = twPathBlockWord blk a k := by
  have hfacts := fun m (h1 : 1 ≤ m) (hn : m ≤ n) ↦ twPath_block_facts_twKFence hP hT hk h1 hn
  have hrange : ∀ i, i < L → 1 ≤ a i ∧ a i ≤ n :=
    fun i hi ↦ twPath_range_twKFence hP hT.1 hT.2.1 hi
  obtain ⟨hL, hMn, hends, hinj, hnew, hlast, hcov, hs⟩ := hP
  rw [isoFenceBlock_eq_twSchedBlock, twPathBlockWord]
  by_cases hk0 : k = 0
  · subst hk0
    rw [ite_eq_left rfl]
    refine twSchedBlock_first_twKFence (hrange 0 hk).1 (hrange 0 hk).2 ?_ hs
      (fun m h1 hn ↦ ?_) (fun m h1 hn ↦ (hfacts m h1 hn).2.1) (fun m h1 hn hc ↦ ?_)
    · rw [hends 0 hk]
      simp only [↓reduceIte, Nat.zero_min, Nat.zero_max]
    · rw [(hfacts m h1 hn).1]
      omega
    · have := (hfacts m h1 hn).2.2.1 hc
      omega
  · have hk1 : 1 ≤ k := by omega
    rw [ite_eq_right hk0]
    have hp := hrange (k - 1) (by omega)
    have hq := hrange k hk
    have hne : a k ≠ a (k - 1) := fun h ↦ by
      have := hinj k (k - 1) hk (by omega) h
      omega
    have hE := hends k hk
    simp only [hk0, ↓reduceIte] at hE
    have hf : ∀ m, 1 ≤ m → m ≤ n →
        (isoFirst ((List.range L).map blk ++ T) m = k ↔ m = a k) :=
      fun m h1 hn ↦ (hfacts m h1 hn).2.1
    have hl : ∀ m, 1 ≤ m → m ≤ n →
        (isoLast ((List.range L).map blk ++ T) m = k ↔ m = a (k - 1)) :=
      fun m h1 hn ↦ by rw [(hfacts m h1 hn).2.2, and_iff_right hk1]
    by_cases hlt : a k < a (k - 1)
    · rw [ite_eq_left hlt]
      obtain ⟨p1, p3, hw⟩ := twSchedBlock_pair_twKFence (lo := a k) (hi := a (k - 1))
        (c := a k) (d := a (k - 1)) (b := blk k) hq.1 hlt hp.2
        (by rw [hE, min_eq_right hlt.le, max_eq_left hlt.le])
        (fun m h1 hn ↦ by rw [(hfacts m h1 hn).1, and_iff_right hk1]) hq hf hp hl
      rw [hw, p1, p3]
    · have hlt' : a (k - 1) < a k := by omega
      rw [ite_eq_right hlt]
      obtain ⟨p1, p3, hw⟩ := twSchedBlock_pair_twKFence (lo := a (k - 1)) (hi := a k)
        (c := a k) (d := a (k - 1)) (b := blk k) hp.1 hlt' hq.2
        (by rw [hE, min_eq_left hlt'.le, max_eq_right hlt'.le])
        (fun m h1 hn ↦ by rw [(hfacts m h1 hn).1, and_iff_right hk1, or_comm]) hq hf hp hl
      rw [hw, p3, p1]

/-- Blocks listed by a function of the index, with their indices. -/
private theorem flatMap_zipIdx_map_range_twKFence {α β : Type} (f : ℕ → α)
    (g : α × ℕ → List β) (N : ℕ) :
    (((List.range N).map f).zipIdx).flatMap g = (List.range N).flatMap fun k ↦ g (f k, k) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.zipIdx_append, List.flatMap_append,
      List.flatMap_append, ih]
    simp

/-- The fence word of a chain followed by the tail: the fence blocks of the chain, then the part
of the tail, which does not depend on the chain. -/
private theorem isoFenceWord_path_twKFence (hP : TwPathOK M j₀ n L blk a)
    (hT : TwTailOK M j₀ T) :
    isoFenceWord n ((List.range L).map blk ++ T) =
      (List.range L).flatMap (twPathBlockWord blk a) ++ twTailWord M j₀ T := by
  have hlen : ((List.range L).map blk).length = L := by rw [List.length_map, List.length_range]
  have hCj : ∀ m, 1 ≤ m → m < M →
      (isoFirst ((List.range L).map blk) m < ((List.range L).map blk).length ↔ m = j₀) := by
    intro m h1 hmM
    constructor
    · intro hlt
      by_contra hmj
      have := isoFirst_path_eq_length_twKFence hP h1 fun i hi ↦ twPath_ne_twKFence hP hmM hmj hi
      omega
    · rintro rfl
      have hlast := hP.2.2.2.2.2.1
      have hF := isoFirst_path_twKFence hP (i := L - 1) (by have := hP.1; omega)
        (by rw [hlast]; exact h1)
      rw [hlast] at hF
      rw [hF, hlen]
      have := hP.1
      omega
  rw [isoFenceWord_head_tail_twKFence hT
    (List.ne_nil_of_length_pos (by rw [hlen]; exact hP.1)) hP.2.1 hCj,
    flatMap_zipIdx_map_range_twKFence]
  congr 1
  exact List.flatMap_congr fun k hk ↦ isoFenceBlock_path_twKFence hP hT (List.mem_range.1 hk)

/-- Every disc of a chain followed by the tail carries two blocks. -/
private theorem isoFenceable_path_twKFence (hP : TwPathOK M j₀ n L blk a)
    (hT : TwTailOK M j₀ T) (hv : ∀ b ∈ (List.range L).map blk ++ T, b.Valid (n + 1)) :
    IsoFenceable n ((List.range L).map blk ++ T) := by
  refine ⟨hv, fun m h1 hn ↦ ?_⟩
  have hL := hP.1
  rw [List.length_append, List.length_map, List.length_range]
  rcases twPath_sched_twKFence hP hT h1 hn with
    ⟨i, hi, -, hF, hL'⟩ | ⟨-, hF, hL', hL''⟩ | ⟨-, hF, hlt, hL'⟩ <;> omega

end Path

/-! ### The three chains of `twChain` as paths -/

/-- A range of length `1 + p + 1 + q + 1`, split into its five pieces. -/
private theorem map_range_five_twKFence {α : Type} (f : ℕ → α) (p q : ℕ) :
    (List.range (1 + p + 1 + q + 1)).map f =
      [f 0] ++ (List.range p).map (fun i ↦ f (1 + i)) ++ [f (1 + p)] ++
        (List.range q).map (fun i ↦ f (1 + p + 1 + i)) ++ [f (1 + p + 1 + q)] := by
  simp only [List.range_add, List.map_append, List.map_map, List.range_one, List.map_cons,
    List.map_nil, Function.comp_def, Nat.add_zero]

/-- The same for a concatenation of words. -/
private theorem flatMap_range_five_twKFence {β : Type} (g : ℕ → List β) (p q : ℕ) :
    (List.range (1 + p + 1 + q + 1)).flatMap g =
      g 0 ++ (List.range p).flatMap (fun i ↦ g (1 + i)) ++ g (1 + p) ++
        (List.range q).flatMap (fun i ↦ g (1 + p + 1 + i)) ++ g (1 + p + 1 + q) := by
  simp only [List.flatMap_def, map_range_five_twKFence, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- A run of equal fence blocks. -/
private theorem flatMap_range_const_twKFence (g : ℕ → MorseWord) (X : MorseWord) (m : ℕ)
    (h : ∀ i, i < m → g i = X) : (List.range m).flatMap g = phaseTwoBlk X m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih fun i hi ↦ h i (by omega),
      List.flatMap_singleton, h m (by omega)]
    simp [phaseTwoBlk, List.replicate_succ', List.flatten_append]

/-- The discs of the chain for `ℓ = -N < 0`: down from `M + N - 1` to `M`, up from `M + N` to
`M + 2N - 1`, then `j₀`. -/
private def twNegDisc (M j₀ N k : ℕ) : ℕ :=
  if k < N then M + N - 1 - k else if k < 2 * N then M + k else j₀

/-- The blocks of the chain for `ℓ = -N < 0`. -/
private def twNegBlk (M j₀ N k : ℕ) : SBlock :=
  if k = 0 then .band 0 (M + N - 1) else if k < N then .band (M + N - 1 - k) (M + N - k)
  else if k = N then .band M (M + N) else if k < 2 * N then .band (M + k - 1) (M + k)
  else .band j₀ (M + 2 * N - 1)

/-- The discs of the chain for `ℓ = N > 0`: up from `M + N + 1` to `M + 2N + 3`, down from
`M + N` to `M`, then `j₀`. -/
private def twPosDisc (M j₀ N k : ℕ) : ℕ :=
  if k < N + 3 then M + N + 1 + k else if k < 2 * N + 4 then M + 2 * N + 3 - k else j₀

/-- The blocks of the chain for `ℓ = N > 0`. -/
private def twPosBlk (M j₀ N k : ℕ) : SBlock :=
  if k = 0 then .band 0 (M + N + 1) else if k < N + 3 then .neg (M + N + k)
  else if k = N + 3 then .band (M + N) (M + 2 * N + 3)
  else if k < 2 * N + 4 then .neg (M + 2 * N + 3 - k) else .band j₀ M

/-- The chain for `ℓ < 0` is a path. -/
private theorem twPathOK_neg_twKFence {M j₀ N : ℕ} (hj1 : 1 ≤ j₀) (hjM : j₀ < M) (hN : 1 ≤ N) :
    TwPathOK M j₀ (M + 2 * N - 1) (2 * N + 1) (twNegBlk M j₀ N) (twNegDisc M j₀ N) := by
  refine ⟨by omega, by omega, fun k hk ↦ ?_, fun i j hi hj h ↦ ?_, fun k hk ↦ ?_, ?_,
    fun m h1 h2 ↦ ?_, ?_⟩
  · unfold twNegBlk twNegDisc
    split_ifs <;> simp only [isoEnds, Prod.mk.injEq] <;> omega
  · unfold twNegDisc at h
    split_ifs at h <;> omega
  · unfold twNegDisc
    split_ifs <;> omega
  · unfold twNegDisc
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · by_cases hm : m < M + N
    · refine ⟨M + N - 1 - m, by omega, ?_⟩
      unfold twNegDisc
      rw [ite_eq_left (by omega)]
      omega
    · refine ⟨m - M, by omega, ?_⟩
      unfold twNegDisc
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
  · unfold twNegBlk
    rw [ite_eq_left rfl]
    rfl

/-- The chain for `ℓ > 0` is a path. -/
private theorem twPathOK_pos_twKFence {M j₀ N : ℕ} (hj1 : 1 ≤ j₀) (hjM : j₀ < M) :
    TwPathOK M j₀ (M + (2 * N + 4) - 1) (2 * N + 5) (twPosBlk M j₀ N) (twPosDisc M j₀ N) := by
  refine ⟨by omega, by omega, fun k hk ↦ ?_, fun i j hi hj h ↦ ?_, fun k hk ↦ ?_, ?_,
    fun m h1 h2 ↦ ?_, ?_⟩
  · unfold twPosBlk twPosDisc
    split_ifs <;> simp only [isoEnds, Prod.mk.injEq] <;> omega
  · unfold twPosDisc at h
    split_ifs at h <;> omega
  · unfold twPosDisc
    split_ifs <;> omega
  · unfold twPosDisc
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · by_cases hm : M + N + 1 ≤ m
    · refine ⟨m - (M + N + 1), by omega, ?_⟩
      unfold twPosDisc
      rw [ite_eq_left (by omega)]
      omega
    · refine ⟨M + 2 * N + 3 - m, by omega, ?_⟩
      unfold twPosDisc
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
  · unfold twPosBlk
    rw [ite_eq_left rfl]
    rfl

/-- The chain for `ℓ < 0`, block by block. -/
private theorem twChain_neg_twKFence (M j₀ : ℕ) {ℓ : ℤ} (hl : ℓ < 0) :
    twChain M j₀ ℓ = (List.range (2 * ℓ.natAbs + 1)).map (twNegBlk M j₀ ℓ.natAbs) := by
  have hN : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne
  rw [twChain, ite_eq_right hl.ne, ite_eq_left hl]
  generalize ℓ.natAbs = N at hN ⊢
  have e0 : twNegBlk M j₀ N 0 = .band 0 (M + N - 1) := by
    unfold twNegBlk
    rw [ite_eq_left rfl]
  have e1 : (List.range (N - 1)).map (fun i ↦ twNegBlk M j₀ N (1 + i)) =
      (List.range (N - 1)).map (fun i ↦ SBlock.band (M + N - 2 - i) (M + N - 1 - i)) :=
    List.map_congr_left fun i hi ↦ by
      rw [List.mem_range] at hi
      unfold twNegBlk
      split_ifs <;> first | omega | (congr 1 <;> omega)
  have e2 : twNegBlk M j₀ N (1 + (N - 1)) = .band M (M + N) := by
    unfold twNegBlk
    split_ifs <;> first | omega | rfl
  have e3 : (List.range (N - 1)).map (fun i ↦ twNegBlk M j₀ N (1 + (N - 1) + 1 + i)) =
      (List.range (N - 1)).map (fun i ↦ SBlock.band (M + N + i) (M + N + 1 + i)) :=
    List.map_congr_left fun i hi ↦ by
      rw [List.mem_range] at hi
      unfold twNegBlk
      split_ifs <;> first | omega | (congr 1 <;> omega)
  have e4 : twNegBlk M j₀ N (1 + (N - 1) + 1 + (N - 1)) = .band j₀ (M + 2 * N - 1) := by
    unfold twNegBlk
    split_ifs <;> first | omega | rfl
  rw [show 2 * N + 1 = 1 + (N - 1) + 1 + (N - 1) + 1 by omega, map_range_five_twKFence, e0, e1,
    e2, e3, e4]

/-- The chain for `ℓ > 0`, block by block. -/
private theorem twChain_pos_twKFence (M j₀ : ℕ) {ℓ : ℤ} (hl : 0 < ℓ) :
    twChain M j₀ ℓ = (List.range (2 * ℓ.natAbs + 5)).map (twPosBlk M j₀ ℓ.natAbs) := by
  rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt]
  generalize ℓ.natAbs = N
  have e0 : twPosBlk M j₀ N 0 = .band 0 (M + N + 1) := by
    unfold twPosBlk
    rw [ite_eq_left rfl]
  have e1 : (List.range (N + 2)).map (fun i ↦ twPosBlk M j₀ N (1 + i)) =
      (List.range (N + 2)).map (fun i ↦ SBlock.neg (M + N + 1 + i)) :=
    List.map_congr_left fun i hi ↦ by
      rw [List.mem_range] at hi
      unfold twPosBlk
      split_ifs <;> first | omega | (congr 1; omega)
  have e2 : twPosBlk M j₀ N (1 + (N + 2)) = .band (M + N) (M + 2 * N + 3) := by
    unfold twPosBlk
    split_ifs <;> first | omega | contradiction | rfl
  have e3 : (List.range N).map (fun i ↦ twPosBlk M j₀ N (1 + (N + 2) + 1 + i)) =
      (List.range N).map (fun i ↦ SBlock.neg (M + N - 1 - i)) :=
    List.map_congr_left fun i hi ↦ by
      rw [List.mem_range] at hi
      unfold twPosBlk
      split_ifs <;> first | omega | (congr 1; omega)
  have e4 : twPosBlk M j₀ N (1 + (N + 2) + 1 + N) = .band j₀ M := by
    unfold twPosBlk
    split_ifs <;> first | omega | rfl
  rw [show 2 * N + 5 = 1 + (N + 2) + 1 + N + 1 by omega, map_range_five_twKFence, e0, e1, e2,
    e3, e4]

/-- The fence blocks of the chain for `ℓ < 0` are those of `twPrefix ℓ`. -/
private theorem flatMap_twPathBlockWord_neg_twKFence {M j₀ : ℕ} (hjM : j₀ < M) {ℓ : ℤ}
    (hl : ℓ < 0) :
    (List.range (2 * ℓ.natAbs + 1)).flatMap
      (twPathBlockWord (twNegBlk M j₀ ℓ.natAbs) (twNegDisc M j₀ ℓ.natAbs)) = twPrefix ℓ := by
  have hN : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne
  rw [twPrefix, ite_eq_right hl.ne, ite_eq_left hl]
  generalize ℓ.natAbs = N at hN ⊢
  have e1 := flatMap_range_const_twKFence
    (fun i ↦ twPathBlockWord (twNegBlk M j₀ N) (twNegDisc M j₀ N) (1 + i)) twDecP (N - 1)
    fun i hi ↦ by
      unfold twPathBlockWord twNegBlk twNegDisc
      split_ifs <;> first | omega | rfl
  have e2 : twPathBlockWord (twNegBlk M j₀ N) (twNegDisc M j₀ N) (1 + (N - 1)) = twIncP := by
    unfold twPathBlockWord twNegBlk twNegDisc
    split_ifs <;> first | omega | rfl
  have e3 := flatMap_range_const_twKFence
    (fun i ↦ twPathBlockWord (twNegBlk M j₀ N) (twNegDisc M j₀ N) (1 + (N - 1) + 1 + i))
    twIncP (N - 1) fun i hi ↦ by
      unfold twPathBlockWord twNegBlk twNegDisc
      split_ifs <;> first | omega | rfl
  have e4 : twPathBlockWord (twNegBlk M j₀ N) (twNegDisc M j₀ N) (1 + (N - 1) + 1 + (N - 1)) =
      twDecP := by
    unfold twPathBlockWord twNegBlk twNegDisc
    split_ifs <;> first | omega | rfl
  have e5 : phaseTwoBlk twIncP N = twIncP ++ phaseTwoBlk twIncP (N - 1) := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons, Nat.add_sub_cancel]
  rw [show 2 * N + 1 = 1 + (N - 1) + 1 + (N - 1) + 1 by omega, flatMap_range_five_twKFence, e1,
    e2, e3, e4, e5]
  simp only [twPathBlockWord, ↓reduceIte, List.append_assoc]

/-- The fence blocks of the chain for `ℓ > 0` are those of `twPrefix ℓ`. -/
private theorem flatMap_twPathBlockWord_pos_twKFence {M j₀ : ℕ} (hjM : j₀ < M) {ℓ : ℤ}
    (hl : 0 < ℓ) :
    (List.range (2 * ℓ.natAbs + 5)).flatMap
      (twPathBlockWord (twPosBlk M j₀ ℓ.natAbs) (twPosDisc M j₀ ℓ.natAbs)) = twPrefix ℓ := by
  rw [twPrefix, ite_eq_right hl.ne', ite_eq_right hl.not_gt]
  generalize ℓ.natAbs = N
  have e1 := flatMap_range_const_twKFence
    (fun i ↦ twPathBlockWord (twPosBlk M j₀ N) (twPosDisc M j₀ N) (1 + i)) twIncN (N + 2)
    fun i hi ↦ by
      unfold twPathBlockWord twPosBlk twPosDisc
      split_ifs <;> first | omega | rfl
  have e2 : twPathBlockWord (twPosBlk M j₀ N) (twPosDisc M j₀ N) (1 + (N + 2)) = twDecP := by
    unfold twPathBlockWord twPosBlk twPosDisc
    split_ifs <;> first | omega | contradiction | rfl
  have e3 := flatMap_range_const_twKFence
    (fun i ↦ twPathBlockWord (twPosBlk M j₀ N) (twPosDisc M j₀ N) (1 + (N + 2) + 1 + i))
    twDecN N fun i hi ↦ by
      unfold twPathBlockWord twPosBlk twPosDisc
      split_ifs <;> first | omega | rfl
  have e4 : twPathBlockWord (twPosBlk M j₀ N) (twPosDisc M j₀ N) (1 + (N + 2) + 1 + N) =
      twDecP := by
    unfold twPathBlockWord twPosBlk twPosDisc
    split_ifs <;> first | omega | rfl
  rw [show 2 * N + 5 = 1 + (N + 2) + 1 + N + 1 by omega, flatMap_range_five_twKFence, e1, e2,
    e3, e4]
  simp only [twPathBlockWord, ↓reduceIte, List.append_assoc]

/-- Every chain of `twChain` is a path whose fence blocks are those of `twPrefix`. -/
private theorem exists_twPath_twKFence {M j₀ : ℕ} (hj1 : 1 ≤ j₀) (hjM : j₀ < M) (ℓ : ℤ) :
    ∃ (L : ℕ) (blk : ℕ → SBlock) (a : ℕ → ℕ), twChain M j₀ ℓ = (List.range L).map blk ∧
      TwPathOK M j₀ (M + twExtra ℓ - 1) L blk a ∧
        (List.range L).flatMap (twPathBlockWord blk a) = twPrefix ℓ := by
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · refine ⟨_, _, _, twChain_neg_twKFence M j₀ hl, ?_,
      flatMap_twPathBlockWord_neg_twKFence hjM hl⟩
    rw [twExtra, ite_eq_left hl.le]
    exact twPathOK_neg_twKFence hj1 hjM (Int.natAbs_pos.2 hl.ne)
  · refine ⟨1, fun _ ↦ .band 0 j₀, fun _ ↦ j₀, by rw [twChain, ite_eq_left rfl]; rfl, ?_, ?_⟩
    · rw [show twExtra 0 = 0 from rfl]
      refine ⟨le_rfl, by omega, fun k hk ↦ ?_, fun i j hi hj _ ↦ by omega,
        fun k hk ↦ by omega, rfl, fun m h1 h2 ↦ by omega, rfl⟩
      obtain rfl : k = 0 := by omega
      simp only [isoEnds, ↓reduceIte, Nat.zero_min, Nat.zero_max]
    · rw [twPrefix, ite_eq_left rfl]
      rfl
  · refine ⟨_, _, _, twChain_pos_twKFence M j₀ hl, ?_,
      flatMap_twPathBlockWord_pos_twKFence hjM hl⟩
    rw [twExtra, ite_eq_right hl.not_ge]
    exact twPathOK_pos_twKFence hj1 hjM

/-! ### The tail of `pairBlocks` -/

/-- Changing the sign of a Hopf letter does not change the discs it is attached to. -/
private theorem isoAttached_twClaspBlock_twKFence (σ : Bool) (m : ℕ) (b : SBlock) :
    isoAttached m (twClaspBlock σ b) = isoAttached m b := by
  cases b <;> cases σ <;> rfl

/-- The first block of a disc does not depend on the clasp sign. -/
private theorem isoFirst_map_twClaspBlock_twKFence (σ : Bool) (B : List SBlock) (m : ℕ) :
    isoFirst (B.map (twClaspBlock σ)) m = isoFirst B m := by
  unfold isoFirst
  rw [List.findIdx_map]
  congr 1
  funext b
  exact isoAttached_twClaspBlock_twKFence σ m b

/-- The last block of a disc does not depend on the clasp sign. -/
private theorem isoLast_map_twClaspBlock_twKFence (σ : Bool) (B : List SBlock) (m : ℕ) :
    isoLast (B.map (twClaspBlock σ)) m = isoLast B m := by
  unfold isoLast
  rw [List.length_map, ← List.map_reverse, List.findIdx_map]
  congr 2
  funext b
  exact isoAttached_twClaspBlock_twKFence σ m b

/-- The head disc `j₀` of `pairBlocks r s` is an old disc `1 ≤ j₀ < M`. -/
private theorem twHeadTop_range_twKFence {r s : ℕ} (h : IsTorusPair r s) :
    1 ≤ twHeadTop r s ∧ twHeadTop r s < pairStrands r s := by
  have hhead : (SBlock.band 0 (twHeadTop r s)).Valid (pairStrands r s) :=
    pairBlocks_valid h _ (by rw [pairBlocks_eq_head_cons h]; exact List.mem_cons_self)
  simp only [SBlock.Valid] at hhead
  omega

/-- The tail of `pairBlocks r s`, with either clasp sign, satisfies the tail hypotheses. -/
private theorem twTailOK_twKFence {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    TwTailOK (pairStrands r s) (twHeadTop r s) ((pairBlocks r s).tail.map (twClaspBlock σ)) := by
  obtain ⟨hj1, hjM⟩ := twHeadTop_range_twKFence h
  have hf := (isoFenceable_pairBlocks h).2
  have hB : pairBlocks r s = [SBlock.band 0 (twHeadTop r s)] ++ (pairBlocks r s).tail :=
    pairBlocks_eq_head_cons h
  have hval : ∀ b ∈ (pairBlocks r s).tail.map (twClaspBlock σ), b.Valid (pairStrands r s) := by
    intro b hb
    have hv := twBlocks_valid h 0 σ b (List.mem_append_right _ hb)
    rwa [show twStrands r s 0 = pairStrands r s by simp [twStrands, twExtra]] at hv
  generalize (pairBlocks r s).tail = T₀ at hB hval ⊢
  have hlast0 : ∀ m, isoLast [SBlock.band 0 (twHeadTop r s)] m = 0 := by
    intro m
    unfold isoLast
    simp
  have key : ∀ m, 1 ≤ m → m < pairStrands r s →
      isoFirst T₀ m < T₀.length ∧ (m ≠ twHeadTop r s → isoFirst T₀ m < isoLast T₀ m) := by
    intro m h1 hm
    obtain ⟨hlt, -⟩ := hf m h1 (by omega)
    rw [hB] at hlt
    have hatt : isoFirst T₀ m < T₀.length := by
      by_contra hna
      have hEq : isoFirst T₀ m = T₀.length :=
        le_antisymm List.findIdx_le_length (not_lt.1 hna)
      rw [isoLast_append_of_not_attached_twKFence hEq, hlast0] at hlt
      omega
    refine ⟨hatt, fun hmj ↦ ?_⟩
    obtain ⟨e, -⟩ :=
      isoLast_append_of_attached_twKFence (C := [SBlock.band 0 (twHeadTop r s)]) hatt
    have hF1 : isoFirst [SBlock.band 0 (twHeadTop r s)] m =
        [SBlock.band 0 (twHeadTop r s)].length :=
      List.findIdx_eq_length.2 fun b hb ↦ by
        rw [List.mem_singleton] at hb
        subst hb
        exact decide_eq_false (by simp only [isoEnds]; omega)
    rw [isoFirst_append_twKFence, hF1, ite_eq_right (lt_irrefl _), e] at hlt
    omega
  refine ⟨hj1, hjM, hval, fun m h1 hm ↦ ?_, fun m h1 hm hmj ↦ ?_⟩
  · rw [isoFirst_map_twClaspBlock_twKFence, List.length_map]
    exact (key m h1 hm).1
  · rw [isoFirst_map_twClaspBlock_twKFence, isoLast_map_twClaspBlock_twKFence]
    exact (key m h1 hm).2 hmj

/-- The fence word of the twisted list: the chain prefix, then the part of the tail. -/
private theorem isoFenceWord_twBlocks_tail_twKFence {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (σ : Bool) :
    isoFenceWord (twStrands r s ℓ - 1) (twBlocks r s ℓ σ) =
      twPrefix ℓ ++ twTailWord (pairStrands r s) (twHeadTop r s)
        ((pairBlocks r s).tail.map (twClaspBlock σ)) := by
  obtain ⟨hj1, hjM⟩ := twHeadTop_range_twKFence h
  obtain ⟨L, blk, a, hC, hP, hW⟩ := exists_twPath_twKFence hj1 hjM ℓ
  rw [twBlocks, hC, twStrands, isoFenceWord_path_twKFence hP (twTailOK_twKFence h σ), hW]

/-- The tail of the fence word of the untwisted list is the part of the tail. -/
private theorem twStripTail_eq_twTailWord_twKFence {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    twStripTail r s σ = twTailWord (pairStrands r s) (twHeadTop r s)
      ((pairBlocks r s).tail.map (twClaspBlock σ)) := by
  have h0 := isoFenceWord_twBlocks_tail_twKFence h 0 σ
  rw [show twStrands r s 0 = pairStrands r s by simp [twStrands, twExtra],
    show twPrefix 0 = [isoU 1, isoX true 0] from rfl] at h0
  rw [twStripTail, h0]
  rfl

/-- The twisted block lists can be thinned and retracted. -/
theorem isoFenceable_twBlocks {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    IsoFenceable (twStrands r s ℓ - 1) (twBlocks r s ℓ σ) := by
  obtain ⟨hj1, hjM⟩ := twHeadTop_range_twKFence h
  obtain ⟨L, blk, a, hC, hP, -⟩ := exists_twPath_twKFence hj1 hjM ℓ
  have hv := twBlocks_valid h ℓ σ
  rw [twBlocks, hC, twStrands] at hv
  rw [twBlocks, hC, twStrands]
  refine isoFenceable_path_twKFence hP (twTailOK_twKFence h σ) ?_
  rwa [show pairStrands r s + twExtra ℓ - 1 + 1 = pairStrands r s + twExtra ℓ by omega]

/-- The fence word of the untwisted list begins with `u1 +0`. -/
theorem isoFenceWord_twBlocks_zero {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    isoFenceWord (pairStrands r s - 1) (twBlocks r s 0 σ) =
      [isoU 1, isoX true 0] ++ twStripTail r s σ := by
  have h0 := isoFenceWord_twBlocks_tail_twKFence h 0 σ
  rw [show twStrands r s 0 = pairStrands r s by simp [twStrands, twExtra],
    show twPrefix 0 = [isoU 1, isoX true 0] from rfl] at h0
  rw [h0, twStripTail_eq_twTailWord_twKFence h σ]

/-- For the negative clasp and `r ≥ 3` the tail is the tail of the strip word of the library. -/
theorem twStripTail_true {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    twStripTail r s true = (pairStrip r s).drop 2 := by
  rw [twStripTail, twBlocks_zero_true h, isoFenceWord_pairBlocks h hr]

/-- Crux (combinatorial): the fence word of the twisted list is the chain prefix followed by the
old tail. -/
theorem isoFenceWord_twBlocks {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    isoFenceWord (twStrands r s ℓ - 1) (twBlocks r s ℓ σ) = twPrefix ℓ ++ twStripTail r s σ := by
  rw [isoFenceWord_twBlocks_tail_twKFence h ℓ σ, twStripTail_eq_twTailWord_twKFence h σ]

/-- Phase I: the long closure of the twisted word reaches the prefixed strip word. -/
theorem morseReach_tw_source_fence {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    MorseReach 1 (morseLongClosure (twStrands r s ℓ) (twWhiteheadWord r s ℓ σ))
      (twPrefix ℓ ++ twStripTail r s σ) := by
  have hp := morseReach_isoPhaseOne (isoFenceable_twBlocks h ℓ σ)
  have hs : twStrands r s ℓ - 1 + 1 = twStrands r s ℓ := by
    have := (twHeadTop_range_twKFence h).2
    rw [twStrands]
    omega
  rw [isoFenceWord_twBlocks h ℓ σ, hs] at hp
  exact hp

end AJConjecture
