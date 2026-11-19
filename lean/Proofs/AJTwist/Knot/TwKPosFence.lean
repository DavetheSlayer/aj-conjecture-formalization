import Mathlib
import AJTwist.Knot.TwKPosWords
import AJTwist.Knot.TwKFence

/-!
# The fence word with the clasp of either sign, in closed form

The fence word of a block list depends on the blocks only through the discs they join (cups,
caps and positions) and through the sign of each block (the middle letter of its band). The
positive clasp replaces the two Hopf blocks `neg (2c - 1)` by `band (2c - 1) (2c)`, which join the
same discs. So the fence word of the positive list is the fence word of the negative one with
the middle letters of the two Hopf bands made positive (`isoFenceWord_map_twClaspBlock`: the
general statement, block by block).

* `twStripTail_eq_twkStripTail` (`r ≥ 3`): `twStripTail r s σ = twkStripTail r s σ`. For
  `σ = true` this is `twStripTail_true` with `twkStripTail_true`. For `σ = false`: by the block
  form, the fence blocks of the two lists agree except at the two Hopf blocks; the last block is
  a suffix of the word, so it is identified by its length (no cup, a band of span two, two
  caps: `isoFirst_le_of_attached`, `le_isoLast_of_attached`, `pairBlocks_getElem?_hopfFirst`,
  `pairBlocks_getElem?_hopfSecond`); the first Hopf block is the only other place of the word
  `pairStrip r s` where a negative crossing follows a positive crossing one position higher.
Checked by evaluating the Lean definitions (`SCR/KP/leancheck/EvalFence.lean`): both statements
hold for `(3,4), (3,5), (4,5), (5,6)`, both signs, and
`(twBlocks r s 0 true).map (twClaspBlock σ) = twBlocks r s 0 σ`.
-/

namespace AJConjecture

/-- Changing the sign of the Hopf letters does not change the discs joined by a block. -/
theorem isoEnds_twClaspBlock (σ : Bool) (b : SBlock) : isoEnds (twClaspBlock σ b) = isoEnds b := by
  cases b with
  | band i j => rfl
  | neg i => cases σ <;> rfl

/-- Changing the sign of a Hopf letter does not change the discs it is attached to. -/
private theorem isoAttached_twClaspBlock_twKPosFence (σ : Bool) (m : ℕ) (b : SBlock) :
    isoAttached m (twClaspBlock σ b) = isoAttached m b := by
  cases b <;> cases σ <;> rfl

/-- The first block of a disc does not depend on the clasp sign. -/
private theorem isoFirst_map_twClaspBlock_twKPosFence (σ : Bool) (B : List SBlock) (m : ℕ) :
    isoFirst (B.map (twClaspBlock σ)) m = isoFirst B m := by
  unfold isoFirst
  rw [List.findIdx_map]
  congr 1
  funext b
  exact isoAttached_twClaspBlock_twKPosFence σ m b

/-- The last block of a disc does not depend on the clasp sign. -/
private theorem isoLast_map_twClaspBlock_twKPosFence (σ : Bool) (B : List SBlock) (m : ℕ) :
    isoLast (B.map (twClaspBlock σ)) m = isoLast B m := by
  unfold isoLast
  rw [List.length_map, ← List.map_reverse, List.findIdx_map]
  congr 2
  funext b
  exact isoAttached_twClaspBlock_twKPosFence σ m b

/-- The positions of the discs do not depend on the clasp sign. -/
private theorem isoPos_map_twClaspBlock_twKPosFence (σ : Bool) (B : List SBlock) (j k : ℕ) :
    isoPos (B.map (twClaspBlock σ)) j k = isoPos B j k := by
  funext m
  simp only [isoPos, isoOpen, isoFirst_map_twClaspBlock_twKPosFence,
    isoLast_map_twClaspBlock_twKPosFence]

/-- The fence word of a block list with the Hopf signs changed, block by block: the cups, the
caps and the positions are those of the original list. -/
theorem isoFenceWord_map_twClaspBlock (n : ℕ) (B : List SBlock) (σ : Bool) :
    isoFenceWord n (B.map (twClaspBlock σ)) =
      B.zipIdx.flatMap fun bk ↦
        isoFenceCups n B 0 bk.2 ++ isoBlockWord (isoPos B 0 bk.2) (twClaspBlock σ bk.1) ++
          isoFenceCaps n B 0 bk.2 := by
  simp only [isoFenceWord, isoFenceAux, Nat.zero_min, List.range_zero, List.map_nil,
    List.reverse_nil, List.nil_append, List.append_nil]
  rw [List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun bk _ ↦ ?_
  simp only [isoFenceBlock_eq, isoFenceCups, isoFenceCaps, isoPos_map_twClaspBlock_twKPosFence,
    isoFirst_map_twClaspBlock_twKPosFence, isoLast_map_twClaspBlock_twKPosFence, Prod.map_fst,
    Prod.map_snd, id_eq]

/-! ### The flip of the Hopf letters as a function of the word -/

/-- The word with every negative crossing that follows a positive crossing one position higher
made positive. The first argument is the position of the preceding letter when it is a positive
crossing. -/
private def twkFlipWord : Option ℕ → MorseWord → MorseWord
  | _, [] => []
  | o, (.cross false, b) :: w => (.cross (decide (o = some (b + 1))), b) :: twkFlipWord none w
  | _, (.cross true, a) :: w => (.cross true, a) :: twkFlipWord (some a) w
  | _, (.cup, a) :: w => (.cup, a) :: twkFlipWord none w
  | _, (.cap, a) :: w => (.cap, a) :: twkFlipWord none w

/-- The word does not begin with a negative crossing. -/
private def twkCalmHead : MorseWord → Prop
  | (.cross false, _) :: _ => False
  | _ => True

/-- In front of a word that does not begin with a negative crossing the state plays no role. -/
private theorem twkFlipWord_of_calmHead {w : MorseWord} (hw : twkCalmHead w) (o : Option ℕ) :
    twkFlipWord o w = twkFlipWord none w := by
  match w, hw with
  | [], _ => rfl
  | (.cross true, _) :: _, _ => rfl
  | (.cup, _) :: _, _ => rfl
  | (.cap, _) :: _, _ => rfl

/-- The flip turns `X` into `Y`, whatever precedes `X`, in front of every word that does not
begin with a negative crossing. -/
private def TwkFlips (X Y : MorseWord) : Prop :=
  ∀ (o : Option ℕ) (v : MorseWord), twkCalmHead v →
    twkCalmHead (X ++ v) ∧ twkFlipWord o (X ++ v) = Y ++ twkFlipWord none v

/-- The empty word is not changed. -/
private theorem twkFlips_nil : TwkFlips [] [] :=
  fun o _ hv ↦ ⟨hv, twkFlipWord_of_calmHead hv o⟩

/-- The flip of a concatenation, piece by piece. -/
private theorem twkFlips_append {X Y X' Y' : MorseWord} (h : TwkFlips X Y)
    (h' : TwkFlips X' Y') : TwkFlips (X ++ X') (Y ++ Y') := by
  intro o v hv
  obtain ⟨c', e'⟩ := h' none v hv
  obtain ⟨c, e⟩ := h o (X' ++ v) c'
  rw [List.append_assoc, List.append_assoc]
  exact ⟨c, by rw [e, e']⟩

/-- The flip of a concatenation of a list of words, piece by piece. -/
private theorem twkFlips_flatMap {α : Type} (L : List α) (f g : α → MorseWord)
    (h : ∀ a ∈ L, TwkFlips (f a) (g a)) : TwkFlips (L.flatMap f) (L.flatMap g) := by
  induction L with
  | nil => exact twkFlips_nil
  | cons a L ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact twkFlips_append (h a List.mem_cons_self) (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-- The flip of a repeated block. -/
private theorem twkFlips_phaseTwoBlk {X Y : MorseWord} (h : TwkFlips X Y) (m : ℕ) :
    TwkFlips (phaseTwoBlk X m) (phaseTwoBlk Y m) := by
  induction m with
  | zero => exact twkFlips_nil
  | succ m ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact twkFlips_append h ih

/-- Cups and caps are not changed. -/
private theorem twkFlips_cupCap (u : MorseWord) (hu : ∀ l ∈ u, l.1 = .cup ∨ l.1 = .cap) :
    TwkFlips u u := by
  induction u with
  | nil => exact twkFlips_nil
  | cons l u ih =>
    have hl := hu l List.mem_cons_self
    have ih' := ih fun l' hl' ↦ hu l' (List.mem_cons_of_mem _ hl')
    intro o v hv
    obtain ⟨-, e⟩ := ih' none v hv
    obtain ⟨k, a⟩ := l
    match k, hl with
    | .cup, _ => exact ⟨trivial, by rw [List.cons_append, twkFlipWord, e]; rfl⟩
    | .cap, _ => exact ⟨trivial, by rw [List.cons_append, twkFlipWord, e]; rfl⟩

/-- A positive band is not changed; after it the state is the position of its only letter when it
has span one. -/
private theorem twkFlipWord_isoBand_true (c d : ℕ) (hcd : c < d) (o : Option ℕ) (v : MorseWord) :
    twkFlipWord o (isoBand c d true ++ v) =
      isoBand c d true ++ twkFlipWord (if d = c + 1 then some c else none) v := by
  obtain ⟨k, rfl⟩ : ∃ k, d = c + 1 + k := ⟨d - (c + 1), by omega⟩
  clear hcd
  induction k generalizing o v with
  | zero =>
    rw [Nat.add_zero, isoBand_span_one, ite_eq_left rfl]
    rfl
  | succ k ih =>
    rw [show c + 1 + (k + 1) = c + 1 + k + 1 by omega, isoBand_peel_right c (c + 1 + k) (by omega),
      ite_eq_right (by omega)]
    simp only [isoX, List.cons_append, List.append_assoc, List.nil_append, twkFlipWord]
    rw [ih]
    simp only [twkFlipWord]
    have hdec : decide ((if c + 1 + k = c + 1 then some c else none) = some (c + 1 + k + 1)) =
        false := by
      split_ifs
      · exact decide_eq_false (by simp only [Option.some.injEq]; omega)
      · exact decide_eq_false (by simp)
    rw [hdec]

/-- A positive band begins with a positive crossing. -/
private theorem twkCalmHead_isoBand_true (c d : ℕ) (hcd : c < d) (v : MorseWord) :
    twkCalmHead (isoBand c d true ++ v) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = c + 1 + k := ⟨d - (c + 1), by omega⟩
  cases k with
  | zero => rw [Nat.add_zero, isoBand_span_one]; trivial
  | succ k =>
    rw [show c + 1 + (k + 1) = c + 1 + k + 1 by omega, isoBand_peel_right c (c + 1 + k) (by omega)]
    trivial

/-- A positive band is not changed. -/
private theorem twkFlips_isoBand_true (c d : ℕ) (hcd : c < d) :
    TwkFlips (isoBand c d true) (isoBand c d true) := by
  intro o v hv
  refine ⟨twkCalmHead_isoBand_true c d hcd v, ?_⟩
  rw [twkFlipWord_isoBand_true c d hcd, twkFlipWord_of_calmHead hv]

/-- A band of span two as a word. -/
private theorem isoBand_span_two_twKPosFence (p : ℕ) (b : Bool) :
    isoBand p (p + 2) b = [isoX true (p + 1), isoX b p, isoX false (p + 1)] := by
  rw [isoBand_peel_right p (p + 1) (by omega), isoBand_span_one]
  rfl

/-- The middle letter of a negative band of span two becomes positive. -/
private theorem twkFlips_isoBand_two (p : ℕ) :
    TwkFlips (isoBand p (p + 2) false) (isoBand p (p + 2) true) := by
  intro o v hv
  rw [isoBand_span_two_twKPosFence, isoBand_span_two_twKPosFence]
  refine ⟨trivial, ?_⟩
  simp only [isoX, List.cons_append, List.nil_append, twkFlipWord, decide_true]
  simp

/-- A word turned into `Y` by the flip is `Y` after the flip. -/
private theorem twkFlips_eq {X Y : MorseWord} (h : TwkFlips X Y) : twkFlipWord none X = Y := by
  have := (h none [] trivial).2
  rwa [List.append_nil, twkFlipWord, List.append_nil] at this

/-! ### The flip on the block form of the fence word -/

/-- A disc attached to the block `k` is open at the block `k`. -/
private theorem isoOpen_of_attached_twKPosFence {B : List SBlock} {k m : ℕ} {b : SBlock}
    (hb : B[k]? = some b) (hm : 1 ≤ m) (ha : isoAttached m b = true) :
    isoOpen B 0 m k = true := by
  simp only [isoOpen, decide_eq_true_eq]
  exact ⟨hm, Or.inr ⟨isoFirst_le_of_attached hb ha, (le_isoLast_of_attached hb ha).1⟩⟩

/-- The disc above a disc of the block sits two places to its right. -/
private theorem isoPos_succ_of_attached_twKPosFence {B : List SBlock} {k m : ℕ} {b : SBlock}
    (hb : B[k]? = some b) (hm : 1 ≤ m) (ha : isoAttached m b = true) :
    isoPos B 0 k (m + 1) = isoPos B 0 k m + 2 := by
  simp only [isoPos, Nat.add_one_ne_zero, ↓reduceIte, show m ≠ 0 by omega,
    length_filter_isoOpen_succ, isoOpen_of_attached_twKPosFence hb hm ha]
  omega

/-- A disc of the block sits left of every disc above it. -/
private theorem isoPos_lt_of_attached_twKPosFence {B : List SBlock} {k i j : ℕ} {b : SBlock}
    (hb : B[k]? = some b) (ha : isoAttached i b = true) (hij : i < j) :
    isoPos B 0 k i < isoPos B 0 k j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have := le_isoPos_of_lt B (j := 0) (k := k) hij
    simp only [isoPos, ↓reduceIte]
    simp only [isoPos] at this
    omega
  · have h1 := isoPos_succ_of_attached_twKPosFence hb hi ha
    have hmono : isoPos B 0 k (i + 1) ≤ isoPos B 0 k j := by
      simp only [isoPos, show j ≠ 0 by omega, Nat.add_one_ne_zero, ↓reduceIte]
      have := ((List.range_sublist.2 (show i + 1 ≤ j by omega)).filter
        (fun x ↦ isoOpen B 0 x k)).length_le
      omega
    omega

/-- The flip turns the fence word of a block list with negative Hopf letters into the fence word
of the list with positive Hopf letters. -/
private theorem twkFlips_isoFenceWord {n : ℕ} {B : List SBlock}
    (hband : ∀ i j, SBlock.band i j ∈ B → i < j) (hneg : ∀ i, SBlock.neg i ∈ B → 1 ≤ i) :
    TwkFlips (isoFenceWord n (B.map (twClaspBlock true)))
      (isoFenceWord n (B.map (twClaspBlock false))) := by
  rw [isoFenceWord_map_twClaspBlock, isoFenceWord_map_twClaspBlock]
  refine twkFlips_flatMap _ _ _ fun bk hbk ↦ ?_
  obtain ⟨b, k⟩ := bk
  have hb : B[k]? = some b := by
    have := List.mem_zipIdx_iff_getElem?.1 hbk
    simpa using this
  refine twkFlips_append (twkFlips_append
    (twkFlips_cupCap _ fun l hl ↦ Or.inl (mem_isoFenceCups hl).1) ?_)
    (twkFlips_cupCap _ fun l hl ↦ Or.inr (mem_isoFenceCaps hl).1)
  cases b with
  | band i j =>
    change TwkFlips (isoBand (isoPos B 0 k i) (isoPos B 0 k j) true)
      (isoBand (isoPos B 0 k i) (isoPos B 0 k j) true)
    exact twkFlips_isoBand_true _ _ (isoPos_lt_of_attached_twKPosFence hb
      (by simp [isoAttached, isoEnds]) (hband i j (List.mem_of_getElem? hb)))
  | neg i =>
    have h2 := isoPos_succ_of_attached_twKPosFence hb (hneg i (List.mem_of_getElem? hb))
      (by simp [isoAttached, isoEnds])
    simp only [isoBlockWord, twClaspBlock, isoEnds, isoSign, h2, ↓reduceIte, Bool.false_eq_true]
    exact twkFlips_isoBand_two _

/-! ### The flip on the closed form -/

/-- A block of cups, a positive band and caps is not changed. -/
private theorem twkFlips_cupBandCap (u n : MorseWord) (c d : ℕ) (hcd : c < d)
    (hu : ∀ l ∈ u, l.1 = .cup ∨ l.1 = .cap) (hn : ∀ l ∈ n, l.1 = .cup ∨ l.1 = .cap) :
    TwkFlips (u ++ isoBand c d true ++ n) (u ++ isoBand c d true ++ n) :=
  twkFlips_append (twkFlips_append (twkFlips_cupCap u hu) (twkFlips_isoBand_true c d hcd))
    (twkFlips_cupCap n hn)

/-- The flip turns the closed form with negative Hopf letters into the one with positive Hopf
letters. -/
private theorem twkFlips_twkStripTail (r s : ℕ) (hr : 1 ≤ r) :
    TwkFlips ([isoU 1, isoX true 0] ++ twkStripTail r s true)
      ([isoU 1, isoX true 0] ++ twkStripTail r s false) := by
  have h0 : TwkFlips [isoU 1, isoX true 0] [isoU 1, isoX true 0] :=
    twkFlips_cupBandCap [isoU 1] [] 0 1 (by omega) (by simp [isoU]) (by simp)
  have hLC : ∀ i, TwkFlips (isoStLC i) (isoStLC i) := fun i ↦ by
    have := twkFlips_cupBandCap [isoU (2 * i - 1), isoU (2 * i + 1)] [] (2 * i - 1) (2 * i + 1)
      (by omega) (by simp [isoU]) (by simp)
    rwa [List.append_nil] at this
  have hDec : TwkFlips (isoStDec (r - 2)) (isoStDec (r - 2)) :=
    twkFlips_cupBandCap _ _ _ _ (by omega) (by simp [isoU]) (by simp [isoN])
  have hInc : TwkFlips (isoStInc (r - 2)) (isoStInc (r - 2)) :=
    twkFlips_cupBandCap _ _ _ _ (by omega) (by simp [isoU]) (by simp [isoN])
  have hR0 : TwkFlips (isoStR0 (r - 2) r) (isoStR0 (r - 2) r) := by
    have := twkFlips_cupBandCap [isoU (2 * (r - 2) + 1), isoU (2 * (r - 2) + 1 + 2 * r)] []
      (2 * (r - 2) + 1) (2 * (r - 2) + 1 + 2 * r) (by omega) (by simp [isoU]) (by simp)
    rwa [List.append_nil] at this
  have hHopf : TwkFlips (twkStHopf (r - 2) r true) (twkStHopf (r - 2) r false) := by
    unfold twkStHopf
    rw [show 2 * (r - 2) + 3 + 2 * r = 2 * (r - 2) + 1 + 2 * r + 2 by omega]
    exact twkFlips_append (twkFlips_cupCap _ (by simp [isoU])) (twkFlips_isoBand_two _)
  have hRound : TwkFlips (isoStRound (r - 2) r) (isoStRound (r - 2) r) :=
    twkFlips_cupBandCap _ _ _ _ (by omega) (by simp [isoU]) (by simp [isoN])
  have hLast : TwkFlips (isoStLast (r - 2) r) (isoStLast (r - 2) r) :=
    twkFlips_cupBandCap [] _ _ _ (by omega) (by simp) (by simp [isoN])
  have hTrc : TwkFlips (isoStTrc (r - 2)) (isoStTrc (r - 2)) :=
    twkFlips_cupBandCap [] _ _ _ (by omega) (by simp) (by simp [isoN])
  have hRd : ∀ i, TwkFlips (isoStRd i) (isoStRd i) := fun i ↦
    twkFlips_cupBandCap [] _ _ _ (by omega) (by simp) (by simp [isoN])
  have hRd0 : TwkFlips isoStRd0 isoStRd0 :=
    twkFlips_cupBandCap [] [isoN 1] 0 1 (by omega) (by simp) (by simp [isoN])
  have hFinal : TwkFlips (twkStFinal true) (twkStFinal false) :=
    twkFlips_append (twkFlips_isoBand_two 1) (twkFlips_cupCap _ (by simp [isoN]))
  unfold twkStripTail
  exact twkFlips_append h0 (twkFlips_append (twkFlips_append (twkFlips_append (twkFlips_append
    (twkFlips_append (twkFlips_append (twkFlips_append (twkFlips_append (twkFlips_append
    (twkFlips_append (twkFlips_append
      (twkFlips_flatMap _ _ _ fun i _ ↦ hLC (i + 1)) (hLC _))
      (twkFlips_phaseTwoBlk hDec _)) (twkFlips_phaseTwoBlk hInc _)) hR0) hHopf)
      (twkFlips_phaseTwoBlk hRound _)) hLast) hTrc)
      (twkFlips_flatMap _ _ _ fun i _ ↦ hRd (i + 1))) hRd0) hFinal)

/-- With the clasp sign `σ` and no twist the blocks are those of `pairBlocks` with the Hopf
letters of sign `σ`. -/
private theorem twBlocks_zero_eq_map_twKPosFence {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    twBlocks r s 0 σ = (pairBlocks r s).map (twClaspBlock σ) := by
  conv_rhs => rw [pairBlocks_eq_head_cons h]
  rw [twBlocks, twChain, ite_eq_left rfl]
  rfl

/-- The fence word of the untwisted list with clasp sign `σ` in closed form, `r ≥ 3`. -/
theorem twStripTail_eq_twkStripTail {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (σ : Bool) :
    twStripTail r s σ = twkStripTail r s σ := by
  have htrue : twStripTail r s true = twkStripTail r s true := by
    rw [twStripTail_true h hr, ← twkStripTail_true]
    rfl
  cases σ with
  | true => exact htrue
  | false =>
    have hband : ∀ i j, SBlock.band i j ∈ pairBlocks r s → i < j := fun i j hb ↦
      (pairBlocks_valid h _ hb).1
    have hneg : ∀ i, SBlock.neg i ∈ pairBlocks r s → 1 ≤ i := by
      intro i hi
      have hc : 1 ≤ pairC r s := by
        obtain ⟨h2, hrs, -⟩ := h
        exact Nat.mul_pos (by omega) (by omega)
      simp only [pairBlocks, List.mem_append, List.mem_map, List.mem_cons, List.mem_range,
        reduceCtorEq, and_false, exists_false, false_or, or_false, SBlock.neg.injEq,
        List.not_mem_nil] at hi
      simp only [pairTop] at hi
      omega
    have hF := twkFlips_eq (twkFlips_isoFenceWord (n := pairStrands r s - 1) hband hneg)
    rw [← twBlocks_zero_eq_map_twKPosFence h, ← twBlocks_zero_eq_map_twKPosFence h,
      isoFenceWord_twBlocks_zero h, isoFenceWord_twBlocks_zero h, htrue,
      twkFlips_eq (twkFlips_twkStripTail r s (by omega))] at hF
    exact (List.append_cancel_left hF).symm

end AJConjecture
