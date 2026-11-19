import Mathlib
import AJHandoff.TorusKnot.PairKIsoCupRise
import AJHandoff.TorusKnot.PairKIsoCapFall
import AJHandoff.TorusKnot.PairKIsoThin

/-!
# Dead-end retraction

`morseReach_isoDeadEnd_step`: releasing the disc `j + 1` takes `isoFenceAux n B (j + 1)` to
`isoFenceAux n B j`: its cup (last of the bottom row) rises block by block to its first block
(`morseReach_isoFence_cupBlock_of_le`), its cap (first of the top row) falls to its last block
(`morseReach_isoFence_capBlock`); between the two the blocks of both words agree. The hypothesis
`isoFirst < isoLast` (every disc carries at least two blocks) holds for a braided annulus with a
plumbed Hopf band.

`morseReach_isoPhaseOne` composes thinning and retraction: the long closure of a block word reaches
its fence word. Generic in the block list.
-/

namespace AJConjecture

/-- The block hypotheses of the retraction: valid blocks, and every disc carries two blocks. -/
def IsoFenceable (n : ℕ) (B : List SBlock) : Prop :=
  (∀ b ∈ B, b.Valid (n + 1)) ∧
    ∀ m, 1 ≤ m → m ≤ n → isoFirst B m < isoLast B m ∧ isoLast B m < B.length

/-- One move preserves fitting. -/
private theorem morseFits_morseApply_deadEnd (n₀ : ℕ) (w w' : MorseWord) (mv : MorseMove)
    (h : morseApply n₀ w mv = some w') (hw : morseFits n₀ w = true) :
    morseFits n₀ w' = true := by
  obtain ⟨p, r, bk⟩ := mv
  obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n₀ w w' p r bk h
  have ho : morseOut (morseOut n₀ a) (if bk then morseRuleRhs r else morseRuleLhs r) =
      morseOut (morseOut n₀ a) (if bk then morseRuleLhs r else morseRuleRhs r) := by
    cases bk
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs hd ⊢
      exact morseOut_rule_sides r _ hok hs hd
    · simp only [↓reduceIte] at hs hd ⊢
      exact (morseOut_rule_sides r _ hok hd hs).symm
  rw [morseFits_append, morseFits_append, Bool.and_eq_true, Bool.and_eq_true,
    morseOut_append] at hw ⊢
  rw [← ho]
  exact ⟨⟨hw.1.1, hd⟩, hw.2⟩

/-- Reachability preserves fitting. -/
private theorem morseFits_of_morseReach_deadEnd {n₀ : ℕ} {w w' : MorseWord}
    (h : MorseReach n₀ w w') (hw : morseFits n₀ w = true) : morseFits n₀ w' = true := by
  obtain ⟨mvs, h⟩ := h
  induction mvs generalizing w with
  | nil =>
    simp only [morseApplyAll, Option.some.injEq] at h
    rw [← h]
    exact hw
  | cons mv mvs ih =>
    simp only [morseApplyAll] at h
    cases h1 : morseApply n₀ w mv with
    | none => simp [h1] at h
    | some w₁ =>
      rw [h1, Option.bind_some] at h
      exact ih (morseFits_morseApply_deadEnd _ _ _ _ h1 hw) h

/-- The fence blocks of a list of indexed blocks. -/
private def isoFenceBlocks (n : ℕ) (B : List SBlock) (j : ℕ) (L : List (SBlock × ℕ)) :
    MorseWord :=
  L.flatMap fun bk ↦ isoFenceBlock n B j bk.2 bk.1

/-- The fence blocks of a concatenation. -/
private theorem isoFenceBlocks_append (n : ℕ) (B : List SBlock) (j : ℕ)
    (L L' : List (SBlock × ℕ)) :
    isoFenceBlocks n B j (L ++ L') = isoFenceBlocks n B j L ++ isoFenceBlocks n B j L' :=
  List.flatMap_append

/-- The cup of the disc `j + 1` rises past the blocks below its first block. -/
private theorem morseReach_isoDeadEnd_cups {n j : ℕ} {B : List SBlock} (hB : IsoFenceable n B)
    (hj : j < n) : ∀ L : List (SBlock × ℕ),
      (∀ x ∈ L, x.2 < isoFirst B (j + 1) ∧ B[x.2]? = some x.1) → ∀ u v : MorseWord,
      morseFits 1 (u ++ [isoU (2 * j + 1)] ++ isoFenceBlocks n B (j + 1) L ++ v) = true →
      MorseReach 1 (u ++ [isoU (2 * j + 1)] ++ isoFenceBlocks n B (j + 1) L ++ v)
        (u ++ isoFenceBlocks n B j L ++ [isoU (2 * j + 1)] ++ v) := by
  have hfl := hB.2 (j + 1) (by omega) (by omega)
  intro L
  induction L with
  | nil => intro _ u v _; simpa [isoFenceBlocks] using morseReach_refl 1 _
  | cons x L ih =>
    intro hL u v hfit
    obtain ⟨hk, hbk⟩ := hL x List.mem_cons_self
    have hfit' := hfit
    simp only [isoFenceBlocks, List.flatMap_cons] at hfit'
    rw [show u ++ [isoU (2 * j + 1)] ++ (isoFenceBlock n B (j + 1) x.2 x.1 ++
      List.flatMap (fun bk ↦ isoFenceBlock n B (j + 1) bk.2 bk.1) L) ++ v =
      u ++ [isoU (2 * j + 1)] ++ isoFenceBlock n B (j + 1) x.2 x.1 ++
      (List.flatMap (fun bk ↦ isoFenceBlock n B (j + 1) bk.2 bk.1) L ++ v) by simp,
      morseFits_append, Bool.and_eq_true] at hfit'
    have h1 := morseReach_isoFence_cupBlock_of_le hB.1 hk hfl.1.le hbk u
      (isoFenceBlocks n B (j + 1) L ++ v) hfit'.1
    have hw : u ++ [isoU (2 * j + 1)] ++ isoFenceBlocks n B (j + 1) (x :: L) ++ v =
        u ++ [isoU (2 * j + 1)] ++ isoFenceBlock n B (j + 1) x.2 x.1 ++
          (isoFenceBlocks n B (j + 1) L ++ v) := by
      simp [isoFenceBlocks]
    rw [hw] at hfit ⊢
    have hfit2 := morseFits_of_morseReach_deadEnd h1 hfit
    have h2 := ih (fun y hy ↦ hL y (List.mem_cons_of_mem _ hy))
      (u ++ isoFenceBlock n B j x.2 x.1) v (by simpa using hfit2)
    have e : u ++ isoFenceBlocks n B j (x :: L) ++ [isoU (2 * j + 1)] ++ v =
        u ++ isoFenceBlock n B j x.2 x.1 ++ isoFenceBlocks n B j L ++ [isoU (2 * j + 1)] ++ v := by
      simp [isoFenceBlocks]
    rw [e]
    simp only [List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- The cap of the disc `j + 1` falls past the blocks above its last block. -/
private theorem morseReach_isoDeadEnd_caps {n j : ℕ} {B : List SBlock} (hB : IsoFenceable n B)
    (hj : j < n) : ∀ L : List (SBlock × ℕ),
      (∀ x ∈ L, isoLast B (j + 1) < x.2 ∧ B[x.2]? = some x.1) → ∀ u v : MorseWord,
      morseFits 1 (u ++ isoFenceBlocks n B (j + 1) L ++ [isoN (2 * j + 1)] ++ v) = true →
      MorseReach 1 (u ++ isoFenceBlocks n B (j + 1) L ++ [isoN (2 * j + 1)] ++ v)
        (u ++ [isoN (2 * j + 1)] ++ isoFenceBlocks n B j L ++ v) := by
  intro L
  induction L with
  | nil => intro _ u v _; simpa [isoFenceBlocks] using morseReach_refl 1 _
  | cons x L ih =>
    intro hL u v hfit
    obtain ⟨hk, hbk⟩ := hL x List.mem_cons_self
    have hw : u ++ isoFenceBlocks n B (j + 1) (x :: L) ++ [isoN (2 * j + 1)] ++ v =
        u ++ isoFenceBlock n B (j + 1) x.2 x.1 ++ isoFenceBlocks n B (j + 1) L ++
          [isoN (2 * j + 1)] ++ v := by
      simp [isoFenceBlocks]
    rw [hw] at hfit ⊢
    have h1 := ih (fun y hy ↦ hL y (List.mem_cons_of_mem _ hy))
      (u ++ isoFenceBlock n B (j + 1) x.2 x.1) v hfit
    have hfit2 := morseFits_of_morseReach_deadEnd h1 hfit
    rw [show u ++ isoFenceBlock n B (j + 1) x.2 x.1 ++ [isoN (2 * j + 1)] ++
      isoFenceBlocks n B j L ++ v = u ++ isoFenceBlock n B (j + 1) x.2 x.1 ++
      [isoN (2 * j + 1)] ++ (isoFenceBlocks n B j L ++ v) by simp,
      morseFits_append, Bool.and_eq_true] at hfit2
    have h2 := morseReach_isoFence_capBlock hB.1 hj hk hbk u (isoFenceBlocks n B j L ++ v)
      hfit2.1
    have e : u ++ [isoN (2 * j + 1)] ++ isoFenceBlocks n B j (x :: L) ++ v =
        u ++ [isoN (2 * j + 1)] ++ isoFenceBlock n B j x.2 x.1 ++
          (isoFenceBlocks n B j L ++ v) := by
      simp [isoFenceBlocks]
    rw [e]
    simp only [List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- At its first block the disc `j + 1` is opened by the block. -/
private theorem isoFenceBlock_first_deadEnd {n j : ℕ} {B : List SBlock} (hB : IsoFenceable n B)
    (hj : j < n) (b : SBlock) :
    [isoU (2 * j + 1)] ++ isoFenceBlock n B (j + 1) (isoFirst B (j + 1)) b =
      isoFenceBlock n B j (isoFirst B (j + 1)) b := by
  have hfl := hB.2 (j + 1) (by omega) (by omega)
  have hp := isoPos_succ_of_open B j (isoFirst B (j + 1)) ⟨le_rfl, hfl.1.le⟩
  simp only [isoFenceBlock, hp, filter_isoDisc_cons n j _ (isoFirst B) rfl hj,
    filter_isoDisc_succ (n + 1) j (isoFirst B (j + 1)) (isoLast B) (by omega), List.map_cons,
    isoPos_succ_self, List.cons_append, List.nil_append]

/-- Between its first and last block the disc `j + 1` is open in both fence words. -/
private theorem isoFenceBlock_mid_deadEnd {n j k : ℕ} {B : List SBlock}
    (hk : isoFirst B (j + 1) < k) (hk' : k < isoLast B (j + 1)) (b : SBlock) :
    isoFenceBlock n B (j + 1) k b = isoFenceBlock n B j k b := by
  have hp := isoPos_succ_of_open B j k ⟨hk.le, hk'.le⟩
  simp only [isoFenceBlock, hp, filter_isoDisc_succ (n + 1) j k (isoFirst B) (by omega),
    filter_isoDisc_succ (n + 1) j k (isoLast B) (by omega)]

/-- At its last block the disc `j + 1` is closed by the block. -/
private theorem isoFenceBlock_last_deadEnd {n j : ℕ} {B : List SBlock} (hB : IsoFenceable n B)
    (hj : j < n) (b : SBlock) :
    isoFenceBlock n B (j + 1) (isoLast B (j + 1)) b ++ [isoN (2 * j + 1)] =
      isoFenceBlock n B j (isoLast B (j + 1)) b := by
  have hfl := hB.2 (j + 1) (by omega) (by omega)
  have hp := isoPos_succ_of_open B j (isoLast B (j + 1)) ⟨hfl.1.le, le_rfl⟩
  simp only [isoFenceBlock, hp, filter_isoDisc_cons n j _ (isoLast B) rfl hj,
    filter_isoDisc_succ (n + 1) j (isoLast B (j + 1)) (isoFirst B) (by omega), List.reverse_cons,
    List.map_append,
    List.map_singleton, isoPos_succ_self, List.append_assoc]

/-- An indexed list splits at a position. -/
private theorem zipIdx_split_deadEnd (B : List SBlock) (i m : ℕ) (hi : i < B.length) :
    B.zipIdx m = (B.take i).zipIdx m ++ (B[i], m + i) :: (B.drop (i + 1)).zipIdx (m + i + 1) := by
  conv_lhs => rw [← List.take_append_drop i B]
  rw [List.zipIdx_append, List.drop_eq_getElem_cons (by simpa using hi), List.zipIdx_cons,
    List.length_take, min_eq_left hi.le]

/-- The bottom row of the fence word with `j + 1` discs kept open. -/
private theorem isoFenceAux_rows_deadEnd {n j : ℕ} (B : List SBlock) (hj : j < n) :
    isoFenceAux n B (j + 1) = (List.range j).map (fun t ↦ isoU (2 * t + 1)) ++
      [isoU (2 * j + 1)] ++ isoFenceBlocks n B (j + 1) B.zipIdx ++ [isoN (2 * j + 1)] ++
      (List.range j).reverse.map (fun t ↦ isoN (2 * t + 1)) ∧
    isoFenceAux n B j = (List.range j).map (fun t ↦ isoU (2 * t + 1)) ++
      isoFenceBlocks n B j B.zipIdx ++ (List.range j).reverse.map (fun t ↦ isoN (2 * t + 1)) := by
  refine ⟨?_, ?_⟩
  · simp only [isoFenceAux, isoFenceBlocks, min_eq_left (show j + 1 ≤ n by omega),
      List.range_succ, List.map_append, List.reverse_append,
      List.reverse_singleton, List.append_assoc, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil]
  · simp only [isoFenceAux, isoFenceBlocks, min_eq_left hj.le]

/-- Releasing the disc `j + 1`, for a fitting word. -/
private theorem morseReach_isoDeadEnd_step_of_fits {n j : ℕ} {B : List SBlock}
    (hB : IsoFenceable n B) (hj : j < n) (hfit : morseFits 1 (isoFenceAux n B (j + 1)) = true) :
    MorseReach 1 (isoFenceAux n B (j + 1)) (isoFenceAux n B j) := by
  have hfl := hB.2 (j + 1) (by omega) (by omega)
  set f := isoFirst B (j + 1) with hf
  set l := isoLast B (j + 1) with hl
  have hsplit : B.zipIdx = (B.take f).zipIdx ++ (B[f]'(by omega), f) ::
      (((B.drop (f + 1)).take (l - f - 1)).zipIdx (f + 1) ++
        ((B.drop (f + 1))[l - f - 1]'(by simp; omega), l) ::
          ((B.drop (f + 1)).drop (l - f - 1 + 1)).zipIdx (l + 1)) := by
    rw [zipIdx_split_deadEnd B f 0 (by omega), Nat.zero_add,
      zipIdx_split_deadEnd (B.drop (f + 1)) (l - f - 1) (f + 1) (by simp; omega)]
    rw [show f + 1 + (l - f - 1) = l by omega]
  set L0 := (B.take f).zipIdx with hL0
  set Lm := ((B.drop (f + 1)).take (l - f - 1)).zipIdx (f + 1) with hLm
  set Le := ((B.drop (f + 1)).drop (l - f - 1 + 1)).zipIdx (l + 1) with hLe
  have hL0m : ∀ x ∈ L0, x.2 < f ∧ B[x.2]? = some x.1 := by
    intro x hx
    rw [hL0, List.mem_zipIdx_iff_le_and_getElem?_sub, Nat.sub_zero, List.getElem?_take] at hx
    split_ifs at hx with h
    · exact ⟨h, hx.2⟩
    · simp at hx
  have hLmm : ∀ x ∈ Lm, f < x.2 ∧ x.2 < l := by
    intro x hx
    rw [hLm, List.mem_zipIdx_iff_le_and_getElem?_sub, List.getElem?_take] at hx
    split_ifs at hx with h
    · omega
    · simp at hx
  have hLem : ∀ x ∈ Le, l < x.2 ∧ B[x.2]? = some x.1 := by
    intro x hx
    rw [hLe, List.mem_zipIdx_iff_le_and_getElem?_sub, List.drop_drop, List.getElem?_drop] at hx
    refine ⟨by omega, ?_⟩
    rw [← hx.2]
    congr 1
    omega
  have hmid : isoFenceBlocks n B (j + 1) Lm = isoFenceBlocks n B j Lm :=
    List.flatMap_congr fun x hx ↦
      isoFenceBlock_mid_deadEnd (hLmm x hx).1 (hLmm x hx).2 x.1
  obtain ⟨hW1, hW0⟩ := isoFenceAux_rows_deadEnd B hj
  set R := (List.range j).map (fun t ↦ isoU (2 * t + 1)) with hR
  set Rc := (List.range j).reverse.map (fun t ↦ isoN (2 * t + 1)) with hRc
  set bf := B[f]'(by omega)
  set bl := (B.drop (f + 1))[l - f - 1]'(by simp; omega)
  have hblk : ∀ j', isoFenceBlocks n B j' B.zipIdx = isoFenceBlocks n B j' L0 ++
      isoFenceBlock n B j' f bf ++ isoFenceBlocks n B j' Lm ++ isoFenceBlock n B j' l bl ++
      isoFenceBlocks n B j' Le := by
    intro j'
    rw [hsplit]
    simp [isoFenceBlocks, List.flatMap_append]
  rw [hblk] at hW1 hW0
  rw [hW1] at hfit ⊢
  rw [hW0]
  set q := 2 * j + 1 with hq
  have h1 := morseReach_isoDeadEnd_cups hB hj L0 hL0m R
    (isoFenceBlock n B (j + 1) f bf ++ isoFenceBlocks n B (j + 1) Lm ++
      isoFenceBlock n B (j + 1) l bl ++ isoFenceBlocks n B (j + 1) Le ++ [isoN q] ++ Rc)
    (by simpa only [List.append_assoc] using hfit)
  have hfit2 := morseFits_of_morseReach_deadEnd h1 (by simpa only [List.append_assoc] using hfit)
  have e2 : R ++ isoFenceBlocks n B j L0 ++ [isoU q] ++
      (isoFenceBlock n B (j + 1) f bf ++ isoFenceBlocks n B (j + 1) Lm ++
        isoFenceBlock n B (j + 1) l bl ++ isoFenceBlocks n B (j + 1) Le ++ [isoN q] ++ Rc) =
      (R ++ isoFenceBlocks n B j L0 ++ isoFenceBlock n B j f bf ++ isoFenceBlocks n B j Lm ++
        isoFenceBlock n B (j + 1) l bl) ++ isoFenceBlocks n B (j + 1) Le ++ [isoN q] ++ Rc := by
    rw [← isoFenceBlock_first_deadEnd hB hj bf, hmid]
    simp only [List.append_assoc]
    rfl
  rw [e2] at h1 hfit2
  have h2 := morseReach_isoDeadEnd_caps hB hj Le hLem
    (R ++ isoFenceBlocks n B j L0 ++ isoFenceBlock n B j f bf ++ isoFenceBlocks n B j Lm ++
      isoFenceBlock n B (j + 1) l bl) Rc hfit2
  have e3 : (R ++ isoFenceBlocks n B j L0 ++ isoFenceBlock n B j f bf ++
      isoFenceBlocks n B j Lm ++ isoFenceBlock n B (j + 1) l bl) ++ [isoN q] ++
      isoFenceBlocks n B j Le ++ Rc =
      R ++ (isoFenceBlocks n B j L0 ++ isoFenceBlock n B j f bf ++ isoFenceBlocks n B j Lm ++
        isoFenceBlock n B j l bl ++ isoFenceBlocks n B j Le) ++ Rc := by
    rw [← isoFenceBlock_last_deadEnd hB hj bl]
    simp only [List.append_assoc]
    rfl
  rw [e3] at h2
  have e1 : R ++ [isoU q] ++ (isoFenceBlocks n B (j + 1) L0 ++ isoFenceBlock n B (j + 1) f bf ++
      isoFenceBlocks n B (j + 1) Lm ++ isoFenceBlock n B (j + 1) l bl ++
      isoFenceBlocks n B (j + 1) Le) ++ [isoN q] ++ Rc =
      R ++ [isoU q] ++ isoFenceBlocks n B (j + 1) L0 ++
      (isoFenceBlock n B (j + 1) f bf ++ isoFenceBlocks n B (j + 1) Lm ++
        isoFenceBlock n B (j + 1) l bl ++ isoFenceBlocks n B (j + 1) Le ++ [isoN q] ++ Rc) := by
    simp only [List.append_assoc]
  rw [e1]
  exact morseReach_trans h1 h2

/-- Every fence word with kept discs fits, from one strand to one strand. -/
private theorem morseFits_isoFenceAux_deadEnd {n : ℕ} {B : List SBlock} (hB : IsoFenceable n B)
    (j : ℕ) (hj : j ≤ n) : morseFits 1 (isoFenceAux n B j) = true := by
  have key : ∀ m, m ≤ n → morseFits 1 (isoFenceAux n B (n - m)) = true := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, isoFenceAux_top hB.1, isoThinWord]
      exact (morseFits_isoThinPartial hB.1 (Nat.zero_le n)).1
    | succ m ih =>
      intro hm
      have hf := ih (by omega)
      rw [show n - m = n - (m + 1) + 1 by omega] at hf
      exact morseFits_of_morseReach_deadEnd
        (morseReach_isoDeadEnd_step_of_fits hB (by omega) hf) hf
  have := key (n - j) (by omega)
  rwa [show n - (n - j) = j by omega] at this

/-- Releasing the disc `j + 1`. -/
theorem morseReach_isoDeadEnd_step {n j : ℕ} {B : List SBlock} (hB : IsoFenceable n B)
    (hj : j < n) : MorseReach 1 (isoFenceAux n B (j + 1)) (isoFenceAux n B j) :=
  morseReach_isoDeadEnd_step_of_fits hB hj (morseFits_isoFenceAux_deadEnd hB (j + 1) hj)

/-- Dead-end retraction (generic): the thin word reaches the fence word. -/
theorem morseReach_isoDeadEnd {n : ℕ} {B : List SBlock} (hB : IsoFenceable n B) :
    MorseReach 1 (isoThinWord n B) (isoFenceWord n B) := by
  have key : ∀ m, m ≤ n → MorseReach 1 (isoFenceAux n B n) (isoFenceAux n B (n - m)) := by
    intro m
    induction m with
    | zero => exact fun _ ↦ morseReach_refl 1 _
    | succ m ih =>
      intro hm
      have h := morseReach_isoDeadEnd_step hB (show n - (m + 1) < n by omega)
      rw [show n - (m + 1) + 1 = n - m by omega] at h
      exact morseReach_trans (ih (by omega)) h
  have := key n le_rfl
  rwa [Nat.sub_self, isoFenceAux_top hB.1] at this

/-- Phase I (generic): the long closure of a block word reaches its fence word. -/
theorem morseReach_isoPhaseOne {n : ℕ} {B : List SBlock} (hB : IsoFenceable n B) :
    MorseReach 1 (morseLongClosure (n + 1) (blocksWord B)) (isoFenceWord n B) :=
  morseReach_trans (morseReach_isoThin hB.1) (morseReach_isoDeadEnd hB)

end AJConjecture
