import Mathlib
import AJHandoff.TorusKnot.PairKIsoEndGadget
import AJHandoff.TorusKnot.PairKIsoParkEndMacros
import AJFamily.Skein.TorusPhaseTwoFinishMacros

/-!
# Stage E: the conjugation of the clasp is removed

The clasp arrives at the top end as `isoClaspU = +0 · claspWord · −0` (stage G); no local move
removes the conjugation (it changes the operator at thickness `2`), and one `kink` is needed
(rotation `2 → 0`). This is stage E of the library for `r = 2` (`phaseTwo_stageE`), with the
doubled core of `pairCore r s` in place of the library's band:

1. `morseReach_pairWG2_WE1`: macro `E1` of the library (`morseReach_phaseTwoMacroE1`, whose left
   side is `isoE1L`: the last two half twists, `isoClaspU`, the last cap) turns the window into the
   clasp with `c₁ = u1 −2 n1` between the last two half twists and `c₂ = u2 +3 n2` on the left
   leg of the cup of the clasp (framed after `[u1] · morseDouble (pairCore) · (−0)^{2C-2}`).
2. `morseReach_pairWE1_WE3`: `c₂` moves to the return strand (`morseReach_isoPark_toR1`, framed),
   down the return strand past the half twists (`morseReach_comm`) and past the doubled core
   (`morseReach_isoBead_commL` with `b = 1`: the return strand lies right of the core, which fits
   on two strands), and around the first cup onto the right edge (`morseReach_isoPark_cupL`).
3. `morseReach_pairWE3_WE4`: the curl `rp = isoCurlR true 1` travels along the whole knot
   (`morseReach_park_bottomToTop` with the bottom stack `[rp]` and the top stack
   `t^{C-1} · ec`, `ec = −0 · c₁ · −0 · claspWord`; `pairParkW_empty`).
4. `morseReach_pairWE4_WE`: the curl passes the `2C - 1` half twists (`C - 1` times
   `morseReach_isoPark_pastPair`, then `morseReach_isoPark_pastOdd`, which moves it to the strand
   `0`) and cancels `c₁` at the clasp (`morseReach_isoPark_cancel`, one `kink`).

All junction words validated (`SCR/ISO2/tools/endgame.py`): Kauffman bracket (thickness one) and
writhe of `pairWC` for `(3,4), (3,5), (4,5), (5,6), (3,7)`; all macros at thickness one and two.
-/

namespace AJConjecture

/-- Macro `E1` (the library macro). -/
theorem morseReach_isoMacroE1 : MorseReach 3 isoE1L isoE1R := by
  have hl : isoE1L = phaseTwoMacroE1_lhs := by decide
  have hr : isoE1R = phaseTwoMacroE1_rhs := by decide
  rw [hl, hr]
  exact morseReach_phaseTwoMacroE1


/-- The double of a fitting letter fits on twice the strands and doubles their number. -/
private theorem morseDoubleLetter_fits_endFix (n : ℕ) (l : MorseLetter)
    (h : l.2 + morseKindIn l.1 ≤ n) :
    morseFits (2 * n) (morseDoubleLetter l) = true ∧
      morseOut (2 * n) (morseDoubleLetter l) = 2 * morseLetterOut n l := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [morseKindIn] at h
    simp only [morseDoubleLetter, morseFits, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩, by omega⟩
  | cap =>
    simp only [morseKindIn] at h
    simp only [morseDoubleLetter, morseFits, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩, by omega⟩
  | cross s =>
    simp only [morseKindIn] at h
    cases s <;>
    · simp only [morseDoubleLetter, cable, cableGen, morseOfBraid, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte,
        show List.range 2 = [0, 1] from rfl, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil, List.flatMap_cons, morseFits, morseOut,
        morseLetterOut, morseKindIn, morseKindOut, Bool.and_true, Bool.and_eq_true]
      exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega), decide_eq_true (by omega),
        decide_eq_true (by omega)⟩, by omega⟩

/-- The double of a fitting word fits on twice the strands. -/
private theorem morseDouble_fits_endFix :
    ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
      morseFits (2 * n) (morseDouble w) = true ∧
        morseOut (2 * n) (morseDouble w) = 2 * morseOut n w
  | [], _, _ => ⟨rfl, rfl⟩
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    have hl := morseDoubleLetter_fits_endFix n l h.1
    have hw := morseDouble_fits_endFix w _ h.2
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from List.flatMap_cons,
      morseFits_append, morseOut_append, hl.1, hl.2, hw.1, hw.2]
    exact ⟨rfl, rfl⟩

/-- The doubled core fits on two strands, with idle strands on the right. -/
private theorem morseFits_dcore_endFix {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (e : ℕ) :
    morseFits (2 + e) (morseDouble (pairCore r s)) = true ∧
      morseOut (2 + e) (morseDouble (pairCore r s)) = 2 + e := by
  have hc := morseFits_pairCore h hr
  have hd := morseDouble_fits_endFix (pairCore r s) 1 hc.1
  rw [hc.2] at hd
  have h1 := morseFits_add_right_iso 2 e _ hd.1
  have h2 := morseOut_add_right 2 e _ hd.1
  rw [hd.2] at h2
  exact ⟨h1, h2⟩

/-- The strands after the first cup, the doubled core and some half twists. -/
private theorem morseOut_prefix_endFix {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (k : ℕ) :
    morseOut 1 ([isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate k (isoX false 0)) = 3 := by
  rw [morseOut_append, morseOut_append, show morseOut 1 [isoU 1] = 2 + 1 from rfl,
    (morseFits_dcore_endFix h hr 1).2]
  exact morseOut_of_cross _ _ (fun b hb ↦ ⟨false, by rw [List.eq_of_mem_replicate hb]; rfl⟩)

/-- The travelling curl passes pairs of half twists. -/
private theorem morseReach_pastPairs_endFix (v : MorseWord) : ∀ (k : ℕ) (u : MorseWord),
    morseOut 1 u = 3 →
    MorseReach 1 (u ++ isoCurlR true 1 ++ List.replicate (2 * k) (isoX false 0) ++ v)
      (u ++ List.replicate (2 * k) (isoX false 0) ++ isoCurlR true 1 ++ v)
  | 0, u, _ => by simpa using morseReach_refl 1 _
  | k + 1, u, hu => by
    have h1 := morseReach_frame 3 1 0 0 u (List.replicate (2 * k) (isoX false 0) ++ v) _ _
      morseReach_isoPark_pastPair (by decide) (by rw [hu])
    have h2 := morseReach_pastPairs_endFix v k (u ++ [isoX false 0, isoX false 0])
      (by rw [morseOut_append, hu]; rfl)
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, List.replicate_add]
    simp only [morseShiftWord_zero_iso, List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- `pairWG2 → pairWE1` (macro `E1`). -/
theorem morseReach_pairWG2_WE1 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWG2 r s) (pairWE1 r s) := by
  have hC : 1 ≤ (r - 1) * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by have := h.2.1; omega))
  have hf := morseReach_frame 3 1 0 0
    ([isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s) - 2) (isoX false 0))
    [] _ _ morseReach_isoMacroE1 (by decide) (by rw [morseOut_prefix_endFix h hr])
  rw [pairWG2, pairWE1, show 2 * ((r - 1) * s) = 2 * ((r - 1) * s) - 2 + 2 by omega,
    List.replicate_add, Nat.add_sub_cancel]
  simpa only [isoE1L, morseShiftWord_zero_iso, List.append_nil, List.append_assoc,
    show List.replicate 2 (isoX false 0) = [isoX false 0, isoX false 0] from rfl] using hf


/-- `pairWE1 → pairWE2 → pairWE3` (to the return strand, down it, around the first cup). -/
theorem morseReach_pairWE1_WE3 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWE1 r s) (pairWE3 r s) := by
  have hC : 1 ≤ (r - 1) * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by have := h.2.1; omega))
  -- the curl `c₂` moves to the return strand
  have h1 := morseReach_frame 3 1 0 0
    ([isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s) - 2) (isoX false 0) ++
      [isoX false 0]) [] _ _ morseReach_isoPark_toR1 (by decide)
    (by rw [List.append_assoc _ _ [isoX false 0], ← List.replicate_succ',
      morseOut_prefix_endFix h hr])
  -- down the return strand past the half twists
  have hX : ∀ b ∈ List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0),
      ∃ s, b.1 = MorseKind.cross s := fun b hb ↦ ⟨false, by rw [List.eq_of_mem_replicate hb]; rfl⟩
  have h2 := morseReach_comm 1 ([isoU 1] ++ morseDouble (pairCore r s))
    (List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0)) (isoCurlL true 2)
    (isoCurlL false 1 ++ [isoX false 0] ++ claspWord ++ [isoN 1]) hX
    (fun b hb a ha ↦ by
      rw [List.eq_of_mem_replicate hb]
      simp only [isoCurlL, isoU, isoX, isoN, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> simp [isoX])
    (by
      rw [morseOut_append, show morseOut 1 [isoU 1] = 2 + 1 from rfl,
        (morseFits_dcore_endFix h hr 1).2, morseFits_append]
      have : morseOut 3 (isoCurlL true 2) = 3 := by decide
      rw [this, morseFits_of_cross _ _ hX (fun b hb ↦ by rw [List.eq_of_mem_replicate hb]; simp [isoX])]
      decide)
  -- past the doubled core
  have h3 := morseReach_isoBead_commL 1 2 1 0 (isoCurlL true 0) [isoU 1]
    (morseDouble (pairCore r s))
    (List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) ++ isoCurlL false 1 ++ [isoX false 0] ++
      claspWord ++ [isoN 1]) (by decide) (by decide) (morseFits_dcore_endFix h hr 0).1 rfl
  rw [(morseFits_dcore_endFix h hr 0).2] at h3
  rw [show morseShiftWord (2 + 0) (isoCurlL true 0) = isoCurlL true 2 from rfl] at h3
  -- around the first cup onto the right edge
  have h4 := morseReach_frame 1 1 0 0 []
    (morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) ++
      isoCurlL false 1 ++ [isoX false 0] ++ claspWord ++ [isoN 1]) _ _ morseReach_isoPark_cupL
    (by decide) rfl
  rw [pairWE1, pairWE3, isoE1R]
  have e : List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) =
      List.replicate (2 * ((r - 1) * s) - 2) (isoX false 0) ++ [isoX false 0] := by
    rw [← List.replicate_succ']; congr 1; omega
  rw [e] at h2 h3 h4 ⊢
  simp only [morseShiftWord_zero_iso, List.append_nil, List.nil_append, List.append_assoc]
    at h1 h2 h3 h4 ⊢
  exact morseReach_trans h1 <| morseReach_trans (morseReach_symm h2) <|
    morseReach_trans (morseReach_symm h3) h4


/-- `pairWE3 → pairWE4` (the curl travels along the knot). -/
theorem morseReach_pairWE3_WE4 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWE3 r s) (pairWE4 r s) := by
  have hC : 1 ≤ (r - 1) * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by have := h.2.1; omega))
  have h1 := morseReach_park_bottomToTop h hr [.rp]
    (List.replicate ((r - 1) * s - 1) .t ++ [.ec])
  rw [pairParkW_empty, pairParkW_empty] at h1
  have hT := isoBeadsWord_replicate_t ((r - 1) * s - 1)
  simp only [isoBeadsWord] at hT
  have e : List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) =
      List.replicate (2 * ((r - 1) * s - 1)) (isoX false 0) ++ [isoX false 0] := by
    rw [← List.replicate_succ']
    congr 1
    omega
  simpa only [pairWE3, pairWE4, isoBeadsWord, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, isoBeadWord, hT, e, List.append_assoc, List.append_nil, List.nil_append,
    List.cons_append] using h1

/-- `pairWE4 → pairWE5 → pairWE` (past the half twists, cancellation at the clasp). -/
theorem morseReach_pairWE4_WE {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWE4 r s) (pairWE r s) := by
  have hC : 1 ≤ (r - 1) * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by have := h.2.1; omega))
  set C := (r - 1) * s with hCdef
  -- the curl passes `C - 1` pairs of half twists
  have h1 := morseReach_pastPairs_endFix ([isoX false 0] ++ isoCurlL false 1 ++ [isoX false 0] ++
    claspWord ++ [isoN 1]) (C - 1) ([isoU 1] ++ morseDouble (pairCore r s))
    (by simpa using morseOut_prefix_endFix h hr 0)
  -- the last half twist
  have h2 := morseReach_frame 3 1 0 0
    ([isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * (C - 1)) (isoX false 0))
    (isoCurlL false 1 ++ [isoX false 0] ++ claspWord ++ [isoN 1]) _ _ morseReach_isoPark_pastOdd
    (by decide) (by rw [morseOut_prefix_endFix h hr])
  -- the curl cancels `c₁` at the clasp
  have h3 := morseReach_frame 3 1 0 0
    ([isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * (C - 1)) (isoX false 0) ++
      [isoX false 0]) [isoN 1] _ _ morseReach_isoPark_cancel (by decide)
    (by rw [List.append_assoc _ _ [isoX false 0], ← List.replicate_succ',
      morseOut_prefix_endFix h hr])
  rw [pairWE4, pairWE, show 2 * C - 1 = 2 * (C - 1) + 1 by omega,
    show 2 * C = 2 * (C - 1) + 1 + 1 by omega, List.replicate_succ', List.replicate_succ',
    List.replicate_succ']
  simp only [morseShiftWord_zero_iso, List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 h3


end AJConjecture
