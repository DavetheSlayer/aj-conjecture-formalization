import Mathlib
import AJHandoff.TorusKnot.PairKIsoBeadStep
import AJHandoff.TorusKnot.PairKIsoParkComm

/-!
# Bead journeys along a doubled long knot (generic)

`morseReach_isoBandBead_journey`: a band bead entering the band at the bottom end of
`morseDouble G` (`G` a connected long knot) slides along the whole knot to the top end, rotated by
`π` if `G` has an odd number of cups and caps. Proof: induction along the trace of `G`
(`isoTraceStep`), one letter step per trace step (`PairKIsoBeadStep`; letters of `G` off the
current strand are passed by exchanges, with the position of the bead shifted by `±2` at cups and
caps on its left). `morseReach_isoEdgeBead_journey` is the same for a curl on the right edge (a
one-strand bead passes crossings by `morseReach_pass` with a one-letter walk, cups and caps by
`cupSlide`/`capSlide` and the curl turning macros of the library, `CAPP`, `CUPP`).
-/

namespace AJConjecture

/-! ### Doubled words and the bead at a segment of the knot -/

/-- A doubled crossing, letter by letter. -/
private theorem morseDoubleLetter_cross_slide (s : Bool) (i : ℕ) :
    morseDoubleLetter (MorseKind.cross s, i) =
      [(MorseKind.cross s, 2 * i + 1), (MorseKind.cross s, if s then 2 * i + 2 else 2 * i),
        (MorseKind.cross s, if s then 2 * i else 2 * i + 2), (MorseKind.cross s, 2 * i + 1)] := by
  cases s <;> simp [morseDoubleLetter, morseOfBraid, cable, cableGen, List.range_succ]

/-- Doubling distributes over concatenation. -/
private theorem morseDouble_append_slide (a b : MorseWord) :
    morseDouble (a ++ b) = morseDouble a ++ morseDouble b := List.flatMap_append

/-- A doubled letter fits on the doubled strands. -/
private theorem morseDoubleLetter_fits_slide (n e : ℕ) (l : MorseLetter)
    (h : l.2 + morseKindIn l.1 ≤ n) :
    morseFits (2 * n + e) (morseDoubleLetter l) = true ∧
      morseOut (2 * n + e) (morseDoubleLetter l) = 2 * morseLetterOut n l + e := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [morseDoubleLetter, morseFits_cons, morseFits_nil, morseOut, morseLetterOut,
      morseKindIn, morseKindOut, and_true] at h ⊢
    omega
  | cap =>
    simp only [morseDoubleLetter, morseFits_cons, morseFits_nil, morseOut, morseLetterOut,
      morseKindIn, morseKindOut, and_true] at h ⊢
    omega
  | cross s =>
    rw [morseDoubleLetter_cross_slide]
    cases s <;> simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, and_true, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;> omega

/-- A doubled word fits on the doubled strands. -/
private theorem morseDouble_fits_slide : ∀ (w : MorseWord) (n e : ℕ), morseFits n w = true →
    morseFits (2 * n + e) (morseDouble w) = true ∧
      morseOut (2 * n + e) (morseDouble w) = 2 * morseOut n w + e
  | [], _, _, _ => ⟨rfl, rfl⟩
  | l :: w, n, e, h => by
    rw [morseFits_cons] at h
    have hl := morseDoubleLetter_fits_slide n e l h.1
    have ih := morseDouble_fits_slide w (morseLetterOut n l) e h.2
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from rfl,
      morseFits_append, morseOut_append, hl.1, hl.2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- A shifted doubled crossing. -/
private theorem morseDouble_cross_shift_slide (s : Bool) (i : ℕ) :
    morseShiftWord (2 * i) (morseDouble [(MorseKind.cross s, 0)]) =
      morseDouble [(MorseKind.cross s, i)] := by
  simp only [morseDouble, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    morseDoubleLetter_cross_slide]
  cases s <;> simp [morseShiftWord, shiftLetter] <;> omega

/-- A band bead passes a doubled crossing of either sign at position `0`, in both directions. -/
private theorem morseReach_beadX_base (s : Bool) (B : MorseWord) (hB : morseFits 2 B = true)
    (hBo : morseOut 2 B = 2) :
    MorseReach 4 (B ++ morseDouble [(MorseKind.cross s, 0)])
        (morseDouble [(MorseKind.cross s, 0)] ++ morseShiftWord 2 B) ∧
      MorseReach 4 (morseShiftWord 2 B ++ morseDouble [(MorseKind.cross s, 0)])
        (morseDouble [(MorseKind.cross s, 0)] ++ B) := by
  cases s with
  | true =>
    have hD : morseDouble [(MorseKind.cross true, 0)] = phaseTwoD := by decide
    rw [hD]
    exact ⟨by simpa using morseReach_beadD_left 4 [] B [] hB hBo le_rfl,
      by simpa using morseReach_beadD_right 4 [] B [] hB hBo le_rfl⟩
  | false =>
    have hD : morseDouble [(MorseKind.cross false, 0)] =
        morseWalkL false 0 2 ++ morseWalkL false 1 2 := by decide
    have hW : morseWalkL false 0 2 ++ morseWalkL false 1 2 =
        [(MorseKind.cross false, 1)] ++ [(MorseKind.cross false, 0), (MorseKind.cross false, 2)] ++
          [(MorseKind.cross false, 1)] := by decide
    have hE : ∀ x y : MorseWord, morseOut 4 x = 4 →
        MorseReach 4 (x ++ [(MorseKind.cross false, 1)] ++
            [(MorseKind.cross false, 0), (MorseKind.cross false, 2)] ++
              ([(MorseKind.cross false, 1)] ++ y))
          (x ++ [(MorseKind.cross false, 1)] ++
            [(MorseKind.cross false, 2), (MorseKind.cross false, 0)] ++
              ([(MorseKind.cross false, 1)] ++ y)) := by
      intro x y hx
      have h := morseReach_isoRule 4 (x ++ [(MorseKind.cross false, 1)])
        ([(MorseKind.cross false, 1)] ++ y)
        (.exch (MorseKind.cross false, 0) (MorseKind.cross false, 2))
        rfl (by rw [morseOut_append, hx]; rfl) (by rw [morseOut_append, hx]; rfl)
      simpa [morseRuleLhs, morseRuleRhs, morseKindIn, morseKindOut] using h
    rw [hD]
    refine ⟨?_, ?_⟩
    · have h1 := morseReach_passL 4 0 2 false [] B (morseWalkL false 1 2) hB (by decide)
        (by rw [hBo]; decide)
      have h2 := morseReach_passL 4 1 2 false (morseWalkL false 0 2) B [] hB (by decide)
        (by rw [hBo]; decide)
      rw [hBo, morseShiftWord_zero_iso] at h1
      rw [hBo] at h2
      simp only [List.nil_append, List.append_nil, Nat.zero_add] at h1 h2
      simpa only [List.append_assoc] using morseReach_trans h1 h2
    · have h1 := morseReach_symm (morseReach_pass 4 1 2 false [] B (morseWalk false 0 2) hB
        (by decide))
      have h2 := morseReach_symm (morseReach_pass 4 0 2 false (morseWalk false 1 2) B [] hB
        (by decide))
      rw [hBo] at h1 h2
      rw [morseShiftWord_zero_iso] at h2
      have hx : morseOut 4 (morseShiftWord 2 B) = 4 := by
        have := (morseOut_shift_iso 2 2 0 B hB).1; rwa [hBo] at this
      have h0 := hE (morseShiftWord 2 B) [] hx
      have h3 := morseReach_symm (hE [] B rfl)
      have hw1 : morseWalk false 1 2 = [(MorseKind.cross false, 1), (MorseKind.cross false,
          2)] := by
        decide
      have hw0 : morseWalk false 0 2 = [(MorseKind.cross false, 0), (MorseKind.cross false,
          1)] := by
        decide
      rw [hw1, hw0] at h1 h2
      rw [hW]
      simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
        show (1 : ℕ) + 1 = 2 from rfl, Nat.zero_add] at h0 h1 h2 h3 ⊢
      exact morseReach_trans h0 (morseReach_trans h1 (morseReach_trans h2 h3))


/-- A band bead passes a doubled crossing of either sign, in both directions. -/
private theorem morseReach_beadX_slide (n₀ i : ℕ) (s : Bool) (B u v : MorseWord)
    (hB : morseFits 2 B = true) (hBo : morseOut 2 B = 2) (hu : 2 * i + 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (2 * i) B ++ morseDoubleLetter (MorseKind.cross s, i) ++ v)
        (u ++ morseDoubleLetter (MorseKind.cross s, i) ++ morseShiftWord (2 * i + 2) B ++ v) ∧
      MorseReach n₀
        (u ++ morseShiftWord (2 * i + 2) B ++ morseDoubleLetter (MorseKind.cross s, i) ++ v)
        (u ++ morseDoubleLetter (MorseKind.cross s, i) ++ morseShiftWord (2 * i) B ++ v) := by
  obtain ⟨h1, h2⟩ := morseReach_beadX_base s B hB hBo
  have hD4 : morseFits 4 (morseDouble [(MorseKind.cross s, 0)]) = true := by cases s <;> decide
  have hf1 : morseFits 4 (B ++ morseDouble [(MorseKind.cross s, 0)]) = true := by
    rw [morseFits_append, morseFits_add_right_iso 2 2 B hB, morseOut_add_right 2 2 B hB, hBo, hD4]
    rfl
  have hf2 : morseFits 4 (morseShiftWord 2 B ++ morseDouble [(MorseKind.cross s, 0)]) = true := by
    have h := morseOut_shift_iso 2 2 0 B hB
    rw [hBo] at h
    rw [morseFits_append, h.2, h.1, hD4]
    rfl
  have hL := morseDouble_cross_shift_slide s i
  have hdl : morseDouble [(MorseKind.cross s, i)] = morseDoubleLetter (MorseKind.cross s, i) := by
    simp [morseDouble]
  rw [hdl] at hL
  have k1 := morseReach_frame 4 n₀ (2 * i) (morseOut n₀ u - 2 * i - 4) u v _ _ h1 hf1 (by omega)
  have k2 := morseReach_frame 4 n₀ (2 * i) (morseOut n₀ u - 2 * i - 4) u v _ _ h2 hf2 (by omega)
  simp only [morseShiftWord_append, morseShiftWord_shift_iso, hL, Nat.add_comm 2 (2 * i)] at k1 k2
  exact ⟨by simpa only [List.append_assoc] using k1, by simpa only [List.append_assoc] using k2⟩

/-- The letters of a doubled letter lie at twice its position or to the right. -/
private theorem mem_morseDoubleLetter_slide {l x : MorseLetter} (hx : x ∈ morseDoubleLetter l) :
    2 * l.2 ≤ x.2 := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [morseDoubleLetter, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  | cap =>
    simp only [morseDoubleLetter, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  | cross s =>
    rw [morseDoubleLetter_cross_slide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    cases s <;> rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- A bead passes a doubled letter lying on its left. -/
private theorem morseReach_slide_passL (n₀ c p q e : ℕ) (l : MorseLetter) (B u v : MorseWord)
    (hB : morseFits 2 B = true) (hBo : morseOut 2 B = 2) (hl : l.2 + morseKindIn l.1 ≤ p)
    (hp : p + 1 ≤ c) (hq : morseLetterOut p l = q) (hu : morseOut n₀ u = 2 * c + e) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p) B ++ morseDoubleLetter l ++ v)
      (u ++ morseDoubleLetter l ++ morseShiftWord (2 * q) B ++ v) := by
  have hd := morseDoubleLetter_fits_slide p 0 l hl
  rw [Nat.add_zero, Nat.add_zero, hq] at hd
  have h := morseReach_isoBead_commL n₀ (2 * p) 2 (2 * c + e - 2 * p - 2) B u
    (morseDoubleLetter l) v hB hBo hd.1 (by omega)
  rwa [hd.2] at h

/-- A bead passes a doubled letter lying on its right. -/
private theorem morseReach_slide_passR (n₀ c p e : ℕ) (l : MorseLetter) (B u v : MorseWord)
    (hB : morseFits 2 B = true) (hBo : morseOut 2 B = 2) (hl : p + 1 ≤ l.2)
    (hlc : l.2 + morseKindIn l.1 ≤ c) (hp : p + 1 ≤ c) (hu : morseOut n₀ u = 2 * c + e) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p) B ++ morseDoubleLetter l ++ v)
      (u ++ morseDoubleLetter l ++ morseShiftWord (2 * p) B ++ v) := by
  have hd := morseDoubleLetter_fits_slide c e l hlc
  exact morseReach_isoBead_commR n₀ (2 * p) 2 B u (morseDoubleLetter l) v hB hBo
    (fun x hx ↦ by have := mem_morseDoubleLetter_slide hx; omega) (by rw [hu]; exact hd.1)
    (by omega)

/-- The word with the bead on the segment `x = (k, p, d)` (rotated when going down). -/
private def isoJW (G T u v : MorseWord) (x : ℕ × ℕ × Bool) : MorseWord :=
  u ++ morseDouble (G.take x.1) ++ morseShiftWord (2 * x.2.1) (if x.2.2 then T else isoRot 2 T) ++
    morseDouble (G.drop x.1) ++ v

/-- A segment of the knot: a level, a strand at that level, downward segments below the top. -/
private def IsoJValid (G : MorseWord) (x : ℕ × ℕ × Bool) : Prop :=
  x.1 ≤ G.length ∧ x.2.1 < morseOut 1 (G.take x.1) ∧ (x.2.2 = false → x.1 < G.length)

/-- The word around the letter of index `k`. -/
private theorem slide_split (G : MorseWord) (k : ℕ) (l : MorseLetter) (hk : G[k]? = some l)
    (hG : morseFits 1 G = true) :
    k < G.length ∧ G.drop k = l :: G.drop (k + 1) ∧ G.take (k + 1) = G.take k ++ [l] ∧
      l.2 + morseKindIn l.1 ≤ morseOut 1 (G.take k) ∧
      morseOut 1 (G.take (k + 1)) = morseLetterOut (morseOut 1 (G.take k)) l := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hk
  have hd : G.drop k = l :: G.drop (k + 1) := by rw [List.drop_eq_getElem_cons hlt, hget]
  have ht : G.take (k + 1) = G.take k ++ [l] := by rw [List.take_add_one, hk]; rfl
  have hf := hG
  rw [← List.take_append_drop k G, morseFits_append, hd, Bool.and_eq_true, morseFits_cons] at hf
  refine ⟨hlt, hd, ht, hf.2.1, ?_⟩
  rw [ht, morseOut_append]
  rfl

/-- The number of strands at a level of a doubled word. -/
private theorem slide_count (G u : MorseWord) (n₀ e k : ℕ) (hG : morseFits 1 G = true)
    (hu : morseOut n₀ u = 2 + e) :
    morseOut n₀ (u ++ morseDouble (G.take k)) = 2 * morseOut 1 (G.take k) + e := by
  have hf := hG
  rw [← List.take_append_drop k G, morseFits_append, Bool.and_eq_true] at hf
  rw [morseOut_append, hu, show 2 + e = 2 * 1 + e by ring,
    (morseDouble_fits_slide _ 1 e hf.1).2]


/-- Doubling a word with a first letter. -/
private theorem morseDouble_cons_slide (l : MorseLetter) (w : MorseWord) :
    morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w := rfl

/-- Doubling a word with a last letter. -/
private theorem morseDouble_concat_slide (w : MorseWord) (l : MorseLetter) :
    morseDouble (w ++ [l]) = morseDouble w ++ morseDoubleLetter l := by
  rw [morseDouble_append_slide, morseDouble_cons_slide]
  simp [morseDouble]

/-- One step of the bead along the knot, upwards. -/
private theorem isoJ_step_up (G T u v : MorseWord) (n₀ e k p : ℕ) (y : ℕ × ℕ × Bool)
    (hG : morseFits 1 G = true) (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2)
    (hu : morseOut n₀ u = 2 + e) (hp : p < morseOut 1 (G.take k))
    (hy : isoTraceStep G (k, p, true) = some y) :
    IsoJValid G y ∧ MorseReach n₀ (isoJW G T u v (k, p, true)) (isoJW G T u v y) := by
  have hR := isoRot_fits T 2 hT
  rw [hTo] at hR
  have hRR : isoRot 2 (isoRot 2 T) = T := by
    have := isoRot_isoRot 2 T hT; rwa [hTo] at this
  cases hl : G[k]? with
  | none => simp [isoTraceStep, hl] at hy
  | some l =>
    obtain ⟨hlt, hdrop, htake, hfit, hout⟩ := slide_split G k l hl hG
    have hc := slide_count G u n₀ e k hG hu
    obtain ⟨lk, i⟩ := l
    cases lk with
    | cross s =>
      simp only [isoTraceStep, hl, Option.some.injEq] at hy
      subst hy
      simp only [morseKindIn] at hfit
      simp only [morseLetterOut, morseKindIn, morseKindOut] at hout
      refine ⟨⟨by omega, ?_, by simp⟩, ?_⟩
      · simp only [hout]; split_ifs <;> omega
      simp only [isoJW, hdrop, htake, morseDouble_cons_slide, morseDouble_concat_slide, ite_true]
      simp only [List.append_assoc]
      split_ifs with h1 h2
      · subst h1
        have h := (morseReach_beadX_slide n₀ p s T (u ++ morseDouble (G.take k))
          (morseDouble (G.drop (k + 1)) ++ v) hT hTo (by rw [hc]; omega)).1
        rw [show 2 * (p + 1) = 2 * p + 2 by ring]
        simpa only [List.append_assoc] using h
      · subst h2
        have h := (morseReach_beadX_slide n₀ i s T (u ++ morseDouble (G.take k))
          (morseDouble (G.drop (k + 1)) ++ v) hT hTo (by rw [hc]; omega)).2
        rw [show 2 * (i + 1) = 2 * i + 2 by ring]
        simpa only [List.append_assoc] using h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · have h := morseReach_slide_passR n₀ _ p e (MorseKind.cross s, i) T
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hT hTo
            (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hc
          simpa only [List.append_assoc] using h
        · have h := morseReach_slide_passL n₀ _ p p e (MorseKind.cross s, i) T
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hT hTo
            (by simp only [morseKindIn]; omega) (by omega)
            (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hc
          simpa only [List.append_assoc] using h
    | cup =>
      simp only [isoTraceStep, hl, Option.some.injEq] at hy
      subst hy
      simp only [morseKindIn] at hfit
      simp only [morseLetterOut, morseKindIn, morseKindOut] at hout
      refine ⟨⟨by omega, ?_, by simp⟩, ?_⟩
      · simp only [hout]; split_ifs <;> omega
      simp only [isoJW, hdrop, htake, morseDouble_cons_slide, morseDouble_concat_slide, ite_true]
      simp only [List.append_assoc]
      split_ifs with h1
      · have h := morseReach_slide_passL n₀ _ p (p + 2) e (MorseKind.cup, i) T
          (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hT hTo
          (by simp only [morseKindIn]; omega) (by omega)
          (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hc
        simpa only [List.append_assoc] using h
      · have h := morseReach_slide_passR n₀ _ p e (MorseKind.cup, i) T
          (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hT hTo
          (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hc
        simpa only [List.append_assoc] using h
    | cap =>
      simp only [morseKindIn] at hfit
      simp only [morseLetterOut, morseKindIn, morseKindOut] at hout
      have hD : morseDouble [isoN i] = morseDoubleLetter (MorseKind.cap, i) := by
        simp [morseDouble, isoN]
      by_cases h1 : p = i
      · subst h1
        simp only [isoTraceStep, hl, Option.some.injEq, ↓reduceIte] at hy
        subst hy
        refine ⟨⟨by dsimp only; omega, by dsimp only; omega, fun _ ↦ hlt⟩, ?_⟩
        simp only [isoJW, hdrop, morseDouble_cons_slide, ite_true, Bool.false_eq_true, ite_false]
        have h := morseReach_isoBead_cap n₀ p T (u ++ morseDouble (G.take k))
          (morseDouble (G.drop (k + 1)) ++ v) hT hTo (by rw [hc]; omega)
        rw [hD] at h
        rw [show 2 * (p + 1) = 2 * p + 2 by ring]
        simpa only [List.append_assoc] using h
      by_cases h2 : p = i + 1
      · subst h2
        simp only [isoTraceStep, hl, h1, Option.some.injEq, ↓reduceIte] at hy
        subst hy
        refine ⟨⟨by dsimp only; omega, by dsimp only; omega, fun _ ↦ hlt⟩, ?_⟩
        simp only [isoJW, hdrop, morseDouble_cons_slide, ite_true, Bool.false_eq_true, ite_false]
        have h := morseReach_symm (morseReach_isoBead_cap n₀ i (isoRot 2 T)
          (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2
          (by rw [hc]; omega))
        rw [hD, hRR] at h
        rw [show 2 * (i + 1) = 2 * i + 2 by ring]
        simpa only [List.append_assoc] using h
      · simp only [isoTraceStep, hl, h1, h2, Option.some.injEq, ↓reduceIte] at hy
        subst hy
        refine ⟨⟨by omega, ?_, by simp⟩, ?_⟩
        · simp only [hout]; split_ifs <;> omega
        simp only [isoJW, hdrop, htake, morseDouble_cons_slide, morseDouble_concat_slide,
          ite_true]
        simp only [List.append_assoc]
        split_ifs with h3
        · have h := morseReach_slide_passL n₀ _ p (p - 2) e (MorseKind.cap, i) T
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hT hTo
            (by simp only [morseKindIn]; omega) (by omega)
            (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hc
          simpa only [List.append_assoc] using h
        · have h := morseReach_slide_passR n₀ _ p e (MorseKind.cap, i) T
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hT hTo
            (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hc
          simpa only [List.append_assoc] using h


/-- One step of the bead along the knot, downwards. -/
private theorem isoJ_step_down (G T u v : MorseWord) (n₀ e k p : ℕ) (y : ℕ × ℕ × Bool)
    (hG : morseFits 1 G = true) (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2)
    (hu : morseOut n₀ u = 2 + e) (hp : p < morseOut 1 (G.take (k + 1)))
    (hy : isoTraceStep G (k + 1, p, false) = some y) :
    IsoJValid G y ∧ MorseReach n₀ (isoJW G T u v (k + 1, p, false)) (isoJW G T u v y) := by
  have hR := isoRot_fits T 2 hT
  rw [hTo] at hR
  have hRR : isoRot 2 (isoRot 2 T) = T := by
    have := isoRot_isoRot 2 T hT; rwa [hTo] at this
  cases hl : G[k]? with
  | none => simp [isoTraceStep, hl] at hy
  | some l =>
    obtain ⟨hlt, hdrop, htake, hfit, hout⟩ := slide_split G k l hl hG
    have hc := slide_count G u n₀ e k hG hu
    rw [hout] at hp
    obtain ⟨lk, i⟩ := l
    cases lk with
    | cross s =>
      simp only [isoTraceStep, hl, Option.some.injEq] at hy
      subst hy
      simp only [morseKindIn] at hfit
      simp only [morseLetterOut, morseKindIn, morseKindOut] at hp
      refine ⟨⟨by dsimp only; omega, ?_, fun _ ↦ by dsimp only; omega⟩, ?_⟩
      · dsimp only; split_ifs <;> omega
      simp only [isoJW, hdrop, htake, morseDouble_cons_slide, morseDouble_concat_slide,
        Bool.false_eq_true, ite_false]
      simp only [List.append_assoc]
      split_ifs with h1 h2
      · subst h1
        have h := (morseReach_beadX_slide n₀ i s (isoRot 2 T) (u ++ morseDouble (G.take k))
          (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2 (by rw [hc]; omega)).1
        rw [show 2 * (i + 1) = 2 * i + 2 by ring]
        exact morseReach_symm (by simpa only [List.append_assoc] using h)
      · subst h2
        have h := (morseReach_beadX_slide n₀ p s (isoRot 2 T) (u ++ morseDouble (G.take k))
          (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2 (by rw [hc]; omega)).2
        rw [show 2 * (p + 1) = 2 * p + 2 by ring]
        exact morseReach_symm (by simpa only [List.append_assoc] using h)
      · rcases Nat.lt_or_ge p i with h3 | h3
        · have h := morseReach_slide_passR n₀ _ p e (MorseKind.cross s, i) (isoRot 2 T)
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2
            (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hc
          exact morseReach_symm (by simpa only [List.append_assoc] using h)
        · have h := morseReach_slide_passL n₀ _ p p e (MorseKind.cross s, i) (isoRot 2 T)
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2
            (by simp only [morseKindIn]; omega) (by omega)
            (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hc
          exact morseReach_symm (by simpa only [List.append_assoc] using h)
    | cup =>
      simp only [morseKindIn] at hfit
      simp only [morseLetterOut, morseKindIn, morseKindOut] at hp
      have hD : morseDouble [isoU i] = morseDoubleLetter (MorseKind.cup, i) := by
        simp [morseDouble, isoU]
      by_cases h1 : p = i
      · subst h1
        simp only [isoTraceStep, hl, Option.some.injEq, ↓reduceIte] at hy
        subst hy
        refine ⟨⟨by dsimp only; omega, ?_, by simp⟩, ?_⟩
        · dsimp only; rw [hout]; simp only [morseLetterOut, morseKindIn, morseKindOut]; omega
        simp only [isoJW, htake, morseDouble_concat_slide, ite_true, Bool.false_eq_true,
          ite_false]
        have h := morseReach_isoBead_cup n₀ p (isoRot 2 T) (u ++ morseDouble (G.take k))
          (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2 (by rw [hc]; omega)
        rw [hD, hRR] at h
        rw [show 2 * (p + 1) = 2 * p + 2 by ring]
        simpa only [List.append_assoc] using h
      by_cases h2 : p = i + 1
      · subst h2
        simp only [isoTraceStep, hl, h1, Option.some.injEq, ↓reduceIte] at hy
        subst hy
        refine ⟨⟨by dsimp only; omega, ?_, by simp⟩, ?_⟩
        · dsimp only; rw [hout]; simp only [morseLetterOut, morseKindIn, morseKindOut]; omega
        simp only [isoJW, htake, morseDouble_concat_slide, ite_true, Bool.false_eq_true,
          ite_false]
        have h := morseReach_symm (morseReach_isoBead_cup n₀ i T (u ++ morseDouble (G.take k))
          (morseDouble (G.drop (k + 1)) ++ v) hT hTo (by rw [hc]; omega))
        rw [hD] at h
        rw [show 2 * (i + 1) = 2 * i + 2 by ring]
        simpa only [List.append_assoc] using h
      · simp only [isoTraceStep, hl, h1, h2, Option.some.injEq, ↓reduceIte] at hy
        subst hy
        refine ⟨⟨by dsimp only; omega, ?_, fun _ ↦ by dsimp only; omega⟩, ?_⟩
        · dsimp only; split_ifs <;> omega
        simp only [isoJW, hdrop, htake, morseDouble_cons_slide, morseDouble_concat_slide,
          Bool.false_eq_true, ite_false]
        simp only [List.append_assoc]
        split_ifs with h3
        · have h := morseReach_slide_passL n₀ _ (p - 2) p e (MorseKind.cup, i) (isoRot 2 T)
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2
            (by simp only [morseKindIn]; omega) (by omega)
            (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hc
          exact morseReach_symm (by simpa only [List.append_assoc] using h)
        · have h := morseReach_slide_passR n₀ _ p e (MorseKind.cup, i) (isoRot 2 T)
            (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2
            (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hc
          exact morseReach_symm (by simpa only [List.append_assoc] using h)
    | cap =>
      simp only [isoTraceStep, hl, Option.some.injEq] at hy
      subst hy
      simp only [morseKindIn] at hfit
      simp only [morseLetterOut, morseKindIn, morseKindOut] at hp
      refine ⟨⟨by dsimp only; omega, ?_, fun _ ↦ by dsimp only; omega⟩, ?_⟩
      · dsimp only; split_ifs <;> omega
      simp only [isoJW, hdrop, htake, morseDouble_cons_slide, morseDouble_concat_slide,
        Bool.false_eq_true, ite_false]
      simp only [List.append_assoc]
      split_ifs with h1
      · have h := morseReach_slide_passL n₀ _ (p + 2) p e (MorseKind.cap, i) (isoRot 2 T)
          (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2
          (by simp only [morseKindIn]; omega) (by omega)
          (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hc
        exact morseReach_symm (by simpa only [List.append_assoc] using h)
      · have h := morseReach_slide_passR n₀ _ p e (MorseKind.cap, i) (isoRot 2 T)
          (u ++ morseDouble (G.take k)) (morseDouble (G.drop (k + 1)) ++ v) hR.1 hR.2
          (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hc
        exact morseReach_symm (by simpa only [List.append_assoc] using h)


/-- The bead follows the trace of the knot. -/
private theorem isoJ_trace (G T u v : MorseWord) (n₀ e : ℕ) (hG : morseFits 1 G = true)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) (hu : morseOut n₀ u = 2 + e) :
    ∀ (fuel : ℕ) (x : ℕ × ℕ × Bool), IsoJValid G x →
      MorseReach n₀ (isoJW G T u v (0, 0, true)) (isoJW G T u v x) →
      ∀ y ∈ isoTrace G fuel x, IsoJValid G y ∧
        MorseReach n₀ (isoJW G T u v (0, 0, true)) (isoJW G T u v y)
  | 0, x, hx, hr, y, hy => by
    simp only [isoTrace, List.mem_singleton] at hy
    subst hy
    exact ⟨hx, hr⟩
  | fuel + 1, x, hx, hr, y, hy => by
    cases hs : isoTraceStep G x with
    | none =>
      simp only [isoTrace, hs, List.mem_singleton] at hy
      subst hy
      exact ⟨hx, hr⟩
    | some z =>
      simp only [isoTrace, hs, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨hx, hr⟩
      · obtain ⟨k, p, d⟩ := x
        have hz : IsoJValid G z ∧
            MorseReach n₀ (isoJW G T u v (k, p, d)) (isoJW G T u v z) := by
          cases d with
          | true => exact isoJ_step_up G T u v n₀ e k p z hG hT hTo hu hx.2.1 hs
          | false =>
            cases k with
            | zero => simp [isoTraceStep] at hs
            | succ k => exact isoJ_step_down G T u v n₀ e k p z hG hT hTo hu hx.2.1 hs
        exact isoJ_trace G T u v n₀ e hG hT hTo hu fuel z hz.1 (morseReach_trans hr hz.2) y hy

/-- The number of turns of a word, letter by letter. -/
private theorem isoTurns_cons_slide (l : MorseLetter) (w : MorseWord) :
    isoTurns (l :: w) = (match l.1 with
      | .cross _ => 0
      | _ => 1) + isoTurns w := by
  obtain ⟨k, i⟩ := l
  cases k <;> simp [isoTurns] <;> omega

/-- Cups and caps change the number of strands by two each. -/
private theorem morseOut_isoTurns_slide : ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
    ∃ c, morseOut n w + 4 * c = n + 2 * isoTurns w
  | [], n, _ => ⟨0, by simp [isoTurns, morseOut]⟩
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    obtain ⟨c, hc⟩ := morseOut_isoTurns_slide w (morseLetterOut n l) h.2
    obtain ⟨k, i⟩ := l
    rw [isoTurns_cons_slide]
    cases k with
    | cup =>
      refine ⟨c, ?_⟩
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut] at hc h ⊢
      omega
    | cap =>
      refine ⟨c + 1, ?_⟩
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut] at hc h ⊢
      omega
    | cross s =>
      refine ⟨c, ?_⟩
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut] at hc h ⊢
      omega

/-- A band bead travels from the bottom end of a doubled connected long knot to its top end. -/
theorem morseReach_isoBandBead_journey (G T u v : MorseWord) (n₀ e : ℕ)
    (hG : morseFits 1 G = true ∧ morseOut 1 G = 1) (hc : IsoConnected G)
    (hT : morseFits 2 T = true ∧ morseOut 2 T = 2) (hu : morseOut n₀ u = 2 + e) :
    MorseReach n₀ (u ++ T ++ morseDouble G ++ v)
      (u ++ morseDouble G ++ (if Even (isoTurns G) then T else isoRot 2 T) ++ v) := by
  have hEven : Even (isoTurns G) := by
    obtain ⟨c, hc⟩ := morseOut_isoTurns_slide G 1 hG.1
    rw [hG.2] at hc
    exact ⟨c, by omega⟩
  simp only [hEven, ↓reduceIte]
  obtain ⟨d, hd⟩ := hc G.length le_rfl 0 (by rw [List.take_length, hG.2]; omega)
  have hstart : IsoJValid G (0, 0, true) := ⟨Nat.zero_le _, by simp [morseOut], by simp⟩
  obtain ⟨hv, hr⟩ := isoJ_trace G T u v n₀ e hG.1 hT.1 hT.2 hu _ (0, 0, true) hstart
    (morseReach_refl n₀ _) _ hd
  cases d with
  | false => exact absurd (hv.2.2 rfl) (lt_irrefl _)
  | true =>
    simp only [isoJW, List.take_zero, List.drop_zero, List.take_length, List.drop_length,
      Nat.mul_zero, morseShiftWord_zero_iso, ite_true] at hr
    simpa [morseDouble] using hr

/-- A right curl on the right edge travels from the bottom end to the top end (even number of
turns). -/
theorem morseReach_isoEdgeBead_journey (G u v : MorseWord) (s : Bool) (n₀ e : ℕ)
    (hG : morseFits 1 G = true ∧ morseOut 1 G = 1) (hc : IsoConnected G)
    (hev : Even (isoTurns G)) (hu : morseOut n₀ u = 2 + e) :
    MorseReach n₀ (u ++ isoCurlR s 1 ++ morseDouble G ++ v)
      (u ++ morseDouble G ++ isoCurlR s 1 ++ v) := by
  have hT : morseFits 2 (isoCurlR s 1) = true ∧ morseOut 2 (isoCurlR s 1) = 2 := by
    cases s <;> decide
  have h := morseReach_isoBandBead_journey G (isoCurlR s 1) u v n₀ e hG hc hT hu
  simpa only [hev, ite_true] using h

/-- The core has an even number of cups and caps. -/
theorem even_isoTurns_pairCore (r s : ℕ) (hr : 3 ≤ r) : Even (isoTurns (pairCore r s)) := by
  have hadd : ∀ a b : MorseWord, isoTurns (a ++ b) = isoTurns a + isoTurns b := fun a b ↦ by
    simp [isoTurns, List.filter_append]
  have hcups : ∀ k, isoTurns ((List.range k).map isoU) = k := fun k ↦ by
    simp [isoTurns, isoU, List.filter_map, Function.comp_def]
  have hcaps : ∀ k, isoTurns ((List.range k).reverse.map isoN) = k := fun k ↦ by
    simp [isoTurns, isoN, List.filter_map, Function.comp_def]
  have hconv : isoTurns (phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) s) = 0 := by
    rw [isoTurns, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro l hl
    rw [phaseTwoBlk, List.mem_flatten] at hl
    obtain ⟨w, hw, hl⟩ := hl
    rw [List.eq_of_mem_replicate hw] at hl
    simp only [morseWalkL, List.mem_map, List.mem_reverse, List.mem_range] at hl
    obtain ⟨i, -, rfl⟩ := hl
    simp
  have h : isoTurns (pairCore r s) = (r - 2) + 1 + 2 + (r - 3) := by
    rw [pairCore, hadd, hadd, hadd, hadd, hcups, hconv, hcaps]
    rfl
  rw [h]
  exact ⟨r - 1, by omega⟩

end AJConjecture
