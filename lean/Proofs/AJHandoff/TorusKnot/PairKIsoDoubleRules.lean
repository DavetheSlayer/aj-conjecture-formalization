import Mathlib
import AJHandoff.TorusKnot.PairKIsoWords
import AJConjecture.SkeinMorseRule

/-!
# Doubled rules

Every rule of the checker, doubled (`morseDouble` of both sides), is a reachability on twice as
many strands: `zig`, `r2`, `r3`, `cupSlide`, `capSlide`, `exch` (nine pairs of kinds) by fixed
macros on at most `12` strands at the shift `2i` (`morseReach_frame`); `kink` by a fixed macro on
four strands using two `kink`s (a doubled curl is a curl on each edge and a full twist of the band;
the full twists cancel by `r2`). Generic in the position and the signs.
-/

namespace AJConjecture

/-- Doubling commutes with shifting. -/
private theorem morseDouble_shift_rules (d : ℕ) (w : MorseWord) :
    morseDouble (morseShiftWord d w) = morseShiftWord (2 * d) (morseDouble w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [morseShiftWord, List.map_cons,
      show morseDouble (shiftLetter d l :: List.map (shiftLetter d) w) =
        morseDoubleLetter (shiftLetter d l) ++ morseDouble (List.map (shiftLetter d) w) from
        List.flatMap_cons]
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from List.flatMap_cons,
      morseShiftWord, List.map_append]
    rw [morseShiftWord] at ih
    rw [ih]
    congr 1
    obtain ⟨k, i⟩ := l
    cases k with
    | cup =>
      simp only [shiftLetter, morseDoubleLetter, List.map_cons, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, true_and, and_true]
      omega
    | cap =>
      simp only [shiftLetter, morseDoubleLetter, List.map_cons, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, true_and, and_true]
      omega
    | cross s =>
      cases s <;>
      · simp only [shiftLetter, morseDoubleLetter, cable, cableGen, morseOfBraid,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte,
          show List.range 2 = [0, 1] from rfl, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.cons.injEq,
          Prod.mk.injEq, true_and, and_true]
        omega

/-- A doubled rule at the position `i`, from the doubled rule at `0` on `m` strands. -/
private theorem morseReach_double_shifted (R : MorseRule) (i m n : ℕ) (hok : morseRuleOk R = true)
    (hfit : morseFits (2 * m) (morseDouble (morseRuleLhs R)) = true)
    (hR : MorseReach (2 * m) (morseDouble (morseRuleLhs R)) (morseDouble (morseRuleRhs R)))
    (hn : i + m ≤ n) :
    MorseReach (2 * n) (morseDouble (morseRuleLhs (shiftRule i R)))
      (morseDouble (morseRuleRhs (shiftRule i R))) := by
  obtain ⟨hL, hRr, -⟩ := shiftRule_sides i R hok
  rw [hL, hRr, morseDouble_shift_rules, morseDouble_shift_rules]
  have := morseReach_frame (2 * m) (2 * n) (2 * i) (2 * n - 2 * i - 2 * m) [] [] _ _ hR hfit
    (by simp only [morseOut]; omega)
  simpa using this

/-- The doubled `zig` rule. -/
private theorem morseReach_double_zig_zero (r : Bool) :
    MorseReach 2 (morseDouble (morseRuleLhs (.zig 0 r))) (morseDouble (morseRuleRhs
        (.zig 0 r))) := by
  cases r
  · exact ⟨
    [(1, .exch (.cap, 1) (.cup, 3), true), (0, .zig 1 false, false), (0, .zig 0 false, false)],
        by decide⟩
  · exact ⟨
    [(1, .exch (.cup, 1) (.cap, 1), false), (0, .zig 0 true, false), (0, .zig 1 true, false)],
        by decide⟩

/-- The doubled second Reidemeister move. -/
private theorem morseReach_double_r2_zero (s : Bool) :
    MorseReach 4 (morseDouble (morseRuleLhs (.r2 0 s))) (morseDouble (morseRuleRhs (.r2 0 s))) := by
  cases s
  · exact ⟨
    [(3, .r2 1 false, false), (2, .r2 2 false, false), (1, .r2 0 false, false),
     (0, .r2 1 false, false)], by decide⟩
  · exact ⟨
    [(3, .r2 1 true, false), (2, .r2 0 true, false), (1, .r2 2 true, false), (0, .r2 1 true,
        false)], by decide⟩

/-- The doubled third Reidemeister move. -/
private theorem morseReach_double_r3_zero (s : Bool) :
    MorseReach 6 (morseDouble (morseRuleLhs (.r3 0 s))) (morseDouble (morseRuleRhs (.r3 0 s))) := by
  cases s
  · exact ⟨
    [(3, .exch (.cross false, 1) (.cross false, 3), false),
     (7, .exch (.cross false, 1) (.cross false, 3), true),
     (6, .exch (.cross false, 1) (.cross false, 4), true), (4, .r3 1 false, false),
     (2, .r3 2 false, false), (1, .exch (.cross false, 0) (.cross false, 3), false),
     (0, .exch (.cross false, 1) (.cross false, 3), false),
     (2, .exch (.cross false, 0) (.cross false, 2), false),
     (4, .exch (.cross false, 1) (.cross false, 3), true),
     (6, .exch (.cross false, 2) (.cross false, 4), false),
     (8, .exch (.cross false, 0) (.cross false, 3), true),
     (7, .exch (.cross false, 0) (.cross false, 2), true),
     (6, .exch (.cross false, 0) (.cross false, 4), true),
     (5, .exch (.cross false, 0) (.cross false, 3), true), (3, .r3 0 false, false),
     (1, .r3 1 false, false), (3, .exch (.cross false, 0) (.cross false, 2), true),
     (8, .r3 2 false, false), (6, .r3 3 false, false),
     (5, .exch (.cross false, 1) (.cross false, 4), false),
     (4, .exch (.cross false, 2) (.cross false, 4), false),
     (3, .exch (.cross false, 0) (.cross false, 4), false),
     (2, .exch (.cross false, 1) (.cross false, 4), false),
     (6, .exch (.cross false, 1) (.cross false, 3), false),
     (8, .exch (.cross false, 2) (.cross false, 4), true),
     (10, .exch (.cross false, 1) (.cross false, 3), true),
     (9, .exch (.cross false, 1) (.cross false, 4), true), (7, .r3 1 false, false),
     (5, .r3 2 false, false), (4, .exch (.cross false, 0) (.cross false, 3), false),
     (3, .exch (.cross false, 1) (.cross false, 3), false),
     (7, .exch (.cross false, 1) (.cross false, 3), true)], by decide⟩
  · exact ⟨
    [(3, .exch (.cross true, 1) (.cross true, 3), false),
     (2, .exch (.cross true, 0) (.cross true, 3), false),
     (4, .exch (.cross true, 1) (.cross true, 4), false),
     (3, .exch (.cross true, 0) (.cross true, 4), false),
     (7, .exch (.cross true, 1) (.cross true, 3), true), (5, .r3 1 true, false),
     (4, .exch (.cross true, 0) (.cross true, 2), false),
     (3, .exch (.cross true, 2) (.cross true, 4), true), (1, .r3 2 true, false),
     (0, .exch (.cross true, 1) (.cross true, 3), false), (7, .r3 2 true, false),
     (6, .exch (.cross true, 1) (.cross true, 3), false),
     (5, .exch (.cross true, 0) (.cross true, 3), false), (3, .r3 3 true, false),
     (2, .exch (.cross true, 2) (.cross true, 4), false),
     (1, .exch (.cross true, 1) (.cross true, 4), false),
     (9, .exch (.cross true, 0) (.cross true, 3), true),
     (8, .exch (.cross true, 0) (.cross true, 2), true), (6, .r3 0 true, false),
     (5, .exch (.cross true, 1) (.cross true, 4), true),
     (4, .exch (.cross true, 1) (.cross true, 3), true), (2, .r3 1 true, false),
     (6, .exch (.cross true, 0) (.cross true, 4), true),
     (10, .exch (.cross true, 1) (.cross true, 3), true), (8, .r3 1 true, false),
     (7, .exch (.cross true, 2) (.cross true, 4), true),
     (6, .exch (.cross true, 0) (.cross true, 2), false), (4, .r3 2 true, false),
     (3, .exch (.cross true, 1) (.cross true, 3), false),
     (6, .exch (.cross true, 0) (.cross true, 3), true),
     (8, .exch (.cross true, 1) (.cross true, 4), true),
     (7, .exch (.cross true, 1) (.cross true, 3), true)], by decide⟩

/-- The doubled `cupSlide` rule. -/
private theorem morseReach_double_cupSlide_zero (s r : Bool) :
    MorseReach 2 (morseDouble (morseRuleLhs (.cupSlide 0 s r))) (morseDouble (morseRuleRhs
        (.cupSlide 0 s r))) := by
  cases s <;> cases r
  · exact ⟨
    [(1, .exch (.cup, 1) (.cross false, 1), false),
     (3, .exch (.cross false, 2) (.cross false, 4), false),
     (2, .exch (.cup, 1) (.cross false, 2), false),
     (5, .exch (.cross false, 1) (.cross false, 3), true), (3, .cupSlide 1 false false, false),
     (4, .exch (.cross false, 0) (.cross false, 3), true),
     (3, .exch (.cross false, 0) (.cup, 2), true),
     (2, .exch (.cross false, 0) (.cross false, 2), true), (0, .cupSlide 0 false false, false),
     (2, .cupSlide 2 false false, false), (2, .exch (.cross false, 1) (.cup, 3), true),
     (0, .cupSlide 1 false false, false)], by decide⟩
  · exact ⟨
    [(1, .exch (.cross false, 1) (.cup, 3), true), (2, .exch (.cross false, 0) (.cup, 3), true),
     (5, .exch (.cross false, 1) (.cross false, 3), false), (3, .cupSlide 2 false true, false),
     (3, .cupSlide 1 false true, false), (3, .exch (.cup, 1) (.cross false, 2), false),
     (2, .exch (.cross false, 0) (.cross false, 2), false), (0, .cupSlide 1 false true, false),
     (2, .exch (.cup, 1) (.cross false, 1), false), (0, .cupSlide 0 false true, false)], by decide⟩
  · exact ⟨
    [(1, .exch (.cup, 1) (.cross true, 1), false), (2, .exch (.cup, 1) (.cross true, 2), false),
     (5, .exch (.cross true, 1) (.cross true, 3), true), (3, .cupSlide 1 true false, false),
     (3, .cupSlide 2 true false, false), (3, .exch (.cross true, 0) (.cup, 3), true),
     (2, .exch (.cross true, 0) (.cross true, 2), true), (0, .cupSlide 0 true false, false),
     (2, .exch (.cross true, 1) (.cup, 3), true), (0, .cupSlide 1 true false, false)], by decide⟩
  · exact ⟨
    [(1, .exch (.cross true, 1) (.cup, 3), true),
     (3, .exch (.cross true, 0) (.cross true, 2), true),
     (2, .exch (.cross true, 0) (.cup, 3), true),
     (5, .exch (.cross true, 1) (.cross true, 3), false), (3, .cupSlide 2 true true, false),
     (4, .exch (.cross true, 1) (.cross true, 4), false),
     (3, .exch (.cup, 2) (.cross true, 2), false),
     (2, .exch (.cross true, 0) (.cross true, 2), false), (0, .cupSlide 1 true true, false),
     (2, .cupSlide 1 true true, false), (2, .exch (.cup, 1) (.cross true, 1), false),
     (0, .cupSlide 0 true true, false)], by decide⟩

/-- The doubled `capSlide` rule. -/
private theorem morseReach_double_capSlide_zero (s r : Bool) :
    MorseReach 6 (morseDouble (morseRuleLhs (.capSlide 0 s r))) (morseDouble (morseRuleRhs
        (.capSlide 0 s r))) := by
  cases s <;> cases r
  · exact ⟨
    [(1, .exch (.cross false, 2) (.cross false, 4), false),
     (3, .exch (.cross false, 1) (.cross false, 3), true),
     (4, .exch (.cross false, 0) (.cross false, 3), true),
     (7, .exch (.cross false, 1) (.cap, 3), false), (5, .capSlide 2 false false, false),
     (4, .exch (.cross false, 0) (.cap, 2), false), (2, .capSlide 1 false false, false),
     (1, .exch (.cap, 1) (.cross false, 4), true), (0, .exch (.cap, 1) (.cross false, 3), true),
     (2, .exch (.cross false, 0) (.cross false, 2), true), (3, .capSlide 1 false false, false),
     (1, .capSlide 0 false false, false)], by decide⟩
  · exact ⟨
    [(3, .exch (.cross false, 1) (.cross false, 3), false),
     (7, .exch (.cap, 1) (.cross false, 3), true), (6, .exch (.cap, 1) (.cross false, 4), true),
     (4, .capSlide 1 false true, false), (2, .capSlide 2 false true, false),
     (1, .exch (.cross false, 0) (.cap, 3), false), (0, .exch (.cross false, 1) (.cap, 3), false),
     (2, .exch (.cross false, 0) (.cross false, 2), false), (3, .capSlide 0 false true, false),
     (1, .capSlide 1 false true, false)], by decide⟩
  · exact ⟨
    [(3, .exch (.cross true, 1) (.cross true, 3), true),
     (7, .exch (.cross true, 1) (.cap, 3), false), (6, .exch (.cross true, 0) (.cap, 3), false),
     (4, .capSlide 2 true false, false), (2, .capSlide 1 true false, false),
     (1, .exch (.cap, 1) (.cross true, 4), true), (0, .exch (.cap, 1) (.cross true, 3), true),
     (2, .exch (.cross true, 0) (.cross true, 2), true), (3, .capSlide 1 true false, false),
     (1, .capSlide 0 true false, false)], by decide⟩
  · exact ⟨
    [(1, .exch (.cross true, 0) (.cross true, 2), true),
     (3, .exch (.cross true, 1) (.cross true, 3), false),
     (4, .exch (.cross true, 1) (.cross true, 4), false),
     (7, .exch (.cap, 1) (.cross true, 3), true), (5, .capSlide 1 true true, false),
     (4, .exch (.cap, 2) (.cross true, 4), true), (2, .capSlide 2 true true, false),
     (1, .exch (.cross true, 0) (.cap, 3), false), (0, .exch (.cross true, 1) (.cap, 3), false),
     (2, .exch (.cross true, 0) (.cross true, 2), false), (3, .capSlide 0 true true, false),
     (1, .capSlide 1 true true, false)], by decide⟩

/-- Normalizes the double of an explicit letter. -/
local macro "dbl_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [morseDoubleLetter,
  cable, cableGen, morseOfBraid, List.flatMap_cons, List.flatMap_nil, List.append_nil,
  Bool.false_eq_true, ↓reduceIte, show List.range 2 = [0, 1] from rfl, List.reverse_cons,
  List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
  List.mem_cons, List.not_mem_nil, or_false, morseShiftWord, shiftLetter, List.cons.injEq,
  Prod.mk.injEq, true_and, and_true] $[$loc]?)

/-- The letters of the double of a letter lie at the positions `2i, 2i + 1, 2i + 2`. -/
private theorem morseDoubleLetter_pos_rules (l : MorseLetter) :
    ∀ c ∈ morseDoubleLetter l, 2 * l.2 ≤ c.2 ∧ c.2 ≤ 2 * l.2 + 2 := by
  obtain ⟨k, i⟩ := l
  intro c hc
  cases k with
  | cup => dbl_norm at hc; rcases hc with rfl | rfl <;> simp
  | cap => dbl_norm at hc; rcases hc with rfl | rfl <;> simp
  | cross s =>
    cases s <;> dbl_norm at hc <;> rcases hc with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- The double of a letter moved two places to the right. -/
private theorem morseDoubleLetter_add_two_rules (l : MorseLetter) :
    morseDoubleLetter (l.1,
        l.2 + 2) = morseShiftWord 2 (morseShiftWord 2 (morseDoubleLetter l)) := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup => dbl_norm; omega
  | cap => dbl_norm; omega
  | cross s => cases s <;> dbl_norm <;> omega

/-- The double of a letter moved two places to the left. -/
private theorem morseDoubleLetter_sub_two_rules (l : MorseLetter) (hl : 2 ≤ l.2) :
    morseDoubleLetter l = morseShiftWord 2 (morseShiftWord 2 (morseDoubleLetter (l.1,
        l.2 - 2))) := by
  obtain ⟨k, i⟩ := l
  have := morseDoubleLetter_add_two_rules (k, i - 2)
  simp only [show i - 2 + 2 = i by simp at hl; omega] at this
  exact this

/-- The double of a fitting letter fits on twice the strands and doubles their number. -/
private theorem morseDoubleLetter_fits_rules (n : ℕ) (l : MorseLetter)
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

/-- The double of a fitting word fits on twice the strands and doubles their number. -/
private theorem morseDouble_fits_rules :
    ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
      morseFits (2 * n) (morseDouble w) = true ∧
        morseOut (2 * n) (morseDouble w) = 2 * morseOut n w
  | [], _, _ => ⟨rfl, rfl⟩
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    have hl := morseDoubleLetter_fits_rules n l h.1
    have hw := morseDouble_fits_rules w _ h.2
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from List.flatMap_cons,
      morseFits_append, morseOut_append, hl.1, hl.2, hw.1, hw.2]
    exact ⟨rfl, rfl⟩

/-- Doubling a word of two letters. -/
private theorem morseDouble_pair_rules (a b : MorseLetter) :
    morseDouble [a, b] = morseDoubleLetter a ++ morseDoubleLetter b := by
  simp [morseDouble]

/-- The letters of a shifted word. -/
private theorem mem_morseShiftWord_rules {d : ℕ} {w : MorseWord} {c : MorseLetter}
    (hc : c ∈ morseShiftWord d w) : ∃ e ∈ w, c = (e.1, e.2 + d) := by
  simp only [morseShiftWord, List.mem_map, shiftLetter] at hc
  obtain ⟨e, he, rfl⟩ := hc
  exact ⟨e, he, rfl⟩

/-- The doubled exchange of a crossing with a letter to its right. -/
private theorem morseReach_double_exch_cross (n i : ℕ) (t : Bool) (b : MorseLetter)
    (hij : i + 2 ≤ b.2)
    (hfit : morseFits (2 * n) (morseDoubleLetter b ++ morseDoubleLetter (.cross t, i)) = true) :
    MorseReach (2 * n) (morseDoubleLetter (.cross t, i) ++ morseDoubleLetter b)
      (morseDoubleLetter b ++ morseDoubleLetter (.cross t, i)) := by
  have h := morseReach_comm (2 * n) [] (morseDoubleLetter (.cross t, i)) (morseDoubleLetter b) []
    (fun c hc ↦ by cases t <;> dbl_norm at hc <;> rcases hc with rfl | rfl | rfl | rfl <;>
      exact ⟨_, rfl⟩)
    (fun c hc d hd ↦ by
      have h1 := morseDoubleLetter_pos_rules _ c hc
      have h2 := morseDoubleLetter_pos_rules _ d hd
      simp only at h1
      omega)
    hfit
  simpa using morseReach_symm h

/-- The doubled exchange of a cup with a letter to its right. -/
private theorem morseReach_double_exch_cup (n i : ℕ) (b : MorseLetter) (hij : i ≤ b.2)
    (hfit : morseFits (2 * n) (morseDoubleLetter b ++ morseDoubleLetter (.cup, i)) = true) :
    MorseReach (2 * n) (morseDoubleLetter (.cup, i) ++ morseDoubleLetter (b.1, b.2 + 2))
      (morseDoubleLetter b ++ morseDoubleLetter (.cup, i)) := by
  rw [morseFits_append, Bool.and_eq_true] at hfit
  obtain ⟨hb, ha⟩ := hfit
  rw [show morseDoubleLetter (.cup, i) = [(.cup, 2 * i), (.cup, 2 * i + 1)] from rfl] at ha
  simp only [morseFits, morseLetterOut, morseKindIn, morseKindOut, Bool.and_true,
    Bool.and_eq_true] at ha
  have ha1 := of_decide_eq_true ha.1
  have hsh := morseOut_fits_shift (2 * n) 2 0 (morseDoubleLetter b) hb
  have e : ∀ X : MorseWord, X.map (fun c ↦ (c.1, c.2 + morseKindOut (MorseKind.cup, 2 * i + 1).1 -
      morseKindIn (MorseKind.cup, 2 * i + 1).1)) = morseShiftWord 2 X := fun X ↦ by
    simp [morseShiftWord, shiftLetter, morseKindOut, morseKindIn]
  have e' : ∀ X : MorseWord, X.map (fun c ↦ (c.1, c.2 + morseKindOut (MorseKind.cup, 2 * i).1 -
      morseKindIn (MorseKind.cup, 2 * i).1)) = morseShiftWord 2 X := fun X ↦ by
    simp [morseShiftWord, shiftLetter, morseKindOut, morseKindIn]
  have s1 := morseReach_sweep (2 * n) [(.cup, 2 * i)] (morseShiftWord 2 (morseDoubleLetter b)) []
    (.cup, 2 * i + 1)
    (fun c hc ↦ by
      obtain ⟨d, hd, rfl⟩ := mem_morseShiftWord_rules hc
      have := morseDoubleLetter_pos_rules b d hd
      simp only [morseKindIn]
      omega)
    (by
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut, morseFits_append]
      rw [show 2 * n + 2 - 0 = 2 + 2 * n + 0 by omega, hsh.2, hsh.1]
      simp only [morseFits, morseKindIn, Bool.and_true, Bool.true_and]
      exact decide_eq_true (by omega))
  have s2 := morseReach_sweep (2 * n) [] (morseDoubleLetter b) [(.cup, 2 * i + 1)] (.cup, 2 * i)
    (fun c hc ↦ by
      have := morseDoubleLetter_pos_rules b c hc
      simp only [morseKindIn]
      omega)
    (by
      simp only [morseOut, morseFits_append, hb, Bool.true_and]
      simp only [morseFits, morseKindIn, Bool.and_true]
      exact decide_eq_true (by omega))
  rw [e] at s1
  rw [e'] at s2
  rw [morseDoubleLetter_add_two_rules]
  simp only [morseDoubleLetter, List.append_nil, List.nil_append, List.cons_append] at s1 s2 ⊢
  exact morseReach_trans s1 s2

/-- The doubled exchange of a cap with a letter to its right. -/
private theorem morseReach_double_exch_cap (n i : ℕ) (b : MorseLetter) (hij : i + 2 ≤ b.2)
    (hfit : morseFits (2 * n)
      (morseDoubleLetter (.cap, i) ++ morseDoubleLetter (b.1, b.2 - 2)) = true)
    (hb : morseFits (2 * n) (morseDoubleLetter b ++ morseDoubleLetter (.cap, i)) = true) :
    MorseReach (2 * n) (morseDoubleLetter (.cap, i) ++ morseDoubleLetter (b.1, b.2 - 2))
      (morseDoubleLetter b ++ morseDoubleLetter (.cap, i)) := by
  have hdb := morseDoubleLetter_sub_two_rules b (by omega)
  generalize morseDoubleLetter (b.1, b.2 - 2) = B' at hfit hdb ⊢
  have hpos : ∀ d ∈ B', 2 * i ≤ d.2 := by
    intro d hd
    have := morseDoubleLetter_pos_rules b
    rw [hdb] at this
    have h1 := this (d.1, d.2 + 2 + 2) (by
      simp only [morseShiftWord, List.map_map, List.mem_map, Function.comp, shiftLetter]
      exact ⟨d, hd, rfl⟩)
    simp only at h1
    omega
  rw [show morseDoubleLetter (.cap, i) = [(.cap, 2 * i + 1), (.cap, 2 * i)] from rfl] at hfit hb ⊢
  rw [morseFits_append, Bool.and_eq_true] at hfit hb
  obtain ⟨hcc, hB'⟩ := hfit
  simp only [morseFits, morseOut, morseLetterOut, morseKindIn, morseKindOut, Bool.and_true,
    Bool.and_eq_true] at hcc hB'
  have hc1 := of_decide_eq_true hcc.1
  have hsh := morseOut_fits_shift (2 * n - 4) 2 0 B'
    (by rw [show 2 * n - 4 = 2 * n + 0 - 2 + 0 - 2 by omega]; exact hB')
  have hsh2 := morseOut_fits_shift (2 + (2 * n - 4) + 0) 2 0 (morseShiftWord 2 B') hsh.2
  rw [show 2 + (2 + (2 * n - 4) + 0) + 0 = 2 * n by omega] at hsh2
  rw [hdb, hsh2.1, hsh.1] at hb
  simp only [morseFits, morseLetterOut, morseKindIn, morseKindOut, Bool.and_true,
    Bool.and_eq_true] at hb
  have hb2 := of_decide_eq_true hb.2.2
  have eg : ∀ X : MorseWord, (morseShiftWord 2 X).map (fun c ↦ (c.1, c.2 +
      morseKindOut MorseKind.cap - morseKindIn MorseKind.cap)) = X := fun X ↦ by
    simp [morseShiftWord, shiftLetter, morseKindOut, morseKindIn, Function.comp_def]
  have s1 := morseReach_sweep (2 * n) [(.cap, 2 * i + 1)] (morseShiftWord 2 B') []
    (.cap, 2 * i)
    (fun c hc ↦ by
      obtain ⟨d, hd, rfl⟩ := mem_morseShiftWord_rules hc
      have := hpos d hd
      simp only [morseKindIn]
      omega)
    (by
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut, morseFits_append]
      rw [show 2 * n + 0 - 2 = 2 + (2 * n - 4) + 0 by omega, hsh.2, hsh.1]
      simp only [morseFits, morseKindIn, Bool.and_true, Bool.true_and]
      exact decide_eq_true (by omega))
  have s2 := morseReach_sweep (2 * n) [] (morseShiftWord 2 (morseShiftWord 2 B'))
    [(.cap, 2 * i)] (.cap, 2 * i + 1)
    (fun c hc ↦ by
      obtain ⟨d, hd, rfl⟩ := mem_morseShiftWord_rules hc
      obtain ⟨e, he, rfl⟩ := mem_morseShiftWord_rules hd
      have := hpos e he
      simp only [morseKindIn]
      omega)
    (by
      simp only [morseOut, morseFits_append]
      rw [hsh2.2, hsh2.1, hsh.1]
      simp only [morseFits, morseKindIn, Bool.and_true, Bool.true_and]
      exact decide_eq_true (by omega))
  rw [eg] at s1 s2
  rw [hdb]
  simp only [List.append_nil, List.nil_append, List.cons_append] at s1 s2 ⊢
  exact morseReach_trans s1 s2

/-- The doubled framed first Reidemeister move: two doubled curls of opposite signs cancel
(each doubled curl is a curl on each edge and a full twist of the band). -/
private theorem morseReach_double_kink_zero (s : Bool) :
    MorseReach 2 (morseDouble (morseRuleLhs (.kink 0 s)))
      (morseDouble (morseRuleRhs (.kink 0 s))) := by
  cases s
  · exact ⟨
    [(3, .exch (.cross false, 0) (.cross false, 2), false),
     (5, .exch (.cross false, 1) (.cap, 3), false), (4, .exch (.cross false, 0) (.cap, 3), false),
     (1, .cupSlide 2 false false, true), (3, .r3 1 false, true),
     (5, .exch (.cross false, 1) (.cap, 3), false),
     (2, .exch (.cross false, 1) (.cross false, 3), true), (3, .capSlide 2 false false, false),
     (0, .exch (.cup, 2) (.cup, 2), true), (1, .exch (.cross false, 1) (.cup, 4), true),
     (2, .exch (.cap, 2) (.cup, 4), true), (4, .r3 0 false, true),
     (6, .exch (.cross false, 0) (.cap, 2), false), (3, .cupSlide 1 false false, true),
     (5, .r3 0 false, true), (7, .exch (.cross false, 0) (.cap, 2), false),
     (4, .exch (.cross false, 0) (.cross false, 2), true), (5, .capSlide 1 false false, false),
     (9, .exch (.cross true, 1) (.cup, 3), true),
     (11, .exch (.cross true, 0) (.cross true, 2), true),
     (10, .exch (.cross true, 0) (.cup, 3), true), (14, .capSlide 2 true true, true),
     (12, .r3 1 true, true), (11, .exch (.cross true, 1) (.cup, 3), true),
     (14, .exch (.cross true, 1) (.cross true, 3), false), (12, .cupSlide 2 true true, false),
     (14, .exch (.cap, 2) (.cap, 4), false), (13, .exch (.cross true, 1) (.cap, 4), false),
     (12, .exch (.cup, 2) (.cap, 2), false), (9, .r3 0 true, true),
     (8, .exch (.cross true, 0) (.cup, 2), true), (12, .capSlide 1 true true, true),
     (10, .r3 0 true, true), (9, .exch (.cross true, 0) (.cup, 2), true),
     (12, .exch (.cross true, 0) (.cross true, 2), false), (10, .cupSlide 1 true true, false),
     (7, .r2 0 false, false), (6, .r2 0 false, false), (3, .kink 0 false, false),
     (0, .kink 1 false, false)], by decide⟩
  · exact ⟨
    [(1, .cupSlide 2 true false, true), (3, .r3 1 true, true),
     (2, .exch (.cross true, 1) (.cross true, 3), true),
     (7, .exch (.cross true, 1) (.cap, 3), false), (6, .exch (.cross true, 0) (.cap, 3), false),
     (5, .exch (.cross true, 1) (.cap, 3), false), (3, .capSlide 2 true false, false),
     (0, .exch (.cup, 2) (.cup, 2), true), (1, .exch (.cross true, 1) (.cup, 4), true),
     (2, .exch (.cap, 2) (.cup, 4), true), (3, .cupSlide 1 true false, true),
     (6, .r3 0 true, true), (5, .r3 0 true, true),
     (4, .exch (.cross true, 0) (.cross true, 2), true),
     (8, .exch (.cross true, 0) (.cap, 2), false), (7, .exch (.cross true, 0) (.cap, 2), false),
     (5, .capSlide 1 true false, false), (9, .exch (.cross false, 1) (.cup, 3), true),
     (10, .exch (.cross false, 0) (.cup, 3), true), (14, .capSlide 2 false true, true),
     (12, .r3 1 false, true), (11, .exch (.cross false, 1) (.cup, 3), true),
     (14, .exch (.cross false, 1) (.cross false, 3), false), (12, .cupSlide 2 false true, false),
     (14, .exch (.cap, 2) (.cap, 4), false), (13, .exch (.cross false, 1) (.cap, 4), false),
     (12, .exch (.cup, 2) (.cap, 2), false), (9, .r3 0 false, true),
     (8, .exch (.cross false, 0) (.cup, 2), true), (12, .capSlide 1 false true, true),
     (10, .r3 0 false, true), (9, .exch (.cross false, 0) (.cup, 2), true),
     (12, .exch (.cross false, 0) (.cross false, 2), false), (10, .cupSlide 1 false true, false),
     (7, .r2 0 true, false), (6, .r2 0 true, false), (3, .kink 0 true, false),
     (0, .kink 1 true, false)], by decide⟩

/-- A doubled rule is a reachability. -/
theorem morseReach_morseDouble_rule (R : MorseRule) (n : ℕ) (hR : morseRuleOk R = true)
    (hl : morseFits n (morseRuleLhs R) = true) (hr : morseFits n (morseRuleRhs R) = true) :
    MorseReach (2 * n) (morseDouble (morseRuleLhs R)) (morseDouble (morseRuleRhs R)) := by
  cases R with
  | zig i r =>
    have hn : i + 1 ≤ n := by
      cases r <;>
        simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn, morseKindOut] at hl <;> omega
    have e : MorseRule.zig i r = shiftRule i (.zig 0 r) := by simp [shiftRule]
    rw [e]
    exact morseReach_double_shifted _ i 1 n rfl (by cases r <;> decide)
      (morseReach_double_zig_zero r) hn
  | r2 i s =>
    have hn : i + 2 ≤ n := by
      simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn, morseKindOut] at hl
      omega
    have e : MorseRule.r2 i s = shiftRule i (.r2 0 s) := by simp [shiftRule]
    rw [e]
    exact morseReach_double_shifted _ i 2 n rfl (by cases s <;> decide)
      (morseReach_double_r2_zero s) hn
  | r3 i s =>
    have hn : i + 3 ≤ n := by
      simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn, morseKindOut] at hl
      omega
    have e : MorseRule.r3 i s = shiftRule i (.r3 0 s) := by simp [shiftRule]
    rw [e]
    exact morseReach_double_shifted _ i 3 n rfl (by cases s <;> decide)
      (morseReach_double_r3_zero s) hn
  | cupSlide i s r =>
    have hn : i + 1 ≤ n := by
      cases r <;>
        simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn, morseKindOut] at hl <;> omega
    have e : MorseRule.cupSlide i s r = shiftRule i (.cupSlide 0 s r) := by simp [shiftRule]
    rw [e]
    exact morseReach_double_shifted _ i 1 n rfl (by cases s <;> cases r <;> decide)
      (morseReach_double_cupSlide_zero s r) hn
  | capSlide i s r =>
    have hn : i + 3 ≤ n := by
      cases r <;>
        simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn, morseKindOut] at hl <;> omega
    have e : MorseRule.capSlide i s r = shiftRule i (.capSlide 0 s r) := by simp [shiftRule]
    rw [e]
    exact morseReach_double_shifted _ i 3 n rfl (by cases s <;> cases r <;> decide)
      (morseReach_double_capSlide_zero s r) hn
  | kink i s =>
    have hn : i + 1 ≤ n := by
      simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn, morseKindOut] at hl
      omega
    have e : MorseRule.kink i s = shiftRule i (.kink 0 s) := by simp [shiftRule]
    rw [e]
    exact morseReach_double_shifted _ i 1 n rfl (by cases s <;> decide)
      (morseReach_double_kink_zero s) hn
  | exch a b =>
    obtain ⟨ka, i⟩ := a
    obtain ⟨kb, j⟩ := b
    have hok := of_decide_eq_true hR
    have hL := (morseDouble_fits_rules _ n hl).1
    have hRr := (morseDouble_fits_rules _ n hr).1
    simp only [morseRuleLhs, morseRuleRhs] at hL hRr ⊢
    simp only [morseDouble_pair_rules] at hL hRr ⊢
    cases ka with
    | cup =>
      simp only [morseKindIn, morseKindOut, Nat.sub_zero] at hok hL ⊢
      exact morseReach_double_exch_cup n i (kb, j) hok hRr
    | cap =>
      simp only [morseKindIn, morseKindOut, Nat.add_zero] at hok hL ⊢
      exact morseReach_double_exch_cap n i (kb, j) hok hL hRr
    | cross t =>
      simp only [morseKindIn, morseKindOut, Nat.add_sub_cancel] at hok hL ⊢
      exact morseReach_double_exch_cross n i t (kb, j) hok hRr

end AJConjecture
