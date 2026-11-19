import Mathlib
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusPhaseTwoWords

/-!
# Phase II: beads on a band

Generic lemmas used by the stages of phase II. A bead is any tangle on the two strands of a band
(twists, half twists, the clasp with its twists); it slides along the band through a doubled
crossing `D = +1 +2 +0 +1` by two applications of a walk-passes-tangle lemma, `morseReach_pass` for
rightward walks and its mirror `morseReach_passL` for leftward walks (`morseReach_beadD_left`,
`morseReach_beadD_right`, `morseReach_beadD_pow`). `morseReach_blocks` applies a fixed
strand-neutral macro to every block of a run.
-/

namespace AJConjecture

/-- The leftward walk: a strand moving from the gap `p + len` to the gap `p` across `len` strands
(`X(p+len-1) ⋯ X(p)`). -/
def morseWalkL (s : Bool) (p len : ℕ) : MorseWord :=
  (List.range len).reverse.map fun i ↦ (MorseKind.cross s, p + i)

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_passL (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- A fitting word, with extra passive strands to its right: the arity. -/
theorem morseOut_add_right (b e : ℕ) (T : MorseWord) (hT : morseFits b T = true) :
    morseOut (b + e) T = morseOut b T + e := by
  induction T generalizing b with
  | nil => rfl
  | cons l T ih =>
    simp only [morseFits, Bool.and_eq_true, decide_eq_true_eq] at hT
    simp only [morseOut]
    rw [show morseLetterOut (b + e) l = morseLetterOut b l + e by
      simp only [morseLetterOut]; omega]
    exact ih _ hT.2

/-- A fitting word still fits with extra passive strands to its right. -/
private theorem morseFits_add_right_passL (b e : ℕ) (T : MorseWord) (hT : morseFits b T = true) :
    morseFits (b + e) T = true := by
  induction T generalizing b with
  | nil => rfl
  | cons l T ih =>
    simp only [morseFits, Bool.and_eq_true, decide_eq_true_eq] at hT ⊢
    refine ⟨by omega, ?_⟩
    rw [show morseLetterOut (b + e) l = morseLetterOut b l + e by
      simp only [morseLetterOut]; omega]
    exact ih _ hT.2

/-- A walk grows at the end. -/
private theorem morseWalk_succ_passL (s : Bool) (p len : ℕ) :
    morseWalk s p (len + 1) = morseWalk s p len ++ [(MorseKind.cross s, p + len)] := by
  simp [morseWalk, List.range_succ]

/-- A leftward walk grows at the front. -/
private theorem morseWalkL_succ_passL (s : Bool) (p len : ℕ) :
    morseWalkL s p (len + 1) = (MorseKind.cross s, p + len) :: morseWalkL s p len := by
  simp [morseWalkL, List.range_succ]

/-- A leftward walk does not change the number of strands. -/
private theorem morseOut_morseWalkL_passL (n : ℕ) (s : Bool) (p len : ℕ) :
    morseOut n (morseWalkL s p len) = n :=
  morseOut_of_cross n _ fun _ hb ↦ by
    simp only [morseWalkL, List.mem_map, List.mem_reverse, List.mem_range] at hb
    obtain ⟨i, -, rfl⟩ := hb
    exact ⟨s, rfl⟩

/-- The second Reidemeister move, cancelling a crossing against its inverse. -/
private theorem morseReach_r2_cancel_passL (n₀ i : ℕ) (s : Bool) (u v : MorseWord)
    (hu : i + 2 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ (MorseKind.cross s, i) :: (MorseKind.cross (!s), i) :: v) (u ++ v) := by
  refine ⟨[(u.length, .r2 i s, false)], ?_⟩
  simp [morseApplyAll, morseApply, morseRuleLhs, morseRuleRhs, morseRuleOk, morseFits,
    morseLetterOut, morseKindIn, morseKindOut, hu, List.isPrefixOf]

/-- A walk followed by the inverse leftward walk cancels. -/
private theorem morseReach_walk_walkL_cancel (n₀ p len : ℕ) (t : Bool) (u v : MorseWord)
    (hu : p + len + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk t p len ++ morseWalkL (!t) p len ++ v) (u ++ v) := by
  induction len generalizing v with
  | zero => simpa [morseWalk, morseWalkL] using morseReach_refl n₀ (u ++ v)
  | succ len ih =>
    have h1 := morseReach_r2_cancel_passL n₀ (p + len) t (u ++ morseWalk t p len)
      (morseWalkL (!t) p len ++ v)
      (by rw [morseOut_append, morseOut_morseWalk]; omega)
    have h2 := ih v (by omega)
    rw [morseWalk_succ_passL, morseWalkL_succ_passL]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A leftward walk followed by the inverse walk cancels. -/
private theorem morseReach_walkL_walk_cancel (n₀ p len : ℕ) (s : Bool) (u v : MorseWord)
    (hu : p + len + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalkL s p len ++ morseWalk (!s) p len ++ v) (u ++ v) := by
  induction len generalizing u v with
  | zero => simpa [morseWalk, morseWalkL] using morseReach_refl n₀ (u ++ v)
  | succ len ih =>
    have hx : morseOut n₀ (u ++ [(MorseKind.cross s, p + len)]) = morseOut n₀ u := by
      rw [morseOut_append, morseOut_of_cross _ _ fun _ hb ↦ by
        rw [List.mem_singleton] at hb
        exact ⟨s, by rw [hb]⟩]
    have h1 := ih (u ++ [(MorseKind.cross s, p + len)]) ((MorseKind.cross (!s), p + len) :: v)
      (by omega)
    have h2 := morseReach_r2_cancel_passL n₀ (p + len) s u v (by omega)
    rw [morseWalk_succ_passL, morseWalkL_succ_passL]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

set_option linter.unusedVariables false in
/-- Mirror of `morseReach_pass`: a strand moving left across the outgoing strands of a tangle `T`
on `b` strands passes `T`. -/
theorem morseReach_passL (n₀ p b : ℕ) (s : Bool) (u T v : MorseWord)
    (hT : morseFits b T = true) (hu : p + b + 1 ≤ morseOut n₀ u)
    (hu' : p + morseOut b T + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord p T ++ morseWalkL s p (morseOut b T) ++ v)
      (u ++ morseWalkL s p b ++ morseShiftWord (p + 1) T ++ v) := by
  obtain ⟨e, he⟩ : ∃ e, morseOut n₀ u = p + 1 + b + e :=
    ⟨morseOut n₀ u - (p + 1 + b), by omega⟩
  have h1 := morseReach_symm (morseReach_walkL_walk_cancel n₀ p b s u
    (morseShiftWord p T ++ morseWalkL s p (morseOut b T) ++ v) hu)
  have h2 := morseReach_pass n₀ p b (!s) (u ++ morseWalkL s p b) T
    (morseWalkL s p (morseOut b T) ++ v) hT
    (by rw [morseOut_append, morseOut_morseWalkL_passL]; omega)
  have hout : morseOut n₀ (u ++ morseWalkL s p b ++ morseShiftWord (p + 1) T) =
      morseOut b T + e + (p + 1) := by
    rw [morseOut_append, morseOut_append, morseOut_morseWalkL_passL, he,
      show p + 1 + b + e = b + e + (p + 1) by omega,
      morseOut_morseShiftWord _ _ _ (morseFits_add_right_passL b e T hT),
      morseOut_add_right b e T hT]
  have h3 := morseReach_walk_walkL_cancel n₀ p (morseOut b T) (!s)
    (u ++ morseWalkL s p b ++ morseShiftWord (p + 1) T) v (by rw [hout]; omega)
  simp only [Bool.not_not, List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- The two middle letters `+2 +0` of the doubled crossing exchange. -/
private theorem morseReach_exch_twoZero_passL (n₀ : ℕ) (x y : MorseWord)
    (hx : 4 ≤ morseOut n₀ x) :
    MorseReach n₀ (x ++ [(MorseKind.cross true, 2)] ++ [(MorseKind.cross true, 0)] ++ y)
      (x ++ [(MorseKind.cross true, 0)] ++ [(MorseKind.cross true, 2)] ++ y) :=
  morseReach_comm n₀ x [(MorseKind.cross true, 0)] [(MorseKind.cross true, 2)] y
    (fun b hb ↦ ⟨true, by rw [List.mem_singleton] at hb; rw [hb]⟩)
    (fun b hb a ha ↦ by
      rw [List.mem_singleton] at hb ha
      rw [hb, ha])
    (morseFits_of_cross _ _ (fun b hb ↦ by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl <;> exact ⟨true, rfl⟩)
      (fun b hb ↦ by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl <;> simp only <;> omega))

/-- A bead on two strands does not change the number of strands. -/
private theorem morseOut_bead_passL (n₀ : ℕ) (u T : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 2 ≤ morseOut n₀ u) :
    morseOut n₀ (u ++ T) = morseOut n₀ u := by
  obtain ⟨e, he⟩ : ∃ e, morseOut n₀ u = 2 + e := ⟨morseOut n₀ u - 2, by omega⟩
  rw [morseOut_append, he, morseOut_add_right 2 e T hT, hTo]

/-- The doubled crossing does not change the number of strands. -/
theorem morseOut_phaseTwoD (n : ℕ) : morseOut n phaseTwoD = n :=
  morseOut_of_cross n _ fun b hb ↦ by
    simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨true, rfl⟩

/-- A bead on the walking (left) band passes a doubled crossing and ends on the right band. -/
theorem morseReach_beadD_left (n₀ : ℕ) (u T v : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ T ++ phaseTwoD ++ v) (u ++ phaseTwoD ++ morseShiftWord 2 T ++ v) := by
  have hW0 : morseWalkL true 0 2 = [(MorseKind.cross true, 1), (MorseKind.cross true, 0)] := rfl
  have hW1 : morseWalkL true 1 2 = [(MorseKind.cross true, 2), (MorseKind.cross true, 1)] := rfl
  have huT := morseOut_bead_passL n₀ u T hT hTo (by omega)
  have h0 := morseReach_exch_twoZero_passL n₀ (u ++ T ++ [(MorseKind.cross true, 1)])
    ([(MorseKind.cross true, 1)] ++ v) (by rw [morseOut_append, huT]; exact hu)
  have h1 := morseReach_passL n₀ 0 2 true u T (morseWalkL true 1 2 ++ v) hT (by omega)
    (by omega)
  have h2 := morseReach_passL n₀ 1 2 true (u ++ morseWalkL true 0 2) T v hT
    (by rw [morseOut_append, morseOut_morseWalkL_passL]; omega)
    (by rw [morseOut_append, morseOut_morseWalkL_passL]; omega)
  have h3 := morseReach_symm (morseReach_exch_twoZero_passL n₀ (u ++ [(MorseKind.cross true, 1)])
    ([(MorseKind.cross true, 1)] ++ morseShiftWord 2 T ++ v)
    (by rw [morseOut_append]; exact hu))
  rw [hTo, morseShiftWord_zero_passL, Nat.zero_add] at h1
  rw [hTo] at h2
  rw [hW0, hW1] at h1 h2
  simp only [phaseTwoD, List.append_assoc, List.cons_append, List.nil_append] at h0 h1 h2 h3 ⊢
  exact morseReach_trans h0 (morseReach_trans h1 (morseReach_trans h2 h3))

/-- A bead on the walked-over (right) band passes a doubled crossing and ends on the left band. -/
theorem morseReach_beadD_right (n₀ : ℕ) (u T v : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord 2 T ++ phaseTwoD ++ v) (u ++ phaseTwoD ++ T ++ v) := by
  have hD : phaseTwoD = morseWalk true 1 2 ++ morseWalk true 0 2 := rfl
  have h1 := morseReach_symm (morseReach_pass n₀ 1 2 true u T (morseWalk true 0 2 ++ v) hT
    (by omega))
  have h2 := morseReach_symm (morseReach_pass n₀ 0 2 true (u ++ morseWalk true 1 2) T v hT
    (by rw [morseOut_append, morseOut_morseWalk]; omega))
  rw [hTo] at h1 h2
  rw [morseShiftWord_zero_passL] at h2
  rw [hD]
  simp only [List.append_assoc] at h1 h2 ⊢
  exact morseReach_trans h1 h2

/-- Both bead travels at once, by induction on the number of blocks. -/
private theorem morseReach_beadD_pow_both (n₀ m : ℕ) (T v : MorseWord)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) :
    ∀ u : MorseWord, 4 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ T ++ phaseTwoBlk phaseTwoD m ++ v)
        (u ++ phaseTwoBlk phaseTwoD m ++ (if m % 2 = 0 then T else morseShiftWord 2 T) ++ v) ∧
      MorseReach n₀ (u ++ morseShiftWord 2 T ++ phaseTwoBlk phaseTwoD m ++ v)
        (u ++ phaseTwoBlk phaseTwoD m ++ (if m % 2 = 0 then morseShiftWord 2 T else T) ++ v) := by
  induction m with
  | zero =>
    intro u _
    simp only [phaseTwoBlk, List.replicate_zero, List.flatten_nil, List.append_nil,
      Nat.zero_mod, ↓reduceIte]
    exact ⟨morseReach_refl n₀ _, morseReach_refl n₀ _⟩
  | succ m ih =>
    intro u hu
    have e : phaseTwoBlk phaseTwoD (m + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD m := by
      simp [phaseTwoBlk, List.replicate_succ]
    obtain ⟨h1, h2⟩ := ih (u ++ phaseTwoD)
      (by rw [morseOut_append, morseOut_phaseTwoD]; exact hu)
    have hL := morseReach_beadD_left n₀ u T (phaseTwoBlk phaseTwoD m ++ v) hT hTo hu
    have hR := morseReach_beadD_right n₀ u T (phaseTwoBlk phaseTwoD m ++ v) hT hTo hu
    rw [e]
    by_cases hm : m % 2 = 0
    · have hm' : ¬ (m + 1) % 2 = 0 := by omega
      simp only [hm, hm', ↓reduceIte, List.append_assoc] at h1 h2 hL hR ⊢
      exact ⟨morseReach_trans hL h2, morseReach_trans hR h1⟩
    · have hm' : (m + 1) % 2 = 0 := by omega
      simp only [hm, hm', ↓reduceIte, List.append_assoc] at h1 h2 hL hR ⊢
      exact ⟨morseReach_trans hL h2, morseReach_trans hR h1⟩

/-- A bead travels along one band of the doubled 2-braid `D^m`, alternating sides. -/
theorem morseReach_beadD_pow (n₀ m : ℕ) (u T v : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ T ++ phaseTwoBlk phaseTwoD m ++ v)
      (u ++ phaseTwoBlk phaseTwoD m ++ (if m % 2 = 0 then T else morseShiftWord 2 T) ++ v) :=
  (morseReach_beadD_pow_both n₀ m T v hT hTo u hu).1

/-- The same, starting on the right band. -/
theorem morseReach_beadD_pow' (n₀ m : ℕ) (u T v : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord 2 T ++ phaseTwoBlk phaseTwoD m ++ v)
      (u ++ phaseTwoBlk phaseTwoD m ++ (if m % 2 = 0 then morseShiftWord 2 T else T) ++ v) :=
  (morseReach_beadD_pow_both n₀ m T v hT hTo u hu).2

private theorem morseShiftWord_zero_phaseTwo (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- A fixed strand-neutral macro applied to every block of a run of blocks. -/
theorem morseReach_blocks (n₀ n m : ℕ) (u v x y : MorseWord) (h : MorseReach n x y)
    (hx : morseFits n x = true) (hyo : morseOut n y = n) (hu : morseOut n₀ u = n) :
    MorseReach n₀ (u ++ phaseTwoBlk x m ++ v) (u ++ phaseTwoBlk y m ++ v) := by
  induction m generalizing u with
  | zero => exact morseReach_refl n₀ _
  | succ m ih =>
    have e : ∀ z : MorseWord, phaseTwoBlk z (m + 1) = z ++ phaseTwoBlk z m := fun z ↦ by
      simp [phaseTwoBlk, List.replicate_succ]
    rw [e x, e y]
    have h1 : MorseReach n₀ (u ++ x ++ (phaseTwoBlk x m ++ v)) (u ++ y ++ (phaseTwoBlk x m ++ v)) := by
      have := morseReach_frame n n₀ 0 0 u (phaseTwoBlk x m ++ v) x y h hx (by omega)
      simpa [morseShiftWord_zero_phaseTwo] using this
    have h2 := ih (u ++ y) (by rw [morseOut_append, hu, hyo])
    simp only [List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

end AJConjecture
