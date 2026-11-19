import Mathlib
import AJFamily.Skein.TorusPhaseTwoPass

/-!
# Stage G of phase II: the clasp with its twists travels to the end of the band

`phaseTwo_stageG`: the clasp `phaseTwoClaspS` with its `2(2k+1)` negative half twists goes around
the doubled closing cup (a fixed macro, then the twists one by one) and, as a bead, along the second
pass (`morseReach_beadD_pow'`). After the caps move in front of it the word is `phaseTwoWG k`, the
target word with the clasp conjugated by a half twist.
-/

namespace AJConjecture

/-- The three opening cups `u1 u2 u3`. -/
private def gadgetCups : MorseWord := [(.cup, 1), (.cup, 2), (.cup, 3)]

/-- The tail of the rotated gadget on the band `(2, 3)`: `+2 u4 +3 +3 n2 −2`. -/
private def gadgetTailH : MorseWord :=
  [(.cross true, 2), (.cup, 4), (.cross true, 3), (.cross true, 3), (.cap, 2), (.cross false, 2)]

/-- The tail of the rotated gadget on the band `(0, 1)`: `+0 u2 +1 +1 n0 −0`. -/
private def gadgetTailF : MorseWord :=
  [(.cross true, 0), (.cup, 2), (.cross true, 1), (.cross true, 1), (.cap, 0), (.cross false, 0)]

/-- Macro `X`, left side: the half twist and the clasp of the gadget next to the doubled cup. -/
private def gadgetMacroX_lhs : MorseWord := [(.cup, 2), (.cup, 3)] ++ phaseTwoClaspS

/-- Macro `X`, right side: they have passed the doubled cup. -/
private def gadgetMacroX_rhs : MorseWord := [(.cup, 2), (.cup, 3)] ++ gadgetTailH

/-- Macro `X`, the moves (45). -/
private def gadgetMacroX_moves : List MorseMove :=
  [(1, .cupSlide 2 false false, true), (3, .exch (.cross false, 2) (.cross false, 4), false),
    (0, .exch (.cup, 2) (.cup, 2), true), (1, .cupSlide 3 false true, false),
    (2, .exch (.cross false, 2) (.cup, 6), false),
    (3, .exch (.cross false, 2) (.cross true, 5), false),
    (4, .exch (.cross false, 2) (.cross true, 5), false),
    (5, .exch (.cross false, 2) (.cap, 4), false), (4, .r2 4 false, true),
    (5, .capSlide 4 true true, false), (2, .cupSlide 5 false false, true),
    (4, .r2 5 false, false), (1, .exch (.cup, 3) (.cup, 3), false),
    (2, .exch (.cup, 3) (.cross false, 4), false), (3, .r2 3 false, true),
    (1, .cupSlide 3 false false, false), (0, .exch (.cup, 2) (.cup, 2), false),
    (5, .capSlide 4 true true, true), (4, .r2 4 false, false),
    (3, .exch (.cup, 3) (.cross true, 3), false), (4, .zig 3 true, false),
    (0, .exch (.cup, 2) (.cup, 2), true), (4, .zig 4 false, true),
    (3, .exch (.cross true, 3) (.cup, 5), false), (5, .capSlide 3 false true, true),
    (4, .r2 3 true, false), (0, .exch (.cup, 2) (.cup, 2), false), (3, .r2 2 true, true),
    (1, .cupSlide 2 true false, false), (2, .exch (.cross false, 2) (.cup, 5), false),
    (1, .exch (.cup, 3) (.cup, 3), false),
    (3, .exch (.cross false, 2) (.cross false, 4), false), (4, .r2 3 false, true),
    (2, .cupSlide 3 false false, false), (5, .capSlide 2 true true, true),
    (4, .r2 2 false, false), (6, .exch (.cross false, 2) (.cross true, 4), false),
    (5, .exch (.cap, 2) (.cross true, 6), false),
    (4, .exch (.cross true, 3) (.cross true, 6), false),
    (3, .exch (.cross true, 3) (.cross true, 6), false),
    (2, .exch (.cup, 4) (.cross true, 4), false), (1, .cupSlide 2 true false, true),
    (3, .exch (.cross true, 2) (.cross true, 4), false), (0, .exch (.cup, 2) (.cup, 2), true),
    (1, .cupSlide 3 true true, false)]

/-- Macro `X` as a reachability statement. -/
private theorem morseReach_gadgetMacroX : MorseReach 3 gadgetMacroX_lhs gadgetMacroX_rhs :=
  ⟨gadgetMacroX_moves, by decide⟩

/-- Macro `Y`: a twist `−4` moves left past the tail `H` (exchanges). -/
private theorem morseReach_gadgetMacroY :
    MorseReach 7 (gadgetTailH ++ [(.cross false, 4)]) ([(.cross false, 4)] ++ gadgetTailH) :=
  ⟨[(5, .exch (.cross false, 2) (.cross false, 4), false),
    (4, .exch (.cap, 2) (.cross false, 6), false),
    (3, .exch (.cross true, 3) (.cross false, 6), false),
    (2, .exch (.cross true, 3) (.cross false, 6), false),
    (1, .exch (.cup, 4) (.cross false, 4), false),
    (0, .exch (.cross true, 2) (.cross false, 4), false)], by decide⟩

/-- Macro `Z`: the caps `n3 n2` move left past the tail `F` (exchanges). -/
private theorem morseReach_gadgetMacroZ :
    MorseReach 7 (gadgetTailF ++ [(.cap, 3), (.cap, 2)]) ([(.cap, 3), (.cap, 2)] ++ gadgetTailF) :=
  ⟨[(5, .exch (.cross false, 0) (.cap, 3), false), (4, .exch (.cap, 0) (.cap, 5), false),
    (3, .exch (.cross true, 1) (.cap, 5), false), (2, .exch (.cross true, 1) (.cap, 5), false),
    (1, .exch (.cup, 2) (.cap, 3), false), (0, .exch (.cross true, 0) (.cap, 3), false),
    (6, .exch (.cross false, 0) (.cap, 2), false), (5, .exch (.cap, 0) (.cap, 4), false),
    (4, .exch (.cross true, 1) (.cap, 4), false), (3, .exch (.cross true, 1) (.cap, 4), false),
    (2, .exch (.cup, 2) (.cap, 2), false), (1, .exch (.cross true, 0) (.cap, 2), false)],
    by decide⟩

/-- Shifting by zero strands does nothing. -/
private theorem morseShiftWord_zero_gadget (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- A run of equal crossings does not change the number of strands. -/
theorem morseOut_replicate (n m q : ℕ) (s : Bool) :
    morseOut n (List.replicate m (MorseKind.cross s, q)) = n :=
  morseOut_of_cross n _ fun _ hb ↦ ⟨s, by rw [List.eq_of_mem_replicate hb]⟩

/-- A run of equal crossings fits when one does. -/
theorem morseFits_replicate (n m q : ℕ) (s : Bool) (h : q + 2 ≤ n) :
    morseFits n (List.replicate m (MorseKind.cross s, q)) = true :=
  morseFits_of_cross n _ (fun _ hb ↦ ⟨s, by rw [List.eq_of_mem_replicate hb]⟩)
    (fun _ hb ↦ by rw [List.eq_of_mem_replicate hb]; exact h)

/-- Blocks of doubled crossings do not change the number of strands. -/
private theorem morseOut_phaseTwoBlk_gadget (n m : ℕ) :
    morseOut n (phaseTwoBlk phaseTwoD m) = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show phaseTwoBlk phaseTwoD (m + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD m by
      simp [phaseTwoBlk, List.replicate_succ], morseOut_append, morseOut_phaseTwoD, ih]

/-- The twists `−4` pass the doubled cup one by one (macro `Y`, exchanges, macro `HCUPM`). -/
private theorem morseReach_gadget_twists (j : ℕ) : ∀ (i : ℕ) (v : MorseWord),
    MorseReach 1 (gadgetCups ++ List.replicate i (MorseKind.cross false, 2) ++ gadgetTailH ++
        List.replicate j (MorseKind.cross false, 4) ++ v)
      (gadgetCups ++ List.replicate (i + j) (MorseKind.cross false, 2) ++ gadgetTailH ++ v) := by
  induction j with
  | zero => intro i v; simpa using morseReach_refl 1 _
  | succ j ih =>
    intro i v
    have hu : morseOut 1 (gadgetCups ++ List.replicate i (MorseKind.cross false, 2)) = 7 := by
      rw [morseOut_append, morseOut_replicate]; rfl
    have h1 := morseReach_frame 7 1 0 0 (gadgetCups ++ List.replicate i (MorseKind.cross false, 2))
      (List.replicate j (MorseKind.cross false, 4) ++ v) _ _ morseReach_gadgetMacroY
      (by decide) hu
    have h2 := morseReach_symm (morseReach_comm 1 gadgetCups
      (List.replicate i (MorseKind.cross false, 2)) [(MorseKind.cross false, 4)]
      (gadgetTailH ++ List.replicate j (MorseKind.cross false, 4) ++ v)
      (fun _ hb ↦ ⟨false, by rw [List.eq_of_mem_replicate hb]⟩)
      (fun _ hb _ ha ↦ by
        rw [List.eq_of_mem_replicate hb, List.mem_singleton.1 ha])
      (morseFits_of_cross _ _ (fun b hb ↦ by
          rcases List.mem_append.1 hb with hb | hb
          · exact ⟨false, by rw [List.mem_singleton.1 hb]⟩
          · exact ⟨false, by rw [List.eq_of_mem_replicate hb]⟩)
        (fun b hb ↦ by
          rcases List.mem_append.1 hb with hb | hb
          · rw [List.mem_singleton.1 hb]; decide
          · rw [List.eq_of_mem_replicate hb]; decide)))
    have h3 := morseReach_frame 0 1 2 1 [(MorseKind.cup, 1)]
      (List.replicate i (MorseKind.cross false, 2) ++ gadgetTailH ++
        List.replicate j (MorseKind.cross false, 4) ++ v)
      _ _ morseReach_phaseTwoMacroHCUPM phaseTwoMacroHCUPM_fits rfl
    have e3 : ∀ w, morseShiftWord 2 w = w.map (shiftLetter 2) := fun _ ↦ rfl
    have h4 := ih (i + 1) v
    rw [morseShiftWord_zero_gadget, morseShiftWord_zero_gadget] at h1
    simp only [e3, phaseTwoMacroHCUPM_lhs, phaseTwoMacroHCUPM_rhs, List.map, shiftLetter] at h3
    rw [show i + (j + 1) = i + 1 + j by omega]
    simp only [gadgetCups, List.replicate_succ, List.append_assoc, List.cons_append,
      List.nil_append, Nat.reduceAdd] at h1 h2 h3 h4 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 h4))

set_option linter.unusedVariables false in
/-- Stage G: the clasp and its twists reach the end of the band. -/
theorem phaseTwo_stageG (k : ℕ) (hk : 1 ≤ k) : MorseReach 1 (phaseTwoWT k) (phaseTwoWG k) := by
  set a := 2 * k + 1 with ha
  set tw : ℕ → List MorseLetter := fun q ↦ List.replicate (2 * a) (MorseKind.cross false, q)
    with htw
  set caps : MorseWord := [(.cap, 3), (.cap, 2), (.cap, 1)] with hcaps
  have hBlk : phaseTwoD ++ phaseTwoBlk phaseTwoD (2 * k) = phaseTwoBlk phaseTwoD a := by
    simp [ha, phaseTwoBlk, List.replicate_succ]
  -- the gadget moves in front of `D₁`
  have h1 := morseReach_symm (morseReach_comm 1 gadgetCups phaseTwoD (phaseTwoClaspS ++ tw 4)
    (phaseTwoBlk phaseTwoD (2 * k) ++ caps)
    (fun b hb ↦ by
      simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨true, rfl⟩)
    (fun b hb c hc ↦ by
      simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
      simp only [phaseTwoClaspS, htw, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_replicate] at hc
      rcases hb with rfl | rfl | rfl | rfl <;>
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | ⟨-, rfl⟩ <;> simp)
    (by
      rw [List.append_assoc, morseFits_append, show morseOut 1 gadgetCups = 7 from rfl,
        show morseFits 7 phaseTwoClaspS = true by decide,
        show morseOut 7 phaseTwoClaspS = 7 by decide, morseFits_append,
        morseFits_replicate 7 _ 4 false (by omega), morseOut_replicate,
        morseFits_of_cross 7 phaseTwoD (fun b hb ↦ by
          simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨true, rfl⟩) (fun b hb ↦ by
          simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> simp)]
      rfl))
  -- the half twists and the clasp pass the doubled cup
  have h2 := morseReach_frame 3 1 0 0 [(MorseKind.cup, 1)]
    (tw 4 ++ phaseTwoBlk phaseTwoD a ++ caps) _ _ morseReach_gadgetMacroX (by decide) rfl
  rw [morseShiftWord_zero_gadget, morseShiftWord_zero_gadget] at h2
  -- the twists pass the doubled cup
  have h3 := morseReach_gadget_twists (2 * a) 0 (phaseTwoBlk phaseTwoD a ++ caps)
  -- the rotated gadget passes `D^a`
  have hGf : morseFits 2 (tw 0 ++ gadgetTailF) = true := by
    rw [morseFits_append, morseFits_replicate 2 _ 0 false (by omega),
      morseOut_replicate]
    decide
  have hGo : morseOut 2 (tw 0 ++ gadgetTailF) = 2 := by
    rw [morseOut_append, morseOut_replicate]
    decide
  have h4 := morseReach_beadD_pow' 1 a gadgetCups (tw 0 ++ gadgetTailF) caps hGf hGo
    (by decide)
  have hodd : ¬ a % 2 = 0 := by omega
  simp only [hodd, ↓reduceIte] at h4
  have hsh : morseShiftWord 2 (tw 0 ++ gadgetTailF) = tw 2 ++ gadgetTailH := by
    simp [htw, morseShiftWord, shiftLetter, List.map_replicate, gadgetTailF, gadgetTailH]
  rw [hsh] at h4
  -- the caps move in front of the gadget
  have hu5 : morseOut 1 (gadgetCups ++ phaseTwoBlk phaseTwoD a ++ tw 0) = 7 := by
    rw [morseOut_append, morseOut_append, morseOut_phaseTwoBlk_gadget, morseOut_replicate]
    rfl
  have h5 := morseReach_frame 7 1 0 0 (gadgetCups ++ phaseTwoBlk phaseTwoD a ++ tw 0)
    [(MorseKind.cap, 1)] _ _ morseReach_gadgetMacroZ (by decide) hu5
  rw [morseShiftWord_zero_gadget, morseShiftWord_zero_gadget] at h5
  have h6 := morseReach_symm (morseReach_comm 1 (gadgetCups ++ phaseTwoBlk phaseTwoD a) (tw 0)
    [(MorseKind.cap, 3), (MorseKind.cap, 2)] (gadgetTailF ++ [(MorseKind.cap, 1)])
    (fun _ hb ↦ ⟨false, by rw [htw] at hb; rw [List.eq_of_mem_replicate hb]⟩)
    (fun _ hb c hc ↦ by
      rw [htw] at hb
      rw [List.eq_of_mem_replicate hb]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp)
    (by
      rw [morseOut_append, morseOut_phaseTwoBlk_gadget, morseFits_append,
        show morseOut 1 gadgetCups = 7 from rfl]
      rw [show morseFits 7 [(MorseKind.cap, 3), (MorseKind.cap, 2)] = true by decide,
        show morseOut 7 [(MorseKind.cap, 3), (MorseKind.cap, 2)] = 3 by decide,
        morseFits_replicate 3 _ 0 false (by omega)]
      rfl))
  have hWT : phaseTwoWT k = gadgetCups ++ phaseTwoD ++ (phaseTwoClaspS ++ tw 4) ++
      (phaseTwoBlk phaseTwoD (2 * k) ++ caps) := by
    simp only [phaseTwoWT, gadgetCups, htw, ha, hcaps, List.append_assoc]
  have hWG : phaseTwoWG k = gadgetCups ++ phaseTwoBlk phaseTwoD a ++
      [(MorseKind.cap, 3), (MorseKind.cap, 2)] ++ tw 0 ++
        (gadgetTailF ++ [(MorseKind.cap, 1)]) := by
    simp only [phaseTwoWG, gadgetCups, htw, ha, gadgetTailF, claspWord, List.append_assoc,
      List.cons_append, List.nil_append]
  rw [hWT, hWG]
  have hBlk' : phaseTwoD ++ (phaseTwoBlk phaseTwoD (2 * k) ++ caps) =
      phaseTwoBlk phaseTwoD a ++ caps := by
    rw [← List.append_assoc, hBlk]
  simp only [List.append_assoc] at h1
  rw [hBlk'] at h1
  simp only [gadgetCups, gadgetMacroX_lhs, gadgetMacroX_rhs, htw, List.append_assoc,
    List.cons_append, List.nil_append, Nat.zero_add, List.replicate_zero] at h1 h2 h3 h4 h5 h6 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3
    (morseReach_trans h4 (morseReach_trans h5 h6))))

end AJConjecture
