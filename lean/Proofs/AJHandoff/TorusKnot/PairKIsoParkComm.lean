import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: generic exchanges of a tangle

A tangle `T` from `b` strands to `b` strands placed at the position `m` (a band bead: `b = 2`,
`m = 2p`; a curl on the return strand: `b = 1`) commutes with any word acting only on strands to
its right (`morseReach_isoBead_commR`: letters at positions `≥ m + b`, which `T` does not shift)
or only on strands to its left (`morseReach_isoBead_commL`: the word fits on the first `m`
strands; `T` is shifted by the change of the number of strands on its left). Proof: the `exch`
rule letter by letter (`morseReach_sweep` and its mirror), by induction on the word. Every stack
of beads is a tangle from two strands to two strands (`morseFits_isoBeadsWord`), and rotation by
`π` is an involution (`isoRot_isoRot`).
-/

namespace AJConjecture

/-- A stack of beads is a tangle from two strands to two strands, with any idle strands on the
right. -/
theorem morseFits_isoBeadsWord (L : List IsoBead) (e : ℕ) :
    morseFits (2 + e) (isoBeadsWord L) = true ∧ morseOut (2 + e) (isoBeadsWord L) = 2 + e := by
  have hb : ∀ b, morseFits 2 (isoBeadWord b) = true ∧ morseOut 2 (isoBeadWord b) = 2 := by
    intro b; cases b <;> decide
  induction L with
  | nil => exact ⟨rfl, rfl⟩
  | cons b L ih =>
    have h1 := morseFits_add_right_iso 2 e _ (hb b).1
    have h2 := morseOut_add_right 2 e _ (hb b).1
    rw [(hb b).2] at h2
    simp only [isoBeadsWord, List.flatMap_cons] at ih ⊢
    rw [morseFits_append, morseOut_append, h1, h2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- A word whose shift fits also fits without the shift. -/
private theorem morseFits_unshift_park (d : ℕ) :
    ∀ (w0 : MorseWord) (N : ℕ), d ≤ N → morseFits N (morseShiftWord d w0) = true →
      morseFits (N - d) w0 = true
  | [], _, _, _ => rfl
  | l :: w0, N, hd, h => by
    simp only [morseShiftWord, List.map_cons] at h
    rw [morseFits_cons] at h ⊢
    simp only [shiftLetter] at h
    refine ⟨by omega, ?_⟩
    have := morseFits_unshift_park d w0 (morseLetterOut N (shiftLetter d l))
      (by simp only [morseLetterOut, shiftLetter]; omega) h.2
    rwa [show morseLetterOut N (shiftLetter d l) - d = morseLetterOut (N - d) l by
      simp only [morseLetterOut, shiftLetter]; omega] at this

/-- A tangle commutes with a word acting on the strands to its right. -/
theorem morseReach_isoBead_commR (n₀ m b : ℕ) (T u w v : MorseWord) (hT : morseFits b T = true)
    (hTo : morseOut b T = b) (hw : ∀ l ∈ w, m + b ≤ l.2)
    (hfit : morseFits (morseOut n₀ u) w = true) (hu : m + b ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord m T ++ w ++ v) (u ++ w ++ morseShiftWord m T ++ v) := by
  set w0 : MorseWord := w.map fun l ↦ (l.1, l.2 - (m + b)) with hw0
  have hw' : morseShiftWord (m + b) w0 = w := by
    simp only [hw0, morseShiftWord, List.map_map]
    conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left fun l hl ↦ by
      have := hw l hl
      simp only [Function.comp, shiftLetter, id]
      exact Prod.ext rfl (by simp only; omega)
  have hX : morseFits (m + b) (morseShiftWord m T) = true := by
    have := morseFits_morseShiftWord b m 0 T hT
    rwa [Nat.add_zero, Nat.add_comm] at this
  have hY : morseFits (morseOut n₀ u - (m + b)) w0 = true :=
    morseFits_unshift_park (m + b) w0 _ hu (by rw [hw']; exact hfit)
  have h := morseReach_isoShiftComm n₀ (m + b) (morseOut n₀ u - (m + b)) 0 u
    (morseShiftWord m T) w0 v hX hY (by omega)
  rw [show morseOut (m + b) (morseShiftWord m T) = m + b by
    rw [Nat.add_comm m b, morseOut_morseShiftWord _ _ _ hT, hTo]] at h
  rw [hw'] at h
  exact morseReach_symm h

set_option linter.unusedVariables false in
/-- A tangle commutes with a word acting on the strands to its left (the tangle is shifted). -/
theorem morseReach_isoBead_commL (n₀ m b e : ℕ) (T u w v : MorseWord) (hT : morseFits b T = true)
    (hTo : morseOut b T = b) (hw : morseFits m w = true) (hu : morseOut n₀ u = m + b + e) :
    MorseReach n₀ (u ++ morseShiftWord m T ++ w ++ v)
      (u ++ w ++ morseShiftWord (morseOut m w) T ++ v) := by
  exact morseReach_isoShiftComm n₀ m b e u w T v hw hT hu

/-- Rotation by `π` is an involution. -/
theorem isoRot_isoRot (n : ℕ) (w : MorseWord) (hw : morseFits n w = true) :
    isoRot (morseOut n w) (isoRot n w) = w := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    rw [morseFits_cons] at hw
    have hR := isoRot_fits w (morseLetterOut n l) hw.2
    rw [isoRot, morseOut, isoRot_append, hR.2, ih _ hw.2]
    simp only [isoRot, List.nil_append, isoRotLetter_isoRotLetter n l hw.1]
    rfl

end AJConjecture
