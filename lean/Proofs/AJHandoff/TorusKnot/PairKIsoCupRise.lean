import Mathlib
import AJHandoff.TorusKnot.PairKIsoFenceDefs

/-!
# A dead-end cup rises past one block

While the discs `1, …, j` are kept open, the disc `j + 1` sits at the position `2j + 1` wherever it
is open. Below its first block its cup is a dead end: it rises past a block `k < isoFirst B (j+1)`
(which is not attached to the disc `j + 1`) by exchanges with the letters on either side of it and
by `cupSlide` where an edge of the band passes in front of both legs of the cup. The block is then
drawn with the disc `j + 1` closed: its positions above `2j + 1` drop by two.

`morseReach_isoFence_capBlock` (file `PairKIsoCapFall`) is the mirror statement for the cap.
-/

namespace AJConjecture

/-- Fitting of a concatenation, split. -/
private theorem morseFits_split_cupRise {n : ℕ} {x y : MorseWord}
    (h : morseFits n (x ++ y) = true) :
    morseFits n x = true ∧ morseFits (morseOut n x) y = true := by
  rwa [morseFits_append, Bool.and_eq_true] at h

/-- The cup of the disc `j + 1` rises past a block below its first block, provided the disc
carries a block (`isoFirst B (j + 1) ≤ isoLast B (j + 1)`; without it the statement
`morseReach_isoFence_cupBlock` fails, see the report of this file). -/
theorem morseReach_isoFence_cupBlock_of_le {n j k n₀ : ℕ} {B : List SBlock} {b : SBlock}
    (hB : ∀ b ∈ B, b.Valid (n + 1)) (hk : k < isoFirst B (j + 1))
    (hfl : isoFirst B (j + 1) ≤ isoLast B (j + 1)) (hbk : B[k]? = some b) (u v : MorseWord)
    (hfit : morseFits n₀ (u ++ [isoU (2 * j + 1)] ++ isoFenceBlock n B (j + 1) k b) = true) :
    MorseReach n₀ (u ++ [isoU (2 * j + 1)] ++ isoFenceBlock n B (j + 1) k b ++ v)
      (u ++ isoFenceBlock n B j k b ++ [isoU (2 * j + 1)] ++ v) := by
  have hno : ¬(isoFirst B (j + 1) ≤ k ∧ k ≤ isoLast B (j + 1)) := by omega
  have hv := isoEnds_lt (hB b (List.mem_of_getElem? hbk))
  have hne := isoEnds_ne_of_not_attached (isoAttached_of_lt_isoFirst hk hbk)
  obtain ⟨a, b', hab⟩ : ∃ a b', isoEnds b = (a, b') := ⟨_, _, rfl⟩
  rw [hab] at hv hne
  simp only at hv hne
  have hpos := fun m ↦ isoPos_succ_of_not_open B j k m hno
  have hP0 : isoPos B j k 0 = 0 := by simp [isoPos]
  have hPa := isoPos_lt_two_mul B j k (m := a)
  have hPb := isoPos_lt_two_mul B j k (m := b')
  have hbw : ∀ f, isoBlockWord f b = isoBand (f a) (f b') (isoSign b) := fun f ↦ by
    simp [isoBlockWord, hab]
  set q := 2 * j + 1 with hq
  set C := isoFenceCups n B j k with hC
  set K := isoFenceCaps n B j k with hK
  set P := isoPos B j k with hP
  set Band' := isoBand (isoPos B (j + 1) k a) (isoPos B (j + 1) k b') (isoSign b) with hBand'
  set Band := isoBand (P a) (P b') (isoSign b) with hBand
  rw [isoFenceBlock_eq, isoFenceCups_succ n B j k hno (by omega),
    isoFenceCaps_succ n B j k hno (by omega), hbw, ← hC, ← hK] at hfit ⊢
  rw [isoFenceBlock_eq, hbw, ← hC, ← hK]
  set N0 := morseOut n₀ u with hN0
  have hCcup : ∀ l ∈ [isoU q] ++ morseShiftWord 2 C, l.1 = MorseKind.cup := by
    intro l hl
    simp only [List.singleton_append, List.mem_cons, morseShiftWord, List.mem_map] at hl
    rcases hl with rfl | ⟨l', hl', rfl⟩
    · rfl
    · exact (mem_isoFenceCups hl').1
  have hout1 : morseOut N0 ([isoU q] ++ morseShiftWord 2 C) = N0 + 2 + 2 * C.length := by
    rw [morseOut_of_cups _ _ hCcup]
    simp only [List.length_append, List.length_singleton, morseShiftWord, List.length_map]
    omega
  have hN : morseOut n₀ (u ++ C) = N0 + 2 * C.length := by
    rw [morseOut_append, morseOut_of_cups _ _ fun l hl ↦ (mem_isoFenceCups hl).1]
  have hf2 : morseFits N0 ([isoU q] ++ morseShiftWord 2 C ++ Band' ++ morseShiftWord 2 K) =
      true := by
    have := hfit
    rw [show u ++ [isoU q] ++ (morseShiftWord 2 C ++ Band' ++ morseShiftWord 2 K) =
      u ++ ([isoU q] ++ morseShiftWord 2 C ++ Band' ++ morseShiftWord 2 K) by simp,
      morseFits_append, Bool.and_eq_true] at this
    exact this.2
  obtain ⟨h12, hZ⟩ := morseFits_split_cupRise hf2
  obtain ⟨h1, hY⟩ := morseFits_split_cupRise h12
  rw [hout1] at hY
  rw [morseOut_append, hout1, hBand', morseOut_isoBand] at hZ
  have hqN0 : q ≤ N0 := by
    have := (morseFits_split_cupRise h1).1
    simp only [isoU, morseFits_cons, morseKindIn] at this
    omega
  have hA := morseReach_isoCupSweep n₀ q u C (Band' ++ morseShiftWord 2 K ++ v)
    (fun l hl ↦ (mem_isoFenceCups hl).2) (by simpa using h1)
  have hB : MorseReach n₀ (u ++ C ++ [isoU q] ++ Band' ++ (morseShiftWord 2 K ++ v))
      (u ++ C ++ Band ++ [isoU q] ++ (morseShiftWord 2 K ++ v)) := by
    by_cases hi : b' ≤ j
    · have e : Band' = Band := by
        rw [hBand', hBand, hpos a, hpos b']
        simp only [show ¬j + 1 < a by omega, show ¬j + 1 < b' by omega, ↓reduceIte,
          Nat.add_zero]
      rw [e]
      refine morseReach_comm n₀ (u ++ C) Band [isoU q] _ (fun _ hl ↦ (mem_isoBand hl).1)
        (fun l hl x hx ↦ ?_) ?_
      · rw [List.mem_singleton.mp hx]
        have hl' := (mem_isoBand hl).2
        have hb2 := hPb (by omega)
        simp only [isoU]
        by_cases ha : a = 0
        · rw [ha, hP0] at hl'
          omega
        · have := hPa (by omega)
          omega
      · rw [hN, List.singleton_append, morseFits_cons]
        refine ⟨by simp only [isoU, morseKindIn]; omega, ?_⟩
        rw [← e]
        simp only [isoU, morseLetterOut, morseKindOut, morseKindIn]
        rw [show N0 + 2 * C.length + 2 - 0 = N0 + 2 + 2 * C.length by omega]
        exact hY
    by_cases hii : j + 1 < a
    · have e : Band' = morseShiftWord 2 Band := by
        rw [hBand', hBand, hpos a, hpos b', ← isoBand_add]
        simp only [hii, show j + 1 < b' by omega, ↓reduceIte]
      rw [e]
      refine morseReach_isoCupSweep n₀ q (u ++ C) Band _ (fun l hl ↦ ?_) ?_
      · have := (mem_isoBand hl).2.1
        have : 2 * j + 1 ≤ P a := le_isoPos_of_lt B (show j < a by omega)
        omega
      · rw [hN, morseFits_cons]
        refine ⟨by simp only [isoU, morseKindIn]; omega, ?_⟩
        rw [← e]
        simp only [isoU, morseLetterOut, morseKindOut, morseKindIn]
        rw [show N0 + 2 * C.length + 2 - 0 = N0 + 2 + 2 * C.length by omega]
        exact hY
    · have e : Band' = isoBand (P a) (P b' + 2) (isoSign b) := by
        rw [hBand', hpos a, hpos b']
        simp only [show ¬j + 1 < a by omega, show j + 1 < b' by omega, ↓reduceIte,
          Nat.add_zero]
      have hca : P a < q := by
        by_cases ha : a = 0
        · rw [ha, hP0]
          omega
        · have := hPa (by omega)
          omega
      have hqb : 2 * j + 1 ≤ P b' := le_isoPos_of_lt B (show j < b' by omega)
      have hYb : P b' + 2 + 1 ≤ N0 + 2 + 2 * C.length := by
        rw [e] at hY
        exact le_of_morseFits_isoBand (by omega) hY
      have := morseReach_isoCupBand n₀ q (P a) (isoSign b) hca (P b' + 2) (by omega) (u ++ C)
        (morseShiftWord 2 K ++ v) (by rw [hN]; omega) (by rw [hN]; omega)
      rw [Nat.add_sub_cancel] at this
      rw [e]
      exact this
  have hC' := morseReach_isoCupSweep n₀ q (u ++ C ++ Band) K v
    (fun l hl ↦ (mem_isoFenceCaps hl).2) (by
      rw [morseOut_append, morseOut_isoBand, hN, morseFits_cons]
      refine ⟨by simp only [isoU, morseKindIn]; omega, ?_⟩
      simpa [isoU, morseLetterOut, morseKindOut, morseKindIn, Nat.add_right_comm] using hZ)
  simp only [List.append_assoc] at hA hB hC' ⊢
  exact morseReach_trans hA (morseReach_trans hB hC')

end AJConjecture
