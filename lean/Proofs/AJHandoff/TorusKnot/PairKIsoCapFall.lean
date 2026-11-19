import Mathlib
import AJHandoff.TorusKnot.PairKIsoFenceDefs

/-!
# A dead-end cap falls past one block

Mirror of `PairKIsoCupRise`: above its last block the cap of the disc `j + 1` (at the position
`2j + 1`) falls past a block `k > isoLast B (j + 1)` by exchanges and `capSlide`.
-/

namespace AJConjecture

set_option linter.unusedVariables false in
/-- The cap of the disc `j + 1` falls past a block above its last block. -/
theorem morseReach_isoFence_capBlock {n j k n₀ : ℕ} {B : List SBlock} {b : SBlock}
    (hB : ∀ b ∈ B, b.Valid (n + 1)) (hj : j < n) (hk : isoLast B (j + 1) < k)
    (hbk : B[k]? = some b) (u v : MorseWord)
    (hfit : morseFits n₀ (u ++ isoFenceBlock n B (j + 1) k b ++ [isoN (2 * j + 1)]) = true) :
    MorseReach n₀ (u ++ isoFenceBlock n B (j + 1) k b ++ [isoN (2 * j + 1)] ++ v)
      (u ++ [isoN (2 * j + 1)] ++ isoFenceBlock n B j k b ++ v) := by
  have hatt := isoAttached_of_isoLast_lt hk hbk
  obtain ⟨hklen, hbk'⟩ := List.getElem?_eq_some_iff.mp hbk
  have hno : ¬(isoFirst B (j + 1) ≤ k ∧ k ≤ isoLast B (j + 1)) := by omega
  have hf : isoFirst B (j + 1) ≠ k := by
    intro h
    have := List.findIdx_getElem (p := isoAttached (j + 1)) (xs := B)
      (w := by rw [show List.findIdx (isoAttached (j + 1)) B = k from h]; exact hklen)
    simp only [show List.findIdx (isoAttached (j + 1)) B = k from h, hbk', hatt] at this
    exact Bool.false_ne_true this
  have hv := isoEnds_lt (hB b (List.mem_of_getElem? hbk))
  have hne := isoEnds_ne_of_not_attached hatt
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
  rw [isoFenceBlock_eq, isoFenceCups_succ n B j k hno hf,
    isoFenceCaps_succ n B j k hno (by omega), hbw, ← hC, ← hK] at hfit ⊢
  rw [isoFenceBlock_eq, hbw, ← hC, ← hK]
  set N0 := morseOut n₀ u with hN0
  have hCcup : ∀ l ∈ morseShiftWord 2 C, l.1 = MorseKind.cup := by
    intro l hl
    simp only [morseShiftWord, List.mem_map] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact (mem_isoFenceCups hl').1
  have hKcap : ∀ l ∈ morseShiftWord 2 K, l.1 = MorseKind.cap := by
    intro l hl
    simp only [morseShiftWord, List.mem_map] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact (mem_isoFenceCaps hl').1
  have hM : morseOut n₀ (u ++ morseShiftWord 2 C) = N0 + 2 * C.length := by
    rw [morseOut_append, morseOut_of_cups _ _ hCcup]
    simp [morseShiftWord, hN0]
  have hM' : morseOut n₀ (u ++ morseShiftWord 2 C ++ Band') = N0 + 2 * C.length := by
    rw [morseOut_append, hM, hBand', morseOut_isoBand]
  rw [show u ++ (morseShiftWord 2 C ++ Band' ++ morseShiftWord 2 K) ++ [isoN q] =
    u ++ morseShiftWord 2 C ++ Band' ++ (morseShiftWord 2 K ++ [isoN q]) by simp] at hfit
  rw [morseFits_append, Bool.and_eq_true, hM'] at hfit
  obtain ⟨hfit1, hKn⟩ := hfit
  rw [morseFits_append, Bool.and_eq_true, hM] at hfit1
  obtain ⟨hfitC, hY⟩ := hfit1
  rw [morseFits_append, Bool.and_eq_true] at hfitC
  have hqM : q + 2 ≤ N0 + 2 * C.length := by
    have := (morseFits_append _ _ _ ▸ hKn : _)
    rw [Bool.and_eq_true, morseOut_of_caps _ _ hKcap] at this
    simp only [isoN, morseFits_cons, morseKindIn] at this
    omega
  have hA := morseReach_isoCapSweep n₀ q (u ++ morseShiftWord 2 C ++ Band') K v
    (fun l hl ↦ (mem_isoFenceCaps hl).2) (by rw [hM']; exact hKn)
  have hB : MorseReach n₀ (u ++ morseShiftWord 2 C ++ Band' ++ [isoN q] ++ (K ++ v))
      (u ++ morseShiftWord 2 C ++ [isoN q] ++ Band ++ (K ++ v)) := by
    by_cases hi : b' ≤ j
    · have e : Band' = Band := by
        rw [hBand', hBand, hpos a, hpos b']
        simp only [show ¬j + 1 < a by omega, show ¬j + 1 < b' by omega, ↓reduceIte,
          Nat.add_zero]
      have hlt : ∀ l ∈ Band, l.2 + 2 ≤ q := by
        intro l hl
        have hl' := (mem_isoBand hl).2
        have hb2 := hPb (by omega)
        by_cases ha : a = 0
        · rw [ha, hP0] at hl'
          omega
        · have := hPa (by omega)
          omega
      rw [e]
      refine morseReach_symm (morseReach_comm n₀ (u ++ morseShiftWord 2 C) Band [isoN q] _
        (fun _ hl ↦ (mem_isoBand hl).1) (fun l hl x hx ↦ ?_) ?_)
      · rw [List.mem_singleton.mp hx]
        exact hlt l hl
      · rw [hM, List.singleton_append, morseFits_cons]
        refine ⟨by simp only [isoN, morseKindIn]; omega, ?_⟩
        refine morseFits_of_cross _ _ (fun _ hl ↦ (mem_isoBand hl).1) fun l hl ↦ ?_
        have := hlt l hl
        simp only [isoN, morseLetterOut, morseKindOut, morseKindIn]
        omega
    by_cases hii : j + 1 < a
    · have e : Band' = morseShiftWord 2 Band := by
        rw [hBand', hBand, hpos a, hpos b', ← isoBand_add]
        simp only [hii, show j + 1 < b' by omega, ↓reduceIte]
      rw [e]
      refine morseReach_isoCapSweep n₀ q (u ++ morseShiftWord 2 C) Band _ (fun l hl ↦ ?_) ?_
      · have := (mem_isoBand hl).2.1
        have : 2 * j + 1 ≤ P a := le_isoPos_of_lt B (show j < a by omega)
        omega
      · rw [hM, morseFits_append, ← e, hY, Bool.true_and, hBand', morseOut_isoBand]
        simp only [isoN, morseFits_cons, morseKindIn, morseFits_nil, and_true]
        omega
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
      have hYb : P b' + 2 + 1 ≤ N0 + 2 * C.length := by
        rw [e] at hY
        exact le_of_morseFits_isoBand (by omega) hY
      have := morseReach_isoCapBand n₀ q (P a) (isoSign b) hca (P b' + 2) (by omega)
        (u ++ morseShiftWord 2 C) (K ++ v) (by rw [hM]; omega)
      rw [Nat.add_sub_cancel] at this
      rw [e]
      exact this
  have hC' := morseReach_isoCapSweep n₀ q u C (Band ++ K ++ v)
    (fun l hl ↦ (mem_isoFenceCups hl).2) (by
      rw [morseFits_append, hfitC.2, Bool.true_and, ← morseOut_append, hM]
      simp only [isoN, morseFits_cons, morseKindIn, morseFits_nil, and_true]
      omega)
  simp only [List.append_assoc] at hA hB hC' ⊢
  exact morseReach_trans hA (morseReach_trans hB hC')

end AJConjecture
