import Mathlib
import AJHandoff.TorusKnot.PairKIsoThinDefs
import AJHandoff.TorusKnot.PairKIsoFlipLetter

/-!
# One thinning step

`morseReach_isoThin_step`: thinning the disc `j + 1` takes `isoThinPartial n B (j + 1)` to
`isoThinPartial n B j`. The return strand `R` of the disc (the right leg of the innermost closing
arc `u_{j+1}`) is flipped over the thin discs inside the loop, in three parts:

1. `morseReach_isoFlip_bottom`: at the cups, `R` passes the `n - j - 1` inner thin cups backwards
   by `cupSlide` (macro `HC` of the library, shifted): the cups become the thin cups of the
   discs `j + 1, …, n`, followed by the walk `morseWalk true (j + 2) (2 (n - j - 1))`;
2. `morseReach_isoFlip_block`: the walk passes the band of one block (letter steps of
   `PairKIsoFlipLetter`, then `r2` and far commutation regroup the letters into the band
   `isoBlockWord (isoThinIndex j) b`);
3. `morseReach_isoFlip_top`: at the caps, the walk is absorbed by `capSlide` (one per inner cap).

Generic in `n`, `j` and the blocks.
-/

namespace AJConjecture

/-- The walk of the flipped return strand of the disc `j + 1`. -/
def isoFlipWalk (n j : ℕ) : MorseWord := morseWalk true (j + 2) (2 * (n - j - 1))

/-- A walk grows by two crossings at its end. -/
private theorem morseWalk_add_two_isoFlip (p m : ℕ) :
    morseWalk true p (m + 2) =
      morseWalk true p m ++ [isoX true (p + m), isoX true (p + m + 1)] := by
  simp only [morseWalk, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append, isoX]
  rfl

/-- The prefix `u` followed by crossings ends on as many strands as `u`. -/
private theorem morseOut_append_cross_isoFlip (n₀ : ℕ) (u x : MorseWord)
    (hx : ∀ b ∈ x, ∃ s, b.1 = MorseKind.cross s) : morseOut n₀ (u ++ x) = morseOut n₀ u := by
  rw [morseOut_append, morseOut_of_cross _ _ hx]

/-- The letters of a walk are crossings. -/
private theorem morseWalk_cross_isoFlip (p ℓ : ℕ) :
    ∀ b ∈ morseWalk true p ℓ, ∃ s, b.1 = MorseKind.cross s :=
  fun _ hb ↦ ⟨true, (mem_morseWalk hb).1⟩

/-- A walk fits on the strands to its right. -/
private theorem morseFits_morseWalk_isoFlip (n p ℓ : ℕ) (h : p + ℓ + 1 ≤ n) :
    morseFits n (morseWalk true p ℓ) = true :=
  morseFits_of_cross _ _ (morseWalk_cross_isoFlip p ℓ) fun b hb ↦ by
    have := mem_morseWalk hb
    omega

/-- A row of cups standing at the position of a strand: the strand passes them by `cupSlide`. -/
private theorem morseReach_isoCupsWalk (n₀ q k : ℕ) (u v : MorseWord)
    (hu : q + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ ((List.range k).map fun t ↦ isoU (q + 2 * t)) ++ v)
      (u ++ ((List.range k).map fun t ↦ isoU (q + 1 + 2 * t)) ++ morseWalk true q (2 * k) ++
        v) := by
  induction k generalizing v with
  | zero => exact ⟨[], by simp [morseApplyAll, morseWalk]⟩
  | succ k ih =>
    have h1 := ih ([isoU (q + 2 * k)] ++ v)
    set C := (List.range k).map fun t ↦ isoU (q + 1 + 2 * t) with hC
    have hout : morseOut n₀ (u ++ C ++ morseWalk true q (2 * k)) = morseOut n₀ u + 2 * k := by
      rw [morseOut_append, morseOut_morseWalk, morseOut_append,
        morseOut_of_cups _ _ (by simp [hC, isoU])]
      simp [hC]
    have h2 := morseReach_symm (morseReach_isoRule n₀ (u ++ C ++ morseWalk true q (2 * k)) v
      (.cupSlide (q + 2 * k) true true) rfl
      (by
        rw [hout]
        simp only [morseRuleLhs, ↓reduceIte, morseFits_cons, morseKindIn, morseLetterOut,
          morseKindOut, morseFits_nil, and_true]
        omega)
      (by
        rw [hout]
        simp only [morseRuleRhs, ↓reduceIte, morseFits_cons, morseKindIn, morseFits_nil,
          and_true]
        omega))
    have h3 := morseReach_symm (morseReach_comm n₀ (u ++ C) (morseWalk true q (2 * k))
      [isoU (q + 2 * k + 1)] ([isoX true (q + 2 * k), isoX true (q + 2 * k + 1)] ++ v)
      (morseWalk_cross_isoFlip q _)
      (fun b hb a ha ↦ by
        rw [List.mem_singleton.mp ha]
        have := mem_morseWalk hb
        simp only [isoU]
        omega)
      (by
        rw [morseOut_append, morseOut_of_cups _ _ (by simp [hC, isoU])]
        simp only [hC, List.length_map, List.length_range, List.singleton_append, isoU,
          morseFits_cons, morseKindIn, morseLetterOut, morseKindOut]
        refine ⟨by omega, morseFits_morseWalk_isoFlip _ _ _ (by omega)⟩))
    have e1 : (List.range (k + 1)).map (fun t ↦ isoU (q + 2 * t)) =
        (List.range k).map (fun t ↦ isoU (q + 2 * t)) ++ [isoU (q + 2 * k)] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    have e2 : (List.range (k + 1)).map (fun t ↦ isoU (q + 1 + 2 * t)) =
        C ++ [isoU (q + 2 * k + 1)] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
      congr 3
      omega
    rw [e1, e2, show 2 * (k + 1) = 2 * k + 2 by ring, morseWalk_add_two_isoFlip]
    simp only [morseRuleLhs, morseRuleRhs, ↓reduceIte] at h2
    simp only [isoU, isoX, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- A walk ending at a row of caps is absorbed by them (`capSlide`). -/
private theorem morseReach_isoWalkCaps (n₀ q k : ℕ) (u v : MorseWord)
    (hu : q + 2 * k + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk true q (2 * k) ++
        ((List.range k).reverse.map fun t ↦ isoN (q + 2 * t)) ++ v)
      (u ++ ((List.range k).reverse.map fun t ↦ isoN (q + 1 + 2 * t)) ++ v) := by
  induction k generalizing u with
  | zero => exact ⟨[], by simp [morseApplyAll, morseWalk]⟩
  | succ k ih =>
    have hout : morseOut n₀ (u ++ morseWalk true q (2 * k)) = morseOut n₀ u := by
      rw [morseOut_append, morseOut_morseWalk]
    have h1 := morseReach_isoRule n₀ (u ++ morseWalk true q (2 * k))
      (((List.range k).reverse.map fun t ↦ isoN (q + 2 * t)) ++ v)
      (.capSlide (q + 2 * k) true true) rfl
      (by
        rw [hout]
        simp only [morseRuleLhs, ↓reduceIte, morseFits_cons, morseKindIn, morseLetterOut,
          morseKindOut, morseFits_nil, and_true]
        omega)
      (by
        rw [hout]
        simp only [morseRuleRhs, ↓reduceIte, morseFits_cons, morseKindIn, morseFits_nil,
          and_true]
        omega)
    have h2 := morseReach_symm (morseReach_comm n₀ u (morseWalk true q (2 * k))
      [isoN (q + 2 * k + 1)] (((List.range k).reverse.map fun t ↦ isoN (q + 2 * t)) ++ v)
      (morseWalk_cross_isoFlip q _)
      (fun b hb a ha ↦ by
        rw [List.mem_singleton.mp ha]
        have := mem_morseWalk hb
        simp only [isoN]
        omega)
      (by
        simp only [List.singleton_append, isoN, morseFits_cons, morseKindIn, morseLetterOut,
          morseKindOut]
        refine ⟨by omega, morseFits_morseWalk_isoFlip _ _ _ (by omega)⟩))
    have h3 := ih (u ++ [isoN (q + 2 * k + 1)]) (by
      rw [morseOut_append]
      simp only [isoN, morseOut, morseLetterOut, morseKindOut, morseKindIn]
      omega)
    have e1 : (List.range (k + 1)).reverse.map (fun t ↦ isoN (q + 2 * t)) =
        isoN (q + 2 * k) :: (List.range k).reverse.map (fun t ↦ isoN (q + 2 * t)) := by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons]
    have e2 : (List.range (k + 1)).reverse.map (fun t ↦ isoN (q + 1 + 2 * t)) =
        isoN (q + 2 * k + 1) :: (List.range k).reverse.map (fun t ↦ isoN (q + 1 + 2 * t)) := by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons]
      congr 2
      omega
    rw [e1, e2, show 2 * (k + 1) = 2 * k + 2 by ring, morseWalk_add_two_isoFlip]
    simp only [morseRuleLhs, morseRuleRhs, ↓reduceIte] at h1
    simp only [isoN, isoX, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- A band of span one is a single crossing. -/
private theorem isoBand_succ_self (c : ℕ) (s : Bool) : isoBand c (c + 1) s = [isoX s c] := by
  simp [isoBand, bandWord, morseOfBraid, isoX]

/-- A band peels: `b(c, d + 1) = σ_d b(c, d) σ_d⁻¹` for `c < d`. -/
private theorem isoBand_succ_right (c d : ℕ) (hcd : c < d) (s : Bool) :
    isoBand c (d + 1) s = isoX true d :: (isoBand c d s ++ [isoX false d]) := by
  obtain ⟨k, hk⟩ : ∃ k, d - 1 - c = k := ⟨_, rfl⟩
  have hk' : d + 1 - 1 - c = k + 1 := by omega
  have h1 : (List.range (k + 1)).map (fun t ↦ (d + 1 - 1 - t, true)) =
      (d, true) :: (List.range k).map (fun t ↦ (d - 1 - t, true)) := by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.cons.injEq]
    refine ⟨by simp, List.map_congr_left fun t _ ↦ ?_⟩
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    omega
  have h2 : (List.range (k + 1)).map (fun t ↦ (c + 1 + t, false)) =
      (List.range k).map (fun t ↦ (c + 1 + t, false)) ++ [(d, false)] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    congr 3
    omega
  simp only [isoBand, bandWord, hk, hk', h1, h2, morseOfBraid, isoX]
  simp

/-- A crossing does not change the number of strands. -/
private theorem morseOut_isoX_isoFlip (n i : ℕ) (s : Bool) : morseOut n [isoX s i] = n := by
  simp only [isoX, morseOut, morseLetterOut, morseKindOut, morseKindIn]
  omega

/-- A crossing in front of a word does not change the number of strands. -/
private theorem morseOut_cross_cons_isoFlip (n i : ℕ) (s : Bool) (w : MorseWord) :
    morseOut n ((MorseKind.cross s, i) :: w) = morseOut n w := by
  simp only [morseOut, morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel]

/-- The band of span two. -/
private theorem isoBand_two_isoFlip (d : ℕ) (s : Bool) :
    isoBand d (d + 1 + 1) s = [isoX true (d + 1), isoX s d, isoX false (d + 1)] := by
  rw [isoBand_succ_right d (d + 1) (by omega), isoBand_succ_self]
  rfl

/-- The shift of a position by the flipped return strand entering at `p`. -/
private def isoFlipShift (p x : ℕ) : ℕ := if x < p then x else x + 1

/-- The walk passes a band `b(c, d)`: positions at or right of `p` move one place right. -/
private theorem morseReach_isoWalk_band (n₀ p ℓ c : ℕ) (s : Bool) (hp : 1 ≤ p) :
    ∀ d, c < d → ∀ u v : MorseWord, d + 1 ≤ p + ℓ → p + ℓ + 1 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseWalk true p ℓ ++ isoBand c d s ++ v)
        (u ++ isoBand (isoFlipShift p c) (isoFlipShift p d) s ++ morseWalk true p ℓ ++ v) := by
  intro d hcd
  induction d, hcd using Nat.le_induction with
  | base =>
    intro u v hd hu
    rw [isoBand_succ_self]
    by_cases h1 : c + 2 ≤ p
    · simp only [isoFlipShift, show c < p by omega, show c + 1 < p by omega, ↓reduceIte,
        isoBand_succ_self]
      exact morseReach_isoWalk_left n₀ p ℓ c s u v h1 hu
    by_cases h2 : c + 1 = p
    · simp only [isoFlipShift, show c < p by omega, show ¬c + 1 < p by omega, ↓reduceIte]
      have := morseReach_isoWalk_boundary n₀ p ℓ s u v hp (by omega) hu
      rwa [show p - 1 = c by omega, show p + 1 = c + 1 + 1 by omega] at this
    · simp only [isoFlipShift, show ¬c < p by omega, show ¬c + 1 < p by omega, ↓reduceIte,
        isoBand_succ_self]
      exact morseReach_isoWalk_inner n₀ p ℓ c s u v (by omega) (by omega) hu
  | succ d hcd ih =>
    intro u v hd hu
    rw [isoBand_succ_right c d hcd]
    have hbc : ∀ x y : ℕ, ∀ t : Bool, ∀ l ∈ isoBand x y t, ∃ s, l.1 = MorseKind.cross s :=
      fun _ _ _ _ hl ↦ (mem_isoBand hl).1
    by_cases h1 : d + 2 ≤ p
    · have h1' := morseReach_isoWalk_left n₀ p ℓ d true u (isoBand c d s ++ [isoX false d] ++ v)
        h1 hu
      have h2' := ih (u ++ [isoX true d]) ([isoX false d] ++ v) (by omega) (by
        simp only [morseOut_append, morseOut_isoX_isoFlip]; omega)
      have h3' := morseReach_isoWalk_left n₀ p ℓ d false
        (u ++ [isoX true d] ++ isoBand (isoFlipShift p c) (isoFlipShift p d) s) v h1 (by
        simp only [morseOut_append, morseOut_isoX_isoFlip, morseOut_isoBand]; omega)
      simp only [isoFlipShift, show c < p by omega, show d < p by omega,
        show d + 1 < p by omega, ↓reduceIte] at h2' h3' ⊢
      rw [isoBand_succ_right c d hcd]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h1' h2' h3' ⊢
      exact morseReach_trans h1' (morseReach_trans h2' h3')
    by_cases h2 : d + 1 = p
    · subst h2
      have h1' := morseReach_isoWalk_boundary n₀ (d + 1) ℓ true u
        (isoBand c d s ++ [isoX false d] ++ v) (by omega) (by omega) hu
      have h2' := ih (u ++ isoBand d (d + 1 + 1) true) ([isoX false d] ++ v) (by omega) (by
        simp only [morseOut_append, morseOut_isoBand]; omega)
      have h3' := morseReach_isoWalk_boundary n₀ (d + 1) ℓ false
        (u ++ isoBand d (d + 1 + 1) true ++ isoBand (isoFlipShift (d + 1) c)
          (isoFlipShift (d + 1) d) s) v (by omega) (by omega) (by
        simp only [morseOut_append, morseOut_isoBand]; omega)
      simp only [isoFlipShift, show c < d + 1 by omega, show d < d + 1 by omega,
        show ¬d + 1 < d + 1 by omega, ↓reduceIte, Nat.add_sub_cancel] at h1' h2' h3' ⊢
      have h4' := morseReach_comm n₀ (u ++ [isoX true (d + 1), isoX true d]) (isoBand c d s)
        [isoX false (d + 1)] ([isoX true (d + 1), isoX false d, isoX false (d + 1)] ++
          morseWalk true (d + 1) ℓ ++ v) (hbc _ _ _)
        (fun b hb a ha ↦ by
          rw [List.mem_singleton.mp ha]
          have := mem_isoBand hb
          simp only [isoX]
          omega)
        (by
          rw [morseFits_append]
          simp only [morseOut_append, isoX, morseOut, morseFits_cons,
            morseKindIn, morseLetterOut, morseKindOut, morseFits_nil, and_true, Bool.and_eq_true]
          refine ⟨by omega, morseFits_of_cross _ _ (hbc _ _ _) fun b hb ↦ ?_⟩
          have := mem_isoBand hb
          omega)
      have h5' := morseReach_isoRule n₀
        (u ++ [isoX true (d + 1), isoX true d] ++ isoBand c d s)
        ([isoX false d, isoX false (d + 1)] ++ morseWalk true (d + 1) ℓ ++ v)
        (.r2 (d + 1) false) rfl
        (by
          simp only [morseOut_append, isoX, morseOut, morseOut_isoBand, morseRuleLhs,
            morseFits_cons, morseKindIn, morseLetterOut, morseKindOut, morseFits_nil, and_true]
          omega)
        rfl
      rw [isoBand_succ_right c (d + 1) (by omega), isoBand_succ_right c d hcd]
      simp only [isoBand_two_isoFlip] at h1' h2' h3'
      simp only [morseRuleLhs, morseRuleRhs, Bool.not_false] at h5'
      simp only [isoX, List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil] at h1' h2' h3' h4' h5' ⊢
      exact morseReach_trans h1' (morseReach_trans h2' (morseReach_trans h3'
        (morseReach_trans h4' h5')))
    · have h1' := morseReach_isoWalk_inner n₀ p ℓ d true u
        (isoBand c d s ++ [isoX false d] ++ v) (by omega) (by omega) hu
      have h2' := ih (u ++ [isoX true (d + 1)]) ([isoX false d] ++ v) (by omega) (by
        simp only [morseOut_append, morseOut_isoX_isoFlip]; omega)
      have h3' := morseReach_isoWalk_inner n₀ p ℓ d false
        (u ++ [isoX true (d + 1)] ++ isoBand (isoFlipShift p c) (isoFlipShift p d) s) v
        (by omega) (by omega) (by
        simp only [morseOut_append, morseOut_isoX_isoFlip, morseOut_isoBand]; omega)
      have hsc : isoFlipShift p c < d + 1 := by
        simp only [isoFlipShift]
        split_ifs <;> omega
      have hsd : isoFlipShift p d = d + 1 := by simp only [isoFlipShift]; split_ifs <;> omega
      have hsd' : isoFlipShift p (d + 1) = d + 1 + 1 := by
        simp only [isoFlipShift]; split_ifs <;> omega
      rw [hsd] at h2' h3'
      rw [hsd', isoBand_succ_right _ _ hsc]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h1' h2' h3' ⊢
      exact morseReach_trans h1' (morseReach_trans h2' h3')

/-- Bottom of the flip: the return strand passes the inner thin cups. -/
theorem morseReach_isoFlip_bottom (n j n₀ : ℕ) (u v : MorseWord) (hj : j < n)
    (hu : j + 1 ≤ morseOut n₀ u) :
    MorseReach n₀
      (u ++ [isoU (j + 1)] ++ ((List.range (n - j - 1)).map fun t ↦ isoU (j + 2 + 2 * t)) ++ v)
      (u ++ ((List.range (n - j)).map fun t ↦ isoU (j + 1 + 2 * t)) ++ isoFlipWalk n j ++ v) := by
  have h := morseReach_isoCupsWalk n₀ (j + 2) (n - j - 1) (u ++ [isoU (j + 1)]) v (by
    rw [morseOut_append]
    simp only [isoU, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega)
  have e : (List.range (n - j)).map (fun t ↦ isoU (j + 1 + 2 * t)) =
      isoU (j + 1) :: (List.range (n - j - 1)).map (fun t ↦ isoU (j + 2 + 1 + 2 * t)) := by
    rw [show n - j = n - j - 1 + 1 by omega, List.range_succ_eq_map, List.map_cons,
      List.map_map, Nat.add_sub_cancel]
    congr 1
    exact List.map_congr_left fun t _ ↦ by simp only [Function.comp_apply]; congr 1; omega
  rw [e, isoFlipWalk]
  simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
    using h

/-- Middle of the flip: the walk passes the band of a block, whose discs are relabelled from
`isoThinIndex (j + 1)` to `isoThinIndex j`. -/
theorem morseReach_isoFlip_block (n j n₀ : ℕ) (b : SBlock) (u v : MorseWord) (hj : j < n)
    (hb : b.Valid (n + 1)) (hu : j + 2 + 2 * (n - j - 1) + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ isoFlipWalk n j ++ isoBlockWord (isoThinIndex (j + 1)) b ++ v)
      (u ++ isoBlockWord (isoThinIndex j) b ++ isoFlipWalk n j ++ v) := by
  have hv := isoEnds_lt hb
  have hsh : ∀ x, isoFlipShift (j + 2) (isoThinIndex (j + 1) x) = isoThinIndex j x := by
    intro x
    simp only [isoFlipShift, isoThinIndex]
    split_ifs <;> omega
  have h := morseReach_isoWalk_band n₀ (j + 2) (2 * (n - j - 1)) (isoThinIndex (j + 1)
    (isoEnds b).1) (isoSign b) (by omega) (isoThinIndex (j + 1) (isoEnds b).2)
    (by simp only [isoThinIndex]; split_ifs <;> omega) u v
    (by simp only [isoThinIndex]; split_ifs <;> omega) hu
  rw [hsh, hsh] at h
  exact h

/-- Top of the flip: the inner thin caps absorb the walk. -/
theorem morseReach_isoFlip_top (n j n₀ : ℕ) (u v : MorseWord) (hj : j < n)
    (hu : morseOut n₀ u = j + 2 + 2 * (n - j - 1) + 1 + j) :
    MorseReach n₀
      (u ++ isoFlipWalk n j ++
        ((List.range (n - j - 1)).reverse.map fun t ↦ isoN (j + 2 + 2 * t)) ++ [isoN (j + 1)] ++ v)
      (u ++ ((List.range (n - j)).reverse.map fun t ↦ isoN (j + 1 + 2 * t)) ++ v) := by
  have h := morseReach_isoWalkCaps n₀ (j + 2) (n - j - 1) u ([isoN (j + 1)] ++ v) (by omega)
  have e : (List.range (n - j)).reverse.map (fun t ↦ isoN (j + 1 + 2 * t)) =
      (List.range (n - j - 1)).reverse.map (fun t ↦ isoN (j + 2 + 1 + 2 * t)) ++
        [isoN (j + 1)] := by
    rw [show n - j = n - j - 1 + 1 by omega, List.range_succ_eq_map, List.reverse_cons,
      List.map_append, List.map_reverse, List.map_reverse, List.map_map]
    congr 2
    · exact List.map_congr_left fun t _ ↦ by simp only [Function.comp_apply]; congr 1; omega
  rw [e, isoFlipWalk]
  simpa only [List.append_assoc] using h

/-- The walk passes the block words of a whole block list. -/
private theorem morseReach_isoFlip_blocks (n j n₀ : ℕ) (B : List SBlock) (hj : j < n)
    (hB : ∀ b ∈ B, b.Valid (n + 1)) :
    ∀ u v : MorseWord, j + 2 + 2 * (n - j - 1) + 1 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ isoFlipWalk n j ++ B.flatMap (isoBlockWord (isoThinIndex (j + 1))) ++ v)
        (u ++ B.flatMap (isoBlockWord (isoThinIndex j)) ++ isoFlipWalk n j ++ v) := by
  induction B with
  | nil => exact fun u v _ ↦ ⟨[], by simp [morseApplyAll]⟩
  | cons b B ih =>
    intro u v hu
    have h1 := morseReach_isoFlip_block n j n₀ b u
      (B.flatMap (isoBlockWord (isoThinIndex (j + 1))) ++ v) hj (hB b List.mem_cons_self) hu
    have h2 := ih (fun x hx ↦ hB x (List.mem_cons_of_mem _ hx))
      (u ++ isoBlockWord (isoThinIndex j) b) v (by
        rw [morseOut_append, isoBlockWord, morseOut_isoBand]
        exact hu)
    simp only [List.flatMap_cons, List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- One thinning step: the disc `j + 1` is thinned. -/
theorem morseReach_isoThin_step {n j : ℕ} {B : List SBlock} (hB : ∀ b ∈ B, b.Valid (n + 1))
    (hj : j < n) : MorseReach 1 (isoThinPartial n B (j + 1)) (isoThinPartial n B j) := by
  set U := (List.range j).map fun i ↦ isoU (i + 1) with hU
  set N := (List.range j).reverse.map fun i ↦ isoN (i + 1) with hN
  set Cn := (List.range (n - j)).map fun t ↦ isoU (j + 1 + 2 * t) with hCn
  have hUout : morseOut 1 U = 2 * j + 1 := by
    rw [morseOut_of_cups _ _ (by simp [hU, isoU])]
    simp only [hU, List.length_map, List.length_range]
    omega
  have hCout : morseOut 1 (U ++ Cn) = 2 * n + 1 := by
    rw [morseOut_append, hUout, morseOut_of_cups _ _ (by simp [hCn, isoU])]
    simp only [hCn, List.length_map, List.length_range]
    omega
  have e1 : isoThinPartial n B (j + 1) = U ++ [isoU (j + 1)] ++
      ((List.range (n - j - 1)).map fun t ↦ isoU (j + 2 + 2 * t)) ++
      B.flatMap (isoBlockWord (isoThinIndex (j + 1))) ++
      ((List.range (n - j - 1)).reverse.map fun t ↦ isoN (j + 2 + 2 * t)) ++ [isoN (j + 1)] ++
      N := by
    simp only [isoThinPartial, hU, hN, List.range_succ, List.map_append, List.map_singleton,
      List.reverse_append, List.reverse_singleton, Nat.sub_sub, List.append_assoc,
      List.cons_append]
    rfl
  have h1 := morseReach_isoFlip_bottom n j 1 U
    (B.flatMap (isoBlockWord (isoThinIndex (j + 1))) ++
      ((List.range (n - j - 1)).reverse.map fun t ↦ isoN (j + 2 + 2 * t)) ++ [isoN (j + 1)] ++
      N) hj (by omega)
  have h2 := morseReach_isoFlip_blocks n j 1 B hj hB (U ++ Cn)
    (((List.range (n - j - 1)).reverse.map fun t ↦ isoN (j + 2 + 2 * t)) ++ [isoN (j + 1)] ++ N)
    (by omega)
  have h3 := morseReach_isoFlip_top n j 1
    (U ++ Cn ++ B.flatMap (isoBlockWord (isoThinIndex j))) N hj (by
      rw [morseOut_append, hCout, morseOut_isoBlockWords]
      omega)
  rw [e1, isoThinPartial]
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

end AJConjecture
