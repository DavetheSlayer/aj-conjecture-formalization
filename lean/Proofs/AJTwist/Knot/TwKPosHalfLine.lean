import Mathlib
import AJTwist.Knot.TwKSourceOp
import AJTwist.Knot.TwKPosFenceTwo
import AJTwist.Knot.TwKPosStripN
import AJTwist.Knot.TwKPosSwing
import AJTwist.Knot.TwKPosTwo
import AJTwist.Knot.TwKPosTwoSwing
import AJTwist.Knot.TwKPosEvac
import AJTwist.Knot.TwKPosBeaded
import AJTwist.Knot.TwKPosBeadedTwo
import AJTwist.Knot.TwKPosBeadAlg

/-!
# The half line `ℓ ≤ 0` for a clasp of either sign: assembly

`twkSrcOp_halfLine`: the operator form of the band-and-clasp identity for the twists
`ℓ = -n ≤ 0` and the clasp of sign `σ`, proved here from the nodes `TwKPos*` (this file has no
`sorry` of its own):

1. the fence word in closed form (`TwKPosFence`, `TwKPosFenceTwo`); the positive clasp changes
   two letters;
2. stage N (`TwKPosStripN`, `TwKPosTwo`): the block normal forms of the library; the positive
   tip is the negative tip after one negative full twist of the Hopf pair
   (`morseReach_twkTipFlip`);
3. stage S and the doubled core with beads (`TwKPosSwing`, `TwKPosTwoSwing`): hook, twist and
   tip are the clasp of sign `σ` (`morseReach_twkKRaw`);
4. evacuation (`TwKPosEvac`): all beads move to the top end of the doubled core, in an order
   that is not computed;
5. the operator of the evacuated word (`TwKPosBeadAlg`) does not depend on that order; it is the
   operator of the band-and-clasp word (`morseOp_twTargetWord`).

No stage of the port chain of Theorem T (normalisation, snowballs, processing, gadget, stage E)
is used, and the clasp is never an element of a bead alphabet. `σ = false` is the positive clasp
(`twSrcOp_halfLine_pos` in `TwKHalfLinePos`); `σ = true` is the statement `twSrcOp_halfLine` of
`TwKHalfLine` (this file does not import `TwKHalfLine`, so that file may use it).
-/

noncomputable section

namespace AJConjecture

/-- A run of crossings on the first two strands does not change the number of strands. -/
private theorem morseOut_replicate_isoX_twKPosHalfLine (b : Bool) (m : ℕ) :
    ∀ j : ℕ, morseOut m (List.replicate j (isoX b 0)) = m
  | 0 => rfl
  | j + 1 => by
    rw [List.replicate_succ]
    show morseOut (morseLetterOut m (isoX b 0)) (List.replicate j (isoX b 0)) = m
    have hm : morseLetterOut m (isoX b 0) = m := by
      simp [morseLetterOut, isoX, morseKindIn, morseKindOut]
    rw [hm]
    exact morseOut_replicate_isoX_twKPosHalfLine b m j

/-- The first cup and the twists of the band end on three strands. -/
private theorem morseOut_frame_twKPosHalfLine (k : ℤ) :
    morseOut 1 ([isoU 1] ++ twTwistWord k) = 2 + 1 := by
  show morseOut (morseLetterOut 1 (isoU 1)) (twTwistWord k) = 2 + 1
  rw [twTwistWord, morseOut_replicate_isoX_twKPosHalfLine]
  rfl

/-- The half line for `r ≥ 3`, both clasp signs. -/
theorem twkSrcOp_halfLine_ge3 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (σ : Bool)
    (c n : ℕ) :
    twSrcOp r s σ c (halfTwistZ c (-(2 * (n : ℤ)))) =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwistZ c (-(2 * (n : ℤ)) - 2 * (((r - 1) * s : ℕ) : ℤ)) * claspSOp c σ)) := by
  rw [← morseOp_tw_bottom r s h σ c (-(2 * (n : ℤ))), twStripTail_eq_twkStripTail h hr σ]
  obtain ⟨Bs, hB, hperm⟩ := isoBeaded_twkQBody h hr σ
  obtain ⟨L, hL, hev⟩ := morseReach_isoBeaded_evac (pairCore r s) (twkQBody r s σ)
    ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ)))) [isoN 1] Bs 1 1 (morseFits_pairCore h hr)
    (isoConnected_pairCore h hr) hB (morseOut_frame_twKPosHalfLine _)
  obtain ⟨mvs, hm⟩ := morseReach_trans (morseReach_twkStripN h hr σ n) <|
    morseReach_trans (morseReach_twkSwing h hr σ n) <|
    morseReach_trans (morseReach_twkSQ h hr σ n) hev
  rw [morseOp_eq_of_morseApplyAll c 1 c c (Nat.mul_one c).symm _ _ mvs hm,
    morseOp_twkEvacuated (pairCore r s) (morseFits_pairCore h hr) (isoConnected_pairCore h hr) σ
      ((r - 1) * s) (-(2 * (n : ℤ))) L (isoRotPerm_of_perm hperm hL) c,
    morseOp_twkCoreTarget h hr _ σ c, morseOp_twTargetWord h _ σ c]

/-- The half line for `r = 2`, both clasp signs. -/
theorem twkSrcOp_halfLine_two {s : ℕ} (h : IsTorusPair 2 s) (σ : Bool) (c n : ℕ) :
    twSrcOp 2 s σ c (halfTwistZ c (-(2 * (n : ℤ)))) =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot 2 s h) (2 * c) *
        (halfTwistZ c (-(2 * (n : ℤ)) - 2 * (((2 - 1) * s : ℕ) : ℤ)) * claspSOp c σ)) := by
  have hs3 : 3 ≤ s := h.2.1
  have hodd : Odd s := Nat.coprime_two_left.1 h.2.2
  have hN : (2 - 1) * s = s := by omega
  rw [hN, ← morseOp_tw_bottom 2 s h σ c (-(2 * (n : ℤ))), twStripTail_two h σ]
  obtain ⟨Bs, hB, hperm⟩ := isoBeaded_twkQ2Body hs3 σ
  obtain ⟨L, hL, hev⟩ := morseReach_isoBeaded_evac (twkCore2 s) (twkQ2Body s σ)
    ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ)))) [isoN 1] Bs 1 1 (morseFits_twkCore2 s)
    (isoConnected_twkCore2 hodd) hB (morseOut_frame_twKPosHalfLine _)
  obtain ⟨mvs, hm⟩ := morseReach_trans (morseReach_twkStrip2N h σ n) <|
    morseReach_trans (morseReach_twkSwing2 h σ n) <|
    morseReach_trans (morseReach_twkSQ2 h σ n) hev
  have htarget : [isoU 1] ++ morseDouble (twkCore2 s) ++
      twTwistWord (-(2 * (n : ℤ)) - 2 * (s : ℤ)) ++ claspSWord σ ++ [isoN 1] =
      twTargetWord 2 s (-(2 * (n : ℤ)) - 2 * (s : ℤ)) σ := by
    rw [twkCore2_eq]
    rfl
  rw [morseOp_eq_of_morseApplyAll c 1 c c (Nat.mul_one c).symm _ _ mvs hm,
    morseOp_twkEvacuated (twkCore2 s) (morseFits_twkCore2 s) (isoConnected_twkCore2 hodd) σ s
      (-(2 * (n : ℤ))) L (isoRotPerm_of_perm hperm hL) c,
    htarget, morseOp_twTargetWord h _ σ c]

/-- The half line `ℓ = -n ≤ 0`, both clasp signs (operator form). -/
theorem twkSrcOp_halfLine {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) (c n : ℕ) :
    twSrcOp r s σ c (halfTwistZ c (-(2 * (n : ℤ)))) =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwistZ c (-(2 * (n : ℤ)) - 2 * (((r - 1) * s : ℕ) : ℤ)) * claspSOp c σ)) := by
  rcases Nat.lt_or_ge r 3 with hr | hr
  · obtain rfl : r = 2 := by have := h.1; omega
    exact twkSrcOp_halfLine_two h σ c n
  · exact twkSrcOp_halfLine_ge3 h hr σ c n

end AJConjecture
