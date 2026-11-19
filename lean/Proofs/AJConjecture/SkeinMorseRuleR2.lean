import Mathlib
import AJConjecture.SkeinMorseRule
import AJConjecture.SkeinThickGenInv

/-!
# Soundness of the rule `r2`

The cabled half twist and its inverse cancel: `Σ_c^s Σ_c^{-s} = 1`.

Proof: `halfTwist c s` is the matrix of `thickGen c c 0 s`, so this is
`AJConjecture.braidMatrix_thickGen_mul_inv` or `AJConjecture.braidMatrix_thickGen_inv_mul`, placed
at the offset `c * i` with `AJConjecture.skPlace_mul` and `AJConjecture.skPlace_one`.
-/

namespace AJConjecture

/-- The cabled half twist and the half twist of the opposite sign cancel. -/
private theorem halfTwist_mul_halfTwist_not_morseRuleR2 (c : ℕ) (s : Bool) :
    halfTwist c s * halfTwist c (!s) = 1 := by
  rw [halfTwist, halfTwist, cableGen_eq_thickCross, cableGen_eq_thickCross]
  cases s
  · exact braidMatrix_thickGen_inv_mul (2 * c) c c (c * 0)
  · exact braidMatrix_thickGen_mul_inv (2 * c) c c (c * 0)

/-- Two opposite half twists at the same offset, followed by the operator of the empty word,
with free intermediate sizes. -/
private theorem skPlace_halfTwist_mul_not_morseRuleR2 (c j N M M' N' : ℕ) (s : Bool)
    (hM : M = N) (hM' : M' = N) (h : j + 2 * c ≤ N) :
    skPlace N M j (halfTwist c s) *
        (skPlace M M' j (halfTwist c (!s)) * skPlace M' N' 0 (1 : SkMat 0 0)) =
      skPlace N N' 0 (1 : SkMat 0 0) := by
  subst hM hM'
  rw [← Matrix.mul_assoc, ← skPlace_mul _ _ _ j _ _ h rfl rfl,
    halfTwist_mul_halfTwist_not_morseRuleR2, skPlace_one _ j (2 * c) h, Matrix.one_mul]

/-- The second Reidemeister move is sound. -/
theorem morseRuleSound_r2 (i : ℕ) (s : Bool) : MorseRuleSound (.r2 i s) := by
  intro c n N N' hN _ hl _
  simp only [morseRuleLhs, morseFits, morseKindIn, Bool.and_eq_true] at hl
  have h : c * i + 2 * c ≤ N := by
    have := Nat.mul_le_mul_left c (of_decide_eq_true hl.1)
    rw [Nat.mul_add] at this
    omega
  exact skPlace_halfTwist_mul_not_morseRuleR2 c (c * i) N _ _ N' s
    (by dsimp only [morseKindOut, morseKindIn]; omega)
    (by dsimp only [morseKindOut, morseKindIn]; omega) h

end AJConjecture
