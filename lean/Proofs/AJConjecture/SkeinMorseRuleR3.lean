import Mathlib
import AJConjecture.SkeinMorseBraid
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinMorseRule
import AJConjecture.SkeinProfileBasic
import AJConjecture.SkeinThickYangBaxter

/-!
# Soundness of the rule `r3`

The third Reidemeister move for three bundles of `c` strands and crossings of one sign.

Proof: `AJConjecture.braidMatrix_thickCross_yangBaxter` with `a = b = c` and the offset `c * i`;
each letter is the matrix of a `thickCross c c` at an offset, by
`AJConjecture.braidMatrix_map_add_eq_skPlace` and `AJConjecture.thickCross_add_off`.
-/

namespace AJConjecture

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem mem_thickCross_morseRuleR3 {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
    (hg : g ∈ thickCross a b off s) : g.1 + 2 ≤ off + a + b := by
  cases s
  · simp only [thickCross, thickGen, Bool.false_eq_true, ite_false, List.mem_flatMap,
      List.mem_reverse, List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    dsimp only
    omega
  · simp only [thickCross, thickGen, ite_true, List.mem_flatMap, List.mem_reverse,
      List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    dsimp only
    omega

/-- The third Reidemeister move for three bundles at the offset `j`, each side followed by the
operator of the empty word, with free intermediate sizes. -/
private theorem skPlace_halfTwist_yangBaxter_morseRuleR3 (c j j' N M₁ M₂ M₃ M₁' M₂' M₃' N' : ℕ)
    (s : Bool) (hj : j' = j + c) (h₁ : M₁ = N) (h₂ : M₂ = N) (h₃ : M₃ = N) (h₁' : M₁' = N)
    (h₂' : M₂' = N) (h₃' : M₃' = N) (h : j + 3 * c ≤ N) :
    skPlace N M₁ j (halfTwist c s) * (skPlace M₁ M₂ j' (halfTwist c s) *
        (skPlace M₂ M₃ j (halfTwist c s) * skPlace M₃ N' 0 (1 : SkMat 0 0))) =
      skPlace N M₁' j' (halfTwist c s) * (skPlace M₁' M₂' j (halfTwist c s) *
        (skPlace M₂' M₃' j' (halfTwist c s) * skPlace M₃' N' 0 (1 : SkMat 0 0))) := by
  subst hj h₁ h₂ h₃ h₁' h₂' h₃'
  have hyb := braidMatrix_thickCross_yangBaxter M₃' c c c j s (by omega)
  rw [skPlace_halfTwist_eq_braidMatrix c _ j s (by omega),
    skPlace_halfTwist_eq_braidMatrix c _ (j + c) s (by omega),
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyb]

/-- The third Reidemeister move is sound. -/
theorem morseRuleSound_r3 (i : ℕ) (s : Bool) : MorseRuleSound (.r3 i s) := by
  intro c n N N' hN _ hl _
  simp only [morseRuleLhs, morseFits, morseKindIn, morseLetterOut, morseKindOut,
    Bool.and_eq_true] at hl
  have h : c * i + 3 * c ≤ N := by
    have h0 : i + 3 ≤ n := by
      have := of_decide_eq_true hl.2.1
      omega
    have := Nat.mul_le_mul_left c h0
    rw [Nat.mul_add] at this
    omega
  exact skPlace_halfTwist_yangBaxter_morseRuleR3 c (c * i) _ N _ _ _ _ _ _ N' s
    (Nat.mul_add_one c i)
    (by dsimp only [morseKindOut, morseKindIn]; omega)
    (by dsimp only [morseKindOut, morseKindIn]; omega)
    (by dsimp only [morseKindOut, morseKindIn]; omega)
    (by dsimp only [morseKindOut, morseKindIn]; omega)
    (by dsimp only [morseKindOut, morseKindIn]; omega)
    (by dsimp only [morseKindOut, morseKindIn]; omega) h

end AJConjecture
