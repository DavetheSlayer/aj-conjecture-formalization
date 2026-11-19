import Mathlib
import AJConjecture.SkeinMorseRule
import AJConjecture.SkeinThickCup

/-!
# Soundness of the rule `zig`

A thick cup followed by a thick cap that shares one bundle with it is the identity: for the
thickness `c`, `(1 ⊗ cup_c)(cap_c ⊗ 1) = 1` on a bundle (`r = false`) and `(cup_c ⊗ 1)(1 ⊗ cap_c) = 1`
(`r = true`).

Proof: `AJConjecture.cupThick_mul_capThick_right` and `AJConjecture.cupThick_mul_capThick_left`,
placed at the offset `c * i` with `AJConjecture.skPlace_mul` and `AJConjecture.skPlace_skPlace`;
the hypothesis that both sides fit gives `i < n`.
-/

namespace AJConjecture

/-- A thick cup at the offset `j` followed by a thick cap at the offset `j + c` and by the
operator of the empty word, with free intermediate sizes. -/
private theorem skPlace_cupThick_mul_capThick_left_morseRuleZig (c j j' N M M' N' : ℕ)
    (hj : j' = j + c) (hM : M = N + 2 * c) (hM' : M' = N) (h : j + c ≤ N) :
    skPlace N M j (cupThick c) *
        (skPlace M M' j' (capThick c) * skPlace M' N' 0 (1 : SkMat 0 0)) =
      skPlace N N' 0 (1 : SkMat 0 0) := by
  subst hj hM hM'
  have e : skPlace M' (M' + 2 * c) j (skPlace c (3 * c) 0 (cupThick c)) =
      skPlace M' (M' + 2 * c) j (cupThick c) :=
    skPlace_skPlace _ _ j 0 (cupThick c) (by omega) (by omega) h (by omega)
  rw [← Matrix.mul_assoc, ← e,
    ← skPlace_skPlace _ _ j c (capThick c) (k' := 3 * c) (l' := c) (by omega) (by omega)
      (by omega) (by omega),
    ← skPlace_mul _ _ _ j _ _ h (by omega) (by omega), cupThick_mul_capThick_left,
    skPlace_one _ j c h, Matrix.one_mul]

/-- A thick cup at the offset `j + c` followed by a thick cap at the offset `j` and by the
operator of the empty word, with free intermediate sizes. -/
private theorem skPlace_cupThick_mul_capThick_right_morseRuleZig (c j j' N M M' N' : ℕ)
    (hj : j' = j + c) (hM : M = N + 2 * c) (hM' : M' = N) (h : j + c ≤ N) :
    skPlace N M j' (cupThick c) *
        (skPlace M M' j (capThick c) * skPlace M' N' 0 (1 : SkMat 0 0)) =
      skPlace N N' 0 (1 : SkMat 0 0) := by
  subst hj hM hM'
  have e : skPlace (M' + 2 * c) M' j (skPlace (3 * c) c 0 (capThick c)) =
      skPlace (M' + 2 * c) M' j (capThick c) :=
    skPlace_skPlace _ _ j 0 (capThick c) (by omega) (by omega) (by omega) (by omega)
  rw [← Matrix.mul_assoc, ← e,
    ← skPlace_skPlace _ _ j c (cupThick c) (k' := c) (l' := 3 * c) (by omega) (by omega) h
      (by omega),
    ← skPlace_mul _ _ _ j _ _ h (by omega) (by omega), cupThick_mul_capThick_right,
    skPlace_one _ j c h, Matrix.one_mul]

/-- The zig-zag rule is sound. -/
theorem morseRuleSound_zig (i : ℕ) (r : Bool) : MorseRuleSound (.zig i r) := by
  intro c n N N' hN _ hl _
  cases r
  · change morseFits n [(.cup, i + 1), (.cap, i)] = true at hl
    simp only [morseFits, morseKindIn, Bool.and_eq_true] at hl
    have h : c * i + c ≤ N := by
      have := Nat.mul_le_mul_left c (of_decide_eq_true hl.1)
      rw [Nat.mul_add_one] at this
      omega
    exact skPlace_cupThick_mul_capThick_right_morseRuleZig c (c * i) _ N _ _ N'
      (Nat.mul_add_one c i)
      (by dsimp only [morseKindOut, morseKindIn]; omega)
      (by dsimp only [morseKindOut, morseKindIn]; omega) h
  · change morseFits n [(.cup, i), (.cap, i + 1)] = true at hl
    simp only [morseFits, morseKindIn, morseLetterOut, morseKindOut, Bool.and_eq_true] at hl
    have h : c * i + c ≤ N := by
      have h0 : i + 1 ≤ n := by
        have := of_decide_eq_true hl.2.1
        omega
      have := Nat.mul_le_mul_left c h0
      rw [Nat.mul_add_one] at this
      omega
    exact skPlace_cupThick_mul_capThick_left_morseRuleZig c (c * i) _ N _ _ N'
      (Nat.mul_add_one c i)
      (by dsimp only [morseKindOut, morseKindIn]; omega)
      (by dsimp only [morseKindOut, morseKindIn]; omega) h

end AJConjecture
