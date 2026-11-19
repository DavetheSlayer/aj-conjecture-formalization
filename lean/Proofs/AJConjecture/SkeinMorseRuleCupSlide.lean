import Mathlib
import AJConjecture.SkeinMorseRuleCapSlide
import AJConjecture.SkeinCableNatural
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinMorseRule
import AJConjecture.SkeinThickCrossCup
import AJConjecture.SkeinThickCupInner

/-!
# Soundness of the rule `cupSlide`

A bundle that crosses both legs of a thick cup, with crossings of one sign, passes to the other
side of the cup: `cup_i X_{i+1}^s X_i^s = cup_{i+1}` (`r = false`) and
`cup_{i+1} X_i^s X_{i+1}^s = cup_i` (`r = true`), all letters thick.

Proof: the two crossings are one crossing of a bundle of `2c` strands with a bundle of `c` strands
(`AJConjecture.thickGen_add_left`, `AJConjecture.braidMatrix_thickGen_add_right`). The thick cup is
`c` nested cups (`AJConjecture.cupThick_succ`); by induction on the number `k` of nested cups,
`AJConjecture.braidMatrix_thickCross_mul_cupAt_fst` (respectively `_snd`) with `j = k` moves the
`k`-th cup through the crossing and makes the crossing bundle thicker by two, starting from the
empty crossing `thickCross 0 c`.
-/

namespace AJConjecture

/-- A placed thick cup on `k + 1` strands: the thick cup on `k` strands, then the innermost
cup. -/
private theorem skPlace_cupThick_succ_inner_morseCupSlide (k m n' i : ℕ) (h : i ≤ n')
    (h' : n' + 2 * k = m) :
    skPlace n' (m + 2) i (cupThick (k + 1)) = skPlace n' m i (cupThick k) * cupAt m (i + k) := by
  rw [cupThick_succ_inner,
    skPlace_mul n' m (m + 2) i (cupThick k) _ (by omega) (by omega) (by omega),
    skPlace_skPlace m (m + 2) i k skCup (by omega) (by omega) (by omega) (by omega)]
  rfl

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem mem_thickCross_morseCupSlide {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
    (hg : g ∈ thickCross a b off s) : off ≤ g.1 ∧ g.1 + 2 ≤ off + a + b := by
  cases s
  · simp only [thickCross, thickGen, Bool.false_eq_true, ite_false, List.mem_flatMap,
      List.mem_reverse, List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    exact ⟨by omega, by omega⟩
  · simp only [thickCross, thickGen, ite_true, List.mem_flatMap, List.mem_reverse,
      List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    exact ⟨by omega, by omega⟩

/-- A bundle that crosses both legs of a thick cup from the left passes to its other side. -/
private theorem skPlace_cupThick_mul_braidMatrix_thickCross_snd_morseCupSlide (a off : ℕ)
    (s : Bool) (k : ℕ) : ∀ m n' b : ℕ, b = 2 * k → off + a ≤ n' → n' + 2 * k = m →
      skPlace n' m (off + a) (cupThick k) * braidMatrix m (thickCross a b off s) =
        skPlace n' m off (cupThick k) := by
  induction k with
  | zero =>
    intro m n' b hb h h'
    obtain rfl : n' = m := by omega
    obtain rfl : b = 0 := by omega
    rw [thickCross_zero_right, braidMatrix_nil, Matrix.mul_one,
      cupThick_zero, skPlace_one n' off 0 (by omega),
      skPlace_one n' (off + a) 0 (by omega)]
  | succ k ih =>
    intro m n' b hb h h'
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    obtain rfl : b = 2 * k + 2 := by omega
    rw [skPlace_cupThick_succ_inner_morseCupSlide k m n' off (by omega) (by omega),
      skPlace_cupThick_succ_inner_morseCupSlide k m n' (off + a) (by omega) (by omega),
      Matrix.mul_assoc,
      ← braidMatrix_thickCross_mul_cupAt_snd m a (2 * k) off k s (by omega) (by omega),
      ← Matrix.mul_assoc, ih m n' (2 * k) rfl (by omega) (by omega)]

/-- A bundle that crosses both legs of a thick cup from the right passes to its other side. -/
private theorem skPlace_cupThick_mul_braidMatrix_thickCross_fst_morseCupSlide (b off : ℕ)
    (s : Bool) (k : ℕ) : ∀ m n' a : ℕ, a = 2 * k → off + b ≤ n' → n' + 2 * k = m →
      skPlace n' m off (cupThick k) * braidMatrix m (thickCross a b off s) =
        skPlace n' m (off + b) (cupThick k) := by
  induction k with
  | zero =>
    intro m n' a ha h h'
    obtain rfl : n' = m := by omega
    obtain rfl : a = 0 := by omega
    rw [thickCross_zero_left, braidMatrix_nil, Matrix.mul_one,
      cupThick_zero, skPlace_one n' off 0 (by omega),
      skPlace_one n' (off + b) 0 (by omega)]
  | succ k ih =>
    intro m n' a ha h h'
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    obtain rfl : a = 2 * k + 2 := by omega
    rw [skPlace_cupThick_succ_inner_morseCupSlide k m n' off (by omega) (by omega),
      skPlace_cupThick_succ_inner_morseCupSlide k m n' (off + b) (by omega) (by omega),
      Matrix.mul_assoc,
      ← braidMatrix_thickCross_mul_cupAt_fst m (2 * k) b off k s (by omega) (by omega),
      ← Matrix.mul_assoc, ih m n' (2 * k) rfl (by omega) (by omega)]

/-- The cup slide from the left, with free intermediate sizes. -/
private theorem cupSlide_true_of_sizes_morseCupSlide (c i N N' N₁ N₂ N₃ N₄ : ℕ) (s : Bool)
    (h₁ : N₁ = N + 2 * c) (h₂ : N₂ = N + 2 * c) (h₃ : N₃ = N + 2 * c) (h₄ : N₄ = N + 2 * c)
    (hN : c * i + c ≤ N) :
    skPlace N N₁ (c * (i + 1)) (cupThick c) * (skPlace N₁ N₂ (c * i) (halfTwist c s) *
        (skPlace N₂ N₃ (c * (i + 1)) (halfTwist c s) * skPlace N₃ N' 0 (1 : SkMat 0 0))) =
      skPlace N N₄ (c * i) (cupThick c) * skPlace N₄ N' 0 (1 : SkMat 0 0) := by
  subst h₁ h₂ h₃ h₄
  rw [Nat.mul_add_one, skPlace_halfTwist c _ (c * i) s (by omega),
    skPlace_halfTwist c _ (c * i + c) s (by omega), ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_assoc (skPlace N (N + 2 * c) (c * i + c) (cupThick c)),
    braidMatrix_thickCross_double_snd,
    skPlace_cupThick_mul_braidMatrix_thickCross_snd_morseCupSlide c (c * i) s c _ _ (c + c)
      (by omega) hN rfl]

/-- The cup slide from the right, with free intermediate sizes. -/
private theorem cupSlide_false_of_sizes_morseCupSlide (c i N N' N₁ N₂ N₃ N₄ : ℕ) (s : Bool)
    (h₁ : N₁ = N + 2 * c) (h₂ : N₂ = N + 2 * c) (h₃ : N₃ = N + 2 * c) (h₄ : N₄ = N + 2 * c)
    (hN : c * i + c ≤ N) :
    skPlace N N₁ (c * i) (cupThick c) * (skPlace N₁ N₂ (c * (i + 1)) (halfTwist c s) *
        (skPlace N₂ N₃ (c * i) (halfTwist c s) * skPlace N₃ N' 0 (1 : SkMat 0 0))) =
      skPlace N N₄ (c * (i + 1)) (cupThick c) * skPlace N₄ N' 0 (1 : SkMat 0 0) := by
  subst h₁ h₂ h₃ h₄
  rw [Nat.mul_add_one, skPlace_halfTwist c _ (c * i) s (by omega),
    skPlace_halfTwist c _ (c * i + c) s (by omega), ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_assoc (skPlace N (N + 2 * c) (c * i) (cupThick c)),
    braidMatrix_thickCross_double_fst,
    skPlace_cupThick_mul_braidMatrix_thickCross_fst_morseCupSlide c (c * i) s c _ _ (c + c)
      (by omega) hN rfl]

/-- The cup slide is sound. -/
theorem morseRuleSound_cupSlide (i : ℕ) (s r : Bool) : MorseRuleSound (.cupSlide i s r) := by
  intro c n N N' hN _ hl _
  cases r
  · simp only [morseRuleLhs, morseRuleRhs, Bool.false_eq_true, ite_false, morseFits,
      morseKindIn, morseLetterOut, morseKindOut, Bool.and_true, Bool.and_eq_true] at hl ⊢
    have h1 := of_decide_eq_true hl.2.1
    have h3 := Nat.mul_le_mul_left c (show i + 1 ≤ n by omega)
    rw [Nat.mul_add] at h3
    simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
    exact cupSlide_false_of_sizes_morseCupSlide c i N N' _ _ _ _ s (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · simp only [morseRuleLhs, morseRuleRhs, ite_true, morseFits,
      morseKindIn, morseLetterOut, morseKindOut, Bool.and_true, Bool.and_eq_true] at hl ⊢
    have h1 := of_decide_eq_true hl.1
    have h3 := Nat.mul_le_mul_left c (show i + 1 ≤ n by omega)
    rw [Nat.mul_add] at h3
    simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
    exact cupSlide_true_of_sizes_morseCupSlide c i N N' _ _ _ _ s (by omega) (by omega)
      (by omega) (by omega) (by omega)

end AJConjecture
