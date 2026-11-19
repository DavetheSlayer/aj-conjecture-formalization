import Mathlib
import AJConjecture.SkeinCableNatural
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinMorseRule
import AJConjecture.SkeinThickCrossCap
import AJConjecture.SkeinThickCupInner

/-!
# Soundness of the rule `capSlide`

A bundle that crosses both legs of a thick cap, with crossings of one sign, passes to the other
side of the cap: `X_{i+1}^s X_i^s cap_{i+1} = cap_i` (`r = false`) and
`X_i^s X_{i+1}^s cap_i = cap_{i+1}` (`r = true`), all letters thick.

Proof: as for the cup slide, with `AJConjecture.capAt_mul_braidMatrix_thickCross_fst` and `_snd`
and `AJConjecture.capThick_succ`; or by transposition from the cup slide
(`AJConjecture.braidMatrix_thickCross_transpose`, `AJConjecture.skPlace_transpose`,
`AJConjecture.cupAt_eq_smul_transpose_capAt`).
-/

namespace AJConjecture

/-- A placed thick cap on `k + 1` strands: the innermost cap, then the thick cap on `k`
strands. -/
private theorem skPlace_capThick_succ_inner_morseCapSlide (k m n' i : ℕ) (h : i + 2 * k ≤ m)
    (h' : m = n' + 2 * k) :
    skPlace (m + 2) n' i (capThick (k + 1)) = capAt m (i + k) * skPlace m n' i (capThick k) := by
  rw [capThick_succ_inner,
    skPlace_mul (m + 2) m n' i _ (capThick k) (by omega) (by omega) (by omega),
    skPlace_skPlace (m + 2) m i k skCap (by omega) (by omega) (by omega) (by omega)]
  rfl

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem mem_thickCross_morseCapSlide {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
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

/-- A placed half twist is the matrix of the thick crossing of two bundles of `c` strands. -/
theorem skPlace_halfTwist (c N off : ℕ) (s : Bool) (h : off + 2 * c ≤ N) :
    skPlace N N off (halfTwist c s) = braidMatrix N (thickCross c c off s) := by
  have h0 : halfTwist c s = braidMatrix (2 * c) (thickCross c c 0 s) := by
    rw [halfTwist, cableGen_eq_thickCross]
    rfl
  have hw : IsOnStrands (2 * c) (thickCross c c 0 s) := fun g hg ↦ by
    have := mem_thickCross_morseCapSlide hg
    omega
  have hp := braidMatrix_map_add_eq_skPlace (2 * c) N off _ hw h
  rw [← thickCross_add_off, Nat.zero_add] at hp
  rw [h0, ← hp]

/-- A thick crossing with an empty second bundle is the empty word. -/
theorem thickCross_zero_right (a off : ℕ) (s : Bool) :
    thickCross a 0 off s = [] := by
  cases s <;> simp [thickCross, thickGen]

/-- A thick crossing with an empty first bundle is the empty word. -/
theorem thickCross_zero_left (b off : ℕ) (s : Bool) :
    thickCross 0 b off s = [] := by
  cases s <;> simp [thickCross, thickGen]

/-- The inverse of a product is the product of the inverses in the other order. -/
theorem inv_mul_inv_eq_of_mul {M : Type*} [Monoid M] {P Q A B A' B' : M}
    (hP : P = A * B) (hPQ : P * Q = 1) (hA : A' * A = 1) (hB : B' * B = 1) : B' * A' = Q := by
  calc B' * A' = B' * A' * (P * Q) := by rw [hPQ, mul_one]
    _ = B' * (A' * A) * B * Q := by rw [hP]; simp only [mul_assoc]
    _ = Q := by rw [hA, mul_one, hB, one_mul]

/-- A bundle that crosses two bundles in turn crosses their union. -/
theorem braidMatrix_thickCross_double_snd (N c off : ℕ) (s : Bool) :
    braidMatrix N (thickCross c c off s) * braidMatrix N (thickCross c c (off + c) s) =
      braidMatrix N (thickCross c (c + c) off s) := by
  cases s
  · simp only [thickCross, Bool.false_eq_true, ite_false]
    exact inv_mul_inv_eq_of_mul
      (P := braidMatrix N (thickGen (c + c) c off true))
      (by rw [thickGen_add_left, braidMatrix_append])
      (braidMatrix_thickGen_mul_inv N _ _ _) (braidMatrix_thickGen_inv_mul N _ _ _)
      (braidMatrix_thickGen_inv_mul N _ _ _)
  · simp only [thickCross, ite_true]
    exact (braidMatrix_thickGen_add_right N c c c off).symm

/-- Two bundles that cross a bundle in turn cross it as their union. -/
theorem braidMatrix_thickCross_double_fst (N c off : ℕ) (s : Bool) :
    braidMatrix N (thickCross c c (off + c) s) * braidMatrix N (thickCross c c off s) =
      braidMatrix N (thickCross (c + c) c off s) := by
  cases s
  · simp only [thickCross, Bool.false_eq_true, ite_false]
    exact inv_mul_inv_eq_of_mul
      (P := braidMatrix N (thickGen c (c + c) off true))
      (braidMatrix_thickGen_add_right N c c c off)
      (braidMatrix_thickGen_mul_inv N _ _ _) (braidMatrix_thickGen_inv_mul N _ _ _)
      (braidMatrix_thickGen_inv_mul N _ _ _)
  · simp only [thickCross, ite_true]
    rw [thickGen_add_left, braidMatrix_append]

/-- A bundle that crosses both legs of a thick cap from the left passes to its other side. -/
private theorem braidMatrix_thickCross_mul_capThick_snd_morseCapSlide (a off : ℕ) (s : Bool)
    (k : ℕ) : ∀ m n' b : ℕ, b = 2 * k → off + a + 2 * k ≤ m → m = n' + 2 * k →
      braidMatrix m (thickCross a b off s) * skPlace m n' off (capThick k) =
        skPlace m n' (off + a) (capThick k) := by
  induction k with
  | zero =>
    intro m n' b hb h h'
    obtain rfl : m = n' := by omega
    obtain rfl : b = 0 := by omega
    rw [thickCross_zero_right, braidMatrix_nil, Matrix.one_mul,
      capThick_zero, skPlace_one m off 0 (by omega),
      skPlace_one m (off + a) 0 (by omega)]
  | succ k ih =>
    intro m n' b hb h h'
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    obtain rfl : b = 2 * k + 2 := by omega
    rw [skPlace_capThick_succ_inner_morseCapSlide k m n' off (by omega) (by omega),
      skPlace_capThick_succ_inner_morseCapSlide k m n' (off + a) (by omega) (by omega),
      ← Matrix.mul_assoc,
      ← capAt_mul_braidMatrix_thickCross_snd m a (2 * k) off k s (by omega) (by omega),
      Matrix.mul_assoc, ih m n' (2 * k) rfl (by omega) (by omega)]

/-- A bundle that crosses both legs of a thick cap from the right passes to its other side. -/
private theorem braidMatrix_thickCross_mul_capThick_fst_morseCapSlide (b off : ℕ) (s : Bool)
    (k : ℕ) : ∀ m n' a : ℕ, a = 2 * k → off + 2 * k + b ≤ m → m = n' + 2 * k →
      braidMatrix m (thickCross a b off s) * skPlace m n' (off + b) (capThick k) =
        skPlace m n' off (capThick k) := by
  induction k with
  | zero =>
    intro m n' a ha h h'
    obtain rfl : m = n' := by omega
    obtain rfl : a = 0 := by omega
    rw [thickCross_zero_left, braidMatrix_nil, Matrix.one_mul,
      capThick_zero, skPlace_one m off 0 (by omega),
      skPlace_one m (off + b) 0 (by omega)]
  | succ k ih =>
    intro m n' a ha h h'
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    obtain rfl : a = 2 * k + 2 := by omega
    rw [skPlace_capThick_succ_inner_morseCapSlide k m n' off (by omega) (by omega),
      skPlace_capThick_succ_inner_morseCapSlide k m n' (off + b) (by omega) (by omega),
      ← Matrix.mul_assoc,
      ← capAt_mul_braidMatrix_thickCross_fst m (2 * k) b off k s (by omega) (by omega),
      Matrix.mul_assoc, ih m n' (2 * k) rfl (by omega) (by omega)]

/-- The cap slide from the left, with free intermediate sizes. -/
private theorem capSlide_true_of_sizes_morseCapSlide (c i N N' N₁ N₂ N₃ N₄ : ℕ) (s : Bool)
    (h₁ : N₁ = N) (h₂ : N₂ = N) (h₃ : N₃ + 2 * c = N) (h₄ : N₄ = N₃)
    (hN : c * i + 3 * c ≤ N) :
    skPlace N N₁ (c * i) (halfTwist c s) * (skPlace N₁ N₂ (c * (i + 1)) (halfTwist c s) *
        (skPlace N₂ N₃ (c * i) (capThick c) * skPlace N₃ N' 0 (1 : SkMat 0 0))) =
      skPlace N N₄ (c * (i + 1)) (capThick c) * skPlace N₄ N' 0 (1 : SkMat 0 0) := by
  subst h₁ h₂ h₃ h₄
  rw [Nat.mul_add_one, skPlace_halfTwist c _ (c * i) s (by omega),
    skPlace_halfTwist c _ (c * i + c) s (by omega), ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, braidMatrix_thickCross_double_snd,
    braidMatrix_thickCross_mul_capThick_snd_morseCapSlide c (c * i) s c _ _ (c + c) (by omega)
      (by omega) rfl]

/-- The cap slide from the right, with free intermediate sizes. -/
private theorem capSlide_false_of_sizes_morseCapSlide (c i N N' N₁ N₂ N₃ N₄ : ℕ) (s : Bool)
    (h₁ : N₁ = N) (h₂ : N₂ = N) (h₃ : N₃ + 2 * c = N) (h₄ : N₄ = N₃)
    (hN : c * i + 3 * c ≤ N) :
    skPlace N N₁ (c * (i + 1)) (halfTwist c s) * (skPlace N₁ N₂ (c * i) (halfTwist c s) *
        (skPlace N₂ N₃ (c * (i + 1)) (capThick c) * skPlace N₃ N' 0 (1 : SkMat 0 0))) =
      skPlace N N₄ (c * i) (capThick c) * skPlace N₄ N' 0 (1 : SkMat 0 0) := by
  subst h₁ h₂ h₃ h₄
  rw [Nat.mul_add_one, skPlace_halfTwist c _ (c * i) s (by omega),
    skPlace_halfTwist c _ (c * i + c) s (by omega), ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, braidMatrix_thickCross_double_fst,
    braidMatrix_thickCross_mul_capThick_fst_morseCapSlide c (c * i) s c _ _ (c + c) (by omega)
      (by omega) rfl]

/-- The cap slide is sound. -/
theorem morseRuleSound_capSlide (i : ℕ) (s r : Bool) : MorseRuleSound (.capSlide i s r) := by
  intro c n N N' hN _ hl _
  cases r
  · simp only [morseRuleLhs, morseRuleRhs, Bool.false_eq_true, ite_false, morseFits,
      morseKindIn, morseLetterOut, morseKindOut, Bool.and_true, Bool.and_eq_true] at hl ⊢
    have h1 := of_decide_eq_true hl.1
    have h3 := Nat.mul_le_mul_left c (show i + 3 ≤ n by omega)
    rw [Nat.mul_add] at h3
    simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
    exact capSlide_false_of_sizes_morseCapSlide c i N N' _ _ _ _ s (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · simp only [morseRuleLhs, morseRuleRhs, ite_true, morseFits,
      morseKindIn, morseLetterOut, morseKindOut, Bool.and_true, Bool.and_eq_true] at hl ⊢
    have h1 := of_decide_eq_true hl.2.1
    have h3 := Nat.mul_le_mul_left c (show i + 3 ≤ n by omega)
    rw [Nat.mul_add] at h3
    simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
    exact capSlide_true_of_sizes_morseCapSlide c i N N' _ _ _ _ s (by omega) (by omega)
      (by omega) (by omega) (by omega)

end AJConjecture
