import Mathlib
import AJConjecture.SkeinKinkRecursion
import AJConjecture.SkeinMorseRule
import AJConjecture.SkeinPtrTailCyclic

/-!
# Soundness of the rule `kink`

A positive and a negative right curl on a bundle of `c` strands cancel:
`kinkOp c s * kinkOp c (!s) = 1`. No projector is involved, and a single curl is not a scalar.

Proof: the three letters `cup (i + 1)`, `cross s i`, `cap (i + 1)` are `kinkOp c s` placed at the
offset `c * i` (`AJConjecture.ptrTail_eq_cupThick_capThick`, `AJConjecture.ptrTail_skPlace_shift`).
The product `kinkOp c s * kinkOp c (!s) = 1` is an induction on `c` with
`AJConjecture.kinkOp_succ`: in
`X_{c,1}^s (1 ⊗ kink_c^s) X_{1,c}^s · X_{c,1}^{-s} (1 ⊗ kink_c^{-s}) X_{1,c}^{-s}` the two middle
crossings are `thickGen 1 c 0 true` and its inverse, then the two kinks cancel by induction, then
the outer crossings (`AJConjecture.braidMatrix_thickGen_mul_inv`); the scalars are `-t^{±3}`.
-/

namespace AJConjecture

/-- The kink of the empty bundle is the identity. -/
private theorem kinkOp_zero_morseKink (s : Bool) : kinkOp 0 s = 1 := by
  rw [kinkOp, halfTwist]
  change ptrTail 0 0 (braidMatrix 0 (cableGen 0 (0, s))) = 1
  rw [ptrTail_self]
  cases s <;> simp [cableGen, braidMatrix]

/-- A thick crossing followed by the crossing back of the opposite sign is the identity. -/
private theorem braidMatrix_thickCross_mul_not_morseKink (n a b off : ℕ) (s : Bool) :
    braidMatrix n (thickCross a b off s) * braidMatrix n (thickCross b a off (!s)) = 1 := by
  cases s
  · simp only [thickCross, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
    exact braidMatrix_thickGen_inv_mul n b a off
  · simp only [thickCross, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    exact braidMatrix_thickGen_mul_inv n a b off

/-- Two triple products cancel when their factors cancel from the inside out. -/
private theorem mul_triple_cancel_morseKink {M : Type*} [Monoid M] {u k v u' k' v' : M}
    (hvu : v * u' = 1) (hk : k * k' = 1) (huv : u * v' = 1) :
    u * k * v * (u' * k' * v') = 1 := by
  calc u * k * v * (u' * k' * v') = u * (k * (v * u') * k') * v' := by simp only [mul_assoc]
    _ = 1 := by rw [hvu, mul_one, hk, mul_one, huv]

/-- The kink scalars `-t^{±3}` of opposite signs are inverse to each other. -/
private theorem kinkSign_mul_not_morseKink (s : Bool) :
    (if s then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) *
      (if (!s) then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) =
        1 := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  cases s
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false, ite_true, neg_mul_neg,
      ← zpow_add₀ hX]
    norm_num
  · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false, neg_mul_neg,
      ← zpow_add₀ hX]
    norm_num

/-- A positive and a negative curl on a bundle cancel. -/
private theorem kinkOp_mul_kinkOp_not_morseKink (c : ℕ) :
    ∀ s : Bool, kinkOp c s * kinkOp c (!s) = 1 := by
  induction c with
  | zero =>
    intro s
    rw [kinkOp_zero_morseKink, kinkOp_zero_morseKink, Matrix.one_mul]
  | succ c ih =>
    intro s
    have hk : skPlace (c + 1) (c + 1) 1 (kinkOp c s) *
        skPlace (c + 1) (c + 1) 1 (kinkOp c (!s)) = 1 := by
      rw [← skPlace_mul (c + 1) (c + 1) (c + 1) 1 _ _ (by omega) (by omega) (by omega), ih s,
        skPlace_one (c + 1) 1 c (by omega)]
    have hvu := braidMatrix_thickCross_mul_not_morseKink (c + 1) 1 c 0 s
    have huv := braidMatrix_thickCross_mul_not_morseKink (c + 1) c 1 0 s
    rw [kinkOp_succ, kinkOp_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_triple_cancel_morseKink hvu hk huv, kinkSign_mul_not_morseKink, one_smul]

/-- The partial trace over the second of two bundles is the closure by a thick cup and a thick
cap, for sizes given up to equality. -/
private theorem ptrTail_eq_cupThick_capThick_of_eq_morseKink (c n M : ℕ) (hn : n = c + c)
    (hM : M = c + 2 * c) (A : SkMat n n) :
    ptrTail c n A =
      skPlace c M c (cupThick c) * skPlace M M 0 A * skPlace M c c (capThick c) := by
  subst hn hM
  exact ptrTail_eq_cupThick_capThick c c A

/-- A thick cup, a half twist and a thick cap: the kink of the bundle, placed. -/
private theorem skPlace_kinkOp_morseKink (c N N₁ off : ℕ) (s : Bool) (hN₁ : N₁ = N + 2 * c)
    (h : off + c ≤ N) :
    skPlace N N₁ (off + c) (cupThick c) * skPlace N₁ N₁ off (halfTwist c s) *
        skPlace N₁ N (off + c) (capThick c) =
      skPlace N N off (kinkOp c s) := by
  subst hN₁
  rw [kinkOp,
    ptrTail_eq_cupThick_capThick_of_eq_morseKink c (2 * c) (3 * c) (by omega) (by omega),
    skPlace_mul N (N + 2 * c) N off _ _ (by omega) (by omega) (by omega),
    skPlace_mul N (N + 2 * c) (N + 2 * c) off _ _ (by omega) (by omega) (by omega),
    skPlace_skPlace N (N + 2 * c) off c (cupThick c) (by omega) (by omega) (by omega)
      (by omega),
    skPlace_skPlace (N + 2 * c) (N + 2 * c) off 0 (halfTwist c s) (by omega) (by omega)
      (by omega) (by omega),
    skPlace_skPlace (N + 2 * c) N off c (capThick c) (by omega) (by omega) (by omega)
      (by omega), Nat.add_zero off]

/-- The kink pair with free intermediate sizes. -/
private theorem kink_of_sizes_morseKink (c i N N' N₁ N₂ N₃ N₄ N₅ N₆ : ℕ) (s : Bool)
    (h₁ : N₁ = N + 2 * c) (h₂ : N₂ = N + 2 * c) (h₃ : N₃ = N) (h₄ : N₄ = N + 2 * c)
    (h₅ : N₅ = N + 2 * c) (h₆ : N₆ = N) (hN : c * i + c ≤ N) :
    skPlace N N₁ (c * (i + 1)) (cupThick c) * (skPlace N₁ N₂ (c * i) (halfTwist c s) *
        (skPlace N₂ N₃ (c * (i + 1)) (capThick c) * (skPlace N₃ N₄ (c * (i + 1)) (cupThick c) *
          (skPlace N₄ N₅ (c * i) (halfTwist c (!s)) * (skPlace N₅ N₆ (c * (i + 1)) (capThick c) *
            skPlace N₆ N' 0 (1 : SkMat 0 0)))))) =
      skPlace N N' 0 (1 : SkMat 0 0) := by
  subst N₁ N₂ N₃ N₄ N₅ N₆
  have k1 := skPlace_kinkOp_morseKink c N (N + 2 * c) (c * i) s rfl hN
  have k2 := skPlace_kinkOp_morseKink c N (N + 2 * c) (c * i) (!s) rfl hN
  have kk : skPlace N N (c * i) (kinkOp c s) * skPlace N N (c * i) (kinkOp c (!s)) = 1 := by
    rw [← skPlace_mul N N N (c * i) _ _ (by omega) (by omega) (by omega),
      kinkOp_mul_kinkOp_not_morseKink, skPlace_one N (c * i) c (by omega)]
  rw [Nat.mul_add_one]
  simp only [← Matrix.mul_assoc]
  rw [k1, Matrix.mul_assoc (skPlace N N (c * i) (kinkOp c s)),
    Matrix.mul_assoc (skPlace N N (c * i) (kinkOp c s)), k2, kk, Matrix.one_mul]

/-- The kink-pair rule is sound. -/
theorem morseRuleSound_kink (i : ℕ) (s : Bool) : MorseRuleSound (.kink i s) := by
  intro c n N N' hN _ hl _
  simp only [morseRuleLhs, morseRuleRhs, morseFits, morseKindIn, morseLetterOut, morseKindOut,
    Bool.and_true, Bool.and_eq_true] at hl ⊢
  have h1 := of_decide_eq_true hl.1
  have h3 := Nat.mul_le_mul_left c (show i + 1 ≤ n by omega)
  rw [Nat.mul_add] at h3
  simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
  exact kink_of_sizes_morseKink c i N N' _ _ _ _ _ _ s (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)

end AJConjecture
