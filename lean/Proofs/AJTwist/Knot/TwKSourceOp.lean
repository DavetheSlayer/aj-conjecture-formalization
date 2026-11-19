import Mathlib
import AJTwist.Knot.TwKTargetOp
import AJConjecture.SkeinMorseCheckSound

/-!
# The long-knot operator of the twisted knot is linear in the inserted twist

By phase I and the prefix normal form, the long closure of `twWhiteheadWord r s ℓ σ` reaches
`u1 +0 · (2ℓ half twists of the band) · twStripTail r s σ`. By soundness of the checker its thick
operator is `twSrcOp r s σ c (halfTwistZ c (2ℓ))`, where

`twSrcOp r s σ c Y = [u1 +0] · (1 ⊗ Y) · [twStripTail r s σ]`

is linear in the operator `Y` placed on the two bundles of the band. The dependence on `ℓ` is
only through `Y`; this is what allows the extension from `ℓ ≤ 0` to all `ℓ` by the
Cayley–Hamilton theorem (`TwKCayley`).
-/

noncomputable section

namespace AJConjecture

/-- The strip word of the untwisted list with an operator `Y` inserted on the two bundles of the
band at its bottom end. -/
def twSrcOp (r s : ℕ) (σ : Bool) (c : ℕ) (Y : SkMat (2 * c) (2 * c)) : SkMat c c :=
  morseOp c [isoU 1, isoX true 0] c (3 * c) * skPlace (3 * c) (3 * c) c Y *
    morseOp c (twStripTail r s σ) (3 * c) c

/-- `twSrcOp` is additive in the inserted operator. -/
theorem twSrcOp_add (r s : ℕ) (σ : Bool) (c : ℕ) (Y Z : SkMat (2 * c) (2 * c)) :
    twSrcOp r s σ c (Y + Z) = twSrcOp r s σ c Y + twSrcOp r s σ c Z := by
  simp only [twSrcOp, skPlace_add, Matrix.mul_add, Matrix.add_mul]

/-- `twSrcOp` commutes with scalars. -/
theorem twSrcOp_smul (r s : ℕ) (σ : Bool) (c : ℕ) (a : RatFunc ℚ) (Y : SkMat (2 * c) (2 * c)) :
    twSrcOp r s σ c (a • Y) = a • twSrcOp r s σ c Y := by
  simp only [twSrcOp, skPlace_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The operator of a word that begins with a crossing, with free sizes. -/
private theorem morseOp_cons_cross_twKSourceOp (c i : ℕ) (s : Bool) (u : MorseWord)
    (N M N' : ℕ) (hM : M = N) :
    morseOp c ((MorseKind.cross s, i) :: u) N N' =
      skPlace N M (c * i) (halfTwist c s) * morseOp c u M N' := by
  have e : N + c * 2 - c * 2 = M := by omega
  rw [← e]
  rfl

/-- Repeated crossings do not change the number of tensor factors. -/
private theorem morseThickOut_replicate_cross_twKSourceOp (c n i : ℕ) (s : Bool) (N : ℕ) :
    morseThickOut c N (List.replicate n (MorseKind.cross s, i)) = N := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change morseThickOut c (N + c * 2 - c * 2) (List.replicate n (MorseKind.cross s, i)) = N
    rw [Nat.add_sub_cancel, ih]

/-- The thick operator of `n` crossings of sign `s` of the second and third bundles. -/
private theorem morseOp_replicate_cross_one_twKSourceOp (c n N : ℕ) (s : Bool)
    (hN : 3 * c ≤ N) :
    morseOp c (List.replicate n (MorseKind.cross s, 1)) N N =
      skPlace N N c (halfTwist c s ^ n) := by
  induction n with
  | zero =>
    rw [List.replicate_zero, morseOp_nil, pow_zero, skPlace_one N c (2 * c) (by omega)]
  | succ n ih =>
    rw [List.replicate_succ, morseOp_cons_cross_twKSourceOp c 1 s _ N N N rfl, Nat.mul_one, ih,
      pow_succ', skPlace_mul N N N c (halfTwist c s) (halfTwist c s ^ n) (by omega)
        rfl rfl]

/-- The shifted run of half twists is a run of crossings at position `1`. -/
private theorem morseShiftWord_twTwistWord_twKSourceOp (k : ℤ) :
    morseShiftWord 1 (twTwistWord k) =
      List.replicate k.natAbs (MorseKind.cross (decide (0 < k)), 1) := by
  rw [twTwistWord, morseShiftWord, List.map_replicate]
  rfl

/-- The thick operator of the shifted run of half twists on at least three bundles. -/
private theorem morseOp_shift_twTwistWord_twKSourceOp (c : ℕ) (k : ℤ) (N : ℕ)
    (hN : 3 * c ≤ N) :
    morseOp c (morseShiftWord 1 (twTwistWord k)) N N = skPlace N N c (halfTwistZ c k) := by
  rw [morseShiftWord_twTwistWord_twKSourceOp, morseOp_replicate_cross_one_twKSourceOp c _ N _ hN,
    halfTwistZ]
  rcases lt_trichotomy 0 k with hk | rfl | hk
  · rw [ite_eq_left hk.le, decide_eq_true hk, show k.natAbs = k.toNat by omega]
  · rfl
  · rw [ite_eq_right (by omega), decide_eq_false (by omega),
      show k.natAbs = (-k).toNat by omega]

set_option linter.unusedVariables false in
/-- The thick operator of the strip word with `k` half twists inserted. -/
theorem morseOp_tw_bottom (r s : ℕ) (h : IsTorusPair r s) (σ : Bool) (c : ℕ) (k : ℤ) :
    morseOp c ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord k) ++ twStripTail r s σ)
      c c = twSrcOp r s σ c (halfTwistZ c k) := by
  have h₁ : morseThickOut c c [isoU 1, isoX true 0] = 3 * c := by
    simp only [isoU, isoX, morseThickOut, morseKindOut, morseKindIn]
    omega
  have h₂ : morseThickOut c (3 * c) (morseShiftWord 1 (twTwistWord k)) = 3 * c := by
    rw [morseShiftWord_twTwistWord_twKSourceOp, morseThickOut_replicate_cross_twKSourceOp]
  rw [List.append_assoc, morseOp_append, h₁, morseOp_append, h₂,
    morseOp_shift_twTwistWord_twKSourceOp c k (3 * c) le_rfl, twSrcOp, Matrix.mul_assoc]

/-- The long-knot operator of the twisted knot. -/
theorem longKnotOp_twWhiteheadKnot_eq_twSrcOp {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (c : ℕ) :
    longKnotOp (twWhiteheadKnot r s h ℓ σ) c = twSrcOp r s σ c (halfTwistZ c (2 * ℓ)) := by
  obtain ⟨mvs, hmvs⟩ := morseReach_tw_source_bottom h ℓ σ
  rw [← morseOp_morseLongClosure_eq_longKnotOp, ← morseOp_tw_bottom r s h σ c (2 * ℓ)]
  exact morseOp_eq_of_morseApplyAll c 1 c c (Nat.mul_one c).symm _ _ mvs hmvs

end AJConjecture
