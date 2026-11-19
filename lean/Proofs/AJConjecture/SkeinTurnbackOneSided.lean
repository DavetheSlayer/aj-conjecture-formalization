import Mathlib
import AJConjecture.SkeinTurnbackEigenBasic
import AJFamily.Skein.TorusOddColorOne
import AJConjecture.SkeinBubble
import AJConjecture.SkeinThickCupInner
import AJConjecture.SkeinTurnbackBasic

/-!
# The turnback recursion against a nest of caps

With `c = a + 1 + k`: `D_1 · caps_k = β_k (f ⊗ f) caps_k + α_k (f ⊗ f) caps_{k+1} · cup · (f_{a+1}
⊗ f_{a+1})`,
where `caps_k` is the nest of `k` caps on the middle strands, the cup re-creates the two middle
strands of the remaining `2a + 2`, `β_k = -[k][2c+1-k]/[c]²` and `α_k = [c-k]²/[c]²`; and for the
full
nest, `D_1 · caps_c = β_c (f ⊗ f) caps_c`.

Route: induction on `k`, for all `a`. For `k = 0` the statement is `AJConjecture.turnback_one`
with `e_{c-1} = capAt * cupAt`. For `k + 1`: write `D_1 = (f ⊗ f) capAt cupAt (f ⊗ f)` and the nest
as its innermost cap followed by the nest of `k` caps on two bundles of `c - 1` strands
(`AJConjecture.capThick_succ_inner`). The innermost cup and cap around `f ⊗ f` are a bubble
(`AJConjecture.skCup_mul_twoBundleProj_mul_skCap`): a multiple `x` of `g = f_{c-1} ⊗ f_{c-1}` plus a
multiple `y` of `g e_{c-2} g`, which is `D_1` of the bundles of `c - 1` strands, to which the
induction hypothesis applies. The projector `g` is absorbed
(`AJConjecture.twoBundleProj_mul_capThick_mul_twoBundleProj`), and the scalars combine by
`x + y β'_k = β_{k+1}`, `y α'_k = α_{k+1}`, that is `[2c] + [k][2c-1-k] = [k+1][2c-k]`.
-/

namespace AJConjecture

/-- The coefficient of `(f ⊗ f) caps_{k+1}` in the induction step:
`x + y β'_k = β_{k+1}`. -/
private theorem beta_step_scalar_oneSided (A K : ℤ) (hC : quantumInt (A + 1 + K) ≠ 0)
    (hC1 : quantumInt (A + 1 + K + 1) ≠ 0) :
    -(quantumInt (2 * (A + 1 + K) + 2)) / quantumInt (A + 1 + K + 1) ^ 2 +
        quantumInt (A + 1 + K) ^ 2 / quantumInt (A + 1 + K + 1) ^ 2 *
          (-(quantumInt K * quantumInt (2 * A + K + 3)) / quantumInt (A + 1 + K) ^ 2) =
      -(quantumInt (K + 1) * quantumInt (2 * A + (K + 1) + 3)) /
        quantumInt (A + 1 + (K + 1)) ^ 2 := by
  have key := quantumInt_mul_shift_sub K (2 * A + K + 3) 1
  rw [quantumInt_one, one_mul,
    show K + (2 * A + K + 3) + 1 = 2 * (A + 1 + K) + 2 from by ring] at key
  rw [show A + 1 + (K + 1) = A + 1 + K + 1 from by ring,
    show 2 * A + (K + 1) + 3 = 2 * A + K + 3 + 1 from by ring]
  field_simp
  linear_combination key

/-- The coefficient of the new term in the induction step: `y α'_k = α_{k+1}`. -/
private theorem alpha_step_scalar_oneSided (A K : ℤ) (hC : quantumInt (A + 1 + K) ≠ 0) :
    quantumInt (A + 1 + K) ^ 2 / quantumInt (A + 1 + K + 1) ^ 2 *
        (quantumInt (A + 1) ^ 2 / quantumInt (A + 1 + K) ^ 2) =
      quantumInt (A + 1) ^ 2 / quantumInt (A + 1 + (K + 1)) ^ 2 := by
  rw [show A + 1 + (K + 1) = A + 1 + K + 1 from by ring]
  field_simp

/-- The coefficient in the induction step for the full nest. -/
private theorem beta_full_scalar_oneSided (C : ℤ) (hC1 : quantumInt (C + 1) ≠ 0) :
    -(quantumInt (2 * C + 2)) / quantumInt (C + 1) ^ 2 +
        quantumInt C ^ 2 / quantumInt (C + 1) ^ 2 *
          (-(quantumInt C * quantumInt (C + 1)) / quantumInt C ^ 2) =
      -(quantumInt (C + 1) * quantumInt (C + 1 + 1)) / quantumInt (C + 1) ^ 2 := by
  have key := quantumInt_mul_shift_sub C (C + 1) 1
  rw [quantumInt_one, one_mul, show C + (C + 1) + 1 = 2 * C + 2 from by ring] at key
  by_cases h0 : quantumInt C = 0
  · rw [h0, zero_mul, sub_zero] at key
    rw [h0, zero_mul, neg_zero, zero_div, mul_zero, add_zero, key]
  · field_simp
    linear_combination key

/-- The thick cap on one strand is the cap. -/
private theorem capThick_one_oneSided : capThick 1 = skCap := by
  ext a b
  simp only [capThick, skCap, Matrix.of_apply, Fin.prod_univ_succ, Fin.val_zero,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rfl

/-- A placed nest of `c + 1` caps: the innermost cap, then the placed nest of `c` caps. -/
private theorem skPlace_capThick_succ_inner_oneSided (c m n' i j : ℕ) (h : i + 2 * c ≤ m)
    (h' : m = n' + 2 * c) (hj : j = i + c) :
    skPlace (m + 2) n' i (capThick (c + 1)) =
      skPlace (m + 2) m j skCap * skPlace m n' i (capThick c) := by
  subst hj
  rw [capThick_succ_inner,
    skPlace_mul (m + 2) m n' i _ (capThick c) (by omega) (by omega) (by omega),
    skPlace_skPlace (m + 2) m i c skCap (by omega) (by omega) (by omega) (by omega)]

/-- One cap below `f ⊗ f` absorbs the projectors of the thinner bundles. -/
private theorem twoBundleProj_mul_skCap_mul_twoBundleProj_oneSided (c : ℕ) :
    twoBundleProj (c + 1) * skPlace (2 * (c + 1)) (2 * c) c skCap * twoBundleProj c =
      twoBundleProj (c + 1) * skPlace (2 * (c + 1)) (2 * c) c skCap := by
  have h := twoBundleProj_mul_capThick_mul_twoBundleProj c 1
  rw [capThick_one_oneSided] at h
  exact h

/-- `D_1` against one cap: the bubble lemma. -/
private theorem turnback_one_mul_skCap_oneSided (c : ℕ) :
    turnback (c + 1) 1 * skPlace (2 * (c + 1)) (2 * c) c skCap =
      (-(quantumInt (2 * (c : ℤ) + 2)) / quantumInt ((c : ℤ) + 1) ^ 2) •
        (twoBundleProj (c + 1) * skPlace (2 * (c + 1)) (2 * c) c skCap) +
      (quantumInt (c : ℤ) ^ 2 / quantumInt ((c : ℤ) + 1) ^ 2) •
        (twoBundleProj (c + 1) * skPlace (2 * (c + 1)) (2 * c) c skCap * turnback c 1) := by
  have hE : tlGenF (2 * (c + 1)) (c + 1 - 1) =
      skPlace (2 * (c + 1)) (2 * c) c skCap * skPlace (2 * c) (2 * (c + 1)) c skCup := by
    rw [Nat.add_sub_cancel]
    exact (capAt_mul_cupAt (2 * c) c (by omega)).symm
  have habs := twoBundleProj_mul_skCap_mul_twoBundleProj_oneSided c
  have hbub := skCup_mul_twoBundleProj_mul_skCap c
  rw [← turnback_one c] at hbub
  rw [turnback_one (c + 1), hE]
  calc twoBundleProj (c + 1) *
          (skPlace (2 * (c + 1)) (2 * c) c skCap * skPlace (2 * c) (2 * (c + 1)) c skCup) *
          twoBundleProj (c + 1) * skPlace (2 * (c + 1)) (2 * c) c skCap =
        twoBundleProj (c + 1) * skPlace (2 * (c + 1)) (2 * c) c skCap *
          (skPlace (2 * c) (2 * (c + 1)) c skCup * twoBundleProj (c + 1) *
            skPlace (2 * (c + 1)) (2 * c) c skCap) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hbub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, habs]

/-- The algebra of the induction step: `D cap = x F cap + y F cap D'`, the induction hypothesis
for `D'`, and the absorption `F cap F' = F cap`. -/
private theorem oneSided_step_alg {K N M L L' : Type*} [CommRing K] [Fintype N] [Fintype M]
    [Fintype L] [Fintype L'] [DecidableEq N] [DecidableEq M] [DecidableEq L]
    (D F : Matrix N N K) (cap : Matrix N M K) (D' F' : Matrix M M K) (P : Matrix M L K)
    (R1 : Matrix M L' K) (R2 : Matrix L' L K) (R3 : Matrix L L K) (x y β α : K)
    (hS : D * cap = x • (F * cap) + y • (F * cap * D'))
    (hIH : D' * P = β • (F' * P) + α • (F' * R1 * R2 * R3))
    (habs : F * cap * F' = F * cap) :
    D * (cap * P) = (x + y * β) • (F * (cap * P)) + (y * α) • (F * (cap * R1) * R2 * R3) := by
  have e1 : F * cap * (F' * P) = F * (cap * P) := by
    rw [← Matrix.mul_assoc, habs, Matrix.mul_assoc]
  have e2 : F * cap * (F' * R1 * R2 * R3) = F * (cap * R1) * R2 * R3 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, habs,
      Matrix.mul_assoc F cap R1]
  rw [← Matrix.mul_assoc, hS, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc (F * cap) D' P, hIH, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, e1, e2,
    Matrix.mul_assoc F cap P]
  module

/-- The algebra of the induction step for the full nest. -/
private theorem oneSided_full_step_alg {K N M L : Type*} [CommRing K] [Fintype N] [Fintype M]
    [Fintype L] [DecidableEq N] [DecidableEq M] [DecidableEq L]
    (D F : Matrix N N K) (cap : Matrix N M K) (D' F' : Matrix M M K) (P : Matrix M L K)
    (x y β : K) (hS : D * cap = x • (F * cap) + y • (F * cap * D'))
    (hIH : D' * P = β • (F' * P)) (habs : F * cap * F' = F * cap) :
    D * (cap * P) = (x + y * β) • (F * (cap * P)) := by
  have e1 : F * cap * (F' * P) = F * (cap * P) := by
    rw [← Matrix.mul_assoc, habs, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hS, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc (F * cap) D' P, hIH, Matrix.mul_smul, e1, Matrix.mul_assoc F cap P]
  module

/-- The turnback recursion against the empty nest of caps. -/
private theorem turnback_one_mul_capThick_place_zero_oneSided (a : ℕ) :
    turnback (a + 1) 1 * skPlace (2 * (a + 1)) (2 * (a + 1)) (a + 1) (capThick 0) =
      (-(quantumInt ((0 : ℕ) : ℤ) * quantumInt (2 * (a : ℤ) + ((0 : ℕ) : ℤ) + 3)) /
          quantumInt ((a : ℤ) + 1 + ((0 : ℕ) : ℤ)) ^ 2) •
        (twoBundleProj (a + 1) * skPlace (2 * (a + 1)) (2 * (a + 1)) (a + 1) (capThick 0)) +
      (quantumInt ((a : ℤ) + 1) ^ 2 / quantumInt ((a : ℤ) + 1 + ((0 : ℕ) : ℤ)) ^ 2) •
        (twoBundleProj (a + 1) * skPlace (2 * (a + 1)) (2 * a) a (capThick 1) *
          skPlace (2 * a) (2 * (a + 1)) a skCup * twoBundleProj (a + 1)) := by
  have hne : quantumInt ((a : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h0 : skPlace (2 * (a + 1)) (2 * (a + 1)) (a + 1) (capThick 0) = 1 := by
    rw [capThick_zero]
    exact skPlace_one (2 * (a + 1)) (a + 1) 0 (by omega)
  have h1 : skPlace (2 * (a + 1)) (2 * a) a (capThick 1) * skPlace (2 * a) (2 * (a + 1)) a skCup =
      tlGenF (2 * (a + 1)) (a + 1 - 1) := by
    rw [capThick_one_oneSided, Nat.add_sub_cancel]
    exact capAt_mul_cupAt (2 * a) a (by omega)
  rw [h0, Matrix.mul_one, Matrix.mul_one, Nat.cast_zero, quantumInt_zero, zero_mul,
    neg_zero, zero_div, zero_smul, zero_add, add_zero, div_self (pow_ne_zero 2 hne), one_smul,
    Matrix.mul_assoc (twoBundleProj (a + 1)), h1]
  exact turnback_one (a + 1)

/-- The induction step of the turnback recursion against a nest of caps. -/
private theorem turnback_one_mul_capThick_place_succ_oneSided (a k : ℕ)
    (ih : turnback (a + 1 + k) 1 *
        skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k) =
      (-(quantumInt (k : ℤ) * quantumInt (2 * (a : ℤ) + k + 3)) /
          quantumInt ((a : ℤ) + 1 + k) ^ 2) •
        (twoBundleProj (a + 1 + k) *
          skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k)) +
      (quantumInt ((a : ℤ) + 1) ^ 2 / quantumInt ((a : ℤ) + 1 + k) ^ 2) •
        (twoBundleProj (a + 1 + k) * skPlace (2 * (a + 1 + k)) (2 * a) a (capThick (k + 1)) *
          skPlace (2 * a) (2 * (a + 1)) a skCup * twoBundleProj (a + 1))) :
    turnback (a + 1 + k + 1) 1 *
        skPlace (2 * (a + 1 + k + 1)) (2 * (a + 1)) (a + 1) (capThick (k + 1)) =
      (-(quantumInt ((k + 1 : ℕ) : ℤ) * quantumInt (2 * (a : ℤ) + ((k + 1 : ℕ) : ℤ) + 3)) /
          quantumInt ((a : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) ^ 2) •
        (twoBundleProj (a + 1 + k + 1) *
          skPlace (2 * (a + 1 + k + 1)) (2 * (a + 1)) (a + 1) (capThick (k + 1))) +
      (quantumInt ((a : ℤ) + 1) ^ 2 / quantumInt ((a : ℤ) + 1 + ((k + 1 : ℕ) : ℤ)) ^ 2) •
        (twoBundleProj (a + 1 + k + 1) *
          skPlace (2 * (a + 1 + k + 1)) (2 * a) a (capThick (k + 1 + 1)) *
          skPlace (2 * a) (2 * (a + 1)) a skCup * twoBundleProj (a + 1)) := by
  have hC : quantumInt ((a : ℤ) + 1 + k) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hC1 : quantumInt ((a : ℤ) + 1 + k + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hS := turnback_one_mul_skCap_oneSided (a + 1 + k)
  have habs := twoBundleProj_mul_skCap_mul_twoBundleProj_oneSided (a + 1 + k)
  have hN1 : skPlace (2 * (a + 1 + k + 1)) (2 * (a + 1)) (a + 1) (capThick (k + 1)) =
      skPlace (2 * (a + 1 + k + 1)) (2 * (a + 1 + k)) (a + 1 + k) skCap *
        skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k) :=
    skPlace_capThick_succ_inner_oneSided k (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (a + 1 + k)
      (by omega) (by omega) (by omega)
  have hN2 : skPlace (2 * (a + 1 + k + 1)) (2 * a) a (capThick (k + 1 + 1)) =
      skPlace (2 * (a + 1 + k + 1)) (2 * (a + 1 + k)) (a + 1 + k) skCap *
        skPlace (2 * (a + 1 + k)) (2 * a) a (capThick (k + 1)) :=
    skPlace_capThick_succ_inner_oneSided (k + 1) (2 * (a + 1 + k)) (2 * a) a (a + 1 + k)
      (by omega) (by omega) (by omega)
  rw [hN1, hN2]
  refine (oneSided_step_alg _ _ _ _ _ _ _ _ _ _ _ _ _ hS ih habs).trans ?_
  push_cast
  rw [beta_step_scalar_oneSided (a : ℤ) (k : ℤ) hC hC1,
    alpha_step_scalar_oneSided (a : ℤ) (k : ℤ) hC]

/-- The turnback recursion against a nest of `k` caps that leaves `2a + 2` strands. -/
theorem turnback_one_mul_capThick_place (a k : ℕ) :
    turnback (a + 1 + k) 1 * skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k) =
      (-(quantumInt (k : ℤ) * quantumInt (2 * (a : ℤ) + k + 3)) /
          quantumInt ((a : ℤ) + 1 + k) ^ 2) •
        (twoBundleProj (a + 1 + k) *
          skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k)) +
      (quantumInt ((a : ℤ) + 1) ^ 2 / quantumInt ((a : ℤ) + 1 + k) ^ 2) •
        (twoBundleProj (a + 1 + k) * skPlace (2 * (a + 1 + k)) (2 * a) a (capThick (k + 1)) *
          skPlace (2 * a) (2 * (a + 1)) a skCup * twoBundleProj (a + 1)) := by
  induction k with
  | zero => exact turnback_one_mul_capThick_place_zero_oneSided a
  | succ k ih => exact turnback_one_mul_capThick_place_succ_oneSided a k ih

/-- The turnback recursion against the full nest of caps. -/
theorem turnback_one_mul_capThick (c : ℕ) :
    turnback c 1 * capThick c =
      (-(quantumInt (c : ℤ) * quantumInt ((c : ℤ) + 1)) / quantumInt (c : ℤ) ^ 2) •
        (twoBundleProj c * capThick c) := by
  induction c with
  | zero =>
    rw [turnback_eq_zero 0 1 (by omega), Matrix.zero_mul, Nat.cast_zero, quantumInt_zero,
      zero_mul, neg_zero, zero_div, zero_smul]
  | succ c ih =>
    have hC1 : quantumInt ((c : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    rw [capThick_succ_inner c]
    refine (oneSided_full_step_alg _ _ _ _ _ _ _ _ _ (turnback_one_mul_skCap_oneSided c) ih
      (twoBundleProj_mul_skCap_mul_twoBundleProj_oneSided c)).trans ?_
    push_cast
    rw [beta_full_scalar_oneSided (c : ℤ) hC1]

end AJConjecture
