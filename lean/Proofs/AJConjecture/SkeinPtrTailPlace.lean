import Mathlib
import AJConjecture.SkeinTraceCyclic
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinPartialTrace
import AJConjecture.SkeinPlaceBasic
import AJConjecture.SkeinTlGenPlace

/-!
# Partial traces of placed operators

The partial trace over the last factors commutes with spectator factors on the left:
`ptr(1_i ⊗ A) = 1_i ⊗ ptr(A)`; and the partial trace of a crossing of the last two strands over
the last strand is the kink scalar `-t^{±3}` (Markov's property as an identity of operators):
`ptr(1) = δ`, `ptr(e) = 1` and `t δ + t⁻¹ = -t³`. Both are entrywise computations with
`AJConjecture.skPlace_append_apply`.
-/

namespace AJConjecture

/-- Proves an equality between two values of states that are defined by cases on the
position. -/
local macro "state_cases_ptrTailPlace" : tactic =>
  `(tactic| (simp only [append_apply_dite, Fin.val_cast]
             split_ifs <;> first | rfl | (exfalso; omega) |
               (congr 1; exact Fin.ext (by dsimp only; omega))))

/-- The entries of a matrix placed on the last factors. -/
private theorem skPlace_tail_append_apply_ptrTailPlace (i : ℕ) {k l : ℕ} (A : SkMat k l)
    (a₁ b₁ : Fin i → Bool) (a₂ : Fin k → Bool) (b₂ : Fin l → Bool) :
    skPlace (i + k) (i + l) i A (Fin.append a₁ a₂) (Fin.append b₁ b₂) =
      if a₁ = b₁ then A a₂ b₂ else 0 := by
  rw [skPlace_apply_of_eq (n := i + k) (n' := i + l) i 0 A rfl rfl
    (Fin.append a₁ a₂) (Fin.append b₁ b₂) a₁ b₁ a₂ b₂ Fin.elim0 Fin.elim0
    (fun x ↦ by state_cases_ptrTailPlace) (fun x ↦ by state_cases_ptrTailPlace)]
  simp

/-- The entries of a matrix placed on the last factors, on the states of a partial trace. -/
private theorem skPlace_tail_dite_apply_ptrTailPlace (i k r : ℕ) (A : SkMat (k + r) (k + r))
    (a₁ b₁ : Fin i → Bool) (a₂ b₂ : Fin k → Bool) (s : Fin r → Bool) :
    skPlace (i + (k + r)) (i + (k + r)) i A
        (fun j ↦ if h : (j : ℕ) < i + k then Fin.append a₁ a₂ ⟨j, h⟩
          else s ⟨j - (i + k), by omega⟩)
        (fun j ↦ if h : (j : ℕ) < i + k then Fin.append b₁ b₂ ⟨j, h⟩
          else s ⟨j - (i + k), by omega⟩) =
      if a₁ = b₁ then A (Fin.append a₂ s) (Fin.append b₂ s) else 0 := by
  rw [skPlace_apply_of_eq (n := i + (k + r)) (n' := i + (k + r)) i 0 A rfl rfl
    (fun j ↦ if h : (j : ℕ) < i + k then Fin.append a₁ a₂ ⟨j, h⟩
      else s ⟨j - (i + k), by omega⟩)
    (fun j ↦ if h : (j : ℕ) < i + k then Fin.append b₁ b₂ ⟨j, h⟩
      else s ⟨j - (i + k), by omega⟩)
    a₁ b₁ (Fin.append a₂ s) (Fin.append b₂ s) Fin.elim0 Fin.elim0
    (fun x ↦ by state_cases_ptrTailPlace) (fun x ↦ by state_cases_ptrTailPlace)]
  simp

/-- The partial trace commutes with spectator factors on the left. -/
theorem ptrTail_skPlace_shift (i k n : ℕ) (h : k ≤ n) (A : SkMat n n) :
    ptrTail (i + k) (i + n) (skPlace (i + n) (i + n) i A) =
      skPlace (i + k) (i + k) i (ptrTail k n A) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  ext a b
  obtain ⟨a₁, a₂, rfl⟩ := exists_append_eq a
  obtain ⟨b₁, b₂, rfl⟩ := exists_append_eq b
  rw [ptrTail_apply_of_eq (i + k) (i + (k + r)) r (by omega),
    skPlace_tail_append_apply_ptrTailPlace, ptrTail_append_apply]
  simp only [skPlace_tail_dite_apply_ptrTailPlace]
  by_cases hab : a₁ = b₁
  · simp only [hab, ite_true]
  · simp only [hab, ite_false, mul_zero, Finset.sum_const_zero]

/-- The partial trace is additive. -/
theorem ptrTail_add (k n : ℕ) (A B : SkMat n n) :
    ptrTail k n (A + B) = ptrTail k n A + ptrTail k n B := by
  ext a b
  simp only [ptrTail, Matrix.of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- The partial trace commutes with scalars. -/
theorem ptrTail_smul (k n : ℕ) (x : RatFunc ℚ) (A : SkMat n n) :
    ptrTail k n (x • A) = x • ptrTail k n A := by
  ext a b
  simp only [ptrTail, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  ring

/-- The embedding `ℤ[t, t⁻¹] → ℚ(t)` sends `t ^ n` to `t ^ n`. -/
private theorem laurentToField_T_ptrTailPlace (n : ℤ) :
    laurentToField (LaurentPolynomial.T n) = (RatFunc.X : RatFunc ℚ) ^ n := by
  rw [laurentToField, LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- The entries of the generator on two strands. -/
private theorem tlGenF_two_zero_apply_ptrTailPlace (c d : Fin 2 → Bool) :
    tlGenF 2 0 c d = laurentToField (cupCapEntry (c 0) (c 1) (d 0) (d 1)) := by
  simp [tlGenF, tlGen, Fin.forall_fin_two]

/-- A sum over the states of one factor. -/
private theorem sum_states_one_ptrTailPlace (f : (Fin 1 → Bool) → RatFunc ℚ) :
    ∑ s, f s = f (fun _ ↦ true) + f (fun _ ↦ false) := by
  rw [← Fintype.sum_bool (fun t ↦ f (fun _ ↦ t))]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _ _ fun s ↦ ?_
  congr 1
  funext x
  rw [Subsingleton.elim x default]
  rfl

/-- Every state of one factor is constant. -/
private theorem exists_eq_const_ptrTailPlace (a : Fin 1 → Bool) : ∃ p : Bool, a = fun _ ↦ p :=
  ⟨a 0, funext fun x ↦ by rw [Subsingleton.elim x 0]⟩

/-- The partial trace over the second of two factors, entrywise. -/
private theorem ptrTail_one_two_apply_ptrTailPlace (M : SkMat 2 2) (p q : Bool) :
    ptrTail 1 2 M (fun _ ↦ p) (fun _ ↦ q) =
      skWeightEntry true * M ![p, true] ![q, true] +
        skWeightEntry false * M ![p, false] ![q, false] := by
  have e : ∀ u t : Bool, (fun j : Fin 2 ↦ if (j : ℕ) < 1 then u else t) = ![u, t] := by
    intro u t
    funext j
    fin_cases j <;> rfl
  rw [ptrTail_apply_of_eq 1 2 1 rfl, sum_states_one_ptrTailPlace]
  simp only [dite_eq_ite, e, Finset.univ_unique, Finset.prod_singleton]

/-- On two strands, the partial trace of the generator is the identity. -/
private theorem ptrTail_tlGenF_two_ptrTailPlace : ptrTail 1 2 (tlGenF 2 0) = 1 := by
  ext a b
  obtain ⟨p, rfl⟩ := exists_eq_const_ptrTailPlace a
  obtain ⟨q, rfl⟩ := exists_eq_const_ptrTailPlace b
  rw [ptrTail_one_two_apply_ptrTailPlace]
  simp only [tlGenF_two_zero_apply_ptrTailPlace, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.one_apply]
  cases p <;> cases q <;>
    simp [cupCapEntry, skWeightEntry, laurentToField_T_ptrTailPlace, RatFunc.X_ne_zero,
      funext_iff]

/-- On two strands, the partial trace of the identity is the loop value. -/
private theorem ptrTail_one_two_ptrTailPlace :
    ptrTail 1 2 (1 : SkMat 2 2) =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • (1 : SkMat 1 1) := by
  ext a b
  obtain ⟨p, rfl⟩ := exists_eq_const_ptrTailPlace a
  obtain ⟨q, rfl⟩ := exists_eq_const_ptrTailPlace b
  rw [ptrTail_one_two_apply_ptrTailPlace]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  cases p <;> cases q <;> simp [skWeightEntry, funext_iff, Fin.forall_fin_two] <;> ring

/-- A crossing of the last two strands is the two-strand crossing placed at the end. -/
private theorem crossingF_last_eq_skPlace_ptrTailPlace (n : ℕ) (s : Bool) :
    crossingF (n + 2) (n, s) = skPlace (n + 2) (n + 2) n (crossingF 2 (0, s)) := by
  cases s
  · rw [crossingF_neg, crossingF_neg, skPlace_add, skPlace_smul, skPlace_smul,
      skPlace_one _ _ _ (by omega), ← tlGenF_eq_skPlace]
  · rw [crossingF_pos, crossingF_pos, skPlace_add, skPlace_smul, skPlace_smul,
      skPlace_one _ _ _ (by omega), ← tlGenF_eq_skPlace]

/-- On two strands, the partial trace of a crossing is the kink scalar. -/
private theorem ptrTail_crossingF_two_ptrTailPlace (s : Bool) :
    ptrTail 1 2 (crossingF 2 (0, s)) =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) •
        (1 : SkMat 1 1) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  cases s
  · rw [crossingF_neg, ptrTail_add, ptrTail_smul,
      ptrTail_smul, ptrTail_one_two_ptrTailPlace, ptrTail_tlGenF_two_ptrTailPlace,
      smul_smul, ← add_smul]
    congr 1
    simp only [zpow_neg, zpow_ofNat, Bool.false_eq_true, ite_false]
    field_simp
    ring
  · rw [crossingF_pos, ptrTail_add, ptrTail_smul,
      ptrTail_smul, ptrTail_one_two_ptrTailPlace, ptrTail_tlGenF_two_ptrTailPlace,
      smul_smul, ← add_smul]
    congr 1
    simp only [zpow_neg, zpow_ofNat, ite_true]
    field_simp
    ring

/-- The partial trace of a crossing of the last two strands over the last strand is `-t³`
(positive crossing) or `-t⁻³` (negative crossing). -/
theorem ptrTail_crossingF_last (n : ℕ) (s : Bool) :
    ptrTail (n + 1) (n + 2) (crossingF (n + 2) (n, s)) =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) •
        (1 : SkMat (n + 1) (n + 1)) := by
  rw [crossingF_last_eq_skPlace_ptrTailPlace, ptrTail_skPlace_shift n 1 2 (by omega),
    ptrTail_crossingF_two_ptrTailPlace, skPlace_smul, skPlace_one _ _ _ (by omega)]

end AJConjecture
