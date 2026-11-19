import Mathlib
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinTlGenPlace

/-!
# The weight is preserved, and the quantum trace is cyclic

Every generator of the calculus intertwines the weights `μ^{⊗ n}`: the generators `e_i` and the
crossings preserve the number of `true` entries, and a cup or a cap creates or removes a pair
`(F, T)` or `(T, F)` of total weight `1`. Hence `qtr(A B) = qtr(B A)` for a rectangular `A` that
intertwines the weights.
-/

namespace AJConjecture

/-- Cyclicity of the quantum trace for a rectangular matrix that intertwines the weights. -/
theorem qtr_mul_comm_of_weight (n n' : ℕ) (A : SkMat n n') (B : SkMat n' n)
    (hA : skWeight n * A = A * skWeight n') : qtr n (A * B) = qtr n' (B * A) := by
  rw [qtr, qtr, ← Matrix.mul_assoc, hA, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc]

/-- Every state of `m + n` factors is a concatenation. -/
theorem exists_append_eq {m n : ℕ} (a : Fin (m + n) → Bool) :
    ∃ (a₁ : Fin m → Bool) (a₂ : Fin n → Bool), a = Fin.append a₁ a₂ :=
  ⟨fun x ↦ a (Fin.castAdd n x), fun x ↦ a (Fin.natAdd m x), Fin.append_castAdd_natAdd.symm⟩

/-- A placement of a matrix that intertwines the weights intertwines the weights. -/
private theorem skWeight_mul_skPlace_traceCyclic (n n' i : ℕ) {k l : ℕ} (A : SkMat k l)
    (hA : skWeight k * A = A * skWeight l) :
    skWeight n * skPlace n n' i A = skPlace n n' i A * skWeight n' := by
  by_cases h : i + k ≤ n ∧ n + l = n' + k
  · obtain ⟨r, rfl⟩ : ∃ r, n = i + k + r := ⟨n - (i + k), by omega⟩
    obtain rfl : n' = i + l + r := by omega
    ext a b
    obtain ⟨a₁₂, a₃, rfl⟩ := exists_append_eq a
    obtain ⟨a₁, a₂, rfl⟩ := exists_append_eq a₁₂
    obtain ⟨b₁₂, b₃, rfl⟩ := exists_append_eq b
    obtain ⟨b₁, b₂, rfl⟩ := exists_append_eq b₁₂
    have hA' := congrFun (congrFun hA a₂) b₂
    rw [skWeight, skWeight, Matrix.diagonal_mul, Matrix.mul_diagonal] at hA'
    rw [skWeight, skWeight, Matrix.diagonal_mul, Matrix.mul_diagonal, skPlace_append_apply]
    simp only [prod_skWeightEntry_append]
    by_cases hc : a₁ = b₁ ∧ a₃ = b₃
    · obtain ⟨rfl, rfl⟩ := hc
      rw [ite_eq_left ⟨rfl, rfl⟩]
      linear_combination ((∏ x, skWeightEntry (a₁ x)) * ∏ x, skWeightEntry (a₃ x)) * hA'
    · rw [ite_eq_right hc, mul_zero, zero_mul]
  · have h0 : skPlace n n' i A = 0 := by
      ext a b
      simp [skPlace, h]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul]

/-- The cup intertwines the weights. -/
private theorem skWeight_mul_skCup_traceCyclic : skWeight 0 * skCup = skCup * skWeight 2 := by
  ext a b
  rw [skWeight, skWeight, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [skCup, Matrix.of_apply, Finset.univ_eq_empty, Finset.prod_empty, Fin.prod_univ_two]
  cases b 0 <;> cases b 1 <;> simp [cupEntry, skWeightEntry, RatFunc.X_ne_zero]

/-- The cap intertwines the weights. -/
theorem skWeight_mul_skCap : skWeight 2 * skCap = skCap * skWeight 0 := by
  ext a b
  rw [skWeight, skWeight, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [skCap, Matrix.of_apply, Finset.univ_eq_empty, Finset.prod_empty, Fin.prod_univ_two]
  cases a 0 <;> cases a 1 <;> simp [capEntry, skWeightEntry, RatFunc.X_ne_zero]

/-- The weight commutes with the Temperley–Lieb generators. -/
theorem skWeight_mul_tlGenF (m i : ℕ) : skWeight m * tlGenF m i = tlGenF m i * skWeight m := by
  rw [tlGenF_eq_skPlace]
  refine skWeight_mul_skPlace_traceCyclic m m i _ ?_
  rw [← skCap_mul_skCup, ← Matrix.mul_assoc, skWeight_mul_skCap, Matrix.mul_assoc,
    skWeight_mul_skCup_traceCyclic, Matrix.mul_assoc]

/-- The weight commutes with the crossing matrices. -/
private theorem skWeight_mul_crossingF_traceCyclic (m : ℕ) (g : ℕ × Bool) :
    skWeight m * crossingF m g = crossingF m g * skWeight m := by
  obtain ⟨i, s⟩ := g
  cases s
  · rw [crossingF_neg, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
      Matrix.mul_smul, Matrix.smul_mul, skWeight_mul_tlGenF]
  · rw [crossingF_pos, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
      Matrix.mul_smul, Matrix.smul_mul, skWeight_mul_tlGenF]

/-- The weight commutes with braid matrices. -/
theorem skWeight_mul_braidMatrix (m : ℕ) (w : BraidWord) :
    skWeight m * braidMatrix m w = braidMatrix m w * skWeight m := by
  induction w with
  | nil => rw [braidMatrix_nil, mul_one, one_mul]
  | cons g w ih =>
    have hcons : braidMatrix m (g :: w) = crossingF m g * braidMatrix m w := by
      rw [braidMatrix, List.map_cons, List.prod_cons, braidMatrix]
    rw [hcons, ← Matrix.mul_assoc, skWeight_mul_crossingF_traceCyclic, Matrix.mul_assoc, ih,
      Matrix.mul_assoc]

/-- A cap intertwines the weights. -/
theorem skWeight_mul_capAt (n i : ℕ) : skWeight (n + 2) * capAt n i = capAt n i * skWeight n :=
  skWeight_mul_skPlace_traceCyclic (n + 2) n i skCap skWeight_mul_skCap

end AJConjecture
