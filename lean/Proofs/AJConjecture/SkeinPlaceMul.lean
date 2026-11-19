import Mathlib
import AJConjecture.SkeinPlaceAppend

/-!
# Placement is functorial

`1 ⊗ (A B) ⊗ 1 = (1 ⊗ A ⊗ 1)(1 ⊗ B ⊗ 1)`, for rectangular `A`, `B` and with the intermediate
ambient size determined by `n + l = n' + k`. Proof: in the entry of the product, the summation
over the intermediate states of `V^{⊗ n'}` collapses to the states that agree with the input
outside the window, which are in bijection with the states of `V^{⊗ l}`; an alternative is to
identify `skPlace` with a re-indexed Kronecker product and use `Matrix.mul_kronecker_mul`.
-/

namespace AJConjecture

/-- Every state of `i + k + r` factors is a concatenation of three states. -/
theorem exists_append (i k r : ℕ) (a : Fin (i + k + r) → Bool) :
    ∃ (a₁ : Fin i → Bool) (a₂ : Fin k → Bool) (a₃ : Fin r → Bool),
      a = Fin.append (Fin.append a₁ a₂) a₃ :=
  ⟨fun x ↦ a (Fin.castAdd r (Fin.castAdd k x)), fun x ↦ a (Fin.castAdd r (Fin.natAdd i x)),
    fun x ↦ a (Fin.natAdd (i + k) x), by
      rw [Fin.append_castAdd_natAdd (f := fun y ↦ a (Fin.castAdd r y)),
        Fin.append_castAdd_natAdd]⟩

/-- A sum over the states of `i + l + s` factors is a sum over the three parts of the state. -/
private theorem sum_append_placeMul (i l s : ℕ) (f : (Fin (i + l + s) → Bool) → RatFunc ℚ) :
    ∑ c, f c = ∑ c₁ : Fin i → Bool, ∑ c₃ : Fin s → Bool, ∑ c₂ : Fin l → Bool,
      f (Fin.append (Fin.append c₁ c₂) c₃) := by
  rw [← (Fin.appendEquiv (i + l) s).sum_comp, Fintype.sum_prod_type,
    ← (Fin.appendEquiv i l).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
  rw [Finset.sum_comm]
  rfl

/-- Functoriality of the placement of a rectangular matrix. -/
theorem skPlace_mul (n n' n'' i : ℕ) {k l r : ℕ} (A : SkMat k l) (B : SkMat l r)
    (h : i + k ≤ n) (h' : n + l = n' + k) (h'' : n' + r = n'' + l) :
    skPlace n n'' i (A * B) = skPlace n n' i A * skPlace n' n'' i B := by
  obtain ⟨s, rfl⟩ : ∃ s, n = i + k + s := ⟨n - (i + k), by omega⟩
  obtain rfl : n' = i + l + s := by omega
  obtain rfl : n'' = i + r + s := by omega
  ext a b
  obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_append i k s a
  obtain ⟨b₁, b₂, b₃, rfl⟩ := exists_append i r s b
  rw [skPlace_append_apply, Matrix.mul_apply, Matrix.mul_apply, sum_append_placeMul i l s]
  simp only [skPlace_append_apply]
  rw [Fintype.sum_eq_single a₁, Fintype.sum_eq_single a₃]
  · by_cases h₁ : a₁ = b₁ <;> by_cases h₃ : a₃ = b₃ <;> simp [h₁, h₃]
  · intro c hc
    simp [Ne.symm hc]
  · intro c hc
    simp [Ne.symm hc]

end AJConjecture
