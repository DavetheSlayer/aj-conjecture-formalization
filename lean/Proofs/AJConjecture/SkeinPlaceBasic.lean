import Mathlib
import AJConjecture.SkeinPlaceComm
import AJConjecture.SkeinPlaceMul
import AJConjecture.SkeinPlaceAppend

/-!
# Placement: identity and linearity

`1_i ⊗ 1_k ⊗ 1_r = 1`, placing at the position `0` of the same space is the identity operation,
and `skPlace` is linear in the placed matrix. Proofs are entrywise from the definition.
-/

namespace AJConjecture

/-- The identity placed anywhere is the identity. -/
theorem skPlace_one (n i k : ℕ) (h : i + k ≤ n) : skPlace n n i (1 : SkMat k k) = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = i + k + r := ⟨n - (i + k), by omega⟩
  ext a b
  obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_append i k r a
  obtain ⟨b₁, b₂, b₃, rfl⟩ := exists_append i k r b
  rw [skPlace_append_apply, Matrix.one_apply, Matrix.one_apply]
  simp only [fin_append_inj]
  by_cases h₁ : a₁ = b₁ <;> by_cases h₂ : a₂ = b₂ <;> by_cases h₃ : a₃ = b₃ <;> simp [h₁, h₂, h₃]

/-- A matrix placed at the position `0` of its own space is itself. -/
theorem skPlace_self (k l : ℕ) (A : SkMat k l) : skPlace k l 0 A = A := by
  ext a b
  have hcond : 0 + k ≤ k ∧ k + l = l + k := by omega
  have h₁ : ∀ x : Fin k, (hx : (x : ℕ) < 0) → a x = b ⟨x, by omega⟩ := fun x hx ↦ by omega
  have h₂ : ∀ x : Fin k, (hx : 0 + k ≤ (x : ℕ)) → a x = b ⟨x + l - k, by omega⟩ :=
    fun x hx ↦ by omega
  have ea : (fun x : Fin k ↦ a ⟨0 + x, by omega⟩) = a := by
    funext x
    congr 1
    ext
    simp
  have eb : (fun y : Fin l ↦ b ⟨0 + y, by omega⟩) = b := by
    funext y
    congr 1
    ext
    simp
  simp only [skPlace, Matrix.of_apply]
  rw [dite_eq_left hcond, ite_eq_left ⟨h₁, h₂⟩, ea, eb]

/-- Placement is additive. -/
theorem skPlace_add (n n' i : ℕ) {k l : ℕ} (A B : SkMat k l) :
    skPlace n n' i (A + B) = skPlace n n' i A + skPlace n n' i B := by
  ext a b
  simp only [skPlace, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

/-- Placement commutes with scalars. -/
theorem skPlace_smul (n n' i : ℕ) {k l : ℕ} (x : RatFunc ℚ) (A : SkMat k l) :
    skPlace n n' i (x • A) = x • skPlace n n' i A := by
  ext a b
  simp only [skPlace, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

end AJConjecture
