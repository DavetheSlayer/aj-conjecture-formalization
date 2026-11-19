import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.SkeinPlaceMul

/-!
# The Temperley–Lieb generator is a cap followed by a cup

Entrywise `cupCapEntry a₀ a₁ b₀ b₁ = cap(a₀, a₁) · cup(b₀, b₁)`, hence `e = cap * cup` on two
strands, the generator `e_i` of `V^{⊗ m}` is this matrix placed at the position `i`, and
`e_i = capAt * cupAt`.
-/

namespace AJConjecture

open LaurentPolynomial in

/-- Entrywise, `e = cap * cup`. -/
private theorem laurentToField_cupCapEntry_tlGenPlace (a₀ a₁ b₀ b₁ : Bool) :
    laurentToField (cupCapEntry a₀ a₁ b₀ b₁) = capEntry a₀ a₁ * cupEntry b₀ b₁ := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    simp [cupCapEntry, capEntry, cupEntry, laurentToField_T, hX]

/-- The entries of the generator on two strands. -/
private theorem tlGenF_two_zero_apply_tlGenPlace (a b : Fin 2 → Bool) :
    tlGenF 2 0 a b = laurentToField (cupCapEntry (a 0) (a 1) (b 0) (b 1)) := by
  have hcond : ∀ k : Fin 2, (k : ℕ) ≠ 0 → (k : ℕ) ≠ 0 + 1 → a k = b k := fun k h₀ h₁ ↦ by omega
  simp only [tlGenF, Matrix.map_apply, tlGen, Matrix.of_apply]
  rw [dite_eq_left (by omega), ite_eq_left hcond]
  rfl

/-- On two strands, `e = cap * cup`. -/
theorem skCap_mul_skCup : skCap * skCup = tlGenF 2 0 := by
  ext a b
  rw [tlGenF_two_zero_apply_tlGenPlace, laurentToField_cupCapEntry_tlGenPlace, Matrix.mul_apply,
    Fintype.sum_eq_single (fun x : Fin 0 ↦ x.elim0) fun c hc ↦ absurd (Subsingleton.elim _ _) hc]
  rfl

/-- The generator `e_i` is the two-strand generator placed at the position `i`. -/
theorem tlGenF_eq_skPlace (m i : ℕ) : tlGenF m i = skPlace m m i (tlGenF 2 0) := by
  ext a b
  by_cases hm : i + 1 < m
  · simp only [tlGenF_two_zero_apply_tlGenPlace, skPlace, Matrix.of_apply]
    simp only [tlGenF, Matrix.map_apply, tlGen, Matrix.of_apply]
    rw [dite_eq_left hm, dite_eq_left ⟨by omega, trivial⟩, apply_ite laurentToField, map_zero]
    refine if_congr ⟨fun hP ↦ ⟨fun x hx ↦ hP x (by omega) (by omega), fun x hx ↦ ?_⟩,
      fun hQ x h₀ h₁ ↦ ?_⟩ rfl rfl
    · exact (hP x (by omega) (by omega)).trans (congrArg b (Fin.ext (by simp)))
    · rcases lt_or_ge (x : ℕ) i with hx | hx
      · exact hQ.1 x hx
      · exact (hQ.2 x (by omega)).trans (congrArg b (Fin.ext (by simp)))
  · have hfit : ¬(i + 2 ≤ m ∧ True) := fun hf ↦ hm (by omega)
    simp only [tlGenF, Matrix.map_apply, tlGen, skPlace, Matrix.of_apply]
    rw [dite_eq_right hm, dite_eq_right hfit, map_zero]

/-- `e_i` is the cap on the strands `i`, `i + 1` followed by the cup at the same position. -/
theorem capAt_mul_cupAt (n i : ℕ) (h : i ≤ n) : capAt n i * cupAt n i = tlGenF (n + 2) i := by
  rw [capAt, cupAt, ← skPlace_mul (n + 2) n (n + 2) i skCap skCup (by omega) (by omega) (by omega),
    skCap_mul_skCup, ← tlGenF_eq_skPlace]

end AJConjecture
