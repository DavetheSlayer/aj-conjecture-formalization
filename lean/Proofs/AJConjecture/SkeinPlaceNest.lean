import Mathlib
import AJConjecture.SkeinPlace

/-!
# Nested placements

Placing at the position `i` a matrix that is itself a placement at the position `j` is the
placement at the position `i + j`. Proof: entrywise.
-/

namespace AJConjecture

/-- A state takes equal values at equal positions. -/
private theorem state_congr_placeNest {n : ℕ} (a : Fin n → Bool) {x y : ℕ} (hx : x < n)
    (hy : y < n) (h : x = y) : a ⟨x, hx⟩ = a ⟨y, hy⟩ := by
  subst h
  rfl

/-- Placements compose by adding the positions. -/
theorem skPlace_skPlace (n n' i j : ℕ) {k l k' l' : ℕ} (A : SkMat k l)
    (hj : j + k ≤ k') (hkl : k' + l = l' + k) (h : i + k' ≤ n) (h' : n + l' = n' + k') :
    skPlace n n' i (skPlace k' l' j A) = skPlace n n' (i + j) A := by
  ext a b
  have c₁ : i + k' ≤ n ∧ n + l' = n' + k' := ⟨h, h'⟩
  have c₂ : j + k ≤ k' ∧ k' + l = l' + k := ⟨hj, hkl⟩
  have c₃ : i + j + k ≤ n ∧ n + l = n' + k := by omega
  simp only [skPlace, Matrix.of_apply, c₁, c₂, c₃, and_self, ↓reduceDIte]
  rw [← ite_and]
  refine if_congr ⟨?_, ?_⟩ ?_ rfl
  · rintro ⟨⟨p₁, p₂⟩, q₁, q₂⟩
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · by_cases hxi : (x : ℕ) < i
      · exact p₁ x hxi
      · have hq := q₁ ⟨x - i, by omega⟩ (by dsimp only; omega)
        dsimp only at hq
        exact (state_congr_placeNest a x.isLt _ (by omega)).trans
          (hq.trans (state_congr_placeNest b _ _ (by omega)))
    · by_cases hxi : i + k' ≤ (x : ℕ)
      · exact (p₂ x hxi).trans (state_congr_placeNest b _ _ (by omega))
      · have hq := q₂ ⟨x - i, by omega⟩ (by dsimp only; omega)
        dsimp only at hq
        exact (state_congr_placeNest a x.isLt _ (by omega)).trans
          (hq.trans (state_congr_placeNest b _ _ (by omega)))
  · rintro ⟨r₁, r₂⟩
    refine ⟨⟨fun x hx ↦ r₁ x (by omega), fun x hx ↦ ?_⟩, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · exact (r₂ x (by omega)).trans (state_congr_placeNest b _ _ (by omega))
    · exact r₁ ⟨i + x, by omega⟩ (by dsimp only; omega)
    · exact (r₂ ⟨i + x, by omega⟩ (by dsimp only; omega)).trans
        (state_congr_placeNest b _ _ (by dsimp only; omega))
  · congr 1 <;> funext x <;> exact state_congr_placeNest _ _ _ (by omega)

end AJConjecture
