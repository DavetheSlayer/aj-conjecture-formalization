import Mathlib
import AJConjecture.SkeinPlace

/-!
# The normal form of a placement

Every state of `V^{⊗ (i + k + r)}` is `Fin.append (Fin.append a₁ a₂) a₃` for states `a₁`, `a₂`, `a₃`
of `i`, `k`, `r` factors (`Fin.appendEquiv`), and on such states the entry of `1_i ⊗ A ⊗ 1_r` is
the entry of `A` when the outer parts agree and `0` otherwise. All properties of
`AJConjecture.skPlace` (identity, functoriality, interchange, nesting, transposition) are proved
from this formula after writing the ambient sizes as `i + k + r` and `i + l + r`, which the
hypotheses of those statements allow (`obtain ⟨r, rfl⟩ : ∃ r, n = i + k + r`).
-/

namespace AJConjecture

/-- The entries of `1_i ⊗ A ⊗ 1_r` on states written as concatenations. -/
theorem skPlace_append_apply (i r : ℕ) {k l : ℕ} (A : SkMat k l) (a₁ b₁ : Fin i → Bool)
    (a₂ : Fin k → Bool) (b₂ : Fin l → Bool) (a₃ b₃ : Fin r → Bool) :
    skPlace (i + k + r) (i + l + r) i A (Fin.append (Fin.append a₁ a₂) a₃)
        (Fin.append (Fin.append b₁ b₂) b₃) =
      if a₁ = b₁ ∧ a₃ = b₃ then A a₂ b₂ else 0 := by
  have hcond : i + k ≤ i + k + r ∧ i + k + r + l = i + l + r + k := by omega
  have e2 : (fun x : Fin k ↦ Fin.append (Fin.append a₁ a₂) a₃ ⟨i + x, by omega⟩) = a₂ := by
    funext x
    have hx : (⟨i + x, by omega⟩ : Fin (i + k + r)) = Fin.castAdd r (Fin.natAdd i x) := by
      ext; simp
    rw [hx, Fin.append_left, Fin.append_right]
  have e2' : (fun y : Fin l ↦ Fin.append (Fin.append b₁ b₂) b₃ ⟨i + y, by omega⟩) = b₂ := by
    funext x
    have hx : (⟨i + x, by omega⟩ : Fin (i + l + r)) = Fin.castAdd r (Fin.natAdd i x) := by
      ext; simp
    rw [hx, Fin.append_left, Fin.append_right]
  have hiff : ((∀ x : Fin (i + k + r), (hx : (x : ℕ) < i) →
        Fin.append (Fin.append a₁ a₂) a₃ x = Fin.append (Fin.append b₁ b₂) b₃ ⟨x, by omega⟩) ∧
      (∀ x : Fin (i + k + r), (hx : i + k ≤ (x : ℕ)) →
        Fin.append (Fin.append a₁ a₂) a₃ x =
          Fin.append (Fin.append b₁ b₂) b₃ ⟨x + l - k, by omega⟩)) ↔ (a₁ = b₁ ∧ a₃ = b₃) := by
    constructor
    · rintro ⟨h1, h3⟩
      constructor
      · funext x
        have h := h1 (Fin.castAdd r (Fin.castAdd k x)) (by simp)
        rw [Fin.append_left, Fin.append_left] at h
        rw [h]
        have e : (⟨((Fin.castAdd r (Fin.castAdd k x) : Fin (i + k + r)) : ℕ), by simp; omega⟩ :
            Fin (i + l + r)) = Fin.castAdd r (Fin.castAdd l x) := by ext; simp
        rw [e, Fin.append_left, Fin.append_left]
      · funext x
        have h := h3 (Fin.natAdd (i + k) x) (by simp)
        rw [Fin.append_right] at h
        rw [h]
        have e : (⟨((Fin.natAdd (i + k) x : Fin (i + k + r)) : ℕ) + l - k, by simp; omega⟩ :
            Fin (i + l + r)) = Fin.natAdd (i + l) x := by ext; simp; omega
        rw [e, Fin.append_right]
    · rintro ⟨rfl, rfl⟩
      constructor
      · intro x hx
        have e : x = Fin.castAdd r (Fin.castAdd k ⟨x, hx⟩) := by ext; simp
        have e' : (⟨(x : ℕ), by omega⟩ : Fin (i + l + r)) =
            Fin.castAdd r (Fin.castAdd l ⟨x, hx⟩) := by ext; simp
        rw [e']
        conv_lhs => rw [e]
        rw [Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left]
      · intro x hx
        have e : x = Fin.natAdd (i + k) ⟨x - (i + k), by omega⟩ := by ext; simp; omega
        have e' : (⟨(x : ℕ) + l - k, by omega⟩ : Fin (i + l + r)) =
            Fin.natAdd (i + l) ⟨x - (i + k), by omega⟩ := by
          ext; simp; omega
        rw [e']
        conv_lhs => rw [e]
        rw [Fin.append_right, Fin.append_right]
  simp only [skPlace, Matrix.of_apply, hcond, and_self, ↓reduceDIte, e2, e2']
  exact if_congr hiff rfl rfl

end AJConjecture
