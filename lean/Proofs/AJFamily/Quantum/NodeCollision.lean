import Mathlib
import AJConjecture.QAlgWeylSymbol

/-!
# Collision-free nodes

The hypothesis `NodeCollisionFree` on the fibre `M = m₀`: `G` and `D` meet only at `l₀`, and `T`
has only simple zeros, shared with neither.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- At the fibre `M = m₀`: the only common zero of `G` and `D` is `l₀`, and every zero of `T` is
a simple zero at which neither `G` nor `D` vanishes. -/
def NodeCollisionFree (G D T : ℤ[X][X]) (m₀ l₀ : ℂ) : Prop :=
  (∀ l : ℂ, evalIntPoint G m₀ l = 0 → evalIntPoint D m₀ l = 0 → l = l₀) ∧
    ∀ l : ℂ, evalIntPoint T m₀ l = 0 →
      evalIntPoint G m₀ l ≠ 0 ∧ evalIntPoint D m₀ l ≠ 0 ∧ evalIntPoint (derivative T) m₀ l ≠ 0

/-- The collision hypothesis is symmetric in `G` and `D`. -/
theorem NodeCollisionFree.symm {G D T : ℤ[X][X]} {m₀ l₀ : ℂ} (h : NodeCollisionFree G D T m₀ l₀) :
    NodeCollisionFree D G T m₀ l₀ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun l hD hG ↦ h1 l hG hD, fun l hT ↦ ?_⟩
  obtain ⟨hG, hD, hT'⟩ := h2 l hT
  exact ⟨hD, hG, hT'⟩

end AJConjecture
