import Mathlib
import AJFamily.Volume.BlochWignerI
import AJFamily.Volume.WhiteheadComplete

/-!
# The volume of the Whitehead link complement

The unique positively oriented complete solution of the gluing equations is `(i, i, i, i)`
(`whiteheadGluing_complete_iff`), and its Bloch–Wigner sum is `4 D(i) = 4G`
(`blochWigner_I`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The complete hyperbolic structure: a unique positively oriented complete solution, of
volume `4G`. -/
theorem whitehead_volume :
    (∃! z : Fin 4 → ℂ, WhiteheadGluing z ∧ WhiteheadComplete z ∧ ∀ j, 0 < (z j).im) ∧
    (∀ z : Fin 4 → ℂ, WhiteheadGluing z → WhiteheadComplete z → (∀ j, 0 < (z j).im) →
        ∑ j, blochWigner (z j) = 4 * catalanConstant) := by
  have hI : WhiteheadGluing (fun _ ↦ Complex.I) ∧ WhiteheadComplete (fun _ ↦ Complex.I) :=
    (whiteheadGluing_complete_iff _).2 (Or.inl rfl)
  have hpos : ∀ z : Fin 4 → ℂ, WhiteheadGluing z → WhiteheadComplete z →
      (∀ j, 0 < (z j).im) → z = fun _ ↦ Complex.I := by
    intro z hg hc him
    rcases (whiteheadGluing_complete_iff z).1 ⟨hg, hc⟩ with h | h
    · exact h
    · have h0 := him 0
      rw [h] at h0
      norm_num at h0
  refine ⟨⟨fun _ ↦ Complex.I, ⟨hI.1, hI.2, fun _ ↦ by simp⟩, ?_⟩, ?_⟩
  · rintro z ⟨hg, hc, him⟩
    exact hpos z hg hc him
  · intro z hg hc him
    rw [hpos z hg hc him]
    simp [blochWigner_I]

end AJConjecture
