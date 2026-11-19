import Mathlib
import AJConjecture.KnotGroup

/-!
# One braid letter acting on a tuple of group elements

A homomorphism from the free group on `m` generators to a group `G` is a tuple `f : Fin m → G`.
Artin's automorphism of one braid letter acts on such tuples by `braidStep`, which is the
crossing rule of a Wirtinger colouring: for `σ_i` the new tuple has `f_i f_{i+1} f_i⁻¹` at
position `i` and `f_i` at position `i + 1`; for `σ_i⁻¹` it has `f_{i+1}` at position `i` and
`f_{i+1}⁻¹ f_i f_{i+1}` at position `i + 1`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- One letter acting on a tuple of group elements: the new entry at position `k` is
`γ * f p * γ⁻¹`, where `(p, c) = artinGen m g k` and `γ` is the value of the word `c` on `f`. -/
def braidStep (m : ℕ) (g : ℕ × Bool) (f : Fin m → G) : Fin m → G := fun k ↦
  FreeGroup.lift f (artinGen m g k).2 * f (artinGen m g k).1 *
    (FreeGroup.lift f (artinGen m g k).2)⁻¹

/-- Evaluating a tuple after Artin's automorphism of one letter is the same as evaluating the
stepped tuple. -/
theorem lift_comp_artinHom (m : ℕ) (g : ℕ × Bool) (f : Fin m → G) :
    (FreeGroup.lift f).comp (artinHom m g) = FreeGroup.lift (braidStep m g f) := by
  ext k
  simp [artinHom, braidStep]

end AJConjecture
