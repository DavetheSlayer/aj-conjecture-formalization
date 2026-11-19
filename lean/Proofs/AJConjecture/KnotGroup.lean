import Mathlib
import AJConjecture.ColoredJones

/-!
# The knot group of a closed braid and its peripheral pair

Artin's presentation: the group of the closure of a braid `β` on `m` strands is
`⟨x_0, …, x_{m-1} | x_k = β · x_k⟩` for Artin's action of the braid group on the free group.
The action sends each `x_k` to a conjugate `c_k x_{p(k)} c_k⁻¹`; the meridian is `x_0`, and the
preferred longitude is the product of the conjugating words met along the knot, corrected by
a power of the meridian.
-/

noncomputable section

namespace AJConjecture

/-- Artin's action of a braid generator on the free group: the generator `x_k` is sent to
`c * x_p * c⁻¹`, where `(p, c) = artinGen m g k`. For `σ_i`: `x_i ↦ x_i x_{i+1} x_i⁻¹`,
`x_{i+1} ↦ x_i`; for `σ_i⁻¹`: `x_i ↦ x_{i+1}`, `x_{i+1} ↦ x_{i+1}⁻¹ x_i x_{i+1}`. -/
def artinGen (m : ℕ) (g : ℕ × Bool) (k : Fin m) : Fin m × FreeGroup (Fin m) :=
  if h : g.1 + 1 < m then
    if (k : ℕ) = g.1 then (⟨g.1 + 1, h⟩, if g.2 then FreeGroup.of k else 1)
    else if (k : ℕ) = g.1 + 1 then (⟨g.1, by omega⟩, if g.2 then 1 else (FreeGroup.of k)⁻¹)
    else (k, 1)
  else (k, 1)

/-- The endomorphism of the free group given by a braid generator. -/
def artinHom (m : ℕ) (g : ℕ × Bool) : FreeGroup (Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift fun k ↦
    (artinGen m g k).2 * FreeGroup.of (artinGen m g k).1 * ((artinGen m g k).2)⁻¹

/-- Artin's action of a braid word: `x_k` is sent to `c * x_p * c⁻¹`, where
`(p, c) = artinWord m w k`; the word `g :: w` acts by the action of `w` followed by that of
`g`. -/
def artinWord (m : ℕ) : BraidWord → Fin m → Fin m × FreeGroup (Fin m)
  | [], k => (k, 1)
  | g :: w, k =>
    ((artinGen m g (artinWord m w k).1).1,
      artinHom m g (artinWord m w k).2 * (artinGen m g (artinWord m w k).1).2)

/-- The relators `x_k⁻¹ * (c_k * x_{p(k)} * c_k⁻¹)` of Artin's presentation of the group of the
closed braid. -/
def artinRels (K : BraidKnot) : Set (FreeGroup (Fin K.strands)) :=
  {r | ∃ k : Fin K.strands, r = (FreeGroup.of k)⁻¹ *
    ((artinWord K.strands K.word k).2 * FreeGroup.of (artinWord K.strands K.word k).1 *
      ((artinWord K.strands K.word k).2)⁻¹)}

/-- The knot group `π₁(S³ ∖ K)`, by Artin's presentation. -/
abbrev KnotGroup (K : BraidKnot) : Type := PresentedGroup (artinRels K)

/-- The meridian: the generator of the strand `0`. -/
def meridian (K : BraidKnot) : KnotGroup K :=
  PresentedGroup.of ⟨0, K.strands_pos⟩

/-- The preferred longitude: the product of the conjugating words met along the knot starting
from the strand `0`, corrected by the power of the meridian that makes its linking number with
the knot zero. -/
def longitude (K : BraidKnot) : KnotGroup K :=
  QuotientGroup.mk
    (((List.range K.strands).map fun j ↦
        (artinWord K.strands K.word
          ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod *
      (FreeGroup.of ⟨0, K.strands_pos⟩) ^ (-(writhe K.word)))

end AJConjecture
