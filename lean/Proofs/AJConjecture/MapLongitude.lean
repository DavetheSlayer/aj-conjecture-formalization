import Mathlib
import AJConjecture.BraidRunOfHom
import AJConjecture.BraidRun

/-!
# The image of the longitude under a representation

The image of the preferred longitude is the product of the conjugators of the run met along
the knot, starting from the strand `0`, corrected by the power of the image of the meridian
given by the writhe.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The image of the longitude, in terms of the run of the braid word on the images of the
generators. -/
theorem map_longitude (K : BraidKnot) (ρ : KnotGroup K →* G) :
    ρ (longitude K) =
      ((List.range K.strands).map fun j ↦
          (braidRun K.strands K.word fun k ↦ ρ (PresentedGroup.of k)).2
            ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩)).prod *
        ρ (meridian K) ^ (-(writhe K.word)) := by
  have h : ρ (longitude K) = FreeGroup.lift (fun k ↦ ρ (PresentedGroup.of k))
      (((List.range K.strands).map fun j ↦
          (artinWord K.strands K.word
            ((fun k ↦ (artinWord K.strands K.word k).1)^[j] ⟨0, K.strands_pos⟩)).2).prod *
        (FreeGroup.of ⟨0, K.strands_pos⟩) ^ (-(writhe K.word))) :=
    map_presentedGroup_mk_eq_lift_of_braidRun ρ _
  rw [h, map_mul, map_list_prod, List.map_map, map_zpow, FreeGroup.lift_apply_of]
  simp only [Function.comp_def, lift_artinWord_snd, meridian]

end AJConjecture
