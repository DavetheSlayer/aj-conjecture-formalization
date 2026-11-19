import Mathlib
import AJConjecture.BraidRun

/-!
# A representation of a closed-braid group is a tuple fixed by the braid
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- A homomorphism from a presented group, composed with the quotient map from the free group,
is the lift of the tuple of the images of the generators. -/
theorem map_presentedGroup_mk_eq_lift_of_braidRun {α : Type*}
    {rels : Set (FreeGroup α)} (ρ : PresentedGroup rels →* G) (x : FreeGroup α) :
    ρ (PresentedGroup.mk rels x) = FreeGroup.lift (fun k ↦ ρ (PresentedGroup.of k)) x := by
  have h : ρ.comp (PresentedGroup.mk rels) =
      FreeGroup.lift (fun k ↦ ρ (PresentedGroup.of k)) := by
    ext k
    simp [PresentedGroup.of]
  exact DFunLike.congr_fun h x

/-- For a homomorphism `ρ` from the group of a closed braid, the tuple of the images of the
generators is fixed by the run of the braid word. -/
theorem braidRun_fst_of_hom (K : BraidKnot) (ρ : KnotGroup K →* G) :
    (braidRun K.strands K.word fun k ↦ ρ (PresentedGroup.of k)).1 =
      fun k ↦ ρ (PresentedGroup.of k) := by
  funext k
  have hmem : (FreeGroup.of k)⁻¹ *
      ((artinWord K.strands K.word k).2 * FreeGroup.of (artinWord K.strands K.word k).1 *
        ((artinWord K.strands K.word k).2)⁻¹) ∈ artinRels K := ⟨k, rfl⟩
  have h := congrArg ρ (PresentedGroup.one_of_mem hmem)
  rw [map_presentedGroup_mk_eq_lift_of_braidRun, map_one, map_mul, map_inv,
    inv_mul_eq_one] at h
  rw [braidRun_fst_apply, ← lift_artinWord_snd]
  simpa using h.symm

end AJConjecture
