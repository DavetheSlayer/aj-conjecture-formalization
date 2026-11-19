import Mathlib
import AJConjecture.BraidRun

/-!
# The run of a concatenated braid word

The run of `u ++ v` on a tuple of colours is the run of `v` on the colours produced by `u`, with
the conjugators of `u` (read at the strands where `v` sends each strand) appended.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The fold of `braidRunStep` from an arbitrary start, in terms of Artin's action of the
word. -/
theorem foldl_braidRunStep_apply {G : Type*} [Group G] (m : ℕ) (w : BraidWord)
    (s : (Fin m → G) × (Fin m → G)) (k : Fin m) :
    (w.foldl (braidRunStep m) s).2 k =
        FreeGroup.lift s.1 (artinWord m w k).2 * s.2 (artinWord m w k).1 ∧
      (w.foldl (braidRunStep m) s).1 k =
        FreeGroup.lift s.1 (artinWord m w k).2 * s.1 (artinWord m w k).1 *
          (FreeGroup.lift s.1 (artinWord m w k).2)⁻¹ := by
  induction w generalizing s with
  | nil => simp [artinWord]
  | cons g w ih =>
    have h (x : FreeGroup (Fin m)) :
        FreeGroup.lift (braidStep m g s.1) x = FreeGroup.lift s.1 (artinHom m g x) :=
      (DFunLike.congr_fun (lift_comp_artinHom m g s.1) x).symm
    obtain ⟨h2, h1⟩ := ih (braidRunStep m s g)
    rw [List.foldl_cons, h2, h1]
    simp only [braidRunStep, h, artinWord, map_mul, mul_inv_rev, braidStep, mul_assoc,
      and_self]

theorem braidRun_append {G : Type*} [Group G] (m : ℕ) (u v : BraidWord) (f : Fin m → G) :
    braidRun m (u ++ v) f =
      ((braidRun m v (braidRun m u f).1).1, fun i ↦
        (braidRun m v (braidRun m u f).1).2 i * (braidRun m u f).2 (artinWord m v i).1) := by
  have key : ∀ s : (Fin m → G) × (Fin m → G),
      v.foldl (braidRunStep m) s = ((braidRun m v s.1).1, fun i ↦
        (braidRun m v s.1).2 i * s.2 (artinWord m v i).1) := by
    intro s
    ext i
    · rw [(foldl_braidRunStep_apply m v s i).2, braidRun,
        (foldl_braidRunStep_apply m v (s.1, fun _ ↦ 1) i).2]
    · dsimp only
      rw [(foldl_braidRunStep_apply m v s i).1, braidRun,
        (foldl_braidRunStep_apply m v (s.1, fun _ ↦ 1) i).1, mul_one]
  rw [braidRun, List.foldl_append]
  exact key _

end AJConjecture
