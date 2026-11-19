import Mathlib
import AJConjecture.BraidStep

/-!
# The run of a braid word on a tuple of group elements

`braidRun m w f` reads the braid word `w` letter by letter, starting from the tuple `f` at the
bottom: its first component is the tuple of colours at the top, its second component the tuple
of conjugators collected on the way. The conjugating words of Artin's action, evaluated on
`f`, are exactly these conjugators, so that representations of the group of a closed braid can
be handled level by level, without writing Artin's words down.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- One letter acting on a tuple of colours together with the conjugators collected so far. -/
def braidRunStep (m : ℕ) (s : (Fin m → G) × (Fin m → G)) (g : ℕ × Bool) :
    (Fin m → G) × (Fin m → G) :=
  (braidStep m g s.1, fun k ↦ FreeGroup.lift s.1 (artinGen m g k).2 * s.2 (artinGen m g k).1)

/-- The run of a braid word on a tuple: the colours at the top and the conjugators. -/
def braidRun (m : ℕ) (w : BraidWord) (f : Fin m → G) : (Fin m → G) × (Fin m → G) :=
  w.foldl (braidRunStep m) (f, fun _ ↦ 1)

/-- The fold of `braidRunStep` over a braid word from an arbitrary start, in terms of Artin's
action of the word: the conjugators and the colours. -/
private theorem foldl_braidRunStep_apply (m : ℕ) (w : BraidWord)
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

/-- The conjugating words of Artin's action, evaluated on a tuple, are computed by the run. -/
theorem lift_artinWord_snd (m : ℕ) (w : BraidWord) (f : Fin m → G) (k : Fin m) :
    FreeGroup.lift f (artinWord m w k).2 = (braidRun m w f).2 k := by
  rw [braidRun, (foldl_braidRunStep_apply m w (f, fun _ ↦ 1) k).1, mul_one]

/-- The colours at the top are the conjugates of the colours at the bottom. -/
theorem braidRun_fst_apply (m : ℕ) (w : BraidWord) (f : Fin m → G) (k : Fin m) :
    (braidRun m w f).1 k =
      (braidRun m w f).2 k * f (artinWord m w k).1 * ((braidRun m w f).2 k)⁻¹ := by
  rw [← lift_artinWord_snd, braidRun, (foldl_braidRunStep_apply m w (f, fun _ ↦ 1) k).2]

end AJConjecture
