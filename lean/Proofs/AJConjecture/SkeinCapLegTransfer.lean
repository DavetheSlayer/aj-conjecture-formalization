import Mathlib
import AJConjecture.SkeinCapSlideThin
import AJConjecture.SkeinCrossingRelations
import AJConjecture.SkeinThickCable

/-!
# A cap transfers a crossing from one leg to the other

A strand that crosses a bundle of `a` strands and is then capped with the strand on its right
is the same as that other strand crossing the bundle backwards (opposite sign) and being capped
at the starting position: `X(1, a)_{off} · cap_{off+a} = X(a, 1)^{-}_{off+1} · cap_{off}`. For one
crossing this is `σ_i^{±1} cap_{i+1} = σ_{i+1}^{∓1} cap_i`, a rewriting of
`AJConjecture.crossingF_mul_crossingF_mul_capAt_succ` with `AJConjecture.crossingF_mul_inv`; the
general case is an induction on `a`, peeling the last letter of the word and commuting the
remaining letters with the new inverse crossing (`AJConjecture.crossingF_commute`).
-/

namespace AJConjecture

/-- `ρ_m` of a word starting with a letter. -/
theorem braidMatrix_cons (n : ℕ) (g : ℕ × Bool) (w : BraidWord) :
    braidMatrix n (g :: w) = crossingF n g * braidMatrix n w := by
  rw [braidMatrix, List.map_cons, List.prod_cons]
  rfl

/-- A crossing before a cap moves to the other leg of the cap, with the opposite sign. -/
private theorem crossingF_mul_capAt_succ_capLegTransfer (n i : ℕ) (s : Bool) (h : i + 1 ≤ n) :
    crossingF (n + 2) (i, s) * capAt n (i + 1) = crossingF (n + 2) (i + 1, !s) * capAt n i := by
  have hinv : crossingF (n + 2) (i + 1, !s) * crossingF (n + 2) (i + 1, s) = 1 := by
    cases s
    · exact crossingF_mul_inv _ _
    · exact crossingF_inv_mul _ _
  have hc := crossingF_mul_crossingF_mul_capAt_succ n i s h
  calc crossingF (n + 2) (i, s) * capAt n (i + 1)
      = crossingF (n + 2) (i + 1, !s) * crossingF (n + 2) (i + 1, s) *
          (crossingF (n + 2) (i, s) * capAt n (i + 1)) := by rw [hinv, Matrix.one_mul]
    _ = crossingF (n + 2) (i + 1, !s) * capAt n i := by
        rw [← hc]
        simp only [Matrix.mul_assoc]

/-- A word on the left of a letter commutes with it. -/
private theorem braidMatrix_commute_crossingF_capLegTransfer (n : ℕ) (g : ℕ × Bool)
    (v : BraidWord) (h : ∀ g' ∈ v, g'.1 + 1 < g.1) :
    Commute (braidMatrix n v) (crossingF n g) := by
  induction v with
  | nil =>
    rw [braidMatrix_nil]
    exact Commute.one_left _
  | cons g' v ih =>
    rw [braidMatrix_cons]
    exact (crossingF_commute n g'.1 g.1 g'.2 g.2 (h g' List.mem_cons_self)).mul_left
      (ih fun g'' hg'' ↦ h g'' (List.mem_cons_of_mem _ hg''))

/-- The leg transfer for the explicit words. -/
private theorem braidMatrix_range_mul_capAt_capLegTransfer (n off : ℕ) (s : Bool) (a : ℕ)
    (h : off + a ≤ n) :
    braidMatrix (n + 2) ((List.range a).map fun x ↦ (off + x, s)) * capAt n (off + a) =
      braidMatrix (n + 2) ((List.range a).reverse.map fun x ↦ (off + 1 + x, !s)) *
        capAt n off := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have hcomm : Commute (braidMatrix (n + 2) ((List.range a).map fun x ↦ (off + x, s)))
        (crossingF (n + 2) (off + a + 1, !s)) := by
      apply braidMatrix_commute_crossingF_capLegTransfer
      intro g' hg'
      simp only [List.mem_map, List.mem_range] at hg'
      obtain ⟨x, hx, rfl⟩ := hg'
      dsimp only
      omega
    rw [List.range_succ, List.map_append, List.reverse_append, List.map_append,
      List.reverse_singleton, List.map_singleton, List.map_singleton, braidMatrix_append,
      List.singleton_append, braidMatrix_cons, braidMatrix_cons,
      braidMatrix_nil, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc,
      ← add_assoc off a 1, crossingF_mul_capAt_succ_capLegTransfer n (off + a) s (by omega),
      ← Matrix.mul_assoc, hcomm.eq, Matrix.mul_assoc, ih (by omega), add_right_comm off 1 a]

/-- A crossing of a strand with a bundle before a cap moves to the other leg of the cap. -/
theorem braidMatrix_thickCross_mul_capAt_leg (n a off : ℕ) (s : Bool) (h : off + a ≤ n) :
    braidMatrix (n + 2) (thickCross 1 a off s) * capAt n (off + a) =
      braidMatrix (n + 2) (thickCross a 1 (off + 1) (!s)) * capAt n off := by
  have key := braidMatrix_range_mul_capAt_capLegTransfer n off s a h
  cases s
  · have h1 : thickCross 1 a off false = (List.range a).map fun x ↦ (off + x, false) := by
      simp [thickCross, thickGen, List.map_eq_flatMap]
    have h2 : thickCross a 1 (off + 1) (!false) =
        (List.range a).reverse.map fun x ↦ (off + 1 + x, !false) := by
      simp [thickCross, thickGen, List.map_eq_flatMap]
    rw [h1, h2]
    exact key
  · have h1 : thickCross 1 a off true = (List.range a).map fun x ↦ (off + x, true) := by
      simp [thickCross, thickGen]
    have h2 : thickCross a 1 (off + 1) (!true) =
        (List.range a).reverse.map fun x ↦ (off + 1 + x, !true) := by
      simp [thickCross, thickGen]
    rw [h1, h2]
    exact key

end AJConjecture
