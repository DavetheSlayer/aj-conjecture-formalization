import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinThickCableBasic
import AJConjecture.SkeinThickGenInv

/-!
# The cabled cyclic braid is one thick crossing (node RA3.1)

`cable_b(σ_0 ⋯ σ_(r-1))` on `r + 1` bundles has the matrix of the thick crossing
`X_(b, b r)(0)` of the first bundle with the other `r` bundles.

Route. `σ_0 ⋯ σ_(r-1) = thickCross 1 r 0 true` as words; the cable of each letter is
`thickCross b b (b i) true` (`cableGen_eq_thickCross`); induction on `r` with
`braidMatrix_thickGen_add_right` (`Γ_(a, b₁ + b₂)(o) = Γ_(a,b₁)(o) Γ_(a,b₂)(o + b₁)`) and
`braidMatrix_append`. For `r = 0` both sides are `1`. Estimate 50–90 lines.
-/

noncomputable section

namespace AJConjecture

/-- The cabled cyclic braid on `r + 1` bundles is the crossing of the first bundle with the
remaining `b r` strands. -/
theorem rjCycleMat_succ (b r : ℕ) :
    rjCycleMat b (r + 1) = braidMatrix (b * (r + 1)) (thickCross b (b * r) 0 true) := by
  rw [rjCycleMat, rjCycleWord, Nat.add_sub_cancel]
  generalize b * (r + 1) = n
  induction r with
  | zero =>
    simp only [List.range_zero, List.map_nil, cable, List.flatMap_nil, mul_zero, thickCross,
      thickGen, ite_true, List.range_zero, List.map_nil]
    rw [List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl]
  | succ r ih =>
    have h1 : cable b (List.map (fun i ↦ (i, true)) (List.range (r + 1))) =
        cable b (List.map (fun i ↦ (i, true)) (List.range r)) ++ thickGen b b (b * r) true := by
      simp only [List.range_succ, List.map_append, cable, List.flatMap_append, List.map_cons,
        List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        cableGen_eq_thickCross, thickCross, ite_true]
    rw [h1, braidMatrix_append, ih, mul_add, mul_one]
    simp only [thickCross, ite_true]
    rw [braidMatrix_thickGen_add_right, zero_add]

end AJConjecture
