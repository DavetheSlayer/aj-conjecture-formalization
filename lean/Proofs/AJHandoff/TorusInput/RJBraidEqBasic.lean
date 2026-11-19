import Mathlib
import AJHandoff.TorusInput.RJProfileSlide

/-!
# Braid words equal for every profile: congruence (node RA5.ii.3)

`RJBraidEq n` is an equivalence, compatible with concatenation, and equal words have equal
coloured closures.

Route. Concatenation: `rj_thickCable_append`, `braidMatrix_append`, `rj_profileEnd_append`; the
profile at the top of `u` has the same total thickness on the columns `< n`
(`rj_profileOffset_profileEnd`), so the hypothesis on `v` applies at it. Closures: unfold
`rjColorTrace` (same profile, same size). Estimate 70–110 lines.
-/

noncomputable section

namespace AJConjecture

/-- `RJBraidEq` is reflexive on words on `n` strands. -/
theorem rj_braidEq_refl (n : ℕ) (w : BraidWord) (hw : IsOnStrands n w) : RJBraidEq n w w :=
  ⟨hw, hw, fun _ _ _ ↦ ⟨rfl, rfl⟩⟩

/-- `RJBraidEq` is symmetric. -/
theorem rj_braidEq_symm {n : ℕ} {w w' : BraidWord} (h : RJBraidEq n w w') : RJBraidEq n w' w :=
  ⟨h.2.1, h.1, fun κ N hN ↦ ⟨(h.2.2 κ N hN).1.symm, (h.2.2 κ N hN).2.symm⟩⟩

/-- `RJBraidEq` is transitive. -/
theorem rj_braidEq_trans {n : ℕ} {w w' w'' : BraidWord} (h : RJBraidEq n w w')
    (h' : RJBraidEq n w' w'') : RJBraidEq n w w'' :=
  ⟨h.1, h'.2.1, fun κ N hN ↦
    ⟨(h.2.2 κ N hN).1.trans (h'.2.2 κ N hN).1, (h.2.2 κ N hN).2.trans (h'.2.2 κ N hN).2⟩⟩

/-- A concatenation of words on `n` strands is on `n` strands. -/
private theorem rj_isOnStrands_append_braidEqBasic {n : ℕ} {u v : BraidWord}
    (hu : IsOnStrands n u) (hv : IsOnStrands n v) : IsOnStrands n (u ++ v) := fun g hg ↦ by
  rcases List.mem_append.mp hg with hg | hg
  · exact hu g hg
  · exact hv g hg

/-- `RJBraidEq` is compatible with concatenation. -/
theorem rj_braidEq_append {n : ℕ} {u u' v v' : BraidWord} (hu : RJBraidEq n u u')
    (hv : RJBraidEq n v v') : RJBraidEq n (u ++ v) (u' ++ v') := by
  refine ⟨rj_isOnStrands_append_braidEqBasic hu.1 hv.1,
    rj_isOnStrands_append_braidEqBasic hu.2.1 hv.2.1, fun κ N hN ↦ ?_⟩
  obtain ⟨hm, he⟩ := hu.2.2 κ N hN
  have hN' : profileOffset (profileEnd κ u) n ≤ N := by
    rw [rj_profileOffset_profileEnd κ n u hu.1]
    exact hN
  obtain ⟨hm', he'⟩ := hv.2.2 (profileEnd κ u) N hN'
  refine ⟨?_, ?_⟩
  · rw [rj_thickCable_append, rj_thickCable_append, braidMatrix_append, braidMatrix_append, hm,
      hm', he]
  · rw [rj_profileEnd_append, rj_profileEnd_append, he', he]

/-- Words equal for every profile have equal coloured closures. -/
theorem rj_colorTrace_of_braidEq (κ : ℕ → ℕ) {n : ℕ} {w w' : BraidWord} (h : RJBraidEq n w w') :
    rjColorTrace κ n w = rjColorTrace κ n w' := by
  unfold rjColorTrace
  rw [(h.2.2 κ (profileOffset κ n) le_rfl).1]

end AJConjecture
