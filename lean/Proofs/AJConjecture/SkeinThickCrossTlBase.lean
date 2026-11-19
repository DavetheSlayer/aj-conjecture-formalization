import Mathlib
import AJConjecture.SkeinCapLegTransfer
import AJConjecture.SkeinCrossingTl
import AJConjecture.SkeinThickCableBasic

/-!
# A generator slides through the crossing of a bundle with a single strand

`thickGen a 1 off true` is the word `σ_{off+a-1} ⋯ σ_{off}` (a bundle of `a` strands crosses the
strand on its right) and `thickGen 1 b off true` is `σ_{off} ⋯ σ_{off+b-1}` (a strand crosses the
bundle of `b` strands on its right). A generator `e_{off+j}` on the bundle commutes with the
letters that do not touch its two strands (`AJConjecture.crossingF_commute` with
`σ = t + t⁻¹ e`), and slides through the two letters that do by
`AJConjecture.tlGenF_mul_crossingF_mul_crossingF`; split the word with
`AJConjecture.thickGen_add_left` at the strands `j`, `j + 1`.
-/

namespace AJConjecture

/-- A generator commutes with a crossing on a disjoint pair of strands. -/
private theorem tlGenF_commute_crossingF_thickCrossTlBase (n i k : ℕ) (s : Bool)
    (h : i + 1 < k ∨ k + 1 < i) : Commute (tlGenF n i) (crossingF n (k, s)) := by
  have hc : Commute (tlGenF n i) (tlGenF n k) := by
    rcases h with h | h
    · exact tlGenF_commute n i k h
    · exact (tlGenF_commute n k i h).symm
  cases s
  · rw [crossingF_neg]
    exact ((Commute.one_right _).smul_right _).add_right (hc.smul_right _)
  · rw [crossingF_pos]
    exact ((Commute.one_right _).smul_right _).add_right (hc.smul_right _)

/-- A generator commutes with a word none of whose letters touches its two strands. -/
private theorem tlGenF_commute_braidMatrix_thickCrossTlBase (n i : ℕ) (w : BraidWord)
    (h : ∀ g ∈ w, i + 1 < g.1 ∨ g.1 + 1 < i) : Commute (tlGenF n i) (braidMatrix n w) := by
  induction w with
  | nil =>
    rw [braidMatrix_nil]
    exact Commute.one_right _
  | cons g w ih =>
    rw [braidMatrix_cons]
    exact (tlGenF_commute_crossingF_thickCrossTlBase n i g.1 g.2 (h g List.mem_cons_self)).mul_right
      (ih fun g' hg' ↦ h g' (List.mem_cons_of_mem _ hg'))

/-- The letters of a thick crossing lie in the window of its two bundles. -/
theorem mem_thickGen_true {a b off : ℕ} {g : ℕ × Bool}
    (hg : g ∈ thickGen a b off true) : off ≤ g.1 ∧ g.1 + 2 ≤ off + a + b := by
  simp only [thickGen, ite_true, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  exact ⟨by omega, by omega⟩

/-- The crossing of one strand with a bundle splits along the bundle as a word. -/
theorem thickGen_one_add (b₁ b₂ off : ℕ) :
    thickGen 1 (b₁ + b₂) off true = thickGen 1 b₁ off true ++ thickGen 1 b₂ (off + b₁) true := by
  simp only [thickGen, ite_true, List.range_one, List.reverse_singleton, List.flatMap_singleton,
    List.range_add, List.map_append, List.map_map, Function.comp_def, zero_add, add_assoc]

/-- An element that commutes with the first factor, slides through the second and commutes with
the third slides through the product. -/
private theorem mul_slide_three_thickCrossTlBase {M : Type*} [Monoid M] {e e' u s v : M}
    (h1 : Commute e u) (hs : e * s = s * e') (h2 : Commute e' v) :
    e * (u * (s * v)) = u * (s * v) * e' := by
  calc e * (u * (s * v)) = u * (e * s) * v := by
        rw [← mul_assoc, h1.eq]
        simp only [mul_assoc]
    _ = u * (s * v) * e' := by
        rw [hs]
        simp only [mul_assoc]
        rw [h2.eq]

/-- A generator on a bundle slides through its crossing with the strand on its right. -/
theorem tlGenF_mul_braidMatrix_thickGen_right_one (n a off j : ℕ) (hn : off + a + 1 ≤ n)
    (hj : j + 1 < a) :
    tlGenF n (off + j) * braidMatrix n (thickGen a 1 off true) =
      braidMatrix n (thickGen a 1 off true) * tlGenF n (off + 1 + j) := by
  obtain ⟨r, rfl⟩ : ∃ r, a = j + 2 + r := ⟨a - (j + 2), by omega⟩
  have h2 : braidMatrix n (thickGen 2 1 (off + j) true) =
      crossingF n (off + j + 1, true) * crossingF n (off + j, true) := by
    rw [show thickGen 2 1 (off + j) true = [(off + j + 1, true), (off + j, true)] from rfl,
      braidMatrix_cons, braidMatrix_cons, braidMatrix_nil,
      Matrix.mul_one]
  have hc1 : Commute (tlGenF n (off + j)) (braidMatrix n (thickGen r 1 (off + (j + 2)) true)) :=
    tlGenF_commute_braidMatrix_thickCrossTlBase n _ _ fun g hg ↦ Or.inl <| by
      have := mem_thickGen_true hg
      omega
  have hc2 : Commute (tlGenF n (off + j + 1)) (braidMatrix n (thickGen j 1 off true)) :=
    tlGenF_commute_braidMatrix_thickCrossTlBase n _ _ fun g hg ↦ Or.inr <| by
      have := mem_thickGen_true hg
      omega
  have hs := tlGenF_mul_crossingF_mul_crossingF n (off + j) true (by omega)
  rw [thickGen_add_left (j + 2) r 1 off, thickGen_add_left j 2 1 off, braidMatrix_append,
    braidMatrix_append, h2, add_right_comm off 1 j]
  exact mul_slide_three_thickCrossTlBase hc1 hs hc2

/-- A generator on a bundle slides through its crossing with the strand on its left. -/
theorem tlGenF_mul_braidMatrix_thickGen_left_one (n b off j : ℕ) (hn : off + 1 + b ≤ n)
    (hj : j + 1 < b) :
    tlGenF n (off + 1 + j) * braidMatrix n (thickGen 1 b off true) =
      braidMatrix n (thickGen 1 b off true) * tlGenF n (off + j) := by
  obtain ⟨r, rfl⟩ : ∃ r, b = j + 2 + r := ⟨b - (j + 2), by omega⟩
  have h2 : braidMatrix n (thickGen 1 2 (off + j) true) =
      crossingF n (off + j, true) * crossingF n (off + j + 1, true) := by
    rw [show thickGen 1 2 (off + j) true = [(off + j, true), (off + j + 1, true)] from rfl,
      braidMatrix_cons, braidMatrix_cons, braidMatrix_nil,
      Matrix.mul_one]
  have hc1 : Commute (tlGenF n (off + j + 1)) (braidMatrix n (thickGen 1 j off true)) :=
    tlGenF_commute_braidMatrix_thickCrossTlBase n _ _ fun g hg ↦ Or.inr <| by
      have := mem_thickGen_true hg
      omega
  have hc2 : Commute (tlGenF n (off + j)) (braidMatrix n (thickGen 1 r (off + (j + 2)) true)) :=
    tlGenF_commute_braidMatrix_thickCrossTlBase n _ _ fun g hg ↦ Or.inl <| by
      have := mem_thickGen_true hg
      omega
  have hs := tlGenF_succ_mul_crossingF_mul_crossingF n (off + j) true (by omega)
  rw [thickGen_one_add (j + 2) r off, thickGen_one_add j 2 off,
    braidMatrix_append, braidMatrix_append, h2, add_right_comm off 1 j, Matrix.mul_assoc]
  exact mul_slide_three_thickCrossTlBase hc1 hs hc2

end AJConjecture
