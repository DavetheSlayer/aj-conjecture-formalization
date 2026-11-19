import Mathlib
import AJConjecture.SkeinCapAtComm
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinPlaceBasic
import AJConjecture.SkeinPlaceNest
import AJConjecture.SkeinTlGenPlace

/-!
# The matrix of a shifted braid word is a placement

For a word `w` on `n` strands, the matrix on `n'` strands of the word shifted by `d` positions is
`1_d ⊗ ρ_n(w) ⊗ 1`. Induction on the word: the placement is additive, multiplicative and sends
`1` to `1`, and `e_{d+i} = 1_d ⊗ e_i ⊗ 1` by `AJConjecture.tlGenF_eq_skPlace` and
`AJConjecture.skPlace_skPlace`.
-/

namespace AJConjecture

/-- The generator `e_{d+i}` on `n'` strands is the placement at `d` of `e_i` on `n` strands. -/
private theorem tlGenF_add_eq_skPlace_braidMatrixPlace (n n' d i : ℕ) (hi : i + 1 < n)
    (h : d + n ≤ n') : tlGenF n' (i + d) = skPlace n' n' d (tlGenF n i) := by
  rw [tlGenF_eq_skPlace n' (i + d), tlGenF_eq_skPlace n i,
    skPlace_skPlace n' n' d i (tlGenF 2 0) (by omega) rfl h rfl, Nat.add_comm i d]

/-- The crossing `σ_{d+i}^{±1}` on `n'` strands is the placement at `d` of `σ_i^{±1}` on `n`
strands. -/
private theorem crossingF_add_eq_skPlace_braidMatrixPlace (n n' d : ℕ) (g : ℕ × Bool)
    (hi : g.1 + 1 < n) (h : d + n ≤ n') :
    crossingF n' (g.1 + d, g.2) = skPlace n' n' d (crossingF n g) := by
  obtain ⟨i, s⟩ := g
  cases s
  · rw [crossingF_neg, crossingF_neg, skPlace_add, skPlace_smul, skPlace_smul,
      skPlace_one n' d n h, tlGenF_add_eq_skPlace_braidMatrixPlace n n' d i hi h]
  · rw [crossingF_pos, crossingF_pos, skPlace_add, skPlace_smul, skPlace_smul,
      skPlace_one n' d n h, tlGenF_add_eq_skPlace_braidMatrixPlace n n' d i hi h]

/-- The matrix of a braid word with a first letter. -/
private theorem braidMatrix_cons_braidMatrixPlace (m : ℕ) (g : ℕ × Bool) (w : BraidWord) :
    braidMatrix m (g :: w) = crossingF m g * braidMatrix m w := by
  rw [braidMatrix, braidMatrix, List.map_cons, List.prod_cons]

/-- The matrix of a shifted braid word is the placement of the matrix of the word. -/
theorem braidMatrix_map_add_eq_skPlace (n n' d : ℕ) (w : BraidWord) (hw : IsOnStrands n w)
    (h : d + n ≤ n') :
    braidMatrix n' (w.map fun g ↦ (g.1 + d, g.2)) = skPlace n' n' d (braidMatrix n w) := by
  induction w with
  | nil => rw [List.map_nil, braidMatrix_nil, braidMatrix_nil, skPlace_one n' d n h]
  | cons g w ih =>
    have hg : g.1 + 1 < n := hw g List.mem_cons_self
    have hw' : IsOnStrands n w := fun x hx ↦ hw x (List.mem_cons_of_mem g hx)
    rw [List.map_cons, braidMatrix_cons_braidMatrixPlace, braidMatrix_cons_braidMatrixPlace,
      ih hw', crossingF_add_eq_skPlace_braidMatrixPlace n n' d g hg h,
      skPlace_mul n' n' n' d (crossingF n g) (braidMatrix n w) h rfl rfl]

end AJConjecture
