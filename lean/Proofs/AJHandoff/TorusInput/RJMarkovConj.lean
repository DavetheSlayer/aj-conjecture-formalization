import Mathlib
import AJHandoff.TorusInput.RJProfileSlide
import AJConjecture.SkeinTraceCyclic
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinProfileBasic

/-!
# Coloured closures: locality and conjugation invariance (node RA5.ii.2)

`rjColorTrace κ n w` depends only on the thicknesses of the columns `< n`; and it is invariant
under conjugation: `⟨u v⟩_κ = ⟨v u⟩_(κ_u)`, `κ_u` the profile at the top of `u`, when the closure
matches the profile.

Route. Locality: `thickCable_congr`, `profileOffset` only sums the columns `< n`, and
`rjProfileProj` only uses them. Conjugation: `rj_thickCable_append`, `braidMatrix_append`,
cyclicity `qtr_mul_comm_of_weight` (braids and projectors intertwine the weights:
`skWeight_mul_braidMatrix`, `skWeight_mul_jwAt`), the sliding
`rj_profileProj_mul_braidMatrix`, `thickCable_congr` for the cable of `u` at the profile
`profileEnd κ (u ++ v)`, and `rj_profileOffset_profileEnd` to identify the sizes. Estimate
80–130 lines.
-/

noncomputable section

namespace AJConjecture

/-- The offsets up to `n` depend only on the columns `< n`. -/
private theorem rj_profileOffset_congr_markovConj (κ κ' : ℕ → ℕ) (n : ℕ)
    (h : ∀ x < n, κ x = κ' x) {x : ℕ} (hx : x ≤ n) : profileOffset κ x = profileOffset κ' x :=
  Finset.sum_congr rfl fun y hy ↦ h y (by rw [Finset.mem_range] at hy; omega)

/-- The profile projectors depend only on the columns `< n`. -/
private theorem rj_profileProj_congr_markovConj (N : ℕ) (κ κ' : ℕ → ℕ) (n : ℕ)
    (h : ∀ x < n, κ x = κ' x) : rjProfileProj N κ n = rjProfileProj N κ' n := by
  unfold rjProfileProj
  congr 1
  refine List.map_congr_left fun x hx ↦ ?_
  rw [List.mem_range] at hx
  rw [rj_profileOffset_congr_markovConj κ κ' n h hx.le, h x hx]

/-- The coloured closure depends only on the columns `< n`. -/
theorem rj_colorTrace_congr (κ κ' : ℕ → ℕ) (n : ℕ) (w : BraidWord) (hw : IsOnStrands n w)
    (h : ∀ x < n, κ x = κ' x) : rjColorTrace κ n w = rjColorTrace κ' n w := by
  unfold rjColorTrace
  rw [rj_profileOffset_congr_markovConj κ κ' n h le_rfl, thickCable_congr n κ κ' w hw h,
    rj_profileProj_congr_markovConj _ κ κ' n h]

set_option linter.unusedVariables false in
/-- Conjugation invariance of the coloured closure. -/
theorem rj_colorTrace_append_comm (κ : ℕ → ℕ) (n : ℕ) (u v : BraidWord) (hu : IsOnStrands n u)
    (hv : IsOnStrands n v) (hc : ∀ x < n, profileEnd κ (u ++ v) x = κ x) :
    rjColorTrace κ n (u ++ v) = rjColorTrace (profileEnd κ u) n (v ++ u) := by
  unfold rjColorTrace
  have hO : profileOffset (profileEnd κ u) n = profileOffset κ n :=
    rj_profileOffset_profileEnd κ n u hu
  have hcu : thickCable (profileEnd (profileEnd κ u) v) u = thickCable κ u := by
    rw [← rj_profileEnd_append]
    exact thickCable_congr n _ _ u hu hc
  rw [hO, rj_thickCable_append, rj_thickCable_append, hcu, braidMatrix_append,
    braidMatrix_append, Matrix.mul_assoc,
    qtr_mul_comm_of_weight _ _ _ _ (skWeight_mul_braidMatrix _ _), Matrix.mul_assoc,
    rj_profileProj_mul_braidMatrix _ κ n u hu le_rfl, Matrix.mul_assoc]

end AJConjecture
