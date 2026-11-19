import Mathlib
import AJHandoff.TorusInput.RJNatClosure
import AJHandoff.TorusInput.RJNatGen
import AJConjecture.SkeinCableNatural
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinKnotTraceJwCols
import AJConjecture.SkeinThickCableBasic
import AJHandoff.TorusInput.RJProfileSlide

/-!
# The column projectors (node RA2.0)

`f_b^{⊗ (r+1)} = (f_b^{⊗ r} ⊗ 1_b) f^{(b(r+1))}_(br, b)`; it is an idempotent, natural, and
commutes with the cabled cyclic braid.

Route. `List.range_succ`, `List.prod_append`, `jwAt_eq_skPlace` and `skPlace_mul` for the first
statement. Projectors of different columns commute (`jwAt_commute_tlGenF`, transport
principle) and are idempotent (`jwAt_mul_self`). Naturality: `rjNat_mul`, `rjNat_jwAt`.
Commutation: `jwAt_mul_braidMatrix_cable` moves the projector of the column `p` to the column
`strandEnd w p`; `strandEnd` of the cyclic word permutes the columns `0, …, r - 1`, so the product
over all columns is unchanged (reorder the commuting factors). Estimate 100–150 lines.
-/

noncomputable section

namespace AJConjecture

/-- The offsets of the constant profile. -/
private theorem rj_profileOffset_const_cycleCols (b x : ℕ) :
    profileOffset (fun _ ↦ b) x = b * x := by
  rw [profileOffset, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- The column projectors are the profile projectors of the constant profile. -/
private theorem rj_colsProj_eq_profileProj_cycleCols (b r N : ℕ) :
    ((List.range r).map fun i ↦ jwAt N (b * i) b).prod = rjProfileProj N (fun _ ↦ b) r := by
  unfold rjProfileProj
  congr 1
  refine List.map_congr_left fun x _ ↦ ?_
  rw [rj_profileOffset_const_cycleCols]

/-- A braid word keeps the constant profile. -/
private theorem rj_profileEnd_const_cycleCols (b : ℕ) (w : BraidWord) :
    profileEnd (fun _ ↦ b) w = fun _ ↦ b := by
  induction w with
  | nil => rfl
  | cons g w ih => exact ih

/-- The column projectors of `r + 1` bundles. -/
theorem rjColsProj_succ (b r : ℕ) :
    rjColsProj b (r + 1) =
      skPlace (b * (r + 1)) (b * (r + 1)) 0 (rjColsProj b r) * jwAt (b * (r + 1)) (b * r) b := by
  rw [rjColsProj, rjColsProj, rj_colsProj_eq_profileProj_cycleCols,
    rj_colsProj_eq_profileProj_cycleCols, rj_profileProj_succ,
    rj_profileProj_eq_skPlace_zero (b * (r + 1)) (b * r) _ r
      (by rw [rj_profileOffset_const_cycleCols]) (Nat.mul_le_mul_left b (by omega)),
    rj_profileOffset_const_cycleCols]

/-- The column projectors form an idempotent. -/
theorem rjColsProj_mul_self (b r : ℕ) : rjColsProj b r * rjColsProj b r = rjColsProj b r := by
  rw [rjColsProj, rj_colsProj_eq_profileProj_cycleCols, rj_profileProj_mul_self]

/-- The column projectors are natural. -/
theorem rjNat_colsProj (b r : ℕ) : RJNat (rjColsProj b r) := by
  rw [rjColsProj]
  have h : ∀ l : List ℕ, (∀ i ∈ l, i < r) →
      RJNat ((l.map fun i ↦ jwAt (b * r) (b * i) b).prod) := by
    intro l hl
    induction l with
    | nil => exact rjNat_one _
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons]
      have hi : i < r := hl i List.mem_cons_self
      refine rjNat_mul (rjNat_jwAt _ _ _ ?_) (ih fun j hj ↦ hl j (List.mem_cons_of_mem _ hj))
      have := Nat.mul_le_mul_left b (show i + 1 ≤ r by omega)
      rw [Nat.mul_add_one] at this
      exact this
  exact h _ fun i hi ↦ List.mem_range.mp hi

/-- The cabled cyclic braid commutes with the column projectors. -/
theorem rjCycleMat_mul_colsProj (b r : ℕ) :
    rjCycleMat b r * rjColsProj b r = rjColsProj b r * rjCycleMat b r := by
  have hw : IsOnStrands r (rjCycleWord r) := fun g hg ↦ by
    simp only [rjCycleWord, List.mem_map, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    simp only
    omega
  have h := rj_profileProj_mul_braidMatrix (b * r) (fun _ ↦ b) r (rjCycleWord r) hw
    (by rw [rj_profileOffset_const_cycleCols])
  rw [rj_profileEnd_const_cycleCols, thickCable_const] at h
  rw [rjCycleMat, rjColsProj, rj_colsProj_eq_profileProj_cycleCols, h]

end AJConjecture
