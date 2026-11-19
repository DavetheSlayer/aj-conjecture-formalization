import Mathlib
import AJConjecture.SkeinTurnbackRecursion

/-!
# The polynomial relation of `D_1`

`(f ⊗ f) ∏_{m=0}^{c} (D_1 - d_{1,m}) = 0`. By the recursion `D_1 D_k = α_k D_{k+1} + β_k D_k` with
`α_k ≠ 0` for `k < c` and `β_k = d_{1,c-k}`, induction on `j` gives
`(f ⊗ f) ∏_{k<j} (D_1 - β_k) = (∏_{k<j} α_k) D_j` for `j ≤ c + 1` (the factors commute, being
polynomials in `D_1`), and `D_{c+1} = 0` (`AJConjecture.turnback_eq_zero`). The product over
`m = 0, …, c` of the statement is the same product in the reverse order.
-/

namespace AJConjecture

/-- `d_{1,c-j} = β_j`, the coefficient of `D_j` in the turnback recursion. -/
private theorem turnbackEigen_one_sub_turnbackMinpoly (c j : ℕ) (hj : j ≤ c) :
    claspAlgTurnbackEigen c 1 (c - j) =
      -(quantumInt (j : ℤ) * quantumInt (2 * (c : ℤ) + 1 - j)) / quantumInt (c : ℤ) ^ 2 := by
  unfold claspAlgTurnbackEigen
  rw [Finset.prod_range_one]
  simp only [Nat.cast_zero, sub_zero]
  rw [Nat.cast_sub hj, show (c : ℤ) - ((c : ℤ) - j) = j from by ring,
    show (c : ℤ) + ((c : ℤ) - j) + 1 = 2 * (c : ℤ) + 1 - j from by ring]

/-- The product of the last `j` factors `D_1 - d_{1,m}`, `c + 1 - j ≤ m ≤ c`, applied to `f ⊗ f`,
is a multiple of `D_j`. -/
private theorem prod_turnback_sub_mul_twoBundleProj_turnbackMinpoly (c : ℕ) :
    ∀ j : ℕ, j ≤ c + 1 → ∃ s : RatFunc ℚ,
      ((List.range' (c + 1 - j) j).map fun m ↦
        turnback c 1 - claspAlgTurnbackEigen c 1 m • (1 : SkMat (2 * c) (2 * c))).prod *
          twoBundleProj c = s • turnback c j := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨1, by rw [List.range'_zero, List.map_nil, List.prod_nil, Matrix.one_mul, turnback_zero,
      one_smul]⟩
  | succ j ih =>
    intro hj
    obtain ⟨s, hs⟩ := ih (by omega)
    have e1 : c + 1 - (j + 1) = c - j := by omega
    have e2 : c - j + 1 = c + 1 - j := by omega
    refine ⟨s * (quantumInt ((c : ℤ) - j) ^ 2 / quantumInt (c : ℤ) ^ 2), ?_⟩
    rw [e1, List.range'_succ, e2, List.map_cons, List.prod_cons, Matrix.mul_assoc, hs,
      Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, turnback_one_mul c j,
      turnbackEigen_one_sub_turnbackMinpoly c j (by omega), add_sub_cancel_right, smul_smul]

/-- `D_1` satisfies on the image of `f ⊗ f` the polynomial with the simple roots `d_{1,m}`,
`m ≤ c`. -/
theorem twoBundleProj_mul_prod_turnback_sub (c : ℕ) :
    twoBundleProj c * ((List.range (c + 1)).map fun m ↦
      turnback c 1 - claspAlgTurnbackEigen c 1 m • (1 : SkMat (2 * c) (2 * c))).prod = 0 := by
  obtain ⟨s, hs⟩ := prod_turnback_sub_mul_twoBundleProj_turnbackMinpoly c (c + 1) le_rfl
  rw [Nat.sub_self, ← List.range_eq_range', turnback_eq_zero c (c + 1) (by omega), smul_zero]
    at hs
  have hFD : Commute (twoBundleProj c) (turnback c 1) := by
    rw [Commute, SemiconjBy, twoBundleProj_mul_turnback, turnback_mul_twoBundleProj]
  have hcomm : Commute (twoBundleProj c) ((List.range (c + 1)).map fun m ↦
      turnback c 1 - claspAlgTurnbackEigen c 1 m • (1 : SkMat (2 * c) (2 * c))).prod := by
    refine Commute.list_prod_right _ _ fun x hx ↦ ?_
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    exact hFD.sub_right ((Commute.one_right _).smul_right _)
  rw [hcomm.eq]
  exact hs

end AJConjecture
