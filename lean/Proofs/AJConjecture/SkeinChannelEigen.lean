import Mathlib
import AJConjecture.SkeinTurnbackEigenBasic
import AJConjecture.SkeinTwoBundle

/-!
# The channel idempotents on eigenvectors of `D_1`

If `Y` lies in the image of `f ⊗ f` and `D_1 Y = d_{1,n'} Y`, then `Q_j Y = Y` for `j = n'` and
`Q_j Y = 0` otherwise. By the definition of `AJConjecture.channelIdem`, each factor
`(D_1 - d_{1,m}) / (d_{1,j} - d_{1,m})` acts on `Y` as the scalar `(d_{1,n'} - d_{1,m}) / (d_{1,j}
- d_{1,m})`:
for `j = n'` all these scalars are `1` (the eigenvalues are distinct,
`AJConjecture.turnbackEigen_one_injective`), and for `j ≠ n'` the factor `m = n'` is `0`. Induction
on
the list of factors. This is the form in which the spectral theory is applied to rectangular
matrices (fusion maps, nests of caps).
-/

namespace AJConjecture

/-- A product of factors `a_m (D - b_m)` acts on an eigenvector of `D` as the product of the
scalars `a_m (e - b_m)`. -/
private theorem list_prod_smul_sub_mul_channelEigen {p l : ℕ} (D : SkMat p p) (Y : SkMat p l)
    (e : RatFunc ℚ) (a b : ℕ → RatFunc ℚ) (hY : D * Y = e • Y) (L : List ℕ) :
    (L.map fun m ↦ a m • (D - b m • (1 : SkMat p p))).prod * Y =
      (L.map fun m ↦ a m * (e - b m)).prod • Y := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, Matrix.one_mul, one_smul]
  | cons m L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Matrix.mul_assoc, ih,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, hY, Matrix.smul_mul, Matrix.one_mul,
      ← sub_smul, smul_smul, smul_smul]
    congr 1
    ring

/-- A channel idempotent acts on an eigenvector of `D_1` as `1` or `0`. -/
theorem channelIdem_mul_of_turnback_one_mul (c j n' : ℕ) {l : ℕ} (Y : SkMat (2 * c) l)
    (hj : j ≤ c) (hn' : n' ≤ c) (hff : twoBundleProj c * Y = Y)
    (hY : turnback c 1 * Y = claspAlgTurnbackEigen c 1 n' • Y) :
    channelIdem c j * Y = if j = n' then Y else 0 := by
  rw [channelIdem, Matrix.mul_assoc,
    list_prod_smul_sub_mul_channelEigen (turnback c 1) Y (claspAlgTurnbackEigen c 1 n')
      (fun m ↦ (claspAlgTurnbackEigen c 1 j - claspAlgTurnbackEigen c 1 m)⁻¹)
      (fun m ↦ claspAlgTurnbackEigen c 1 m) hY, Matrix.mul_smul, hff]
  split_ifs with h
  · subst h
    have h1 : (((List.range (c + 1)).filter (· ≠ j)).map fun m ↦
        (claspAlgTurnbackEigen c 1 j - claspAlgTurnbackEigen c 1 m)⁻¹ *
          (claspAlgTurnbackEigen c 1 j - claspAlgTurnbackEigen c 1 m)).prod = 1 := by
      refine List.prod_eq_one fun x hx ↦ ?_
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_filter, List.mem_range] at hm
      refine inv_mul_cancel₀ (sub_ne_zero.2 fun hd ↦ ?_)
      exact of_decide_eq_true hm.2 (turnbackEigen_one_injective c j m hj (by omega) hd).symm
    rw [h1, one_smul]
  · have h0 : (((List.range (c + 1)).filter (· ≠ j)).map fun m ↦
        (claspAlgTurnbackEigen c 1 j - claspAlgTurnbackEigen c 1 m)⁻¹ *
          (claspAlgTurnbackEigen c 1 n' - claspAlgTurnbackEigen c 1 m)).prod = 0 := by
      refine List.prod_eq_zero (List.mem_map.2 ⟨n', ?_, by rw [sub_self, mul_zero]⟩)
      rw [List.mem_filter, List.mem_range]
      exact ⟨by omega, decide_eq_true fun hn ↦ h hn.symm⟩
    rw [h0, zero_smul]

end AJConjecture
