import Mathlib
import AJHandoff.LocalTheory.LocGraphTheorem

/-!
# I-CTRL / I: the degree-two toy operator `u² - 2u + z(2 - z)` is irreducible over `ℂ((h))(z)`

With `c = 1`, `σ(z) = exp(h) z`, the operator `P = u² - 2u + z(2 - z)` (coefficients in
`ℂ[z] ⊆ ℂ[[h]][z]`, so `P₁ = 0`) has residual blocks `G = u - z`, `H = u + z - 2`, meeting only at
`(z, u) = (1, 1)` with `G_u = H_u = 1`, `G_z = -1`, `H_z = 1`, `J = 2`; the constant coefficient
`z(2 - z)` is a unit at `z = 1`, there is no other block and no other mixed root on the fibre.
Formula (4) gives `I_G = I_H = -1/2`, so Theorem 4 (with the one-edge graph on two vertices)
proves irreducibility over `ℂ((h))(z)`. This lies outside the Whitehead finite-sum family.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The source's toy dilation `σ(z) = exp(h) z` (`c = 1`). -/
abbrev toyDilation : LocDilation := LocDilation.exp 1 one_ne_zero

/-- The toy operator `u² - 2u + z(2 - z)`. -/
def locToyOp : LocOp := X ^ 2 - C 2 * X + C ((X : LocPoly) * (2 - X))

/-- Its residual blocks `u - z` and `u + z - 2`. -/
def locToyBlock : Fin 2 → ℂ[X][X]
  | 0 => X - C X
  | 1 => X + C (X - 2)

/-- The toy operator with coefficients in `ℂ[z]`. -/
private def toyBasePoly : ℂ[X][X] := X ^ 2 - C 2 * X + C (X * (2 - X))

/-- The toy operator is the base change of `toyBasePoly` along `ℂ ⊆ ℂ[[h]]`. -/
private theorem locToyOp_eq_map :
    locToyOp = toyBasePoly.map (Polynomial.mapRingHom (PowerSeries.C (R := ℂ))) := by
  simp [locToyOp, toyBasePoly]

/-- The residual symbol of the toy operator. -/
private theorem opJet0_locToyOp : opJet0 locToyOp = toyBasePoly := by
  rw [locToyOp_eq_map, opJet0, Polynomial.map_map]
  ext k n
  simp [locJet0]

/-- An operator with coefficients in `ℂ[z]` has zero first jet. -/
private theorem opJet1_map_C_toy (p : ℂ[X][X]) :
    opJet1 (p.map (Polynomial.mapRingHom (PowerSeries.C (R := ℂ)))) = 0 := by
  ext k n
  rw [coeff_opJet1, coeff_locJet1]
  simp

/-- The residual symbol is the product of the two blocks. -/
private theorem toyBasePoly_eq_prod : toyBasePoly = locToyBlock 0 * locToyBlock 1 := by
  simp only [toyBasePoly, locToyBlock, map_sub, map_mul, map_ofNat]
  ring

/-- The residual symbol is monic. -/
private theorem toyBasePoly_monic : toyBasePoly.Monic := by
  rw [toyBasePoly_eq_prod]
  exact (monic_X_sub_C _).mul (monic_X_add_C _)

/-- The residual symbol has degree two. -/
private theorem toyBasePoly_natDegree : toyBasePoly.natDegree = 2 := by
  rw [toyBasePoly_eq_prod]
  simp only [locToyBlock]
  rw [(monic_X_sub_C _).natDegree_mul (monic_X_add_C _), natDegree_X_sub_C, natDegree_X_add_C]

/-- The toy operator has order two. -/
private theorem locToyOp_natDegree : locToyOp.natDegree = 2 := by
  rw [locToyOp_eq_map, natDegree_map_eq_of_injective
    (Polynomial.map_injective _ PowerSeries.C_injective), toyBasePoly_natDegree]

/-- The inner derivative of `u + a(z)`. -/
private theorem innerDerivative_X_add_C_toy (a : ℂ[X]) :
    innerDerivative (X + C a : ℂ[X][X]) = C (derivative a) := by
  rw [innerDerivative_add, innerDerivative_C]
  have hX : innerDerivative (X : ℂ[X][X]) = 0 := by
    unfold innerDerivative
    rw [sum_X_index (by simp)]
    simp
  rw [hX, zero_add]

/-- Both blocks restricted to the fibre `z = 1` are `u - 1`. -/
private theorem evalPoint_locToyBlock_one (i : Fin 2) (l : ℂ) :
    evalPoint (locToyBlock i) (1, l) = l - 1 := by
  fin_cases i <;> simp [locToyBlock, evalPoint]
  ring

/-- The blocks over `ℂ(z)` are monic of degree one. -/
private theorem locToyBlock_map_monic_degree (i : Fin 2) :
    ((locToyBlock i).map (algebraMap ℂ[X] (RatFunc ℂ))).Monic ∧
      ((locToyBlock i).map (algebraMap ℂ[X] (RatFunc ℂ))).degree = 1 := by
  fin_cases i
  · simp only [locToyBlock, Polynomial.map_sub, map_X, map_C]
    exact ⟨monic_X_sub_C _, degree_X_sub_C _⟩
  · simp only [locToyBlock, Polynomial.map_add, map_X, map_C]
    exact ⟨monic_X_add_C _, degree_X_add_C _⟩

theorem locToy_residualBlocks : LocResidualBlocks locToyOp locToyBlock := by
  refine ⟨⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩, fun i ↦ ?_, fun i j hij hass ↦ ?_⟩
  · rw [Fin.prod_univ_two, opJet0_locToyOp, toyBasePoly_eq_prod]
  · exact Polynomial.irreducible_of_degree_eq_one (locToyBlock_map_monic_degree i).2
  · have heq := Polynomial.eq_of_monic_of_associated (locToyBlock_map_monic_degree i).1
      (locToyBlock_map_monic_degree j).1 hass
    have hB := congrArg (evalPoint · (0, 0))
      (Polynomial.map_injective _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ)) heq)
    fin_cases i <;> fin_cases j <;> simp_all [locToyBlock, evalPoint]

/-- The first and inner derivatives of the blocks at `(1, 1)`. -/
private theorem evalPoint_derivatives_locToyBlock :
    evalPoint (derivative (locToyBlock 0)) (1, 1) = 1 ∧
      evalPoint (derivative (locToyBlock 1)) (1, 1) = 1 ∧
      evalPoint (innerDerivative (locToyBlock 0)) (1, 1) = -1 ∧
      evalPoint (innerDerivative (locToyBlock 1)) (1, 1) = 1 := by
  have h0 : locToyBlock 0 = X + C (-X) := by rw [locToyBlock, map_neg, sub_eq_add_neg]
  have h1 : locToyBlock 1 = X + C (X - 2) := rfl
  rw [h0, h1, innerDerivative_X_add_C_toy, innerDerivative_X_add_C_toy]
  simp [evalPoint]

theorem locToy_allowedNode : LocAllowedNode locToyOp locToyBlock 1 1 0 1 1 1 := by
  obtain ⟨d0, d1, i0, i1⟩ := evalPoint_derivatives_locToyBlock
  have hsym : C 1 * opJet0 locToyOp = C 1 * ∏ i, locToyBlock i := by
    rw [Fin.prod_univ_two, opJet0_locToyOp, toyBasePoly_eq_prod]
  exact
    { sym := hsym
      κ₁_ne := by simp
      κ₂_ne := by simp
      ne := by decide
      z₀_ne := one_ne_zero
      lam_ne := one_ne_zero
      natDegree_eq := by rw [opJet0_locToyOp, toyBasePoly_natDegree, locToyOp_natDegree]
      lead_ne := by rw [opJet0_locToyOp, toyBasePoly_monic.leadingCoeff]; simp
      const_ne := by rw [opJet0_locToyOp]; norm_num [toyBasePoly]
      root_g := by rw [evalPoint_locToyBlock_one]; ring
      root_h := by rw [evalPoint_locToyBlock_one]; ring
      du_g := by rw [d0]; exact one_ne_zero
      du_h := by rw [d1]; exact one_ne_zero
      jac := by rw [d0, d1, i0, i1]; norm_num
      other := fun i hi hi' ↦ by fin_cases i <;> simp_all
      fibre := fun i j hij l hi hj ↦ by
        rw [evalPoint_locToyBlock_one, sub_eq_zero] at hi
        refine ⟨hi, ?_⟩
        fin_cases i <;> fin_cases j <;> simp_all }

/-- Both allocation indices are `-1/2`. -/
theorem locToy_nodeIndex :
    locNodeIndex 1 1 1 (opJet1 locToyOp) (locToyBlock 0) (locToyBlock 1)
        (locCofactor locToyBlock 0 1) 1 1 = -1 / 2 := by
  obtain ⟨d0, d1, i0, i1⟩ := evalPoint_derivatives_locToyBlock
  have hT : locCofactor locToyBlock 0 1 = 1 := by
    rw [locCofactor, show ((Finset.univ : Finset (Fin 2)).erase 0).erase 1 = ∅ by decide,
      Finset.prod_empty]
  rw [locToyOp_eq_map, opJet1_map_C_toy, hT, locNodeIndex, d0, d1, i0, i1]
  simp [evalPoint]
  norm_num

/-- The toy operator is irreducible in `ℂ((h))(z)[u; σ]`. -/
theorem locToy_oreIrreducible :
    OreIrreducible toyDilation.fieldShiftHom (locToyOp.map (algebraMap LocPoly LocField)) := by
  have hc : toyDilation.c = 1 := LocDilation.exp_c 1 one_ne_zero
  have hI : ∀ n : ℤ, (-1 / 2 : ℂ) ≠ n := fun n h ↦ by
    have h2 : ((2 * n : ℤ) : ℂ) = ((-1 : ℤ) : ℂ) := by push_cast; rw [← h]; ring
    have h3 := Int.cast_injective h2
    omega
  refine oreIrreducible_of_connected toyDilation (by rw [locToyOp_natDegree]; norm_num)
    (by rw [opJet0_locToyOp, toyBasePoly_natDegree, locToyOp_natDegree])
    (by
      rw [opJet0_locToyOp]
      norm_num [toyBasePoly]
      intro h
      simpa using congrArg (eval 0) h) locToy_residualBlocks ⊤
    SimpleGraph.connected_top fun i j hij ↦ ⟨1, 1, 1, 1, ?_⟩
  rw [hc]
  have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨locToy_allowedNode, by rw [locToy_nodeIndex]; exact hI⟩
  · refine ⟨locToy_allowedNode.symm, ?_⟩
    obtain ⟨d0, d1, i0, i1⟩ := evalPoint_derivatives_locToyBlock
    rw [locCofactor_swap, locNodeIndex_swap one_ne_zero one_ne_zero one_ne_zero
      (by rw [d0, d1, i0, i1]; norm_num), locToy_nodeIndex]
    intro n
    convert hI n using 1
    ring

/-- The residual symbol of the toy operator is the product of its two blocks. -/
theorem opJet0_locToyOp_eq_mul : opJet0 locToyOp = locToyBlock 0 * locToyBlock 1 := by
  rw [opJet0_locToyOp, toyBasePoly_eq_prod]

/-- The toy operator has zero first jet. -/
theorem opJet1_locToyOp : opJet1 locToyOp = 0 := by
  rw [locToyOp_eq_map, opJet1_map_C_toy]

/-- The first and inner derivatives of the toy blocks at the node `(1, 1)`. -/
theorem evalPoint_derivative_locToyBlock_one :
    evalPoint (derivative (locToyBlock 0)) (1, 1) = 1 ∧
      evalPoint (derivative (locToyBlock 1)) (1, 1) = 1 ∧
      evalPoint (innerDerivative (locToyBlock 0)) (1, 1) = -1 ∧
      evalPoint (innerDerivative (locToyBlock 1)) (1, 1) = 1 :=
  evalPoint_derivatives_locToyBlock

/-- With two blocks the cofactor is `1`. -/
theorem locCofactor_locToyBlock :
    locCofactor locToyBlock 0 1 = 1 ∧ locCofactor locToyBlock 1 0 = 1 := by
  have h : locCofactor locToyBlock 0 1 = 1 := by
    rw [locCofactor, show ((Finset.univ : Finset (Fin 2)).erase 0).erase 1 = ∅ by decide,
      Finset.prod_empty]
  exact ⟨h, by rw [locCofactor_swap, h]⟩

end AJConjecture
