import Mathlib
import AJConjecture.QAlgNodeIndexEuler
import AJHandoff.LocalTheory.LocNodeData
import AJHandoff.TorusQuantum.PairQJetsIndexBlock

/-!
# T-JETS: forward node data give an allowed node of index `-1/2` of the backward row

Let `P ∈ ℤ[t][M][L]` have symbol `κ₁ P₀ = κ₂ ∏ b_i` (`P₀ = P(-1, M, L)`, of full degree `d`),
and let `(m₀, l₀)` be a transverse collision-free node of `b_g` and `b_h` in the forward picture
(the hypotheses of the library's index criterion) at which the Weyl symbol
`P₁ + (L ∂_L)(M ∂_M) P₀` vanishes. Then in the M-backward convention (`z = M`, `u = L⁻¹`,
`σ(z) = exp(-h/2) z`, `c = -1/2`) the point `(m₀, l₀⁻¹)` is an allowed transverse mixed node
(`LocAllowedNode`) of the reversed blocks `b̂_g`, `b̂_h` of the backward row `pairQJetRow P`,
and formula (4) gives the allocation index `-1/2` for both allocations.

Proof. Every quantity of formula (4) at `u = l₀⁻¹` is a power of `l₀` times its forward
counterpart (`evalPoint_pairQJetBlock` and its derivatives); the first jet of the row is the
reversal of `-(1/4) P₁ - (d/2) z ∂_z P₀` (`opJet1_pairQJetRow`), where `∂_M P₀ = 0` at the node
and `P₁ = -(L ∂_L)(M ∂_M) P₀ = -κ₂/κ₁ · l₀ m₀ (G_L H_M + G_M H_L) T` there. Substituting, the
powers of `l₀` cancel (`d = deg G + deg H + deg T`) and (4) reduces to `-1/2`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- At a common zero of `G` and `D` the `M`-derivative of `P₀` vanishes. -/
theorem evalIntPoint_coeffDerivative_of_symbol_node_pairQ {P₀ G D T : ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hsym : C κ₁ * P₀ = C κ₂ * (G * D * T)) {m₀ l₀ : ℂ}
    (hκ₁ : (κ₁.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hG : evalIntPoint G m₀ l₀ = 0) (hD : evalIntPoint D m₀ l₀ = 0) :
    evalIntPoint (coeffDerivative P₀) m₀ l₀ = 0 := by
  have hP := (evalIntPoint_derivatives_of_symbol_node hsym hκ₁ hG hD).1
  have e := congrArg (fun p ↦ pairQJetEvalHom m₀ l₀ (innerDerivative p)) hsym
  rw [evalIntPoint_eq_pairQJetEvalHom] at hP hG hD
  simp only [innerDerivative_mul, innerDerivative_C, map_add, map_mul, hP, hG, hD, mul_zero,
    zero_mul, add_zero, zero_add, pairQJetEvalHom_C] at e
  rw [coeffDerivative_eq_innerDerivative, evalIntPoint_eq_pairQJetEvalHom]
  exact (mul_eq_zero.mp e).resolve_left hκ₁

/-- The value of the first jet of the backward row at `u = l⁻¹`. -/
theorem evalPoint_opJet1_pairQJetRow (P : RecOp) (m : ℂ) {l : ℂ} (hl : l ≠ 0) :
    evalPoint (opJet1 (pairQJetRow P)) (m, l⁻¹) * l ^ P.natDegree =
      -(1 / 4) * evalIntPoint (specializeJet P) m l -
        P.natDegree / 2 * m * evalIntPoint (coeffDerivative (specialize P)) m l := by
  have hle : (C (C (-(1 / 4) : ℂ)) * pairQJetJet P +
      C (C (-(P.natDegree : ℂ) / 2) * X) * innerDerivative (pairQJetSymbol P)).natDegree ≤
        P.natDegree := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
    rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_innerDerivative_pairQ, pairQJetJet,
      pairQJetSymbol, coeff_map, coeff_map, coeff_specializeJet, coeff_specialize,
      coeff_eq_zero_of_natDegree_lt hn]
    simp [coeffJet]
  rw [opJet1_pairQJetRow, evalPoint_reflect_inv_pairQ hle m hl, pairQJetSymbol,
    innerDerivative_map, coeffDerivative_eq_innerDerivative]
  simp only [evalPoint, eval₂_add, eval₂_mul, eval₂_C, coe_evalRingHom, eval_C,
    eval_mul, eval_X, pairQJetJet, evalIntPoint]
  ring

/-- The `u^d` coefficient of the residual symbol of the row is the constant coefficient of `P₀`. -/
theorem coeff_natDegree_opJet0_pairQJetRow (P : RecOp) :
    (opJet0 (pairQJetRow P)).coeff P.natDegree = (pairQJetSymbol P).coeff 0 := by
  rw [opJet0_pairQJetRow, coeff_reflect, revAt_le le_rfl, Nat.sub_self]

/-- The constant coefficient of the residual symbol of the row is the `L^d` coefficient of
`P₀`. -/
theorem coeff_zero_opJet0_pairQJetRow (P : RecOp) :
    (opJet0 (pairQJetRow P)).coeff 0 = (pairQJetSymbol P).coeff P.natDegree := by
  rw [opJet0_pairQJetRow, coeff_reflect, revAt_zero]

/-- If `P₀` has nonzero constant coefficient, the row and its residual symbol have order `d`. -/
theorem natDegree_pairQJetRow {P : RecOp} (h0 : (pairQJetSymbol P).coeff 0 ≠ 0) :
    (opJet0 (pairQJetRow P)).natDegree = P.natDegree ∧
      (pairQJetRow P).natDegree = P.natDegree := by
  have hle : (pairQJetRow P).natDegree ≤ P.natDegree :=
    natDegree_reflect_le.trans (max_le le_rfl natDegree_map_le)
  have hle0 : (opJet0 (pairQJetRow P)).natDegree ≤ P.natDegree :=
    natDegree_map_le.trans hle
  have hc : (opJet0 (pairQJetRow P)).coeff P.natDegree ≠ 0 := by
    rwa [coeff_natDegree_opJet0_pairQJetRow]
  have hc' : (pairQJetRow P).coeff P.natDegree ≠ 0 := fun h ↦
    hc (by rw [opJet0, coeff_map, h, map_zero])
  exact ⟨le_antisymm hle0 (le_natDegree_of_ne_zero hc),
    le_antisymm hle (le_natDegree_of_ne_zero hc')⟩

/-- The cofactor of the reversed blocks is the reversed cofactor. -/
theorem locCofactor_pairQJetBlock {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℤ[X][X])
    (g h : ι) :
    locCofactor (fun i ↦ pairQJetBlock (b i)) g h =
      pairQJetBlock (∏ i ∈ (Finset.univ.erase g).erase h, b i) := by
  rw [locCofactor, pairQJetBlock, Polynomial.map_prod, reverse_prod_pairQ]
  rfl

/-- **T-JETS, transfer.** Forward node data at `(m₀, l₀)` with vanishing Weyl symbol give an
allowed transverse mixed node at `(m₀, l₀⁻¹)` of the backward row with allocation index
`-1/2` (formula (4), `c = -1/2`). -/
theorem pairQJet_allowedNode_index {P : RecOp} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℤ[X][X]} {κ₁ κ₂ : ℤ[X]} (hsym : C κ₁ * specialize P = C κ₂ * ∏ i, b i)
    (hdeg : (specialize P).natDegree = P.natDegree) {g h : ι} (hgh : g ≠ h) {m₀ l₀ : ℂ}
    (hm₀ : m₀ ≠ 0) (hl₀ : l₀ ≠ 0) (hκ₁ : (κ₁.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hκ₂ : (κ₂.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hlead : ((specialize P).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hconst : (((specialize P).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hG : evalIntPoint (b g) m₀ l₀ = 0) (hH : evalIntPoint (b h) m₀ l₀ = 0)
    (hGL : evalIntPoint (derivative (b g)) m₀ l₀ ≠ 0)
    (hHL : evalIntPoint (derivative (b h)) m₀ l₀ ≠ 0)
    (hJ : evalIntPoint (derivative (b g)) m₀ l₀ * evalIntPoint (coeffDerivative (b h)) m₀ l₀ -
      evalIntPoint (derivative (b h)) m₀ l₀ * evalIntPoint (coeffDerivative (b g)) m₀ l₀ ≠ 0)
    (hother : ∀ i, i ≠ g → i ≠ h → evalIntPoint (b i) m₀ l₀ ≠ 0)
    (hfibre : ∀ i j, i ≠ j → ∀ l : ℂ, evalIntPoint (b i) m₀ l = 0 →
      evalIntPoint (b j) m₀ l = 0 → l = l₀ ∧ ((i = g ∧ j = h) ∨ (i = h ∧ j = g)))
    (hW : evalIntPoint (weylSymbol P) m₀ l₀ = 0) :
    LocAllowedNode (pairQJetRow P) (fun i ↦ pairQJetBlock (b i)) (κ₁.map (Int.castRingHom ℂ))
        (κ₂.map (Int.castRingHom ℂ)) g h m₀ l₀⁻¹ ∧
      locNodeIndex pairQJetDilation.c m₀ l₀⁻¹ (opJet1 (pairQJetRow P)) (pairQJetBlock (b g))
        (pairQJetBlock (b h)) (locCofactor (fun i ↦ pairQJetBlock (b i)) g h)
        (κ₁.map (Int.castRingHom ℂ)) (κ₂.map (Int.castRingHom ℂ)) = -1 / 2 := by
  set T : ℤ[X][X] := ∏ i ∈ (Finset.univ.erase g).erase h, b i with hT
  have hprod : ∏ i, b i = b g * b h * T := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ g),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hgh.symm, Finset.mem_univ h⟩),
      mul_assoc]
  have hsym' : C κ₁ * specialize P = C κ₂ * (b g * b h * T) := by rw [hsym, hprod]
  obtain ⟨-, -, -, hEuler⟩ := evalIntPoint_derivatives_of_symbol_node hsym' hκ₁ hG hH
  have hP0M := evalIntPoint_coeffDerivative_of_symbol_node_pairQ hsym' hκ₁ hG hH
  -- degrees: `d = deg G + deg H + deg T`
  have hS0 : specialize P ≠ 0 := fun h0 ↦ hconst (by simp [h0])
  have hκ₁0 : κ₁ ≠ 0 := fun h0 ↦ hκ₁ (by simp [h0])
  have hκ₂0 : κ₂ ≠ 0 := fun h0 ↦ hκ₂ (by simp [h0])
  have hGHT0 : b g * b h * T ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsym'
    exact hS0 ((mul_eq_zero.mp hsym').resolve_left (by simpa using hκ₁0))
  have hdsum : P.natDegree = (b g).natDegree + (b h).natDegree + T.natDegree := by
    have h1 := congrArg natDegree hsym'
    rw [natDegree_C_mul hκ₁0, natDegree_C_mul hκ₂0, hdeg, natDegree_mul (left_ne_zero_of_mul hGHT0)
      (right_ne_zero_of_mul hGHT0), natDegree_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hGHT0))
      (right_ne_zero_of_mul (left_ne_zero_of_mul hGHT0))] at h1
    exact h1
  -- values in the backward picture
  have hl₀' : l₀⁻¹ ≠ 0 := inv_ne_zero hl₀
  have hpow : ∀ n : ℕ, l₀ ^ n ≠ 0 := fun n ↦ pow_ne_zero n hl₀
  have eG := evalPoint_pairQJetBlock (b g) m₀ hl₀
  have eH := evalPoint_pairQJetBlock (b h) m₀ hl₀
  have eT := evalPoint_pairQJetBlock T m₀ hl₀
  have eGu := evalPoint_derivative_pairQJetBlock (b g) m₀ hl₀
  have eHu := evalPoint_derivative_pairQJetBlock (b h) m₀ hl₀
  have eGz := evalPoint_innerDerivative_pairQJetBlock (b g) m₀ hl₀
  have eHz := evalPoint_innerDerivative_pairQJetBlock (b h) m₀ hl₀
  have eP := evalPoint_opJet1_pairQJetRow P m₀ hl₀
  rw [hG] at eG eGu
  rw [hH] at eH eHu
  rw [hP0M, hdsum, pow_add, pow_add] at eP
  have hW' : evalIntPoint (specializeJet P) m₀ l₀ =
      -evalIntPoint (eulerEuler (specialize P)) m₀ l₀ := by
    rw [weylSymbol, evalIntPoint_eq_pairQJetEvalHom, map_add] at hW
    rw [evalIntPoint_eq_pairQJetEvalHom, evalIntPoint_eq_pairQJetEvalHom]
    linear_combination hW
  rw [hW'] at eP
  have hTv : evalIntPoint T m₀ l₀ ≠ 0 := by
    rw [hT, evalIntPoint_eq_pairQJetEvalHom, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_
    obtain ⟨hih, hi'⟩ := Finset.mem_erase.mp hi
    exact hother i (Finset.ne_of_mem_erase hi') hih
  -- explicit backward values
  set pG := l₀ ^ (b g).natDegree
  set pH := l₀ ^ (b h).natDegree
  set pT := l₀ ^ T.natDegree
  set a := evalIntPoint (derivative (b g)) m₀ l₀
  set a' := evalIntPoint (derivative (b h)) m₀ l₀
  set gm := evalIntPoint (coeffDerivative (b g)) m₀ l₀
  set hm := evalIntPoint (coeffDerivative (b h)) m₀ l₀
  have hGu : evalPoint (derivative (pairQJetBlock (b g))) (m₀, l₀⁻¹) = -(l₀ ^ 2 * a) / pG := by
    rw [eq_div_iff (hpow _)]; linear_combination eGu
  have hHu : evalPoint (derivative (pairQJetBlock (b h))) (m₀, l₀⁻¹) = -(l₀ ^ 2 * a') / pH := by
    rw [eq_div_iff (hpow _)]; linear_combination eHu
  have hGz : evalPoint (innerDerivative (pairQJetBlock (b g))) (m₀, l₀⁻¹) = gm / pG := by
    rw [eq_div_iff (hpow _)]; exact eGz
  have hHz : evalPoint (innerDerivative (pairQJetBlock (b h))) (m₀, l₀⁻¹) = hm / pH := by
    rw [eq_div_iff (hpow _)]; exact eHz
  have hjac : evalPoint (derivative (pairQJetBlock (b g))) (m₀, l₀⁻¹) *
        evalPoint (innerDerivative (pairQJetBlock (b h))) (m₀, l₀⁻¹) -
      evalPoint (derivative (pairQJetBlock (b h))) (m₀, l₀⁻¹) *
        evalPoint (innerDerivative (pairQJetBlock (b g))) (m₀, l₀⁻¹) =
      -(l₀ ^ 2 * (a * hm - a' * gm)) / (pG * pH) := by
    rw [hGu, hHu, hGz, hHz]
    field_simp
    ring
  -- endpoints
  have hS00 : (pairQJetSymbol P).coeff 0 ≠ 0 := by
    intro h0
    apply hconst
    rw [pairQJetSymbol, coeff_map, coe_mapRingHom] at h0
    rw [h0, eval_zero]
  obtain ⟨hdeg0, hdegR⟩ := natDegree_pairQJetRow hS00
  have hconst' : ((opJet0 (pairQJetRow P)).coeff 0).eval m₀ ≠ 0 := by
    rw [coeff_zero_opJet0_pairQJetRow, pairQJetSymbol, coeff_map, coe_mapRingHom, ← hdeg]
    exact hlead
  have hsymu := pairQJet_sym hsym hdeg
  have hnode : LocAllowedNode (pairQJetRow P) (fun i ↦ pairQJetBlock (b i))
      (κ₁.map (Int.castRingHom ℂ)) (κ₂.map (Int.castRingHom ℂ)) g h m₀ l₀⁻¹ :=
    { sym := hsymu
      κ₁_ne := hκ₁
      κ₂_ne := hκ₂
      ne := hgh
      z₀_ne := hm₀
      lam_ne := hl₀'
      natDegree_eq := by rw [hdeg0, hdegR]
      lead_ne := by
        rw [leadingCoeff, hdeg0, coeff_natDegree_opJet0_pairQJetRow, pairQJetSymbol, coeff_map,
          coe_mapRingHom]
        exact hconst
      const_ne := hconst'
      root_g := (mul_eq_zero.mp eG).resolve_right (hpow _)
      root_h := (mul_eq_zero.mp eH).resolve_right (hpow _)
      du_g := by
        rw [hGu]
        exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hl₀) hGL)) (hpow _)
      du_h := by
        rw [hHu]
        exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hl₀) hHL)) (hpow _)
      jac := by
        rw [hjac]
        exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hl₀) hJ))
          (mul_ne_zero (hpow _) (hpow _))
      other := fun i hi hi' ↦ left_ne_zero_of_mul
        ((evalPoint_pairQJetBlock (b i) m₀ hl₀).symm ▸ hother i hi hi')
      fibre := by
        intro i j hij l hi hj
        by_cases hl : l = 0
        · exfalso
          subst hl
          have h0 := congrArg (fun p ↦ evalPoint p (m₀, 0)) hsymu
          simp only [evalPoint, eval₂_mul, eval₂_C, eval₂_finsetProd, coe_evalRingHom] at h0 hi
          rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero, eval₂_at_zero,
            coe_evalRingHom] at h0
          exact mul_ne_zero hκ₁ hconst' h0
        · have hi' := evalPoint_pairQJetBlock (b i) m₀ (inv_ne_zero hl)
          have hj' := evalPoint_pairQJetBlock (b j) m₀ (inv_ne_zero hl)
          rw [inv_inv, hi, zero_mul] at hi'
          rw [inv_inv, hj, zero_mul] at hj'
          obtain ⟨hl', hc⟩ := hfibre i j hij l⁻¹ hi'.symm hj'.symm
          exact ⟨inv_eq_iff_eq_inv.mp hl', hc⟩ }
  refine ⟨hnode, ?_⟩
  -- the index
  have hTval : evalPoint (pairQJetBlock T) (m₀, l₀⁻¹) = evalIntPoint T m₀ l₀ / pT := by
    rw [eq_div_iff (hpow _)]; exact eT
  have hPval : evalPoint (opJet1 (pairQJetRow P)) (m₀, l₀⁻¹) =
      evalIntPoint (eulerEuler (specialize P)) m₀ l₀ / (4 * (pG * pH * pT)) := by
    rw [eq_div_iff (mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (hpow _) (hpow _))
      (hpow _)))]
    linear_combination 4 * eP
  rw [locNodeIndex, locCofactor_pairQJetBlock, ← hT, hjac, hHu, hGz, hTval, hPval,
    pairQJetDilation_c]
  have hpG : pG ≠ 0 := hpow _
  have hpH : pH ≠ 0 := hpow _
  have hpT : pT ≠ 0 := hpow _
  field_simp
  linear_combination (-4) * hEuler

end AJConjecture
