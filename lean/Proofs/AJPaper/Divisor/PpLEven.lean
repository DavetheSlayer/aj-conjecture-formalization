import Mathlib
import AJConjecture.QAlgOreMulMap
import AJPaper.Divisor.PpLUnique
import AJPaper.Divisor.PpLJet

/-!
# Descent of a right factor of order one of the adjoint to the variable `x = M²` (Unit PpL,
node `PpL_Even`)

Source: Section 5.6 of the paper (`operators.tex`): "Suppose `u - r_0` is a right divisor over
`ℚ(t, M)`. The involution `M ↦ -M` commutes with the shift and fixes `P`; uniqueness implies
`r_0 ∈ ℚ(t, x)`." Mirror of `AJTwist/Factor/TwFZeroEven.lean` for the adjoint; as there, only
this first descent is used (the constants stay in `ℚ(t)`).

`ppl_adjoint_exists_even_solution`: a right pseudo-factor of degree one of `pplAdjOp` yields
`e₀, e₁ ∈ ℤ[t][x]` with `e₁(-1, x) ≠ 0`, `e₀(-1, x) = -e₁(-1, x)`, solving the Riccati equation
of `pplAdjOpX` for the shift `x ↦ t⁴ x`, and with logarithmic first jet `2 (5x - 3)/(x - 1)`:
`(ė₀ ē₁ - ē₀ ė₁)(x - 1) = ē₀ ē₁ · 2 (5x - 3)`.

Route (the template's, with two simplifications: the operator is already explicit, so no
determinant scalar and no passage through `twZeroExplicitOp_mul_eq`).
1. Normalise (`exists_normalized_pseudoFactor`, `specialize_pplAdjOp_ne_zero`): `β'(-1, M) ≠ 0`,
   `R' = r₁ L + r₀`, `specialize R' ≠ 0`; by `ppl_adjoint_rightFactor_symbol`, `r̄₀ = -r̄₁ ≠ 0`.
2. `pplAdjOp.map twfNegM = pplAdjOp`: `pplAdjOp = pplAdjOpX.map twfSq` (`map_twfSq_pplAdjOpX`)
   and `twfNegM (twfSq c) = twfSq c` (`(c.comp (X ^ 2)).comp (-X)`). `twfNegM` commutes with
   `coeffShift` and is an involution (private lemmas of the template), so `map_oreMul` gives the
   second right pseudo-factor `R'.map twfNegM`, and `ppl_adjoint_rightFactor_unique` gives
   `r₀ ν(r₁) = r₁ ν(r₀)`.
3. `ν(r₁) r₀` and `ν(r₁) r₁` are fixed by `ν`, hence `twfSq e₀`, `twfSq e₁`
   (`exists_twfSq_eq_of_twfNegM_eq`).
4. Riccati: `oreRiccati_eq_zero_of_pseudoFactor` for `R'`, `oreRiccati_mul_left` for the factor
   `ν(r₁)`, then `oreRiccati_map twfSq twfShiftX coeffShift twfSq_twfShiftX` and
   `twfSq_injective`.
5. Jet: `nodeNumer_mul_of_rightFactor_pplAdjOp` for `R'` (unfold `nodeNumer`, `nodeDenom`,
   `coeff_specializeJet`, `coeff_specialize`), multiplied by `ν(r₁)(-1, M)²`, read through
   `twfSq` (`ppl_coeffJet_twfSq`, `ppl_map_evalRingHom_twfSq`, `ppl_coeffJet_mul`) and
   `expand_injective`.

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The involution `M ↦ -M` commutes with the shift. -/
private theorem twfNegM_coeffShift_pplEven (c : Coeff) :
    twfNegM (coeffShift c) = coeffShift (twfNegM c) := by
  have hq : (C (X ^ 2) * X : Coeff).comp (-X) = (-X : Coeff).comp (C (X ^ 2) * X) := by
    rw [mul_comp, C_comp, X_comp, neg_comp, X_comp]
    ring
  change (c.comp (C (X ^ 2) * X)).comp (-X) = (c.comp (-X)).comp (C (X ^ 2) * X)
  rw [comp_assoc, comp_assoc, hq]

/-- `M ↦ -M` is an involution. -/
private theorem twfNegM_twfNegM_pplEven (c : Coeff) : twfNegM (twfNegM c) = c :=
  comp_neg_X_comp_neg_X c

/-- `M ↦ -M` is injective. -/
private theorem twfNegM_injective_pplEven : Function.Injective twfNegM :=
  Function.LeftInverse.injective twfNegM_twfNegM_pplEven

/-- `M ↦ -M` fixes the adjoint. -/
private theorem map_twfNegM_pplAdjOp_pplEven : pplAdjOp.map twfNegM = pplAdjOp := by
  have hfix : ∀ c : Coeff, twfNegM (twfSq c) = twfSq c := by
    intro c
    change (c.comp (X ^ 2)).comp (-X) = c.comp (X ^ 2)
    have h2 : (-X : Coeff) ^ 2 = X ^ 2 := by ring
    rw [comp_assoc, X_pow_comp, h2]
  rw [← map_twfSq_pplAdjOpX]
  ext k : 2
  rw [coeff_map, coeff_map, hfix]

/-- The value at `t = -1` commutes with `M ↦ -M`. -/
private theorem map_evalRingHom_twfNegM_pplEven (c : Coeff) :
    (twfNegM c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      (c.map (Polynomial.evalRingHom (-1 : ℤ))).comp (-X) := by
  change (c.comp (-X)).map (Polynomial.evalRingHom (-1 : ℤ)) = _
  rw [map_comp, Polynomial.map_neg, map_X]

/-- Normalisation: a right pseudo-factor of degree one of the adjoint with scalar nonzero at
`t = -1` and symbol proportional to `L - 1`. -/
private theorem exists_normalized_linear_pplEven {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * pplAdjOp = oreMul coeffShift S R) (hR : R.natDegree = 1) :
    ∃ (β' : Coeff) (S' R' : RecOp), β'.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      R'.natDegree = 1 ∧ C β' * pplAdjOp = oreMul coeffShift S' R' ∧
      (R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      (R'.coeff 0).map (Polynomial.evalRingHom (-1 : ℤ)) =
        -(R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  obtain ⟨β', S', R', hβ', -, hR', -, hRdeg, h', -⟩ :=
    exists_normalized_pseudoFactor specialize_pplAdjOp_ne_zero hβ h
  have hR'1 : R'.natDegree = 1 := hRdeg.trans hR
  have hsym := ppl_adjoint_rightFactor_symbol hβ' h' hR'1
  have hdeg : (specialize R').natDegree < 2 := by
    have hle : (specialize R').natDegree ≤ R'.natDegree := by
      rw [specialize, coe_mapRingHom]
      exact natDegree_map_le
    omega
  rw [eval_eq_sum_range' hdeg] at hsym
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, mul_one,
    coeff_specialize] at hsym
  have h01 := eq_neg_of_add_eq_zero_left hsym
  refine ⟨β', S', R', hβ', hR'1, h', fun h1 ↦ hR' ?_, h01⟩
  rw [(specialize R').as_sum_range' 2 hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_specialize, h01, h1,
    neg_zero, monomial_zero_right, add_zero]

/-- By uniqueness, the right factor and its image under `M ↦ -M` are proportional. -/
private theorem twfNegM_proportional_pplEven {β' : Coeff} (hβ' : β' ≠ 0) {S' R' : RecOp}
    (h' : C β' * pplAdjOp = oreMul coeffShift S' R') (hR' : R'.natDegree = 1) :
    R'.coeff 0 * twfNegM (R'.coeff 1) = R'.coeff 1 * twfNegM (R'.coeff 0) := by
  have hmap := congrArg (Polynomial.map twfNegM) h'
  rw [map_oreMul twfNegM coeffShift coeffShift twfNegM_coeffShift_pplEven,
    Polynomial.map_mul, map_C, map_twfNegM_pplAdjOp_pplEven] at hmap
  have hν : twfNegM β' ≠ 0 := (map_ne_zero_iff twfNegM twfNegM_injective_pplEven).mpr hβ'
  have hdeg : (R'.map twfNegM).natDegree = 1 := by
    rw [natDegree_map_eq_of_injective twfNegM_injective_pplEven, hR']
  have hu := ppl_adjoint_rightFactor_unique hβ' hν h' hmap hR' hdeg
  rwa [coeff_map, coeff_map] at hu

/-- The coefficients of the right factor multiplied by `ν(r₁)` are polynomials in `M²`. -/
private theorem exists_twfSq_pair_pplEven {r₀ r₁ : Coeff}
    (h : r₀ * twfNegM r₁ = r₁ * twfNegM r₀) :
    ∃ e₀ e₁ : Coeff, twfSq e₀ = twfNegM r₁ * r₀ ∧ twfSq e₁ = twfNegM r₁ * r₁ := by
  obtain ⟨e₀, he₀⟩ := exists_twfSq_eq_of_twfNegM_eq (c := twfNegM r₁ * r₀)
    (by rw [map_mul, twfNegM_twfNegM_pplEven, ← h, mul_comm])
  obtain ⟨e₁, he₁⟩ := exists_twfSq_eq_of_twfNegM_eq (c := twfNegM r₁ * r₁)
    (by rw [map_mul, twfNegM_twfNegM_pplEven, mul_comm])
  exact ⟨e₀, e₁, he₀, he₁⟩

/-- Every multiple of the right factor solves the Riccati equation of the adjoint. -/
private theorem oreRiccati_pplAdjOp_eq_zero_pplEven {β' : Coeff} (hβ' : β' ≠ 0)
    {S' R' : RecOp} (h' : C β' * pplAdjOp = oreMul coeffShift S' R')
    (hR' : R'.natDegree = 1) (γ : Coeff) :
    oreRiccati coeffShift 3 pplAdjOp (γ * R'.coeff 0) (γ * R'.coeff 1) = 0 := by
  have h0 := oreRiccati_eq_zero_of_pseudoFactor coeffShift_injective hβ' h' hR'
    natDegree_pplAdjOp.le
  rw [oreRiccati_mul_left, h0, mul_zero]

/-- The logarithmic first jet of the right factor, in the variable `M`. -/
private theorem jet_identity_pplEven {β' : Coeff}
    (hβ' : β'.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S' R' : RecOp}
    (h' : C β' * pplAdjOp = oreMul coeffShift S' R') (hR' : R'.natDegree = 1) :
    (coeffJet (R'.coeff 0) * (R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) -
        (R'.coeff 0).map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet (R'.coeff 1)) *
        (X ^ 2 - 1) =
      (R'.coeff 0).map (Polynomial.evalRingHom (-1 : ℤ)) *
        (R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) * (2 * (5 * X ^ 2 - 3)) := by
  have hsym := ppl_adjoint_rightFactor_symbol hβ' h' hR'
  have hn := nodeNumer_mul_of_rightFactor_pplAdjOp hβ' h' hR' hsym
  rwa [nodeNumer, nodeDenom, hR', coeff_specializeJet, coeff_specializeJet, coeff_specialize,
    coeff_specialize] at hn

/-- The descent: a right pseudo-factor of degree one of the adjoint of `P_0` yields a solution
in `ℤ[t][x]` of the Riccati equation of the adjoint for the shift `x ↦ t⁴ x`, equal to `1` at
`t = -1` and with logarithmic first jet `2 (5x - 3)/(x - 1)`. -/
theorem ppl_adjoint_exists_even_solution {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * pplAdjOp = oreMul coeffShift S R) (hR : R.natDegree = 1) :
    ∃ e₀ e₁ : Coeff, e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ∧
      oreRiccati twfShiftX 3 pplAdjOpX e₀ e₁ = 0 ∧
      (coeffJet e₀ * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) -
          e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet e₁) * (X - 1) =
        e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) *
          (2 * (5 * X - 3)) := by
  obtain ⟨β', S', R', hβ', hR', h', hr₁, h01⟩ := exists_normalized_linear_pplEven hβ h hR
  have hβ'0 : β' ≠ 0 := fun h0 ↦ hβ' (by rw [h0, Polynomial.map_zero])
  obtain ⟨e₀, e₁, he₀, he₁⟩ :=
    exists_twfSq_pair_pplEven (twfNegM_proportional_pplEven hβ'0 h' hR')
  have hric := oreRiccati_pplAdjOp_eq_zero_pplEven hβ'0 h' hR' (twfNegM (R'.coeff 1))
  have hjet := jet_identity_pplEven hβ' h' hR'
  have hγ : (twfNegM (R'.coeff 1)).map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    rw [map_evalRingHom_twfNegM_pplEven]
    exact comp_neg_X_eq_zero_iff.not.mpr hr₁
  have hs₀ := ppl_map_evalRingHom_twfSq e₀
  have hs₁ := ppl_map_evalRingHom_twfSq e₁
  rw [he₀, Polynomial.map_mul] at hs₀
  rw [he₁, Polynomial.map_mul] at hs₁
  have hj₀ := ppl_coeffJet_twfSq e₀
  have hj₁ := ppl_coeffJet_twfSq e₁
  rw [he₀, ppl_coeffJet_mul] at hj₀
  rw [he₁, ppl_coeffJet_mul] at hj₁
  have hinj : Function.Injective (expand ℤ 2) := expand_injective two_pos
  refine ⟨e₀, e₁, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, zero_comp] at hs₁
    exact mul_ne_zero hγ hr₁ hs₁
  · apply hinj
    rw [expand_eq_comp_X_pow, expand_eq_comp_X_pow, neg_comp, ← hs₀, ← hs₁, h01]
    ring
  · apply twfSq_injective
    rw [map_zero, oreRiccati_map twfSq twfShiftX coeffShift twfSq_twfShiftX,
      map_twfSq_pplAdjOpX, he₀, he₁]
    exact hric
  · apply hinj
    rw [expand_eq_comp_X_pow, expand_eq_comp_X_pow]
    simp only [mul_comp, sub_comp, X_comp, one_comp, ofNat_comp, Nat.cast_ofNat]
    rw [← hs₀, ← hs₁, ← hj₀, ← hj₁, h01] at *
    linear_combination ((twfNegM (R'.coeff 1)).map (Polynomial.evalRingHom (-1 : ℤ))) ^ 2 * hjet

end AJConjecture
