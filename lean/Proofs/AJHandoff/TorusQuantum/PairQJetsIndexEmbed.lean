import Mathlib
import AJConjecture.QAlgCoeffShift
import AJConjecture.QAlgNodeJetBasic
import AJConjecture.QAlgWeylSymbol
import AJHandoff.LocalTheory.LocOpJets

/-!
# T-JETS: the transfer operator as an operator over `ℂ((h))(z)` (M-backward convention)

The library's operators live in `ℤ[t][M][L]` with `L a = τ(a) L`, `τ(M) = t² M`. The embedding
`t ↦ -exp(h/4)`, `M ↦ z` (`pairQJetEmbed`) sends `q = t⁴` to `exp(h)` and `τ` to `z ↦ exp(h/2) z`.
In the backward variable `u = L⁻¹` one has `u a = τ⁻¹(a) u`, i.e. the dilation
`σ(z) = exp(-h/2) z` of the local theory with `c = -1/2` (`pairQJetDilation`,
`pairQJetDilation_shift_embed_coeffShift`): this is the "M-backward convention" of the contract.
An operator `P = ∑_k a_k L^k` of order `d` gives the backward row
`L^(-d) P = ∑_k σ^d(a_k) u^(d-k)` (`pairQJetRow`).

Its jets (`opJet0_pairQJetRow`, `opJet1_pairQJetRow`): with `P₀ = specialize P`,
`P₁ = specializeJet P` (the `t`-jet at `t = -1`) mapped to `ℂ`,
* residual symbol: the reversal `u^d P₀(z, 1/u)`;
* first jet: the reversal of `-(1/4) P₁ - (d/2) z ∂_z P₀`
(`t + 1 = -h/4 + O(h²)`, and `σ^d` contributes `d c z ∂_z`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value `t = -exp(h/4)` in `ℂ[[h]]`. -/
def pairQJetT : PowerSeries ℂ := -PowerSeries.rescale (1 / 4 : ℂ) (PowerSeries.exp ℂ)

/-- The evaluation `ℤ[t] → ℂ[[h]]`, `t ↦ -exp(h/4)`. -/
def pairQJetInner : ℤ[X] →+* PowerSeries ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries ℂ)) pairQJetT

/-- The embedding `ℤ[t][M] → ℂ[[h]][z]`, `t ↦ -exp(h/4)`, `M ↦ z`. -/
def pairQJetEmbed : Coeff →+* LocPoly :=
  Polynomial.mapRingHom pairQJetInner

/-- The M-backward dilation `σ(z) = exp(-h/2) z` (`c = -1/2`). -/
def pairQJetDilation : LocDilation :=
  LocDilation.exp (-1 / 2) (by norm_num)

/-- The dilation constant of the M-backward convention is `c = -1/2`. -/
theorem pairQJetDilation_c : pairQJetDilation.c = -1 / 2 :=
  LocDilation.exp_c _ _

/-- The backward row of `P = ∑_k a_k L^k` of order `d`: `L^(-d) P = ∑_k σ^d(a_k) u^(d-k)`,
`u = L⁻¹`, with coefficients embedded by `t ↦ -exp(h/4)`, `M ↦ z`. -/
def pairQJetRow (P : RecOp) : LocOp :=
  reflect P.natDegree (P.map ((pairQJetDilation.shiftHom ^ P.natDegree).comp pairQJetEmbed))

/-- The symbol `P(-1, M, L)` with complex coefficients. -/
def pairQJetSymbol (P : RecOp) : ℂ[X][X] :=
  (specialize P).map (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- The `t`-jet `∂_t P(-1, M, L)` with complex coefficients. -/
def pairQJetJet (P : RecOp) : ℂ[X][X] :=
  (specializeJet P).map (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- `t² = exp(h/2)` is inverse to the multiplier `exp(-h/2)` of `σ`. -/
theorem pairQJetT_sq_mul_Q :
    pairQJetT ^ 2 * (pairQJetDilation.Q : PowerSeries ℂ) = 1 := by
  rw [pairQJetT, neg_sq, sq, pairQJetDilation, LocDilation.exp, IsUnit.unit_spec,
    PowerSeries.exp_mul_exp_eq_exp_add, PowerSeries.exp_mul_exp_eq_exp_add]
  norm_num

/-- Intertwining: `σ(ι(τ a)) = ι(a)`, i.e. `u = L⁻¹` acts by `σ = τ⁻¹`. -/
theorem pairQJetDilation_shift_embed_coeffShift (a : Coeff) :
    pairQJetDilation.shift (pairQJetEmbed (coeffShift a)) = pairQJetEmbed a := by
  change ((a.comp (C (X ^ 2) * X)).map pairQJetInner).comp _ = a.map pairQJetInner
  rw [Polynomial.map_comp, Polynomial.map_mul, map_C, map_X, comp_assoc, mul_comp, C_comp, X_comp,
    ← mul_assoc, ← C_mul]
  have h : (pairQJetInner (X ^ 2) : PowerSeries ℂ) * (pairQJetDilation.Q : PowerSeries ℂ) = 1 := by
    rw [map_pow]
    simpa [pairQJetInner] using pairQJetT_sq_mul_Q
  rw [h, C_1, one_mul, comp_X]

/-- The constant term of `exp(a h)` is `1`. -/
private theorem constantCoeff_rescale_exp_pairQ (a : ℂ) :
    PowerSeries.constantCoeff (PowerSeries.rescale a (PowerSeries.exp ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]
  simp

/-- The constant term of `a(-exp(h/4))` is `a(-1)`. -/
private theorem constantCoeff_comp_pairQJetInner :
    PowerSeries.constantCoeff.comp pairQJetInner =
      (Int.castRingHom ℂ).comp (Polynomial.evalRingHom (-1)) := by
  refine Polynomial.ringHom_ext (fun a ↦ by simp) ?_
  simp [pairQJetInner, pairQJetT, constantCoeff_rescale_exp_pairQ]

/-- The `h`-coefficient of `a(-exp(h/4))` is `-a'(-1)/4`. -/
private theorem coeff_one_pairQJetInner (a : ℤ[X]) :
    PowerSeries.coeff 1 (pairQJetInner a) = -(1 / 4) * (((derivative a).eval (-1) : ℤ) : ℂ) := by
  induction a using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, derivative_add, eval_add, Int.cast_add]; ring
  | monomial n c =>
    have hT1 : PowerSeries.coeff 1 pairQJetT = -(1 / 4) := by
      simp [pairQJetT, PowerSeries.coeff_rescale]
    have hT0 : PowerSeries.constantCoeff pairQJetT = -1 := by
      simp [pairQJetT, constantCoeff_rescale_exp_pairQ]
    rw [pairQJetInner, coe_eval₂RingHom, eval₂_monomial, eq_intCast,
      ← map_intCast (PowerSeries.C (R := ℂ)),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_one_pow, hT1, hT0, derivative_monomial,
      eval_monomial]
    push_cast
    ring

/-- The reduction of an embedded coefficient is its value at `t = -1`. -/
theorem locJet0_pairQJetEmbed (a : Coeff) :
    locJet0 (pairQJetEmbed a) = (a.map (Polynomial.evalRingHom (-1))).map (Int.castRingHom ℂ) := by
  rw [locJet0, pairQJetEmbed, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map,
    constantCoeff_comp_pairQJetInner, Polynomial.map_map]

/-- The first jet of an embedded coefficient is `-1/4` times its `t`-jet at `t = -1`. -/
theorem locJet1_pairQJetEmbed (a : Coeff) :
    locJet1 (pairQJetEmbed a) = C (-(1 / 4) : ℂ) * (coeffJet a).map (Int.castRingHom ℂ) := by
  ext n
  rw [coeff_locJet1, coeff_C_mul, coeff_map, pairQJetEmbed, coe_mapRingHom, coeff_map,
    coeff_one_pairQJetInner, coeffJet, Polynomial.sum_def, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h]; simp

/-- The coefficients of the inner derivative. -/
theorem coeff_innerDerivative_pairQ {A : Type*} [CommSemiring A] (p : A[X][X]) (k : ℕ) :
    (innerDerivative p).coeff k = derivative (p.coeff k) := by
  unfold innerDerivative
  rw [Polynomial.sum_def, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, derivative_zero]

/-- The residual symbol of the backward row is the reversal of `P(-1, M, L)`. -/
theorem opJet0_pairQJetRow (P : RecOp) :
    opJet0 (pairQJetRow P) = reflect P.natDegree (pairQJetSymbol P) := by
  rw [opJet0, pairQJetRow, ← reflect_map, Polynomial.map_map, pairQJetSymbol, specialize,
    coe_mapRingHom, Polynomial.map_map]
  have h : locJet0.comp ((pairQJetDilation.shiftHom ^ P.natDegree).comp pairQJetEmbed) =
      (Polynomial.mapRingHom (Int.castRingHom ℂ)).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom (-1))) := by
    refine RingHom.ext fun a ↦ ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_pow, locJet0_shift,
      locJet0_pairQJetEmbed]
    rfl
  rw [h]

/-- The first jet of the backward row is the reversal of `-(1/4) P₁ - (d/2) z ∂_z P₀`. -/
theorem opJet1_pairQJetRow (P : RecOp) :
    opJet1 (pairQJetRow P) = reflect P.natDegree
      (C (C (-(1 / 4) : ℂ)) * pairQJetJet P +
        C (C (-(P.natDegree : ℂ) / 2) * X) * innerDerivative (pairQJetSymbol P)) := by
  ext i : 2
  rw [coeff_opJet1, pairQJetRow, coeff_reflect, coeff_reflect, coeff_map, RingHom.comp_apply,
    RingHom.coe_pow, locJet1_shift, locJet1_pairQJetEmbed, locJet0_pairQJetEmbed, coeff_add,
    coeff_C_mul, coeff_C_mul, pairQJetJet, coeff_map, coeff_specializeJet, pairQJetDilation_c]
  rw [coeff_innerDerivative_pairQ, pairQJetSymbol, coeff_map, coeff_specialize,
    show ((P.natDegree : ℂ) * (-1 / 2)) = -(P.natDegree : ℂ) / 2 by ring, mul_assoc]
  rfl

end AJConjecture
