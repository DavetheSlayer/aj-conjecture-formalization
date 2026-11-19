import Mathlib
import AJConjecture.QAlgDualJetBasic
import AJTwist.Factor.TwFBasisJet
import AJTwist.Factor.TwFCramerJet
import AJTwist.Factor.TwFSymbolHessian
import AJTwist.Factor.TwFSymbolMixed

/-!
# The Weyl symbol of the operator of a target at a double point of the target (TwF, crux, generic)

Source: revision 5, Section 5.2, eq. (physical-basis-jet), (physical-derivatives),
(physical-indices): at a simple mixed node the two indices are `-(κ - s_G)/(s_H - s_G)` and
`-(κ - s_H)/(s_G - s_H)`; they are both `-1/2` exactly when `κ = (s_G + s_H)/2`.

In the library's language the two indices are `-1/2` exactly when the Weyl subprincipal symbol
`P₁ + (L ∂_L)(M ∂_M) P₀` vanishes at the node
(`toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision`). This file computes it for the
operator `twCramerOp d T` of **any** target in **any** window, at any double point `(x₀, J₀)` of
the target `p = T|_{q=1}` (`p = ∂_J p = ∂_x p = 0`), with `x₀ = m₀²`, `l₀ = (1 - x₀J₀)/(J₀ - x₀)`:

`γ (x₀² - 1) · W(m₀, l₀) = det|_{q=1}(x₀) · (h₁ (x₀² - 1) - 2 x₀ (1 - x₀J₀)(x₀ - J₀) ∂_x∂_J p)`,

where `h₁ ε` is the value of the target at `t = -1 + ε` (`q = 1 - 4ε`, `x = (1 - 4dε) x₀`,
`J = J₀`). The second derivative `∂_J² p` drops out: its coefficient is
`c (1 - x₀J₀)(J₀ - x₀) + 2 x₀ (1 - J₀²) = 0` for the basis-jet constant
`c = famBasisJetC x₀ J₀ = 2 x₀ (1 - J₀²)/((x₀ - J₀)(1 - x₀J₀))`. In the paper's notation this is
`Ḣ/f_* = -(A_*/(2 D_*)) x ∂_x ∂_J p` ⟺ `κ = (s_G + s_H)/2`: the terms `ρ D_u² p` cancel.

So at each node the vanishing of the Weyl symbol is the single identity
`h₁ (x₀² - 1) = 2 x₀ (1 - x₀J₀)(x₀ - J₀) ∂_x∂_J p` between the first quantum jet of the target and
the mixed classical derivative, in the coordinates `(x, J)` where both are short
(`evalIntPoint_weylSymbol_twCramerOp_eq_zero`). This replaces the certificate identities in the
coordinates `(M, L)` of `AJFamily/Quantum/AbNodeCertificateIdentity.lean`,
`EbNodeCertificateIdentity.lean`.

Route: `evalEval_twBasisPoly_dual_node` (basis jets), then
`evalIntPoint_specializeJet_twCramerOp_of_jets` (its hypotheses `h0`, `h1` from
`evalIntPoint_specialize_twCramerOp_node`, `evalIntPoint_derivative_specialize_twCramerOp_node`),
then `evalIntPoint_derivative_derivative_specialize_twCramerOp_node`,
`evalIntPoint_eulerEuler_specialize_twCramerOp_node`, `weylSymbol`, `evalIntPoint_add`, and one
`field_simp`/`linear_combination` (unfold `famBasisJetC`, `famNodeL`).

Checked: the displayed formula at random points for random targets with a double point,
`d = 2, …, 6` (scratch `check_generic_cert.py`); for the targets of `P_a`, `-7 ≤ a ≤ 7`, `a ≠ 0`,
at both nodes, where both sides vanish (scratch `check_weyl.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first component, as a ring homomorphism from the dual numbers. -/
private def dualFstHomTwfWeyl : DualNumber ℂ →+* ℂ :=
  (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

/-- The first component of the value at `t = -1 + ε` is the value at `t = -1`. -/
private theorem dualFstHomTwfWeyl_comp_dualJetHom :
    dualFstHomTwfWeyl.comp dualJetHom =
      (Int.castRingHom ℂ).comp (Polynomial.evalRingHom (-1 : ℤ)) := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [dualFstHomTwfWeyl, dualJetHom]

/-- The first component of the target at `t = -1 + ε` is the target at `t = -1`. -/
private theorem fst_evalEval_map_dualJetHom_TwfWeyl (d : ℕ) (T : ℤ[X][X][X]) (m₀ J₀ : ℂ) :
    ((T.map (Polynomial.mapRingHom dualJetHom)).evalEval (twDualX d m₀)
      (TrivSqZeroExt.inl J₀)).fst = evalIntPoint (twfTargetOne T) (m₀ ^ 2) J₀ := by
  have hx : dualFstHomTwfWeyl (twDualX d m₀) = m₀ ^ 2 := by
    simp [dualFstHomTwfWeyl, twDualX]
  have hJ : dualFstHomTwfWeyl (TrivSqZeroExt.inl J₀) = J₀ := rfl
  have h := map_mapRingHom_evalEval dualFstHomTwfWeyl (T.map (Polynomial.mapRingHom dualJetHom))
    (twDualX d m₀) (TrivSqZeroExt.inl J₀)
  rw [hx, hJ, Polynomial.map_map, mapRingHom_comp, dualFstHomTwfWeyl_comp_dualJetHom] at h
  rw [evalIntPoint, evalPoint, eval₂_evalRingHom, twfTargetOne, Polynomial.map_map,
    mapRingHom_comp, h]
  rfl

/-- The second derivative in `J` of the target drops out of the Weyl symbol: the combination of
the three second-order identities. -/
private theorem weyl_combination_TwfWeyl {x J γ det h₁ c l P₁ D2 EE pJJ pxJ : ℂ}
    (hl : l * (J - x) = 1 - x * J)
    (hc : c * ((x - J) * (1 - x * J)) = 2 * J * (1 - x * J) + 2 * (x - J))
    (E3 : γ * (P₁ + c * l ^ 2 * D2) = det * h₁)
    (E4 : γ * (x ^ 2 - 1) ^ 2 * D2 = det * (J - x) ^ 4 * pJJ)
    (E5 : γ * (x ^ 2 - 1) ^ 2 * EE =
      2 * x * det * ((1 - x * J) * (J - x)) * ((x ^ 2 - 1) * pxJ - (1 - J ^ 2) * pJJ)) :
    (x ^ 2 - 1) * (γ * (x ^ 2 - 1) * (P₁ + EE)) =
      (x ^ 2 - 1) * (det * (h₁ * (x ^ 2 - 1) - 2 * x * ((1 - x * J) * (x - J)) * pxJ)) := by
  linear_combination (x ^ 2 - 1) ^ 2 * E3 - c * l ^ 2 * E4 + E5 -
    det * pJJ * c * (J - x) ^ 2 * (l * (J - x) + (1 - x * J)) * hl +
    det * pJJ * (1 - x * J) * (J - x) * hc

/-- The Weyl subprincipal symbol of the operator of a target at a double point of the target. -/
theorem evalIntPoint_weylSymbol_twCramerOp_mul (d : ℕ) (T : ℤ[X][X][X]) (hT : T.natDegree ≤ d)
    {m₀ J₀ h₁ : ℂ} (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ -1) (hJ : m₀ ^ 2 ≠ J₀)
    (hJ' : m₀ ^ 2 * J₀ ≠ 1)
    (hpJ : evalIntPoint (derivative (twfTargetOne T)) (m₀ ^ 2) J₀ = 0)
    (hpx : evalIntPoint (coeffDerivative (twfTargetOne T)) (m₀ ^ 2) J₀ = 0)
    (htarget : (T.map (Polynomial.mapRingHom dualJetHom)).evalEval (twDualX d m₀)
      (TrivSqZeroExt.inl J₀) = TrivSqZeroExt.inl h₁ * DualNumber.eps) :
    twBasisGamma d (m₀ ^ 2) J₀ * ((m₀ ^ 2) ^ 2 - 1) *
        evalIntPoint (weylSymbol (twCramerOp d T)) m₀ (famNodeL (m₀ ^ 2) J₀) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
        (h₁ * ((m₀ ^ 2) ^ 2 - 1) -
          2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * J₀) * (m₀ ^ 2 - J₀)) *
            evalIntPoint (derivative (coeffDerivative (twfTargetOne T))) (m₀ ^ 2) J₀) := by
  have hp : evalIntPoint (twfTargetOne T) (m₀ ^ 2) J₀ = 0 := by
    rw [← fst_evalEval_map_dualJetHom_TwfWeyl d, htarget]
    simp
  have hx : (m₀ ^ 2) ^ 2 - 1 ≠ 0 := by
    have hf : (m₀ ^ 2) ^ 2 - 1 = (m₀ ^ 2 - 1) * (m₀ ^ 2 + 1) := by ring
    rw [hf]
    exact mul_ne_zero (sub_ne_zero.mpr h1) fun h0 ↦ h2 (eq_neg_of_add_eq_zero_left h0)
  have hγ : twBasisGamma d (m₀ ^ 2) J₀ ≠ 0 := twBasisGamma_ne_zero d h1 hJ
  have hJx : J₀ - m₀ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hJ)
  have hxJ : m₀ ^ 2 - J₀ ≠ 0 := sub_ne_zero.mpr hJ
  have hN : 1 - m₀ ^ 2 * J₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hJ')
  have h0 : evalIntPoint (specialize (twCramerOp d T)) m₀ (famNodeL (m₀ ^ 2) J₀) = 0 := by
    have h := evalIntPoint_specialize_twCramerOp_node d T hT hJ
    rw [hp, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hγ
  have h1' : evalIntPoint (derivative (specialize (twCramerOp d T))) m₀
      (famNodeL (m₀ ^ 2) J₀) = 0 := by
    have h := evalIntPoint_derivative_specialize_twCramerOp_node d T hT hJ hp
    rw [hpJ, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hγ hx)
  obtain ⟨a, b, hbasis⟩ := evalEval_twBasisPoly_dual_node d h1 hJ hJ'
  have E3 := evalIntPoint_specializeJet_twCramerOp_of_jets d T hT hbasis htarget h0 h1'
  have E4 := evalIntPoint_derivative_derivative_specialize_twCramerOp_node d T hT hJ hp hpJ
  have E5 := evalIntPoint_eulerEuler_specialize_twCramerOp_node d T hT hJ hp hpJ hpx
  have hl : famNodeL (m₀ ^ 2) J₀ * (J₀ - m₀ ^ 2) = 1 - m₀ ^ 2 * J₀ := by
    rw [famNodeL, div_mul_cancel₀ _ hJx]
  have hc : famBasisJetC (m₀ ^ 2) J₀ * ((m₀ ^ 2 - J₀) * (1 - m₀ ^ 2 * J₀)) =
      2 * J₀ * (1 - m₀ ^ 2 * J₀) + 2 * (m₀ ^ 2 - J₀) := by
    have hN' : 1 - J₀ * m₀ ^ 2 ≠ 0 := by rwa [mul_comm]
    rw [famBasisJetC]
    field_simp
  rw [weylSymbol, evalIntPoint_add]
  exact mul_left_cancel₀ hx (weyl_combination_TwfWeyl hl hc E3 E4 E5)

/-- The Weyl subprincipal symbol of the operator of a target vanishes at a double point of the
target where the first quantum jet of the target is the mixed classical derivative. -/
theorem evalIntPoint_weylSymbol_twCramerOp_eq_zero (d : ℕ) (T : ℤ[X][X][X])
    (hT : T.natDegree ≤ d) {m₀ J₀ h₁ : ℂ} (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ -1)
    (hJ : m₀ ^ 2 ≠ J₀) (hJ' : m₀ ^ 2 * J₀ ≠ 1)
    (hpJ : evalIntPoint (derivative (twfTargetOne T)) (m₀ ^ 2) J₀ = 0)
    (hpx : evalIntPoint (coeffDerivative (twfTargetOne T)) (m₀ ^ 2) J₀ = 0)
    (htarget : (T.map (Polynomial.mapRingHom dualJetHom)).evalEval (twDualX d m₀)
      (TrivSqZeroExt.inl J₀) = TrivSqZeroExt.inl h₁ * DualNumber.eps)
    (hcert : h₁ * ((m₀ ^ 2) ^ 2 - 1) =
      2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * J₀) * (m₀ ^ 2 - J₀)) *
        evalIntPoint (derivative (coeffDerivative (twfTargetOne T))) (m₀ ^ 2) J₀) :
    evalIntPoint (weylSymbol (twCramerOp d T)) m₀ (famNodeL (m₀ ^ 2) J₀) = 0 := by
  have h := evalIntPoint_weylSymbol_twCramerOp_mul d T hT h1 h2 hJ hJ' hpJ hpx htarget
  rw [hcert, sub_self, mul_zero] at h
  have hx : (m₀ ^ 2) ^ 2 - 1 ≠ 0 := by
    have hf : (m₀ ^ 2) ^ 2 - 1 = (m₀ ^ 2 - 1) * (m₀ ^ 2 + 1) := by ring
    rw [hf]
    exact mul_ne_zero (sub_ne_zero.mpr h1) fun h0 ↦ h2 (eq_neg_of_add_eq_zero_left h0)
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (twBasisGamma_ne_zero d h1 hJ) hx)

end AJConjecture
