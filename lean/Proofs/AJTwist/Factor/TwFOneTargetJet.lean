import Mathlib
import AJFamily.Quantum.FamTargetNodeJet
import AJFamily.Quantum.FamTargetAtOne
import AJFamily.Quantum.EbNodeFacts
import AJTwist.Factor.TwFTargetBridge

/-!
# The target of `P_1` at its two nodes (TwF, unit F3)

Source: revision 5, Section 5.3 (`operators.tex`): "In particular at `a = 1` the derivative
product is `160/351`, the raw jet divided by `f_*` is `106/351`, and the same simple crossing
binds `E` to `B_1`"; Section 5.5: "The raw jet is `2 (1 - x₀)^(-5)` by the abelian crossing
calculation, where `ρ = 0` also at `a = 1`."

* `evalEval_famTarget_one_dual_node`: the library's `evalEval_famTarget_dual_node` (stated for
  `m ≥ 2`) holds for `m = 1` with the same closed form `famTargetJet 1`: the truncated exponents
  `m - 1 - 1`, `m - 1 - 2` occur with vanishing coefficients. Route: `famTarget 1` is explicit
  (`famCheb 1 q 0 n = 2 n`): `evalEval_famTarget_of_sq_eq_zero`, `transferLucas_dual_double`,
  `fst_transferLucasDeriv_dual_double`, `fst_transferLucasHasse_dual_double` at `k = 0, 1, 2`.
* `famOne_ebNode_cert`, `famOne_abNode_cert`: the certificate identities
  `h₁ (x₀² - 1) = 2 x₀ (1 - x₀J₀)(x₀ - J₀) ∂_x∂_J p` of
  `evalIntPoint_weylSymbol_twTransferOp_eq_zero` at the `E/B_1` node
  (`3 x₀² + 7 x₀ + 3 = 0`, `J₀ = -1/3`, `w = -x₀`) and at the degenerate
  abelian node (`x₀² - 3 x₀ + 1 = 0`, `J₀ = 1`, `w = x₀`), for
  `p = famTarget 1 1 = (1 - J)(ζ + 2x) T̂_1` (`famTarget_one_eq`),
  `T̂_1 = x J² - (x² - x + 1) J + x`. At the abelian node `∂_x∂_J p = -4 x₀ (3 - 2 x₀)` and
  `h₁ = -8 x₀²` on the node quadratic (the paper's raw jet `2`); everything is an explicit
  polynomial identity modulo the node quadratic.

Checked against the dual-number evaluation of the definitions (scratch `check_target_jet.py`,
`check_weyl.py`, `check_paper5.py`: the values `160/351`, `106/351`, `2` of the paper).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first component of `dualQ` is `1`. -/
private theorem fst_dualQ_twfOneTargetJet : dualQ.fst = 1 := by
  simp [dualQ]

/-- The second component of `dualQ` is `-4`. -/
private theorem snd_dualQ_twfOneTargetJet : dualQ.snd = -4 := by
  simp [dualQ, fst_ofNat_dual, snd_ofNat_dual]

/-- The first component of `famDualX m m₀` is `m₀²`. -/
private theorem fst_famDualX_twfOneTargetJet (m : ℕ) (m₀ : ℂ) :
    (famDualX m m₀).fst = m₀ ^ 2 := by
  simp [famDualX]

/-- The second component of `famDualX m m₀` is `-4(2m+3)m₀²`. -/
private theorem snd_famDualX_twfOneTargetJet (m : ℕ) (m₀ : ℂ) :
    (famDualX m m₀).snd = -4 * (2 * m + 3) * m₀ ^ 2 := by
  simp [famDualX, fst_ofNat_dual]

/-- The parameter `ζ` at `q = dualQ`, `x = famDualX m m₀`, `j = J₀`. -/
private theorem famJetZeta_dual_twfOneTargetJet (m : ℕ) (m₀ J₀ : ℂ) :
    famJetZeta m dualQ (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl (famJetZeta m 1 (m₀ ^ 2) J₀) +
        TrivSqZeroExt.inl (-8 * (2 * m + 3) * (m₀ ^ 2) ^ 2 - 4 * (2 * m + 3) * (1 + m₀ ^ 2) -
          4 * (2 * m + 3) * m₀ ^ 2 +
          J₀ * (-8 * (2 * m + 3) * m₀ ^ 2 + 4 * ((2 * m + 3) + 1) + 4 * m₀ ^ 2 * (1 + m₀ ^ 2) +
            4 * (2 * m + 3) * m₀ ^ 2 * (1 + m₀ ^ 2) + 4 * (2 * m + 3) * (m₀ ^ 2) ^ 2) -
          (8 + 4 * (2 * m + 3)) * m₀ ^ 2 * J₀ ^ 2) * DualNumber.eps := by
  ext
  · simp [famJetZeta, fst_dualQ_twfOneTargetJet, fst_famDualX_twfOneTargetJet]
  · simp [famJetZeta, fst_dualQ_twfOneTargetJet, fst_famDualX_twfOneTargetJet,
      snd_dualQ_twfOneTargetJet, snd_famDualX_twfOneTargetJet]
    ring

/-- The parameter `s` at `q = dualQ`, `x = famDualX m m₀`. -/
private theorem famJetS_dual_twfOneTargetJet (m : ℕ) {m₀ w : ℂ} (hw2 : w ^ 2 = (m₀ ^ 2) ^ 2) :
    dualQ ^ (4 * m + 5) * famDualX m m₀ ^ 2 =
      TrivSqZeroExt.inl (w ^ 2) +
        TrivSqZeroExt.inl (-(16 * (2 * m + 3) - 4) * (m₀ ^ 2) ^ 2) * DualNumber.eps := by
  ext
  · simp [fst_dualQ_twfOneTargetJet, fst_famDualX_twfOneTargetJet, hw2]
  · simp [fst_dualQ_twfOneTargetJet, fst_famDualX_twfOneTargetJet, snd_dualQ_twfOneTargetJet,
      snd_famDualX_twfOneTargetJet]
    ring

/-- The closed form of the library for the first jet of the target holds at `m = 1`. -/
theorem evalEval_famTarget_one_dual_node {m₀ J₀ w : ℂ}
    (hw : 2 * w = famJetZeta 1 (1 : ℂ) (m₀ ^ 2) J₀) (hw2 : w ^ 2 = (m₀ ^ 2) ^ 2)
    (hval : (m₀ ^ 2) ^ 2 + m₀ ^ 2 * (1 - J₀) * w - J₀ * w ^ 2 = 0) :
    (famTarget 1 dualQ).evalEval (famDualX 1 m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl (famTargetJet 1 (m₀ ^ 2) J₀ w) * DualNumber.eps := by
  rw [evalEval_famTarget_of_sq_eq_zero one_sub_dualQ_sq, famTargetJetValue]
  simp only [famChebJetValue, famJetZeta_dual_twfOneTargetJet, famJetS_dual_twfOneTargetJet 1 hw2,
    ← hw, transferLucas_dual_double]
  ext
  · simp [fst_dualQ_twfOneTargetJet, fst_famDualX_twfOneTargetJet]
    linear_combination 2 * hval
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_neg, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.snd_neg]
    simp only [fst_transferLucasDeriv_dual_double, fst_transferLucasHasse_dual_double]
    simp [famTargetJet, famJetCubic, famJetZetaDeriv, fst_dualQ_twfOneTargetJet,
      fst_famDualX_twfOneTargetJet, snd_dualQ_twfOneTargetJet, snd_famDualX_twfOneTargetJet,
      fst_ofNat_dual]
    ring

/-- The mixed derivative `∂_x∂_J p` of `p = famTarget 1 1 = (1 - J)(ζ + 2x) T̂_1`. -/
private theorem evalIntPoint_mixed_famTarget_one_twfOneTargetJet (x J : ℂ) :
    evalIntPoint (derivative (coeffDerivative (famTarget 1 (1 : ℤ)))) x J =
      -10 * J ^ 4 * x + J ^ 3 * (24 * x ^ 2 + 8) + J ^ 2 * (-12 * x ^ 3 - 18 * x ^ 2 - 30 * x - 6) +
        J * (16 * x ^ 3 + 18 * x ^ 2 + 20 * x + 6) - 4 * x ^ 3 - 12 * x ^ 2 - 4 * x - 4 := by
  have h1 : innerDerivative (1 : ℤ[X][X]) = 0 := by
    rw [← C_1, innerDerivative_C, derivative_one, C_0]
  rw [evalIntPoint_eq, famTarget_one_eq 1 le_rfl, symbolTwist, symbolZeta,
    coeffDerivative_eq_innerDerivative]
  simp only [innerDerivative_add, innerDerivative_sub, innerDerivative_mul, innerDerivative_C,
    innerDerivative_X, h1, pow_succ, pow_zero, one_mul]
  simp [evalIntHomTwistNode, derivative_mul]
  ring

/-- The certificate identity at the `E/B_1` node of `P_1`. -/
theorem famOne_ebNode_cert {m₀ : ℂ} (heb : 3 * (m₀ ^ 2) ^ 2 + 7 * m₀ ^ 2 + 3 = 0) :
    famTargetJet 1 (m₀ ^ 2) (ebNodeJ 1) (-(m₀ ^ 2)) * ((m₀ ^ 2) ^ 2 - 1) =
      2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * ebNodeJ 1) * (m₀ ^ 2 - ebNodeJ 1)) *
        evalIntPoint (derivative (coeffDerivative (famTarget 1 (1 : ℤ)))) (m₀ ^ 2)
          (ebNodeJ 1) := by
  have hJ : ebNodeJ 1 = -1 / 3 := by
    rw [ebNodeJ]
    norm_num
  rw [evalIntPoint_mixed_famTarget_one_twfOneTargetJet, hJ]
  simp only [famTargetJet, Nat.cast_one, Nat.sub_self, Nat.zero_sub, Nat.cast_zero,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.add_one_sub_one, pow_zero, pow_one]
  linear_combination (176 * (m₀ ^ 2) ^ 4 / 81 + 2056 * (m₀ ^ 2) ^ 3 / 243 +
    2528 * (m₀ ^ 2) ^ 2 / 729 + 8 * (m₀ ^ 2) / 81 + 16 / 81) * heb

/-- The certificate identity at the degenerate abelian node `K = 3` of `P_1`. -/
theorem famOne_abNode_cert {m₀ : ℂ} (hab : (m₀ ^ 2) ^ 2 - 3 * m₀ ^ 2 + 1 = 0) :
    famTargetJet 1 (m₀ ^ 2) 1 (m₀ ^ 2) * ((m₀ ^ 2) ^ 2 - 1) =
      2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * 1) * (m₀ ^ 2 - 1)) *
        evalIntPoint (derivative (coeffDerivative (famTarget 1 (1 : ℤ)))) (m₀ ^ 2) 1 := by
  rw [evalIntPoint_mixed_famTarget_one_twfOneTargetJet]
  simp only [famTargetJet, Nat.cast_one, Nat.sub_self, Nat.zero_sub, Nat.cast_zero,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.add_one_sub_one, pow_zero, pow_one]
  linear_combination (8 * (m₀ ^ 2) ^ 3 - 32 * (m₀ ^ 2) ^ 2 + 24 * (m₀ ^ 2)) * hab

end AJConjecture
