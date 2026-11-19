import Mathlib
import AJConjecture.QAlgDualNumeral
import AJFamily.Quantum.FamTargetJetValue
import AJFamily.Quantum.LucasDoublePoint
import AJFamily.Quantum.NodeClosedForms

/-!
# First-order jet of the target polynomial at a node

`evalEval_famTarget_dual_node`: at `q = 1 - 4ε`, `x = famDualX m m₀`, `J = J₀`, where `ζ` has the
double point `2w`, the family target polynomial is `famTargetJet m x₀ J₀ w · ε`. It serves both
nodes (`w = ±x₀`).
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The first component of `dualQ` is `1`. -/
private theorem fst_dualQ_famNode : dualQ.fst = 1 := by
  simp [dualQ]

/-- The second component of `dualQ` is `-4`. -/
private theorem snd_dualQ_famNode : dualQ.snd = -4 := by
  simp [dualQ, fst_ofNat_dual, snd_ofNat_dual]

/-- The first component of `famDualX m m₀` is `m₀²`. -/
private theorem fst_famDualX_famNode (m : ℕ) (m₀ : ℂ) : (famDualX m m₀).fst = m₀ ^ 2 := by
  simp [famDualX]

/-- The second component of `famDualX m m₀` is `-4(2m+3)m₀²`. -/
private theorem snd_famDualX_famNode (m : ℕ) (m₀ : ℂ) :
    (famDualX m m₀).snd = -4 * (2 * m + 3) * m₀ ^ 2 := by
  simp [famDualX, fst_ofNat_dual]

/-- The parameter `ζ` at `q = dualQ`, `x = famDualX m m₀`, `j = J₀`. -/
private theorem famJetZeta_dual_famNode (m : ℕ) (m₀ J₀ : ℂ) :
    famJetZeta m dualQ (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl (famJetZeta m 1 (m₀ ^ 2) J₀) +
        TrivSqZeroExt.inl (-8 * (2 * m + 3) * (m₀ ^ 2) ^ 2 - 4 * (2 * m + 3) * (1 + m₀ ^ 2) -
          4 * (2 * m + 3) * m₀ ^ 2 +
          J₀ * (-8 * (2 * m + 3) * m₀ ^ 2 + 4 * ((2 * m + 3) + 1) + 4 * m₀ ^ 2 * (1 + m₀ ^ 2) +
            4 * (2 * m + 3) * m₀ ^ 2 * (1 + m₀ ^ 2) + 4 * (2 * m + 3) * (m₀ ^ 2) ^ 2) -
          (8 + 4 * (2 * m + 3)) * m₀ ^ 2 * J₀ ^ 2) * DualNumber.eps := by
  ext
  · simp [famJetZeta, fst_dualQ_famNode, fst_famDualX_famNode]
  · simp [famJetZeta, fst_dualQ_famNode, fst_famDualX_famNode, snd_dualQ_famNode,
      snd_famDualX_famNode]
    ring

/-- The parameter `s` at `q = dualQ`, `x = famDualX m m₀`. -/
private theorem famJetS_dual_famNode (m : ℕ) {m₀ w : ℂ} (hw2 : w ^ 2 = (m₀ ^ 2) ^ 2) :
    dualQ ^ (4 * m + 5) * famDualX m m₀ ^ 2 =
      TrivSqZeroExt.inl (w ^ 2) +
        TrivSqZeroExt.inl (-(16 * (2 * m + 3) - 4) * (m₀ ^ 2) ^ 2) * DualNumber.eps := by
  ext
  · simp [fst_dualQ_famNode, fst_famDualX_famNode, hw2]
  · simp [fst_dualQ_famNode, fst_famDualX_famNode, snd_dualQ_famNode,
      snd_famDualX_famNode]
    ring

/-- At `t = -1 + ε`, at a node with double point `ζ₀ = 2w` and vanishing value, the family
target polynomial is `ε · famTargetJet`. -/
theorem evalEval_famTarget_dual_node (m : ℕ) (hm : 2 ≤ m) {m₀ J₀ w : ℂ}
    (hw : 2 * w = famJetZeta m (1 : ℂ) (m₀ ^ 2) J₀) (hw2 : w ^ 2 = (m₀ ^ 2) ^ 2)
    (hval : (m₀ ^ 2) ^ 2 + m₀ ^ 2 * (1 - J₀) * w - J₀ * w ^ 2 = 0) :
    (famTarget m dualQ).evalEval (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl (famTargetJet m (m₀ ^ 2) J₀ w) * DualNumber.eps := by
  rw [evalEval_famTarget_of_sq_eq_zero one_sub_dualQ_sq, famTargetJetValue]
  simp only [famChebJetValue, famJetZeta_dual_famNode, famJetS_dual_famNode m hw2, ← hw,
    transferLucas_dual_double]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  ext
  · simp [fst_dualQ_famNode, fst_famDualX_famNode]
    linear_combination 2 * w ^ (n + 1) * hval
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_neg, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.snd_neg]
    simp only [fst_transferLucasDeriv_dual_double, fst_transferLucasHasse_dual_double]
    simp [famTargetJet, famJetCubic, famJetZetaDeriv, fst_dualQ_famNode, fst_famDualX_famNode,
      snd_dualQ_famNode, snd_famDualX_famNode, fst_ofNat_dual]
    ring

end AJConjecture
