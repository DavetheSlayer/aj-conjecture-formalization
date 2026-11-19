import Mathlib
import AJFamily.Quantum.AbNodeCertificateIdentity
import AJFamily.Quantum.AbNodeFacts
import AJFamily.Quantum.FamBasisNodeJet
import AJFamily.Quantum.FamNodeCertificateWeyl
import AJFamily.Quantum.FamTargetNodeJet

/-!
# Abelian node: the Weyl symbol vanishes

`evalIntPoint_weylSymbol_famTransferOp_abNode`, from
`evalIntPoint_weylSymbol_famTransferOp_of_certificate` and `abNode_certificate_identity`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `(L - 1)(m, l) = l - 1`. -/
theorem evalIntPoint_X_sub_one (m l : ℂ) :
    evalIntPoint (X - 1) m l = l - 1 := by
  simp [evalIntPoint, evalPoint]

/-- The Weyl subprincipal symbol of the family transfer operator vanishes at the abelian node
`(m₀, 1)`, where `m (m₀²)² - (2m + 1) m₀² + m = 0`. -/
theorem evalIntPoint_weylSymbol_famTransferOp_abNode (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) :
    evalIntPoint (weylSymbol (famTransferOp m)) m₀ 1 = 0 := by
  obtain ⟨_, h1, h2, hB, -, -, -⟩ := abNode_facts m hm hab
  have hx1 : (1 : ℂ) - m₀ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hL : famNodeL (m₀ ^ 2) 1 = 1 := by
    rw [famNodeL, mul_one]
    exact div_self hx1
  have hbasis := fun i ↦ evalEval_famBasisPoly_dual_node m (J₀ := 1) h1 h1
    (by rwa [mul_one]) i
  simp only [hL] at hbasis
  have hw : 2 * m₀ ^ 2 = famJetZeta m (1 : ℂ) (m₀ ^ 2) 1 := by
    simp only [famJetZeta, one_pow, one_mul, mul_one]
    ring
  have htarget := evalEval_famTarget_dual_node m hm hw rfl (by ring)
  have hκ : (m₀ ^ 2 - 1) ^ (2 * m + 3) * ((m₀ ^ 2) ^ 2 - 1) ^ (2 * m + 3) ≠ 0 := by
    have h3 : (m₀ ^ 2) ^ 2 - 1 ≠ 0 := by
      have : (m₀ ^ 2) ^ 2 - 1 = (m₀ ^ 2 - 1) * (m₀ ^ 2 + 1) := by ring
      rw [this]
      exact mul_ne_zero (sub_ne_zero.mpr h1) (by
        intro h; exact h2 (eq_neg_of_add_eq_zero_left h))
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h1)) (pow_ne_zero _ h3)
  have hγ : famBasisGamma m (m₀ ^ 2) 1 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero hx1 (sub_ne_zero.mpr h1))
  exact evalIntPoint_weylSymbol_famTransferOp_of_certificate m (by omega)
    (G := X - 1) (D := twistPoly m) (T := extraFactor) (by ring) hγ hκ
    (by rw [evalIntPoint_X_sub_one, sub_self]) hB hbasis htarget
    (abNode_certificate_identity m hm hab)

end AJConjecture
