import Mathlib
import AJFamily.Quantum.EbNodeCertificateIdentity
import AJFamily.Quantum.FamBasisNodeJet
import AJFamily.Quantum.FamNodeCertificateWeyl
import AJFamily.Quantum.FamTargetNodeJet

/-!
# E/B node: the Weyl symbol vanishes

`evalIntPoint_weylSymbol_famTransferOp_ebNode`, from
`evalIntPoint_weylSymbol_famTransferOp_of_certificate` and `ebNode_certificate_identity`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The Weyl subprincipal symbol of the family transfer operator vanishes at the E/B node
`(m₀, ebNodeL m m₀)`. -/
theorem evalIntPoint_weylSymbol_famTransferOp_ebNode (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (heb : (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0) :
    evalIntPoint (weylSymbol (famTransferOp m)) m₀ (ebNodeL m m₀) = 0 := by
  obtain ⟨-, h1, h2, h3, h4, -, -, hE, hB, -, -, -⟩ := ebNode_facts m hm heb
  have hbasis := fun i ↦ evalEval_famBasisPoly_dual_node m (J₀ := ebNodeJ m) h1 h3 h4 i
  have hs0 : 2 * (m : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : 2 * m + 1 ≠ 0)
  have hw : 2 * -(m₀ ^ 2) = famJetZeta m (1 : ℂ) (m₀ ^ 2) (ebNodeJ m) := by
    simp only [famJetZeta, ebNodeJ, one_pow, one_mul]
    field_simp
    linear_combination (-4 : ℂ) * heb
  have htarget := evalEval_famTarget_dual_node m hm hw (by ring) (by ring)
  have hκ : (m₀ ^ 2 - 1) ^ (2 * m + 3) * ((m₀ ^ 2) ^ 2 - 1) ^ (2 * m + 3) ≠ 0 := by
    have h3' : (m₀ ^ 2) ^ 2 - 1 ≠ 0 := by
      have : (m₀ ^ 2) ^ 2 - 1 = (m₀ ^ 2 - 1) * (m₀ ^ 2 + 1) := by ring
      rw [this]
      exact mul_ne_zero (sub_ne_zero.mpr h1) (by
        intro h; exact h2 (eq_neg_of_add_eq_zero_left h))
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h1)) (pow_ne_zero _ h3')
  have hγ : famBasisGamma m (m₀ ^ 2) (ebNodeJ m) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (sub_ne_zero.mpr (Ne.symm h1)) (sub_ne_zero.mpr h3))
  exact evalIntPoint_weylSymbol_famTransferOp_of_certificate m (by omega)
    (G := extraFactor) (D := twistPoly m) (T := X - 1) (by ring) hγ hκ hE hB hbasis htarget
    (ebNode_certificate_identity m hm heb)

end AJConjecture
