import Mathlib
import AJTwist.Quantum.TwQTransferOp
import AJTwist.Quantum.TwQSymbolFacts
import AJTwist.Factor.TwFWeylCertificate

/-!
# The Weyl certificate for the operators `P_a` (TwF, generic)

The generic certificate `evalIntPoint_weylSymbol_twCramerOp_eq_zero` specialised to
`twTransferOp a = twCramerOp (twWindow a) (twTarget a t⁴)`: the target at `q = 1` is
`twTarget a (1 : ℤ)` and at `t = -1 + ε` it is `twTarget a dualQ`. For `a = m ≥ 1` this is the
library's `famTransferOp m` (`twTransferOp_natCast`) with `twTarget m = famTarget m`; for `a = -b`
the target is `twNegTarget b`.

At a double point `(x₀, J₀) = (m₀², J₀)` of `p = twTarget a 1` the Weyl subprincipal symbol of
`P_a` at `(m₀, l₀)`, `l₀ = (1 - x₀J₀)/(J₀ - x₀)`, vanishes as soon as
`h₁ (x₀² - 1) = 2 x₀ (1 - x₀J₀)(x₀ - J₀) ∂_x∂_J p`, where `h₁ ε` is the value of the target at
`t = -1 + ε`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value of `q = t⁴` at `t = -1 + ε` is `1 - 4ε`. -/
theorem twf_dualJetHom_X_pow_four : dualJetHom (X ^ 4) = dualQ := by
  rw [map_pow, dualJetHom, coe_eval₂RingHom, eval₂_X, dualQ,
    show (4 : DualNumber ℂ) = TrivSqZeroExt.inl 4 from rfl]
  ext
  · simp
    norm_num
  · simp [TrivSqZeroExt.snd_pow]
    norm_num

/-- The target of `P_a` at `t = -1` is the cleared numerator at `q = 1`. -/
theorem twfTargetOne_twTarget (a : ℤ) :
    twfTargetOne (twTarget a (X ^ 4 : ℤ[X])) = twTarget a (1 : ℤ) := by
  rw [twfTargetOne, map_twTarget]
  simp

/-- The target of `P_a` at `t = -1 + ε` is the cleared numerator at `q = 1 - 4ε`. -/
theorem map_dualJetHom_twTarget (a : ℤ) :
    (twTarget a (X ^ 4 : ℤ[X])).map (Polynomial.mapRingHom dualJetHom) = twTarget a dualQ := by
  rw [map_twTarget, twf_dualJetHom_X_pow_four]

/-- The Weyl subprincipal symbol of `P_a` vanishes at a double point of its target where the
first quantum jet of the target is the mixed classical derivative. -/
theorem evalIntPoint_weylSymbol_twTransferOp_eq_zero (a : ℤ) {m₀ J₀ h₁ : ℂ}
    (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ -1) (hJ : m₀ ^ 2 ≠ J₀) (hJ' : m₀ ^ 2 * J₀ ≠ 1)
    (hpJ : evalIntPoint (derivative (twTarget a (1 : ℤ))) (m₀ ^ 2) J₀ = 0)
    (hpx : evalIntPoint (coeffDerivative (twTarget a (1 : ℤ))) (m₀ ^ 2) J₀ = 0)
    (htarget : (twTarget a dualQ).evalEval (twDualX (twWindow a) m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl h₁ * DualNumber.eps)
    (hcert : h₁ * ((m₀ ^ 2) ^ 2 - 1) =
      2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * J₀) * (m₀ ^ 2 - J₀)) *
        evalIntPoint (derivative (coeffDerivative (twTarget a (1 : ℤ)))) (m₀ ^ 2) J₀) :
    evalIntPoint (weylSymbol (twTransferOp a)) m₀ (famNodeL (m₀ ^ 2) J₀) = 0 := by
  have hT := twfTargetOne_twTarget a
  have hD := map_dualJetHom_twTarget a
  have key := evalIntPoint_weylSymbol_twCramerOp_eq_zero (h₁ := h₁) (m₀ := m₀) (J₀ := J₀)
    (twWindow a) (twTarget a (X ^ 4 : ℤ[X])) (natDegree_twTarget_le a _) h1 h2 hJ hJ'
  rw [hT, hD] at key
  exact key hpJ hpx htarget hcert

end AJConjecture
