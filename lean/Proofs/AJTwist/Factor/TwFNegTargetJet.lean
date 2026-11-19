import Mathlib
import AJConjecture.QAlgDualJet
import AJConjecture.QAlgDualNumeral
import AJFamily.Quantum.LucasDoublePoint
import AJTwist.Quantum.TwQCramerSymbol
import AJTwist.Quantum.TwQTarget
import AJTwist.Factor.TwFAdjointJet

/-!
# The first jet of the target of negative index at a double point (TwF, unit F2)

Source: revision 5, Section 5.4, eq. (negative-jet):
`Ṅ_(-b) = (b/2) p + (1/2) S_(b+1) - J S_b - (1/2) J S_(b-1) + (Z/2 + α_d) p_Z
  + ω (Z_J p_{ZZ}/2 + p_{ZJ})`.

* `twNegTargetJetValue`, `evalEval_twNegTarget_of_sq_eq_zero`: when `(1 - q)² = 0` the value of
  `twNegTarget b q` at `(x, j)` is the combination of `twChebJetValue` read off the definition
  (window `d = 2b + 2`, seeds `1`, `1 - qJ`, `J`).
* `twNegTargetJet`, `evalEval_twNegTarget_dual_node`: at `t = -1 + ε` (`q = 1 - 4ε`,
  `x = (1 - 4dε) x₀`) and at a point where the Lucas recursion has the double root `w`
  (`ζ(x₀, J₀) = 2w`, `w² = x₀²`) and the target vanishes
  (`w² + x₀ w (1 - J₀) - x₀² J₀ = 0`, i.e. `w = -x₀`, or `w = x₀` and `J₀ = 1`), the target is
  `twNegTargetJet b x₀ J₀ w · ε`. The closed form uses
  `S_k = 2 w^k`, `S_k' = k² w^(k-1)`, `S_k''/2 = k²(k²-1)/12 · w^(k-2)`,
  `∂_s S_k = -k(k-1) w^(k-2)` (`transferLucas_dual_double` and its companions), the jets
  `z₁`, `s₁` of `ζ̃` and `q^(2d-1) x²`, `1 - q = 4ε`, and the prefactors
  `q^(b+1) = 1 - 4(b+1)ε`, `q^(b+d) x = x₀ (1 - (4b+8d)ε)`, `q^(b+2d) x² = x₀² (1 - (4b+16d)ε)`.
  It is the analogue of `famTargetJet` (`AJFamily/Quantum/NodeClosedForms.lean`) and of
  `evalEval_famTarget_dual_node` (`FamTargetNodeJet.lean`); truncated exponents `k - 1`, `k - 2`
  occur only with vanishing coefficients, so the statement holds for every `b ≥ 1`.

In the paper's notation `twNegTargetJet = -4 x₀^(b+1) Ṅ_(-b)` at a node.
Checked against the dual-number evaluation of the definition for `b = 1, …, 7` on both loci
(scratch `check_target_jet.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first-order value of `twNegTarget b q` at `(x, j)` (window `d = 2b + 2`). -/
def twNegTargetJetValue {R : Type*} [CommRing R] (b : ℕ) (q x j : R) : R :=
  q ^ b * (q * twChebJetValue (2 * b + 2) q x j (b + 1) 1 0 +
    q ^ (2 * b + 2) * x * twChebJetValue (2 * b + 2) q x j b (1 - q * j) (-q) -
      (q ^ (2 * b + 2) * x) ^ 2 * twChebJetValue (2 * b + 2) q x j (b - 1) j 1)

/-- If `(1 - q)² = 0`, the value of `twNegTarget b q` at `(x, j)` is `twNegTargetJetValue`. -/
theorem evalEval_twNegTarget_of_sq_eq_zero {R : Type*} [CommRing R] {q : R}
    (hq : (1 - q) ^ 2 = 0) (b : ℕ) (x j : R) :
    (twNegTarget b q).evalEval x j = twNegTargetJetValue b q x j := by
  have h1 : (derivative (1 : R[X][X])) = 0 := derivative_one
  have h2 : derivative (1 - C (C q) * X : R[X][X]) = C (C (-q)) := by
    simp
  have h3 : derivative (X : R[X][X]) = 1 := derivative_X
  have hd : 1 ≤ 2 * b + 2 := by omega
  rw [twNegTarget, twNegTargetJetValue, ← coe_evalEvalRingHom]
  simp only [map_mul, map_sub, map_add]
  simp only [coe_evalEvalRingHom, evalEval_twCheb_of_sq_eq_zero hq _ hd, h1, h2, h3]
  simp only [evalEval, eval_mul, eval_pow, eval_C, eval_X, eval_sub, eval_one, eval_zero]

/-- The first jet of the target of index `-b` at a point where the Lucas recursion has the
double root `w` (`ζ₀ = 2w`, `w² = x₀²`) and the target vanishes. -/
def twNegTargetJet (b : ℕ) (x₀ J₀ w : ℂ) : ℂ :=
  let d : ℂ := 2 * b + 2
  let z₁ : ℂ := -8 * d * x₀ ^ 2 - 4 * d * (1 + x₀) - 4 * d * x₀ +
    J₀ * (-8 * d * x₀ + 4 * (d + 1) + 4 * x₀ * (1 + x₀) + 4 * d * x₀ * (1 + x₀) + 4 * d * x₀ ^ 2) -
    (8 + 4 * d) * x₀ * J₀ ^ 2
  let s₁ : ℂ := -(16 * d - 4) * x₀ ^ 2
  let A₀ : ℂ := (1 - J₀) * (x₀ - J₀) * (1 - x₀ * J₀)
  let zJ : ℂ := -1 - x₀ ^ 2 + 2 * x₀ * J₀
  let S : ℕ → ℂ := fun k ↦ 2 * w ^ k
  let S₁ : ℕ → ℂ := fun k ↦
    (k : ℂ) ^ 2 * w ^ (k - 1) * z₁ - (k : ℂ) * ((k : ℂ) - 1) * w ^ (k - 2) * s₁
  let Sd : ℕ → ℂ := fun k ↦ (k : ℂ) ^ 2 * w ^ (k - 1)
  let Sh : ℕ → ℂ := fun k ↦ (k : ℂ) ^ 2 * ((k : ℂ) ^ 2 - 1) / 12 * w ^ (k - 2)
  (S₁ (b + 1) - 4 * (b + 1) * S (b + 1) + 4 * A₀ * Sh (b + 1) * zJ) +
    x₀ * ((1 - J₀) * S₁ b + 4 * J₀ * S b - (4 * b + 8 * d) * (1 - J₀) * S b +
      4 * A₀ * (-Sd b + Sh b * zJ * (1 - J₀))) -
    x₀ ^ 2 * (J₀ * S₁ (b - 1) - (4 * b + 16 * d) * J₀ * S (b - 1) +
      4 * A₀ * (Sd (b - 1) + Sh (b - 1) * zJ * J₀))

/-- The first component of `dualQ` is `1`. -/
private theorem fst_dualQ_twfNegTargetJet : dualQ.fst = 1 := by
  simp [dualQ]

/-- The second component of `dualQ` is `-4`. -/
private theorem snd_dualQ_twfNegTargetJet : dualQ.snd = -4 := by
  simp [dualQ, fst_ofNat_dual, snd_ofNat_dual]

/-- The first component of `twDualX d m₀` is `m₀²`. -/
private theorem fst_twDualX_twfNegTargetJet (d : ℕ) (m₀ : ℂ) : (twDualX d m₀).fst = m₀ ^ 2 := by
  simp [twDualX]

/-- The second component of `twDualX d m₀` is `-4 d m₀²`. -/
private theorem snd_twDualX_twfNegTargetJet (d : ℕ) (m₀ : ℂ) :
    (twDualX d m₀).snd = -4 * d * m₀ ^ 2 := by
  simp [twDualX, fst_ofNat_dual]

/-- The parameter `ζ̃` at `q = dualQ`, `x = twDualX d m₀`, `j = J₀`. -/
private theorem twJetZeta_dual_twfNegTargetJet (d : ℕ) (m₀ J₀ : ℂ) :
    twJetZeta d dualQ (twDualX d m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl (twJetZeta d 1 (m₀ ^ 2) J₀) +
        TrivSqZeroExt.inl (-8 * d * (m₀ ^ 2) ^ 2 - 4 * d * (1 + m₀ ^ 2) -
          4 * d * m₀ ^ 2 +
          J₀ * (-8 * d * m₀ ^ 2 + 4 * (d + 1) + 4 * m₀ ^ 2 * (1 + m₀ ^ 2) +
            4 * d * m₀ ^ 2 * (1 + m₀ ^ 2) + 4 * d * (m₀ ^ 2) ^ 2) -
          (8 + 4 * d) * m₀ ^ 2 * J₀ ^ 2) * DualNumber.eps := by
  ext
  · simp [twJetZeta, fst_dualQ_twfNegTargetJet, fst_twDualX_twfNegTargetJet]
  · simp [twJetZeta, fst_dualQ_twfNegTargetJet, fst_twDualX_twfNegTargetJet,
      snd_dualQ_twfNegTargetJet, snd_twDualX_twfNegTargetJet]
    ring

/-- The parameter `s = q^(2d-1) x²` at `q = dualQ`, `x = twDualX d m₀`. -/
private theorem twJetS_dual_twfNegTargetJet (d : ℕ) (hd : 1 ≤ d) {m₀ w : ℂ}
    (hw2 : w ^ 2 = (m₀ ^ 2) ^ 2) :
    dualQ ^ (2 * d - 1) * twDualX d m₀ ^ 2 =
      TrivSqZeroExt.inl (w ^ 2) +
        TrivSqZeroExt.inl (-(16 * d - 4) * (m₀ ^ 2) ^ 2) * DualNumber.eps := by
  have hc : ((2 * d - 1 : ℕ) : ℂ) = 2 * d - 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ 2 * d by omega)]
    ring
  ext
  · simp [fst_dualQ_twfNegTargetJet, fst_twDualX_twfNegTargetJet, hw2]
  · simp [fst_dualQ_twfNegTargetJet, fst_twDualX_twfNegTargetJet, snd_dualQ_twfNegTargetJet,
      snd_twDualX_twfNegTargetJet, hc]
    ring

/-- At `t = -1 + ε`, at a point with double root `ζ₀ = 2w` and vanishing value, the target of
index `-b` is `ε · twNegTargetJet`. -/
theorem evalEval_twNegTarget_dual_node (b : ℕ) (hb : 1 ≤ b) {m₀ J₀ w : ℂ}
    (hw : 2 * w = twJetZeta (2 * b + 2) (1 : ℂ) (m₀ ^ 2) J₀) (hw2 : w ^ 2 = (m₀ ^ 2) ^ 2)
    (hval : w ^ 2 + m₀ ^ 2 * w * (1 - J₀) - (m₀ ^ 2) ^ 2 * J₀ = 0) :
    (twNegTarget b dualQ).evalEval (twDualX (2 * b + 2) m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl (twNegTargetJet b (m₀ ^ 2) J₀ w) * DualNumber.eps := by
  rw [evalEval_twNegTarget_of_sq_eq_zero one_sub_dualQ_sq, twNegTargetJetValue]
  simp only [twChebJetValue, twJetZeta_dual_twfNegTargetJet,
    twJetS_dual_twfNegTargetJet (2 * b + 2) (by omega) hw2, ← hw, transferLucas_dual_double]
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  ext
  · simp [fst_dualQ_twfNegTargetJet, fst_twDualX_twfNegTargetJet]
    linear_combination 2 * w ^ n * hval
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_neg, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.snd_neg]
    simp only [fst_transferLucasDeriv_dual_double, fst_transferLucasHasse_dual_double]
    simp [twNegTargetJet, twJetCubic, twJetZetaDeriv, fst_dualQ_twfNegTargetJet,
      fst_twDualX_twfNegTargetJet, snd_dualQ_twfNegTargetJet, snd_twDualX_twfNegTargetJet,
      fst_ofNat_dual]
    ring

end AJConjecture
