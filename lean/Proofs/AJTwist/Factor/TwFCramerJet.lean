import Mathlib
import AJConjecture.QAlgDualJet
import AJConjecture.QAlgDualJetBasic
import AJConjecture.QAlgIntFibreBasic
import AJConjecture.QAlgWeylSymbol
import AJTwist.Quantum.TwQCramerSymbol

/-!
# The first jet of the operator of a target at a double point of its symbol (TwF, generic)

Source: revision 5, Section 5.2, eq. (physical-basis-jet):
`Ṗ_a/f_* = Ḣ/f_* - 2ρ (D_u G)(D_u H)` at a mixed double zero.

`evalIntPoint_specializeJet_twCramerOp_of_jets`: for the operator `twCramerOp d T` of an arbitrary
target `T` in an arbitrary window `d`, at a point `(m₀, l₀)` where its symbol has a double zero
in `L`, the first jet `P₁` satisfies `γ (P₁ + c l₀² ∂_L² P₀) = det|_{q=1}(m₀²) · h₁`, given the
first-order expansion of the pole basis (`γ l₀^(d-i) (1 + (a + b i + c i²) ε)`) and of the target
(`h₁ ε`) at `t = -1 + ε`.

Route: `AJFamily/Quantum/FamNodeCertificate.lean`
(`evalIntPoint_specializeJet_famTransferOp_of_jets`, the case `d = 2m + 3`, `T = famTarget m`) with
`evalDualPoint_famTransferOp → evalDualPoint_twCramerOp`,
`sum_famCoeff_mul_famBasisPoly → sum_twCoeff_mul_twBasisPoly` (over `DualNumber ℂ`, needs `hT`),
`specialize_famTransferOp_eq_sum → specialize_twCramerOp_eq_sum`, `map_famCoeff → map_twCoeff`,
`map_famDet → map_twDet`. The private helpers of that file are restated with the suffix
`_twfCramerJet`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first component, as a ring homomorphism from the dual numbers. -/
private def dualFstHom_twfCramerJet : DualNumber ℂ →+* ℂ :=
  (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

/-- The first-component homomorphism is the first component. -/
private theorem dualFstHom_apply_twfCramerJet (z : DualNumber ℂ) :
    dualFstHom_twfCramerJet z = z.fst :=
  rfl

/-- The first component of `dualQ = 1 - 4ε` is `1`. -/
private theorem dualFstHom_dualQ_twfCramerJet : dualFstHom_twfCramerJet dualQ = 1 := by
  simp [dualFstHom_apply_twfCramerJet, dualQ]

/-- The first component of `twDualX d m = (1 - 4dε) m²` is `m²`. -/
private theorem dualFstHom_twDualX_twfCramerJet (d : ℕ) (m : ℂ) :
    dualFstHom_twfCramerJet (twDualX d m) = m ^ 2 := by
  simp [dualFstHom_apply_twfCramerJet, twDualX]

/-- The first component of the value at `t = -1 + ε` is the value at `t = -1`. -/
private theorem dualFstHom_comp_dualJetHom_twfCramerJet :
    dualFstHom_twfCramerJet.comp dualJetHom =
      (Int.castRingHom ℂ).comp (Polynomial.evalRingHom (-1 : ℤ)) := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [dualFstHom_apply_twfCramerJet, dualJetHom]

/-- The first component of a Cramer numerator over the dual numbers is the Cramer numerator at
`q = 1`. -/
private theorem fst_eval_twCoeff_dualQ_twfCramerJet (d : ℕ) (T : ℤ[X][X][X]) (m : ℂ)
    (i : Fin (d + 1)) :
    ((twCoeff d dualQ (T.map (Polynomial.mapRingHom dualJetHom)) i).eval (twDualX d m)).fst =
      ((twCoeff d (1 : ℤ) (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ)))) i).map
        (Int.castRingHom ℂ)).eval (m ^ 2) := by
  rw [← dualFstHom_apply_twfCramerJet, ← eval_map_apply, map_twCoeff, map_twCoeff,
    dualFstHom_dualQ_twfCramerJet, dualFstHom_twDualX_twfCramerJet, map_one, Polynomial.map_map,
    Polynomial.map_map, mapRingHom_comp, mapRingHom_comp,
    dualFstHom_comp_dualJetHom_twfCramerJet]

/-- The first component of the determinant over the dual numbers is the determinant at
`q = 1`. -/
private theorem fst_eval_twDet_dualQ_twfCramerJet (d : ℕ) (m : ℂ) :
    ((twDet d dualQ).eval (twDualX d m)).fst =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m ^ 2) := by
  rw [← dualFstHom_apply_twfCramerJet, ← eval_map_apply, map_twDet, map_twDet,
    dualFstHom_dualQ_twfCramerJet, dualFstHom_twDualX_twfCramerJet, map_one]

/-- The Cramer identity evaluated at a point. -/
private theorem sum_twCoeff_eval_mul_evalEval_twfCramerJet {A : Type*} [CommRing A]
    (d : ℕ) (q : A) (T : A[X][X]) (hT : T.natDegree ≤ d) (x J : A) :
    ∑ i : Fin (d + 1), (twCoeff d q T i).eval x * (twBasisPoly d q i).evalEval x J =
      (twDet d q).eval x * T.evalEval x J := by
  have h := congrArg (evalEvalRingHom x J) (sum_twCoeff_mul_twBasisPoly d q T hT)
  simp only [map_sum, map_mul, coe_evalEvalRingHom, evalEval_C] at h
  exact h

/-- The fibre over `M = m` of the symbol of the operator of a target. -/
private theorem intFibre_specialize_twCramerOp_twfCramerJet (d : ℕ) (T : ℤ[X][X][X]) (m : ℂ) :
    intFibre (specialize (twCramerOp d T)) m =
      ∑ k : Fin (d + 1),
        C (((twCoeff d (1 : ℤ) (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))))
          (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m ^ 2)) * X ^ (k : ℕ) := by
  rw [specialize_twCramerOp_eq_sum d, intFibre, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coe_eval₂RingHom, eval₂_comp,
    eval₂_pow, eval₂_X, eval_map]

/-- The value, the derivative and the second derivative of `∑_k c_k L^k` at `L = l`. -/
private theorem eval_derivatives_sum_twfCramerJet (N : ℕ) (c : Fin N → ℂ) (l : ℂ) :
    (∑ k : Fin N, C (c k) * X ^ (k : ℕ)).eval l = ∑ k : Fin N, c k * l ^ (k : ℕ) ∧
      (derivative (∑ k : Fin N, C (c k) * X ^ (k : ℕ))).eval l =
        ∑ k : Fin N, c k * (((k : ℕ) : ℂ) * l ^ ((k : ℕ) - 1)) ∧
      (derivative (derivative (∑ k : Fin N, C (c k) * X ^ (k : ℕ)))).eval l =
        ∑ k : Fin N, c k * (((k : ℕ) : ℂ) * (((k : ℕ) - 1 : ℕ) : ℂ) * l ^ ((k : ℕ) - 1 - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [eval_mul, eval_C, eval_pow, eval_X]
  · rw [derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [derivative_C_mul_X_pow, eval_mul, eval_C, eval_pow, eval_X, mul_assoc]
  · rw [derivative_sum, derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [derivative_C_mul_X_pow, derivative_C_mul_X_pow, eval_mul, eval_C, eval_pow, eval_X,
      mul_assoc, mul_assoc, mul_assoc]

/-- Powers of `l` weighted by `k` and `k (k - 1)`. -/
private theorem natCast_mul_pow_twfCramerJet (l : ℂ) (k : ℕ) :
    (k : ℂ) * l ^ k = l * ((k : ℂ) * l ^ (k - 1)) ∧
      (k : ℂ) * ((k : ℂ) - 1) * l ^ k =
        l ^ 2 * ((k : ℂ) * ((k - 1 : ℕ) : ℂ) * l ^ (k - 1 - 1)) := by
  rcases k with _ | _ | k
  · simp
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    constructor <;> ring

/-- The second component of `z · g (1 + e ε)`. -/
private theorem snd_mul_inl_mul_one_add_twfCramerJet (z : DualNumber ℂ) (g e : ℂ) :
    (z * (TrivSqZeroExt.inl g * (1 + TrivSqZeroExt.inl e * DualNumber.eps))).snd =
      z.fst * (g * e) + z.snd * g := by
  simp

/-- The second component of `z · h ε`. -/
private theorem snd_mul_inl_mul_eps_twfCramerJet (z : DualNumber ℂ) (h : ℂ) :
    (z * (TrivSqZeroExt.inl h * DualNumber.eps)).snd = z.fst * h := by
  simp

/-- The second component of `z · l^k`. -/
private theorem snd_mul_inl_pow_twfCramerJet (z : DualNumber ℂ) (l : ℂ) (k : ℕ) :
    (z * TrivSqZeroExt.inl l ^ k).snd = z.snd * l ^ k := by
  rw [TrivSqZeroExt.inl_pow]
  simp

/-- The values at `(m, l)` of the symbol of the operator of a target and of its first two
derivatives in `L`. -/
private theorem evalIntPoint_specialize_twCramerOp_sum_twfCramerJet (d : ℕ) (T : ℤ[X][X][X])
    (m l : ℂ) :
    evalIntPoint (specialize (twCramerOp d T)) m l =
        ∑ k : Fin (d + 1), ((twCoeff d (1 : ℤ)
          (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))))
          (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m ^ 2) * l ^ (k : ℕ) ∧
      evalIntPoint (derivative (specialize (twCramerOp d T))) m l =
        ∑ k : Fin (d + 1), ((twCoeff d (1 : ℤ)
          (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))))
          (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m ^ 2) *
            (((k : ℕ) : ℂ) * l ^ ((k : ℕ) - 1)) ∧
      evalIntPoint (derivative (derivative (specialize (twCramerOp d T)))) m l =
        ∑ k : Fin (d + 1), ((twCoeff d (1 : ℤ)
          (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))))
          (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m ^ 2) *
            (((k : ℕ) : ℂ) * (((k : ℕ) - 1 : ℕ) : ℂ) * l ^ ((k : ℕ) - 1 - 1)) := by
  rw [evalIntPoint_eq_eval_intFibre, evalIntPoint_eq_eval_intFibre,
    evalIntPoint_eq_eval_intFibre, intFibre_derivative, intFibre_derivative,
    intFibre_derivative, intFibre_specialize_twCramerOp_twfCramerJet]
  exact eval_derivatives_sum_twfCramerJet _ _ l

/-- The first jet of the operator of a target at a double zero of its symbol, from the
first-order expansions of the pole basis and of the target. -/
theorem evalIntPoint_specializeJet_twCramerOp_of_jets (d : ℕ) (T : ℤ[X][X][X])
    (hT : T.natDegree ≤ d) {m₀ l₀ J₀ γ a b c h₁ : ℂ}
    (hbasis : ∀ i : Fin (d + 1),
      (twBasisPoly d dualQ i).evalEval (twDualX d m₀) (TrivSqZeroExt.inl J₀) =
        TrivSqZeroExt.inl (γ * l₀ ^ (d - (i : ℕ))) *
          (1 + TrivSqZeroExt.inl (a + b * ((i : ℕ) : ℂ) + c * ((i : ℕ) : ℂ) ^ 2) *
            DualNumber.eps))
    (htarget : (T.map (Polynomial.mapRingHom dualJetHom)).evalEval (twDualX d m₀)
      (TrivSqZeroExt.inl J₀) = TrivSqZeroExt.inl h₁ * DualNumber.eps)
    (h0 : evalIntPoint (specialize (twCramerOp d T)) m₀ l₀ = 0)
    (h1 : evalIntPoint (derivative (specialize (twCramerOp d T))) m₀ l₀ = 0) :
    γ * (evalIntPoint (specializeJet (twCramerOp d T)) m₀ l₀ +
        c * l₀ ^ 2 *
          evalIntPoint (derivative (derivative (specialize (twCramerOp d T)))) m₀ l₀) =
      ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) * h₁ := by
  set D : ℂ := ((d : ℕ) : ℂ) with hD
  set T₁ : ℤ[X][X] := T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))) with hT₁
  have hTd : (T.map (Polynomial.mapRingHom dualJetHom)).natDegree ≤ d :=
    natDegree_map_le.trans hT
  obtain ⟨hv0, hv1, hv2⟩ :=
    evalIntPoint_specialize_twCramerOp_sum_twfCramerJet d T m₀ l₀
  rw [hv0] at h0
  rw [hv1] at h1
  have hP1 : evalIntPoint (specializeJet (twCramerOp d T)) m₀ l₀ =
      ∑ k : Fin (d + 1),
        ((twCoeff d dualQ (T.map (Polynomial.mapRingHom dualJetHom)) (Fin.rev k)).eval
          (twDualX d m₀)).snd * l₀ ^ (k : ℕ) := by
    rw [← snd_evalDualPoint, evalDualPoint_twCramerOp d, TrivSqZeroExt.snd_sum]
    exact Finset.sum_congr rfl fun k _ ↦ snd_mul_inl_pow_twfCramerJet _ _ _
  have hC := congrArg TrivSqZeroExt.snd
    (sum_twCoeff_eval_mul_evalEval_twfCramerJet d dualQ _ hTd (twDualX d m₀)
      (TrivSqZeroExt.inl J₀))
  rw [htarget, snd_mul_inl_mul_eps_twfCramerJet, fst_eval_twDet_dualQ_twfCramerJet,
    TrivSqZeroExt.snd_sum, ← Equiv.sum_comp Fin.revPerm] at hC
  have hterm : ∀ k : Fin (d + 1),
      ((twCoeff d dualQ (T.map (Polynomial.mapRingHom dualJetHom)) (Fin.revPerm k)).eval
          (twDualX d m₀) *
        (twBasisPoly d dualQ (Fin.revPerm k)).evalEval (twDualX d m₀)
          (TrivSqZeroExt.inl J₀)).snd =
      γ * (((twCoeff d dualQ (T.map (Polynomial.mapRingHom dualJetHom)) (Fin.rev k)).eval
          (twDualX d m₀)).snd * l₀ ^ (k : ℕ)) +
        γ * c * l₀ ^ 2 * (((twCoeff d (1 : ℤ) T₁ (Fin.rev k)).map (Int.castRingHom ℂ)).eval
          (m₀ ^ 2) * (((k : ℕ) : ℂ) * (((k : ℕ) - 1 : ℕ) : ℂ) * l₀ ^ ((k : ℕ) - 1 - 1))) +
        γ * (a + D * b + D ^ 2 * c) *
          (((twCoeff d (1 : ℤ) T₁ (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
            l₀ ^ (k : ℕ)) -
        γ * (b + (2 * D - 1) * c) * l₀ *
          (((twCoeff d (1 : ℤ) T₁ (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
            (((k : ℕ) : ℂ) * l₀ ^ ((k : ℕ) - 1))) := by
    intro k
    have hk : d - (d + 1 - ((k : ℕ) + 1)) = (k : ℕ) := by omega
    have hc : ((d + 1 - ((k : ℕ) + 1) : ℕ) : ℂ) = D - ((k : ℕ) : ℂ) := by
      rw [hD, Nat.cast_sub (by omega)]
      push_cast
      ring
    obtain ⟨e1, e2⟩ := natCast_mul_pow_twfCramerJet l₀ k
    rw [Fin.revPerm_apply, hbasis, snd_mul_inl_mul_one_add_twfCramerJet,
      fst_eval_twCoeff_dualQ_twfCramerJet, Fin.val_rev, hk, hc]
    linear_combination
      (γ * c * ((twCoeff d (1 : ℤ) T₁ (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2)) * e2 -
      (γ * (b + (2 * D - 1) * c) *
        ((twCoeff d (1 : ℤ) T₁ (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2)) * e1
  rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hC
  rw [hP1, hv2]
  linear_combination hC - (γ * (a + D * b + D ^ 2 * c)) * h0 + (γ * (b + (2 * D - 1) * c) * l₀) * h1

end AJConjecture
