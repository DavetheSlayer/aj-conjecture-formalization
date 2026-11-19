import Mathlib
import AJConjecture.QAlgDualJetBasic
import AJConjecture.QAlgIntFibreBasic
import AJFamily.Quantum.FamDualTransferOp
import AJFamily.Quantum.FamSpecialize
import AJFamily.Quantum.FamTransferCramer

/-!
# The first jet of the family operator at a node

`evalIntPoint_specializeJet_famTransferOp_of_jets` computes the first jet of `famTransferOp m` at
a node from the first-order expansions of the basis and target polynomials at `t = -1 + ε`, as the
`ε`-component of the Cramer identity.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The first component, as a ring homomorphism from the dual numbers. -/
private def dualFstHomFamNodeCertificate : DualNumber ℂ →+* ℂ :=
  (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

/-- The first-component homomorphism is the first component. -/
private theorem dualFstHomFamNodeCertificate_apply (z : DualNumber ℂ) :
    dualFstHomFamNodeCertificate z = z.fst :=
  rfl

/-- The first component of `dualQ = 1 - 4ε` is `1`. -/
private theorem dualFstHomFamNodeCertificate_dualQ : dualFstHomFamNodeCertificate dualQ = 1 := by
  simp [dualFstHomFamNodeCertificate_apply, dualQ]

/-- The first component of `famDualX n m = (1 - 4dε) m²` is `m²`. -/
private theorem dualFstHomFamNodeCertificate_famDualX (n : ℕ) (m : ℂ) :
    dualFstHomFamNodeCertificate (famDualX n m) = m ^ 2 := by
  simp [dualFstHomFamNodeCertificate_apply, famDualX]

/-- The first component of a family Cramer coefficient over the dual numbers is the family
Cramer coefficient at `q = 1`. -/
private theorem fst_eval_famCoeff_dualQ_famNodeCertificate (n : ℕ) (m : ℂ)
    (i : Fin (2 * n + 4)) :
    ((famCoeff n dualQ i).eval (famDualX n m)).fst =
      ((famCoeff n (1 : ℤ) i).map (Int.castRingHom ℂ)).eval (m ^ 2) := by
  rw [← dualFstHomFamNodeCertificate_apply, ← eval_map_apply, map_famCoeff, map_famCoeff,
    dualFstHomFamNodeCertificate_dualQ, dualFstHomFamNodeCertificate_famDualX, map_one]

/-- The first component of the family determinant over the dual numbers is the family
determinant at `q = 1`. -/
private theorem fst_eval_famDet_dualQ_famNodeCertificate (n : ℕ) (m : ℂ) :
    ((famDet n dualQ).eval (famDualX n m)).fst =
      ((famDet n (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m ^ 2) := by
  rw [← dualFstHomFamNodeCertificate_apply, ← eval_map_apply, map_famDet, map_famDet,
    dualFstHomFamNodeCertificate_dualQ, dualFstHomFamNodeCertificate_famDualX, map_one]

/-- The Cramer identity of the family evaluated at a point. -/
private theorem sum_famCoeff_eval_mul_evalEval_famNodeCertificate {A : Type*} [CommRing A]
    (n : ℕ) (hn : 1 ≤ n) (q x J : A) :
    ∑ i : Fin (2 * n + 4), (famCoeff n q i).eval x * (famBasisPoly n q i).evalEval x J =
      (famDet n q).eval x * (famTarget n q).evalEval x J := by
  have h := congrArg (evalEvalRingHom x J) (sum_famCoeff_mul_famBasisPoly n hn q)
  simp only [map_sum, map_mul, coe_evalEvalRingHom, evalEval_C] at h
  exact h

/-- The fibre over `M = m` of the symbol of `famTransferOp n`. -/
private theorem intFibre_specialize_famTransferOp_famNodeCertificate (n : ℕ) (m : ℂ) :
    intFibre (specialize (famTransferOp n)) m =
      ∑ k : Fin (2 * n + 4),
        C (((famCoeff n (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m ^ 2)) *
          X ^ (k : ℕ) := by
  rw [specialize_famTransferOp_eq_sum n, intFibre, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coe_eval₂RingHom, eval₂_comp,
    eval₂_pow, eval₂_X, eval_map]

/-- The value, the derivative and the second derivative of `∑_k c_k L^k` at `L = l`. -/
private theorem eval_derivatives_sum_famNodeCertificate (N : ℕ) (c : Fin N → ℂ) (l : ℂ) :
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
private theorem natCast_mul_pow_famNodeCertificate (l : ℂ) (k : ℕ) :
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
private theorem snd_mul_inl_mul_one_add_famNodeCertificate (z : DualNumber ℂ) (g e : ℂ) :
    (z * (TrivSqZeroExt.inl g * (1 + TrivSqZeroExt.inl e * DualNumber.eps))).snd =
      z.fst * (g * e) + z.snd * g := by
  simp

/-- The second component of `z · h ε`. -/
private theorem snd_mul_inl_mul_eps_famNodeCertificate (z : DualNumber ℂ) (h : ℂ) :
    (z * (TrivSqZeroExt.inl h * DualNumber.eps)).snd = z.fst * h := by
  simp

/-- The second component of `z · l^k`. -/
private theorem snd_mul_inl_pow_famNodeCertificate (z : DualNumber ℂ) (l : ℂ) (k : ℕ) :
    (z * TrivSqZeroExt.inl l ^ k).snd = z.snd * l ^ k := by
  rw [TrivSqZeroExt.inl_pow]
  simp

/-- The values at `(m, l)` of the symbol of `famTransferOp n` and of its first two derivatives
in `L`. -/
private theorem evalIntPoint_specialize_famTransferOp_famNodeCertificate (n : ℕ) (m l : ℂ) :
    evalIntPoint (specialize (famTransferOp n)) m l =
        ∑ k : Fin (2 * n + 4), ((famCoeff n (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval
          (m ^ 2) * l ^ (k : ℕ) ∧
      evalIntPoint (derivative (specialize (famTransferOp n))) m l =
        ∑ k : Fin (2 * n + 4), ((famCoeff n (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval
          (m ^ 2) * (((k : ℕ) : ℂ) * l ^ ((k : ℕ) - 1)) ∧
      evalIntPoint (derivative (derivative (specialize (famTransferOp n)))) m l =
        ∑ k : Fin (2 * n + 4), ((famCoeff n (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval
          (m ^ 2) * (((k : ℕ) : ℂ) * (((k : ℕ) - 1 : ℕ) : ℂ) * l ^ ((k : ℕ) - 1 - 1)) := by
  rw [evalIntPoint_eq_eval_intFibre, evalIntPoint_eq_eval_intFibre,
    evalIntPoint_eq_eval_intFibre, intFibre_derivative, intFibre_derivative,
    intFibre_derivative, intFibre_specialize_famTransferOp_famNodeCertificate]
  exact eval_derivatives_sum_famNodeCertificate _ _ l

/-- The first jet of `famTransferOp m` at a node, from the first-order expansion of the basis
polynomials and of the target polynomial. -/
theorem evalIntPoint_specializeJet_famTransferOp_of_jets (m : ℕ) (hm : 1 ≤ m)
    {m₀ l₀ J₀ γ a b c h₁ : ℂ}
    (hbasis : ∀ i : Fin (2 * m + 4),
      (famBasisPoly m dualQ i).evalEval (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
        TrivSqZeroExt.inl (γ * l₀ ^ (2 * m + 3 - (i : ℕ))) *
          (1 + TrivSqZeroExt.inl (a + b * ((i : ℕ) : ℂ) + c * ((i : ℕ) : ℂ) ^ 2) *
            DualNumber.eps))
    (htarget : (famTarget m dualQ).evalEval (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl h₁ * DualNumber.eps)
    (h0 : evalIntPoint (specialize (famTransferOp m)) m₀ l₀ = 0)
    (h1 : evalIntPoint (derivative (specialize (famTransferOp m))) m₀ l₀ = 0) :
    γ * (evalIntPoint (specializeJet (famTransferOp m)) m₀ l₀ +
        c * l₀ ^ 2 * evalIntPoint (derivative (derivative (specialize (famTransferOp m)))) m₀ l₀) =
      ((famDet m (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) * h₁ := by
  set D : ℂ := ((2 * m + 3 : ℕ) : ℂ) with hD
  obtain ⟨hv0, hv1, hv2⟩ := evalIntPoint_specialize_famTransferOp_famNodeCertificate m m₀ l₀
  rw [hv0] at h0
  rw [hv1] at h1
  have hP1 : evalIntPoint (specializeJet (famTransferOp m)) m₀ l₀ =
      ∑ k : Fin (2 * m + 4),
        ((famCoeff m dualQ (Fin.rev k)).eval (famDualX m m₀)).snd * l₀ ^ (k : ℕ) := by
    rw [← snd_evalDualPoint, evalDualPoint_famTransferOp m, TrivSqZeroExt.snd_sum]
    exact Finset.sum_congr rfl fun k _ ↦ snd_mul_inl_pow_famNodeCertificate _ _ _
  have hC := congrArg TrivSqZeroExt.snd
    (sum_famCoeff_eval_mul_evalEval_famNodeCertificate m hm dualQ (famDualX m m₀)
      (TrivSqZeroExt.inl J₀))
  rw [htarget, snd_mul_inl_mul_eps_famNodeCertificate, fst_eval_famDet_dualQ_famNodeCertificate,
    TrivSqZeroExt.snd_sum, ← Equiv.sum_comp Fin.revPerm] at hC
  have hterm : ∀ k : Fin (2 * m + 4),
      ((famCoeff m dualQ (Fin.revPerm k)).eval (famDualX m m₀) *
        (famBasisPoly m dualQ (Fin.revPerm k)).evalEval (famDualX m m₀)
          (TrivSqZeroExt.inl J₀)).snd =
      γ * (((famCoeff m dualQ (Fin.rev k)).eval (famDualX m m₀)).snd * l₀ ^ (k : ℕ)) +
        γ * c * l₀ ^ 2 * (((famCoeff m (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval
          (m₀ ^ 2) * (((k : ℕ) : ℂ) * (((k : ℕ) - 1 : ℕ) : ℂ) * l₀ ^ ((k : ℕ) - 1 - 1))) +
        γ * (a + D * b + D ^ 2 * c) *
          (((famCoeff m (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
            l₀ ^ (k : ℕ)) -
        γ * (b + (2 * D - 1) * c) * l₀ *
          (((famCoeff m (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
            (((k : ℕ) : ℂ) * l₀ ^ ((k : ℕ) - 1))) := by
    intro k
    have hk : 2 * m + 3 - (2 * m + 4 - ((k : ℕ) + 1)) = (k : ℕ) := by omega
    have hc : ((2 * m + 4 - ((k : ℕ) + 1) : ℕ) : ℂ) = D - ((k : ℕ) : ℂ) := by
      rw [hD, Nat.cast_sub (by omega)]
      push_cast
      ring
    obtain ⟨e1, e2⟩ := natCast_mul_pow_famNodeCertificate l₀ k
    rw [Fin.revPerm_apply, hbasis, snd_mul_inl_mul_one_add_famNodeCertificate,
      fst_eval_famCoeff_dualQ_famNodeCertificate, Fin.val_rev, hk, hc]
    linear_combination
      (γ * c * ((famCoeff m (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2)) * e2 -
      (γ * (b + (2 * D - 1) * c) *
        ((famCoeff m (1 : ℤ) (Fin.rev k)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2)) * e1
  rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hC
  rw [hP1, hv2]
  linear_combination hC - (γ * (a + D * b + D ^ 2 * c)) * h0 + (γ * (b + (2 * D - 1) * c) * l₀) * h1

end AJConjecture
