import Mathlib
import AJConjecture.QAlgDualJet
import AJFamily.Quantum.FamJetData
import AJFamily.Quantum.FamTransferPoly
import AJFamily.Quantum.NodeClosedForms

/-!
# First-order jets of the basis polynomials at a node

`evalEval_famBasisPoly_dual_node`: at `q = 1 - 4ε`, `x = famDualX m m₀`, `J = J₀`, the `i`-th
basis polynomial is `γ L₀^(d-i) (1 + (a + b i + c i²) ε)`, given by `famBasisGamma`, `famNodeL`,
`famBasisJetA`, `famBasisJetB`, `famBasisJetC`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The value of a family basis polynomial at a point `(x, J)`. -/
private theorem evalEval_famBasisPoly_eq_prod {A : Type*} [CommRing A] (m : ℕ)
    (q x J : A) (i : ℕ) :
    (famBasisPoly m q i).evalEval x J =
      (∏ r ∈ Finset.range i, (q ^ r - x) * (x - q ^ (r + 1) * J)) *
        ∏ r ∈ Finset.Ico i (2 * m + 3), (x - q ^ (r + 1)) * (q ^ r - x * J) := by
  rw [← coe_evalEvalRingHom, famBasisPoly, map_mul, map_prod, map_prod]
  simp only [map_mul, map_sub, coe_evalEvalRingHom, evalEval_C, evalEval_X, eval_C, eval_X]

/-- The components of `dualQ ^ r = 1 - 4rε`. -/
private theorem fst_snd_dualQ_pow_famNode (r : ℕ) :
    (dualQ ^ r).fst = 1 ∧ (dualQ ^ r).snd = -4 * (r : ℂ) := by
  have h : dualQ.fst = 1 ∧ dualQ.snd = -4 := by
    rw [dualQ, show (4 : DualNumber ℂ) = ((4 : ℕ) : DualNumber ℂ) from rfl,
      ← TrivSqZeroExt.inl_natCast]
    simp
  rw [TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, h.1, h.2]
  simp only [one_pow, smul_eq_mul, mul_neg, one_mul, smul_neg, nsmul_eq_mul, neg_mul, neg_inj,
    true_and]
  ring

/-- The components of `famDualX m m₀ = (1 - 4dε) m₀²`. -/
private theorem fst_snd_famDualX_famNode (m : ℕ) (m₀ : ℂ) :
    (famDualX m m₀).fst = m₀ ^ 2 ∧
      (famDualX m m₀).snd = -(4 * (2 * (m : ℂ) + 3)) * m₀ ^ 2 := by
  rw [famDualX, ← TrivSqZeroExt.inl_natCast]
  simp

/-- The components of a product of dual numbers with common first component `g` and
logarithmic `ε`-jets `u + v r`. -/
private theorem fst_snd_prod_of_affine_famNode (z : ℕ → DualNumber ℂ) (g u v : ℂ)
    (hz : ∀ r : ℕ, (z r).fst = g ∧ (z r).snd = g * (u + v * (r : ℂ))) (n : ℕ) :
    (∏ r ∈ Finset.range n, z r).fst = g ^ n ∧
      (∏ r ∈ Finset.range n, z r).snd =
        g ^ n * (u * (n : ℂ) + v * ((n : ℂ) * ((n : ℂ) - 1) / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ih.1, ih.2,
      (hz n).1, (hz n).2, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    constructor
    · ring
    · push_cast
      ring

/-- The components of the factor `(q^r - x̂)(x̂ - q^(r+1) J₀)` at the node. -/
private theorem fst_snd_factorLow_famNode (m : ℕ) {m₀ J₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h2 : m₀ ^ 2 ≠ J₀) (r : ℕ) :
    ((dualQ ^ r - famDualX m m₀) *
        (famDualX m m₀ - dualQ ^ (r + 1) * TrivSqZeroExt.inl J₀)).fst =
        (1 - m₀ ^ 2) * (m₀ ^ 2 - J₀) ∧
      ((dualQ ^ r - famDualX m m₀) *
          (famDualX m m₀ - dualQ ^ (r + 1) * TrivSqZeroExt.inl J₀)).snd =
        (1 - m₀ ^ 2) * (m₀ ^ 2 - J₀) *
          ((4 * (2 * (m : ℂ) + 3) * m₀ ^ 2 / (1 - m₀ ^ 2) +
              (4 * J₀ - 4 * (2 * (m : ℂ) + 3) * m₀ ^ 2) / (m₀ ^ 2 - J₀)) +
            (-4 / (1 - m₀ ^ 2) + 4 * J₀ / (m₀ ^ 2 - J₀)) * (r : ℂ)) := by
  have ha : (1 - m₀ ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hb : (m₀ ^ 2 - J₀) ≠ 0 := sub_ne_zero.mpr h2
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    (fst_snd_dualQ_pow_famNode _).1, (fst_snd_dualQ_pow_famNode _).2,
    (fst_snd_famDualX_famNode _ _).1, (fst_snd_famDualX_famNode _ _).2, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  constructor
  · ring
  · field_simp
    push_cast
    ring

/-- The components of the factor `(x̂ - q^(r+1))(q^r - x̂ J₀)` at the node. -/
private theorem fst_snd_factorHigh_famNode (m : ℕ) {m₀ J₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h3 : m₀ ^ 2 * J₀ ≠ 1) (r : ℕ) :
    ((famDualX m m₀ - dualQ ^ (r + 1)) *
        (dualQ ^ r - famDualX m m₀ * TrivSqZeroExt.inl J₀)).fst =
        (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) ∧
      ((famDualX m m₀ - dualQ ^ (r + 1)) *
          (dualQ ^ r - famDualX m m₀ * TrivSqZeroExt.inl J₀)).snd =
        (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) *
          (((4 - 4 * (2 * (m : ℂ) + 3) * m₀ ^ 2) / (m₀ ^ 2 - 1) +
              4 * (2 * (m : ℂ) + 3) * m₀ ^ 2 * J₀ / (1 - m₀ ^ 2 * J₀)) +
            (4 / (m₀ ^ 2 - 1) - 4 / (1 - m₀ ^ 2 * J₀)) * (r : ℂ)) := by
  have ha : (m₀ ^ 2 - 1) ≠ 0 := sub_ne_zero.mpr h1
  have hb : (1 - m₀ ^ 2 * J₀) ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    (fst_snd_dualQ_pow_famNode _).1, (fst_snd_dualQ_pow_famNode _).2,
    (fst_snd_famDualX_famNode _ _).1, (fst_snd_famDualX_famNode _ _).2, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  refine ⟨trivial, ?_⟩
  field_simp
  push_cast
  ring

/-- The sum of the logarithmic `ε`-jets of the factors of the `t`-th basis polynomial is the
quadratic `a + b t + c t²`. -/
private theorem sum_logJets_eq_famBasisJet (m : ℕ) {x J : ℂ} (h1 : x ≠ 1) (h2 : x ≠ J)
    (h3 : x * J ≠ 1) (t : ℂ) :
    ((4 * (2 * (m : ℂ) + 3) * x / (1 - x) + (4 * J - 4 * (2 * (m : ℂ) + 3) * x) / (x - J)) * t +
        (-4 / (1 - x) + 4 * J / (x - J)) * (t * (t - 1) / 2)) +
      ((((4 - 4 * (2 * (m : ℂ) + 3) * x) / (x - 1) +
            4 * (2 * (m : ℂ) + 3) * x * J / (1 - x * J)) +
          (4 / (x - 1) - 4 / (1 - x * J)) * t) * (2 * (m : ℂ) + 3 - t) +
        (4 / (x - 1) - 4 / (1 - x * J)) *
          ((2 * (m : ℂ) + 3 - t) * ((2 * (m : ℂ) + 3 - t) - 1) / 2)) =
      famBasisJetA m x J + famBasisJetB m x J * t + famBasisJetC x J * t ^ 2 := by
  have ha : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha' : (x - 1) ≠ 0 := sub_ne_zero.mpr h1
  have hb : (x - J) ≠ 0 := sub_ne_zero.mpr h2
  have hc : (1 - x * J) ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
  rw [famBasisJetA, famBasisJetB, famBasisJetC]
  field_simp
  ring

/-- The first-order expansion of the family basis polynomials at a node. -/
theorem evalEval_famBasisPoly_dual_node (m : ℕ) {m₀ J₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ J₀)
    (h3 : m₀ ^ 2 * J₀ ≠ 1) (i : Fin (2 * m + 4)) :
    (famBasisPoly m dualQ i).evalEval (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl (famBasisGamma m (m₀ ^ 2) J₀ * famNodeL (m₀ ^ 2) J₀ ^ (2 * m + 3 - (i : ℕ))) *
        (1 + TrivSqZeroExt.inl (famBasisJetA m (m₀ ^ 2) J₀ + famBasisJetB m (m₀ ^ 2) J₀ * ((i : ℕ) : ℂ) +
          famBasisJetC (m₀ ^ 2) J₀ * ((i : ℕ) : ℂ) ^ 2) * DualNumber.eps) := by
  have hi : (i : ℕ) ≤ 2 * m + 3 := by omega
  have hb : (m₀ ^ 2 - J₀) ≠ 0 := sub_ne_zero.mpr h2
  have hzB : ∀ k : ℕ,
      ((famDualX m m₀ - dualQ ^ ((i : ℕ) + k + 1)) *
        (dualQ ^ ((i : ℕ) + k) - famDualX m m₀ * TrivSqZeroExt.inl J₀)).fst =
          (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) ∧
      ((famDualX m m₀ - dualQ ^ ((i : ℕ) + k + 1)) *
        (dualQ ^ ((i : ℕ) + k) - famDualX m m₀ * TrivSqZeroExt.inl J₀)).snd =
          (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) *
            ((((4 - 4 * (2 * (m : ℂ) + 3) * m₀ ^ 2) / (m₀ ^ 2 - 1) +
                4 * (2 * (m : ℂ) + 3) * m₀ ^ 2 * J₀ / (1 - m₀ ^ 2 * J₀)) +
              (4 / (m₀ ^ 2 - 1) - 4 / (1 - m₀ ^ 2 * J₀)) * ((i : ℕ) : ℂ)) +
            (4 / (m₀ ^ 2 - 1) - 4 / (1 - m₀ ^ 2 * J₀)) * (k : ℂ)) := by
    intro k
    obtain ⟨hk1, hk2⟩ := fst_snd_factorHigh_famNode m h1 h3 ((i : ℕ) + k)
    refine ⟨hk1, ?_⟩
    rw [hk2]
    push_cast
    ring
  obtain ⟨hA1, hA2⟩ := fst_snd_prod_of_affine_famNode _ _ _ _
    (fst_snd_factorLow_famNode m h1 h2) (i : ℕ)
  obtain ⟨hB1, hB2⟩ := fst_snd_prod_of_affine_famNode _ _ _ _ hzB (2 * m + 3 - (i : ℕ))
  have hh : (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) =
      (1 - m₀ ^ 2) * (m₀ ^ 2 - J₀) * famNodeL (m₀ ^ 2) J₀ := by
    rw [famNodeL]
    field_simp
    ring
  have hfst : ((1 - m₀ ^ 2) * (m₀ ^ 2 - J₀)) ^ (i : ℕ) *
      ((m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀)) ^ (2 * m + 3 - (i : ℕ)) =
      famBasisGamma m (m₀ ^ 2) J₀ * famNodeL (m₀ ^ 2) J₀ ^ (2 * m + 3 - (i : ℕ)) := by
    rw [hh, mul_pow ((1 - m₀ ^ 2) * (m₀ ^ 2 - J₀)), ← mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hi, famBasisGamma]
  have key := sum_logJets_eq_famBasisJet m h1 h2 h3 ((i : ℕ) : ℂ)
  rw [evalEval_famBasisPoly_eq_prod, Finset.prod_Ico_eq_prod_range]
  ext
  · rw [TrivSqZeroExt.fst_mul, hA1, hB1, hfst, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
    simp
  · rw [TrivSqZeroExt.snd_mul, hA1, hA2, hB1, hB2, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, ← hfst, Nat.cast_sub hi]
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
      TrivSqZeroExt.fst_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [DualNumber.fst_eps, DualNumber.snd_eps]
    push_cast
    linear_combination ((1 - m₀ ^ 2) * (m₀ ^ 2 - J₀)) ^ (i : ℕ) *
      ((m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀)) ^ (2 * m + 3 - (i : ℕ)) * key

end AJConjecture
