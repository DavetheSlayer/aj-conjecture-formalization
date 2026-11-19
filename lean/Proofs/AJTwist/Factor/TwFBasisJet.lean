import Mathlib
import AJConjecture.QAlgDualJet
import AJFamily.Quantum.NodeClosedForms
import AJTwist.Quantum.TwQCramerSymbol

/-!
# First-order jets of the pole basis of an arbitrary window at a point (package TwF, generic)

Source: revision 5, Section 5.2 (`operators.tex`, "The nodes and the physical first jet"):
`Ṙ_i/u^i = ρ i(i-1) + β i`, `ρ = (J² - 1)/(2 A_*)`.

`evalEval_twBasisPoly_dual_node`: at `q = 1 - 4ε`, `x = twDualX d m₀ = (1 - 4dε) m₀²`, `J = J₀`,
the `i`-th basis polynomial of the window `d` is `γ L₀^(d-i) (1 + (a + b i + c i²) ε)` with
`γ = twBasisGamma d m₀² J₀`, `L₀ = famNodeL m₀² J₀` and `c = famBasisJetC m₀² J₀ = -4ρ`,
independent of `d`. Only `c` is used downstream, so `a`, `b` are existential.

Route: `AJFamily/Quantum/FamBasisNodeJet.lean` (`evalEval_famBasisPoly_dual_node`, the case
`d = 2m + 3`) with `2m + 3` replaced by `d`; that proof gives
`a = (2d(d+1) - 4d² x)/(x - 1) + (4d² xJ - 2d(d-1))/(1 - xJ)` and
`b = 4/(1 - x) + (4J - 4dx)/(x - J) - 4dxJ/(1 - xJ) - c`. Nothing there uses the parity of the
window. Checked at random points for `d = 2, 3, 4, 6` (scratch `check_generic_parts.py` (B)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value `γ = ((1 - x₀)(x₀ - J₀))^d` of the basis polynomials of the window `d` at
`q = 1`, up to the power `L₀^(d-i)`. -/
def twBasisGamma (d : ℕ) (x₀ J₀ : ℂ) : ℂ := ((1 - x₀) * (x₀ - J₀)) ^ d

theorem twBasisGamma_ne_zero (d : ℕ) {x₀ J₀ : ℂ} (h1 : x₀ ≠ 1) (h2 : x₀ ≠ J₀) :
    twBasisGamma d x₀ J₀ ≠ 0 :=
  pow_ne_zero _ (mul_ne_zero (sub_ne_zero.mpr (Ne.symm h1)) (sub_ne_zero.mpr h2))

/-- The value of a basis polynomial of the window `d` at a point `(x, J)`. -/
private theorem evalEval_twBasisPoly_eq_prod_twfBasisJet {A : Type*} [CommRing A] (d : ℕ)
    (q x J : A) (i : ℕ) :
    (twBasisPoly d q i).evalEval x J =
      (∏ r ∈ Finset.range i, (q ^ r - x) * (x - q ^ (r + 1) * J)) *
        ∏ r ∈ Finset.Ico i d, (x - q ^ (r + 1)) * (q ^ r - x * J) := by
  rw [← coe_evalEvalRingHom, twBasisPoly, map_mul, map_prod, map_prod]
  simp only [map_mul, map_sub, coe_evalEvalRingHom, evalEval_C, evalEval_X, eval_C, eval_X]

/-- The components of `dualQ ^ r = 1 - 4rε`. -/
private theorem fst_snd_dualQ_pow_twfBasisJet (r : ℕ) :
    (dualQ ^ r).fst = 1 ∧ (dualQ ^ r).snd = -4 * (r : ℂ) := by
  have h : dualQ.fst = 1 ∧ dualQ.snd = -4 := by
    rw [dualQ, show (4 : DualNumber ℂ) = ((4 : ℕ) : DualNumber ℂ) from rfl,
      ← TrivSqZeroExt.inl_natCast]
    simp
  rw [TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_pow, h.1, h.2]
  simp only [one_pow, smul_eq_mul, mul_neg, one_mul, smul_neg, nsmul_eq_mul, neg_mul, neg_inj,
    true_and]
  ring

/-- The components of `twDualX d m₀ = (1 - 4dε) m₀²`. -/
private theorem fst_snd_twDualX_twfBasisJet (d : ℕ) (m₀ : ℂ) :
    (twDualX d m₀).fst = m₀ ^ 2 ∧
      (twDualX d m₀).snd = -(4 * (d : ℂ)) * m₀ ^ 2 := by
  rw [twDualX, ← TrivSqZeroExt.inl_natCast]
  simp

/-- The components of a product of dual numbers with common first component `g` and
logarithmic `ε`-jets `u + v r`. -/
private theorem fst_snd_prod_of_affine_twfBasisJet (z : ℕ → DualNumber ℂ) (g u v : ℂ)
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
private theorem fst_snd_factorLow_twfBasisJet (d : ℕ) {m₀ J₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h2 : m₀ ^ 2 ≠ J₀) (r : ℕ) :
    ((dualQ ^ r - twDualX d m₀) *
        (twDualX d m₀ - dualQ ^ (r + 1) * TrivSqZeroExt.inl J₀)).fst =
        (1 - m₀ ^ 2) * (m₀ ^ 2 - J₀) ∧
      ((dualQ ^ r - twDualX d m₀) *
          (twDualX d m₀ - dualQ ^ (r + 1) * TrivSqZeroExt.inl J₀)).snd =
        (1 - m₀ ^ 2) * (m₀ ^ 2 - J₀) *
          ((4 * (d : ℂ) * m₀ ^ 2 / (1 - m₀ ^ 2) +
              (4 * J₀ - 4 * (d : ℂ) * m₀ ^ 2) / (m₀ ^ 2 - J₀)) +
            (-4 / (1 - m₀ ^ 2) + 4 * J₀ / (m₀ ^ 2 - J₀)) * (r : ℂ)) := by
  have ha : (1 - m₀ ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hb : (m₀ ^ 2 - J₀) ≠ 0 := sub_ne_zero.mpr h2
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    (fst_snd_dualQ_pow_twfBasisJet _).1, (fst_snd_dualQ_pow_twfBasisJet _).2,
    (fst_snd_twDualX_twfBasisJet _ _).1, (fst_snd_twDualX_twfBasisJet _ _).2, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  constructor
  · ring
  · field_simp
    push_cast
    ring

/-- The components of the factor `(x̂ - q^(r+1))(q^r - x̂ J₀)` at the node. -/
private theorem fst_snd_factorHigh_twfBasisJet (d : ℕ) {m₀ J₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h3 : m₀ ^ 2 * J₀ ≠ 1) (r : ℕ) :
    ((twDualX d m₀ - dualQ ^ (r + 1)) *
        (dualQ ^ r - twDualX d m₀ * TrivSqZeroExt.inl J₀)).fst =
        (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) ∧
      ((twDualX d m₀ - dualQ ^ (r + 1)) *
          (dualQ ^ r - twDualX d m₀ * TrivSqZeroExt.inl J₀)).snd =
        (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) *
          (((4 - 4 * (d : ℂ) * m₀ ^ 2) / (m₀ ^ 2 - 1) +
              4 * (d : ℂ) * m₀ ^ 2 * J₀ / (1 - m₀ ^ 2 * J₀)) +
            (4 / (m₀ ^ 2 - 1) - 4 / (1 - m₀ ^ 2 * J₀)) * (r : ℂ)) := by
  have ha : (m₀ ^ 2 - 1) ≠ 0 := sub_ne_zero.mpr h1
  have hb : (1 - m₀ ^ 2 * J₀) ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    (fst_snd_dualQ_pow_twfBasisJet _).1, (fst_snd_dualQ_pow_twfBasisJet _).2,
    (fst_snd_twDualX_twfBasisJet _ _).1, (fst_snd_twDualX_twfBasisJet _ _).2, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  refine ⟨trivial, ?_⟩
  field_simp
  push_cast
  ring

/-- The sum of the logarithmic `ε`-jets of the factors of the `t`-th basis polynomial is the
quadratic `a + b t + c t²`. -/
private theorem sum_logJets_eq_twfBasisJet (d : ℕ) {x J : ℂ} (h1 : x ≠ 1) (h2 : x ≠ J)
    (h3 : x * J ≠ 1) (t : ℂ) :
    ((4 * (d : ℂ) * x / (1 - x) + (4 * J - 4 * (d : ℂ) * x) / (x - J)) * t +
        (-4 / (1 - x) + 4 * J / (x - J)) * (t * (t - 1) / 2)) +
      ((((4 - 4 * (d : ℂ) * x) / (x - 1) +
            4 * (d : ℂ) * x * J / (1 - x * J)) +
          (4 / (x - 1) - 4 / (1 - x * J)) * t) * ((d : ℂ) - t) +
        (4 / (x - 1) - 4 / (1 - x * J)) *
          (((d : ℂ) - t) * (((d : ℂ) - t) - 1) / 2)) =
      ((2 * (d : ℂ) * ((d : ℂ) + 1) - 4 * (d : ℂ) ^ 2 * x) / (x - 1) +
          (4 * (d : ℂ) ^ 2 * x * J - 2 * (d : ℂ) * ((d : ℂ) - 1)) / (1 - x * J)) +
        (4 / (1 - x) + (4 * J - 4 * (d : ℂ) * x) / (x - J) - 4 * (d : ℂ) * x * J / (1 - x * J) -
          famBasisJetC x J) * t + famBasisJetC x J * t ^ 2 := by
  have ha : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha' : (x - 1) ≠ 0 := sub_ne_zero.mpr h1
  have hb : (x - J) ≠ 0 := sub_ne_zero.mpr h2
  have hc : (1 - x * J) ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
  rw [famBasisJetC]
  field_simp
  ring

/-- The first-order expansion of the basis polynomials of the window `d` at a point. -/
theorem evalEval_twBasisPoly_dual_node (d : ℕ) {m₀ J₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ J₀)
    (h3 : m₀ ^ 2 * J₀ ≠ 1) :
    ∃ a b : ℂ, ∀ i : Fin (d + 1),
      (twBasisPoly d dualQ i).evalEval (twDualX d m₀) (TrivSqZeroExt.inl J₀) =
        TrivSqZeroExt.inl (twBasisGamma d (m₀ ^ 2) J₀ * famNodeL (m₀ ^ 2) J₀ ^ (d - (i : ℕ))) *
          (1 + TrivSqZeroExt.inl (a + b * ((i : ℕ) : ℂ) +
            famBasisJetC (m₀ ^ 2) J₀ * ((i : ℕ) : ℂ) ^ 2) * DualNumber.eps) := by
  have hb : (m₀ ^ 2 - J₀) ≠ 0 := sub_ne_zero.mpr h2
  have hh : (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) =
      (1 - m₀ ^ 2) * (m₀ ^ 2 - J₀) * famNodeL (m₀ ^ 2) J₀ := by
    rw [famNodeL]
    field_simp
    ring
  refine ⟨(2 * (d : ℂ) * ((d : ℂ) + 1) - 4 * (d : ℂ) ^ 2 * m₀ ^ 2) / (m₀ ^ 2 - 1) +
      (4 * (d : ℂ) ^ 2 * m₀ ^ 2 * J₀ - 2 * (d : ℂ) * ((d : ℂ) - 1)) / (1 - m₀ ^ 2 * J₀),
    4 / (1 - m₀ ^ 2) + (4 * J₀ - 4 * (d : ℂ) * m₀ ^ 2) / (m₀ ^ 2 - J₀) -
      4 * (d : ℂ) * m₀ ^ 2 * J₀ / (1 - m₀ ^ 2 * J₀) - famBasisJetC (m₀ ^ 2) J₀, fun i ↦ ?_⟩
  have hi : (i : ℕ) ≤ d := by omega
  have hzB : ∀ k : ℕ,
      ((twDualX d m₀ - dualQ ^ ((i : ℕ) + k + 1)) *
        (dualQ ^ ((i : ℕ) + k) - twDualX d m₀ * TrivSqZeroExt.inl J₀)).fst =
          (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) ∧
      ((twDualX d m₀ - dualQ ^ ((i : ℕ) + k + 1)) *
        (dualQ ^ ((i : ℕ) + k) - twDualX d m₀ * TrivSqZeroExt.inl J₀)).snd =
          (m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀) *
            ((((4 - 4 * (d : ℂ) * m₀ ^ 2) / (m₀ ^ 2 - 1) +
                4 * (d : ℂ) * m₀ ^ 2 * J₀ / (1 - m₀ ^ 2 * J₀)) +
              (4 / (m₀ ^ 2 - 1) - 4 / (1 - m₀ ^ 2 * J₀)) * ((i : ℕ) : ℂ)) +
            (4 / (m₀ ^ 2 - 1) - 4 / (1 - m₀ ^ 2 * J₀)) * (k : ℂ)) := by
    intro k
    obtain ⟨hk1, hk2⟩ := fst_snd_factorHigh_twfBasisJet d h1 h3 ((i : ℕ) + k)
    refine ⟨hk1, ?_⟩
    rw [hk2]
    push_cast
    ring
  obtain ⟨hA1, hA2⟩ := fst_snd_prod_of_affine_twfBasisJet _ _ _ _
    (fst_snd_factorLow_twfBasisJet d h1 h2) (i : ℕ)
  obtain ⟨hB1, hB2⟩ := fst_snd_prod_of_affine_twfBasisJet _ _ _ _ hzB (d - (i : ℕ))
  have hfst : ((1 - m₀ ^ 2) * (m₀ ^ 2 - J₀)) ^ (i : ℕ) *
      ((m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀)) ^ (d - (i : ℕ)) =
      twBasisGamma d (m₀ ^ 2) J₀ * famNodeL (m₀ ^ 2) J₀ ^ (d - (i : ℕ)) := by
    rw [hh, mul_pow ((1 - m₀ ^ 2) * (m₀ ^ 2 - J₀)), ← mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hi, twBasisGamma]
  have key := sum_logJets_eq_twfBasisJet d h1 h2 h3 ((i : ℕ) : ℂ)
  rw [evalEval_twBasisPoly_eq_prod_twfBasisJet, Finset.prod_Ico_eq_prod_range]
  ext
  · rw [TrivSqZeroExt.fst_mul, hA1, hB1, hfst, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
    simp
  · rw [TrivSqZeroExt.snd_mul, hA1, hA2, hB1, hB2, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, ← hfst, Nat.cast_sub hi]
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
      TrivSqZeroExt.fst_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [DualNumber.fst_eps, DualNumber.snd_eps]
    linear_combination ((1 - m₀ ^ 2) * (m₀ ^ 2 - J₀)) ^ (i : ℕ) *
      ((m₀ ^ 2 - 1) * (1 - m₀ ^ 2 * J₀)) ^ (d - (i : ℕ)) * key

end AJConjecture
