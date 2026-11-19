import Mathlib
import AJConjecture.SkeinKnotTraceJwStep
import AJConjecture.SkeinBandClaspCompress
import AJConjecture.SkeinSatelliteEval
import AJConjecture.SkeinChannelTrace
import AJConjecture.SkeinLongKnotChannel
import AJHandoff.TorusQuantum.PairQFormulaBasic
import AJHandoff.TorusQuantum.PairQSatellite

/-!
# Evaluation of the band-and-clasp trace from the companion's odd colours

If the bracket of the `2n`-cable of the companion `C` with the projector `f_{2n}` is
`t^(4w n(n+1)) u_n` for every `n` (that is, `u_n` is the zero-framed coloured Jones polynomial of
`C` at the colour `2n + 1` when `w` is the writhe of `C`), then
`pairQSatTrace C w c = (-1)^c θ_c^(2w-2) [c+1] F_{c+1}` with `F` the reduced formula of `u`.

The proof is that of `torusSatelliteTrace_eq`: the band operator is diagonal on the channels
(`halfTwist_false_pow_mul_channelIdem`,
`twoBundleProj_mul_bandClaspOp_mul_twoBundleProj_eq_sum`), the trace of the long knot of `C` on
the channel `Q_n` is the bracket of `f_{2n}` (`qtr_longKnotOp_mul_channelIdem`), the framing
scalars combine to `t^(2w c(c+2))` (`pairQ_halfTwistEigen_inv_pow_mul`), and the channel sum is
evaluated by `pairQ_sum_claspEigen_mul`. The companion enters only through `hC`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `λ_{c,n}^(-2w) t^(4w n(n+1)) = t^(2w c(c+2))`: the framing scalar does not depend on the
channel. -/
theorem pairQ_halfTwistEigen_inv_pow_mul (w c n : ℕ) :
    ((claspAlgHalfTwistEigen c n)⁻¹) ^ (2 * w) *
        (RatFunc.X : RatFunc ℚ) ^ (4 * (w : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) =
      (RatFunc.X : RatFunc ℚ) ^ (2 * (w : ℤ) * (c : ℤ) * ((c : ℤ) + 2)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : ((-1 : RatFunc ℚ) ^ (c + n)) ^ (2 * w) = 1 := by
    rw [← pow_mul, show (c + n) * (2 * w) = 2 * ((c + n) * w) from by ring,
      pow_mul, neg_one_sq, one_pow]
  rw [claspAlgHalfTwistEigen, inv_pow, mul_pow, h1, one_mul, ← zpow_natCast, ← zpow_mul,
    ← zpow_neg, ← zpow_add₀ hX]
  congr 1
  push_cast
  ring

/-- The quantum trace of a finite sum. -/
private theorem qtr_sum_pairQSatEval (n : ℕ) (s : Finset ℕ) (f : ℕ → SkMat n n) :
    qtr n (∑ i ∈ s, f i) = ∑ i ∈ s, qtr n (f i) := by
  simp only [qtr, Matrix.mul_sum, Matrix.trace_sum]

/-- The trace of the long knot of the companion on the channel `Q_n`, for `n ≤ c`. -/
private theorem qtr_longKnotOp_mul_channelIdem_pairQ_of_le (C : BraidKnot) (w : ℕ)
    (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (w : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (c n : ℕ) (hn : n ≤ c) :
    qtr (2 * c) (longKnotOp C (2 * c) * channelIdem c n) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (w : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) * u n := by
  obtain ⟨m, rfl⟩ : ∃ m, c = n + m := ⟨c - n, by omega⟩
  rw [qtr_longKnotOp_mul_channelIdem, hC]

/-- The operator of the band-and-clasp trace on the channels. -/
private theorem pairQSatOp_eq_sum_channelIdem (w c : ℕ) :
    twoBundleProj c * halfTwist c false ^ (2 * w) * bandClaspOp c * twoBundleProj c =
      ∑ n ∈ Finset.range (c + 1),
        (claspAlgClaspEigen c n * ((claspAlgHalfTwistEigen c n)⁻¹) ^ (2 * w)) •
          channelIdem c n := by
  have hcomm : Commute (halfTwist c false ^ (2 * w)) (twoBundleProj c) :=
    (show Commute (halfTwist c false) (twoBundleProj c) from
      halfTwist_mul_twoBundleProj c false).pow_left _
  rw [← hcomm.eq, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (twoBundleProj c),
    twoBundleProj_mul_bandClaspOp_mul_twoBundleProj_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Matrix.mul_smul, halfTwist_false_pow_mul_channelIdem c n _
    (by have := Finset.mem_range.mp hn; omega), smul_smul]

/-- `(-1)^c θ_c^(2w-2) (-1)^c t^(2c(c+2)) = t^(2w c(c+2))`. -/
private theorem kinkScalar_zpow_mul_pairQSatEval (w c : ℕ) :
    (-1 : RatFunc ℚ) ^ c * kinkScalar c ^ (2 * (w : ℤ) - 2) *
        ((-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2))) =
      (RatFunc.X : RatFunc ℚ) ^ (2 * (w : ℤ) * (c : ℤ) * ((c : ℤ) + 2)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : ((-1 : RatFunc ℚ) ^ c) ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hs : (-1 : RatFunc ℚ) ^ c * (-1) ^ c = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have e : (2 : ℤ) * (w : ℤ) - 2 = 2 * ((w : ℤ) - 1) := by ring
  rw [kinkScalar, mul_zpow, e, zpow_mul ((-1 : RatFunc ℚ) ^ c) 2, h1, one_zpow, one_mul,
    ← zpow_mul]
  calc (-1 : RatFunc ℚ) ^ c *
        (RatFunc.X : RatFunc ℚ) ^ ((c : ℤ) * ((c : ℤ) + 2) * (2 * ((w : ℤ) - 1))) *
        ((-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2)))
      = ((-1 : RatFunc ℚ) ^ c * (-1) ^ c) *
        ((RatFunc.X : RatFunc ℚ) ^ ((c : ℤ) * ((c : ℤ) + 2) * (2 * ((w : ℤ) - 1))) *
          (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2))) := by ring
    _ = (RatFunc.X : RatFunc ℚ) ^ (2 * (w : ℤ) * (c : ℤ) * ((c : ℤ) + 2)) := by
      rw [hs, one_mul, ← zpow_add₀ hX]
      congr 1
      ring

/-- The band-and-clasp trace as a sum over the channels. -/
private theorem pairQSatTrace_eq_sum (C : BraidKnot) (w : ℕ) (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (w : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (c : ℕ) :
    pairQSatTrace C w c =
      ∑ n ∈ Finset.range (c + 1), claspAlgClaspEigen c n *
        (((claspAlgHalfTwistEigen c n)⁻¹) ^ (2 * w) *
          ((RatFunc.X : RatFunc ℚ) ^ (4 * (w : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) * u n)) := by
  rw [pairQSatTrace, knotTrace_eq_qtr_longKnotOp, pairQSatOp_eq_sum_channelIdem,
    Finset.mul_sum, qtr_sum_pairQSatEval]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Matrix.mul_smul, qtr_smul, qtr_longKnotOp_mul_channelIdem_pairQ_of_le C w u hC
    c n (by have := Finset.mem_range.mp hn; omega), mul_assoc]

/-- The band-and-clasp trace over a companion with odd-colour input `u`. -/
theorem pairQSatTrace_eq (C : BraidKnot) (w : ℕ) (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (w : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (c : ℕ) :
    pairQSatTrace C w c =
      (-1) ^ c * kinkScalar c ^ (2 * (w : ℤ) - 2) * pairQFormula u ((c : ℤ) + 1) := by
  rw [pairQSatTrace_eq_sum C w u hC, ← pairQ_sum_claspEigen_mul, ← mul_assoc,
    kinkScalar_zpow_mul_pairQSatEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [← mul_assoc (_ ^ (2 * w)), pairQ_halfTwistEigen_inv_pow_mul]
  ring

end AJConjecture
