import Mathlib
import AJConjecture.SkeinKnotTraceJwStep
import AJConjecture.SkeinChannelTrace
import AJConjecture.SkeinHalfTwistSpectral
import AJConjecture.SkeinKnotTraceJwCols
import AJConjecture.SkeinLongKnotChannel
import AJFamily.Skein.TorusHalfTwistSum
import AJFamily.Skein.TorusKnot

/-!
# Channel traces of `T(2, 2k+1)`

`qtr_longKnotOp_torusKnot_mul_channelIdem`: the trace of the long-knot operator of `torusKnot k` on
the channel of colour `2n` of two bundles is `X^(4(2k+1) n(n+1)) · torusOddColor (2k+1) n`. The
cabled braid of `σ_0^(2k+1)` is a power of the half twist, which acts on each channel by a scalar.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The quantum trace of a finite sum. -/
theorem qtr_sum (n : ℕ) (s : Finset ℕ) (f : ℕ → SkMat n n) :
    qtr n (∑ i ∈ s, f i) = ∑ i ∈ s, qtr n (f i) := by
  simp only [qtr, Matrix.mul_sum, Matrix.trace_sum]

/-- The cabled braid of `σ_0^m` is the `m`-th power of the cabled half twist. -/
private theorem braidMatrix_cable_replicate_torusTrace (a m : ℕ) :
    braidMatrix (2 * a) (cable a (List.replicate m (0, true))) = halfTwist a true ^ m := by
  induction m with
  | zero => simp only [List.replicate_zero, cable, List.flatMap_nil, braidMatrix_nil, pow_zero]
  | succ m ih =>
    have hw : cable a (List.replicate (m + 1) (0, true)) =
        cableGen a (0, true) ++ cable a (List.replicate m (0, true)) := by
      simp only [cable, List.replicate_succ, List.flatMap_cons]
    rw [hw, braidMatrix_append, ih, pow_succ']
    rfl

/-- A power of the half twist acts on a channel idempotent by the power of its eigenvalue. -/
private theorem halfTwist_pow_mul_channelIdem_torusTrace (a j m : ℕ) (hj : j ≤ a) :
    halfTwist a true ^ m * channelIdem a j =
      claspAlgHalfTwistEigen a j ^ m • channelIdem a j := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, one_smul]
  | succ m ih =>
    have h := halfTwist_mul_channelIdem a j true hj
    simp only [↓reduceIte] at h
    rw [pow_succ, Matrix.mul_assoc, h, Matrix.mul_smul, ih, smul_smul, pow_succ,
      mul_comm (claspAlgHalfTwistEigen a j)]

/-- A positive power of the half twist on two bundles with projectors, by channels. -/
private theorem halfTwist_pow_mul_twoBundleProj_torusTrace (a m : ℕ) :
    halfTwist a true ^ (m + 1) * twoBundleProj a =
      ∑ j ∈ Finset.range (a + 1), claspAlgHalfTwistEigen a j ^ (m + 1) • channelIdem a j := by
  have hTB : halfTwist a true * twoBundleProj a =
      ∑ j ∈ Finset.range (a + 1), claspAlgHalfTwistEigen a j • channelIdem a j := by
    have h := halfTwist_mul_twoBundleProj_eq_sum a true
    simpa only [↓reduceIte] using h
  rw [pow_succ, Matrix.mul_assoc, hTB, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Matrix.mul_smul, halfTwist_pow_mul_channelIdem_torusTrace a j m
    (by have := Finset.mem_range.mp hj; omega), smul_smul, pow_succ,
    mul_comm (claspAlgHalfTwistEigen a j)]

/-- The cabled bracket of the torus knot with projectors on both bundles, the number of strands
a free parameter. -/
private theorem qtr_cable_torusWord_mul_jwAt_torusTrace (k a : ℕ) :
    ∀ N : ℕ, N = 2 * a →
      qtr N (braidMatrix N (cable a (torusWord k)) * (jwAt N 0 a * jwAt N a a)) =
        qtr (2 * a) (halfTwist a true ^ (2 * k + 1) * twoBundleProj a) := by
  intro N hN
  subst hN
  rw [torusWord, braidMatrix_cable_replicate_torusTrace]
  rfl

/-- The bracket of the `a`-cable of `T(2, 2k+1)` with the projector `f_a`. -/
private theorem knotTrace_torusKnot_jwAt_torusTrace (k a : ℕ) :
    knotTrace (torusKnot k) a (jwAt a 0 a) =
      ∑ j ∈ Finset.range (a + 1),
        claspAlgHalfTwistEigen a j ^ (2 * k + 1) * quantumInt (2 * (j : ℤ) + 1) := by
  have hcols := knotTrace_jwAt_eq_qtr_cols (torusKnot k) a [1] (by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact Nat.one_lt_two)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hcols
  rw [hcols]
  refine (qtr_cable_torusWord_mul_jwAt_torusTrace k a (a * 2) (Nat.mul_comm a 2)).trans ?_
  rw [halfTwist_pow_mul_twoBundleProj_torusTrace, qtr_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [qtr_smul, qtr_channelIdem a j (by have := Finset.mem_range.mp hj; omega)]

/-- The trace of the long knot of `T(2, 2k+1)` on the channel of colour `2n` of two bundles. -/
theorem qtr_longKnotOp_torusKnot_mul_channelIdem (k n m : ℕ) :
    qtr (2 * (n + m)) (longKnotOp (torusKnot k) (2 * (n + m)) * channelIdem (n + m) n) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) *
        torusOddColor (2 * k + 1) n := by
  rw [qtr_longKnotOp_mul_channelIdem, knotTrace_torusKnot_jwAt_torusTrace,
    claspAlg_sum_halfTwistEigen_pow_torus]

end AJConjecture
