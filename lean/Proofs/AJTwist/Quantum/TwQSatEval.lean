import Mathlib
import AJTwist.Quantum.TwQSatTrace
import AJTwist.Quantum.TwQClaspEigen
import AJHandoff.TorusQuantum.PairQSatelliteEval

/-!
# Evaluation of the twisted band-and-clasp trace (Unit Q2)

Let the bracket of the `2n`-cable of the companion `C` with the projector `f_{2n}` be
`t^(4 w n(n+1)) u_n` for every `n` (`hC`: `u_n` is the zero-framed coloured Jones polynomial of
`C` at the colour `2n + 1` when `w` is the writhe of `C`; `w` may be negative). With `2κ` signed
half twists the band has framing `w + κ` and:

* negative clasp (`twSatTrace_true_eq`):
  `twSatTrace C (2κ) true c = (-1)^c θ_c^(-2κ-2) [c+1] F_{c+1}(v)`, `v_n = q^((w+κ) n(n+1)) u_n`;
* positive clasp (`twSatTrace_false_eq`):
  `twSatTrace C (2κ) false c = (-1)^c θ_c^(-2κ+2) \overline{[c+1] F_{c+1}(v')}`,
  `v'_n = q^(-(w+κ) n(n+1)) \bar u_n`.

Route: as `pairQSatTrace_eq`. The band operator is diagonal on the channels
(`halfTwistZ_mul_channelIdem`, `twoBundleProj_mul_claspSOp_mul_twoBundleProj_eq_sum`), the trace
of the long knot of `C` on `Q_n` is the bracket of `f_{2n}` (`qtr_longKnotOp_mul_channelIdem`),
the framing scalars combine by `twQ_halfTwistEigen_zpow_mul`, and the channel sum is
`pairQ_sum_claspEigen_mul` (applied to `v'` and then barred for the positive clasp).

Both statements were checked in the matrix model of the library for the unknot, `T(2,3)` and its
mirror at `c = 1, 2` (scratch `check_clasp.py`, `check_clasp_mirror.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The quantum trace of a finite sum. -/
private theorem qtr_sum_twQSatEval (n : ℕ) (s : Finset ℕ) (f : ℕ → SkMat n n) :
    qtr n (∑ i ∈ s, f i) = ∑ i ∈ s, qtr n (f i) := by
  simp only [qtr, Matrix.mul_sum, Matrix.trace_sum]

/-- The trace of the long knot of the companion on the channel `Q_n`, for `n ≤ c`. -/
private theorem qtr_longKnotOp_mul_channelIdem_twQSatEval (C : BraidKnot) (w : ℤ)
    (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (c n : ℕ) (hn : n ≤ c) :
    qtr (2 * c) (longKnotOp C (2 * c) * channelIdem c n) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) * u n := by
  obtain ⟨m, rfl⟩ : ∃ m, c = n + m := ⟨c - n, by omega⟩
  rw [qtr_longKnotOp_mul_channelIdem, hC]

/-- The operator of the twisted band-and-clasp trace on the channels. -/
private theorem twSatOp_eq_sum_channelIdem_twQSatEval (k : ℤ) (σ : Bool) (c : ℕ) :
    twoBundleProj c * halfTwistZ c k * claspSOp c σ * twoBundleProj c =
      ∑ n ∈ Finset.range (c + 1),
        (twClaspEigen σ c n * (claspAlgHalfTwistEigen c n) ^ k) • channelIdem c n := by
  rw [← (halfTwistZ_commute_twoBundleProj c k).eq, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc (twoBundleProj c),
    twoBundleProj_mul_claspSOp_mul_twoBundleProj_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Matrix.mul_smul, halfTwistZ_mul_channelIdem c n k
    (by have := Finset.mem_range.mp hn; omega), smul_smul]

/-- An even power of the kink scalar is a power of `t`. -/
private theorem kinkScalar_zpow_two_mul_twQSatEval (c : ℕ) (e : ℤ) :
    kinkScalar c ^ (2 * e) = (RatFunc.X : RatFunc ℚ) ^ (2 * e * (c : ℤ) * ((c : ℤ) + 2)) := by
  have h1 : ((-1 : RatFunc ℚ) ^ c) ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [kinkScalar, mul_zpow, zpow_mul ((-1 : RatFunc ℚ) ^ c) 2, h1, one_zpow, one_mul,
    ← zpow_mul]
  congr 1
  ring

/-- The framing scalar of the twisted trace: `(-1)^c θ_c^(2e) (-1)^c t^m = t^(2e c(c+2) + m)`. -/
private theorem kinkScalar_zpow_mul_twQSatEval (c : ℕ) (e m : ℤ) :
    (-1 : RatFunc ℚ) ^ c * kinkScalar c ^ (2 * e) * ((-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ m) =
      (RatFunc.X : RatFunc ℚ) ^ (2 * e * (c : ℤ) * ((c : ℤ) + 2) + m) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hs : (-1 : RatFunc ℚ) ^ c * (-1) ^ c = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [kinkScalar_zpow_two_mul_twQSatEval, zpow_add₀ hX]
  linear_combination ((RatFunc.X : RatFunc ℚ) ^ (2 * e * (c : ℤ) * ((c : ℤ) + 2)) *
    (RatFunc.X : RatFunc ℚ) ^ m) * hs

/-- The twisted band-and-clasp trace as a sum over the channels. -/
theorem twSatTrace_eq_sum (C : BraidKnot) (w κ : ℤ) (σ : Bool) (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (c : ℕ) :
    twSatTrace C (2 * κ) σ c =
      (RatFunc.X : RatFunc ℚ) ^ (-(2 * κ) * (c : ℤ) * ((c : ℤ) + 2)) *
        ∑ n ∈ Finset.range (c + 1), twClaspEigen σ c n *
          (qParam ^ ((w + κ) * (n : ℤ) * ((n : ℤ) + 1)) * u n) := by
  rw [twSatTrace, knotTrace_eq_qtr_longKnotOp, twSatOp_eq_sum_channelIdem_twQSatEval,
    Finset.mul_sum, qtr_sum_twQSatEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Matrix.mul_smul, qtr_smul, qtr_longKnotOp_mul_channelIdem_twQSatEval C w u hC
    c n (by have := Finset.mem_range.mp hn; omega), mul_assoc, ← mul_assoc (_ ^ (2 * κ)),
    twQ_halfTwistEigen_zpow_mul]
  ring

/-- The twisted trace with the negative clasp. -/
theorem twSatTrace_true_eq (C : BraidKnot) (w κ : ℤ) (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (c : ℕ) :
    twSatTrace C (2 * κ) true c =
      (-1) ^ c * kinkScalar c ^ (-(2 * κ) - 2) *
        pairQFormula (fun n ↦ qParam ^ ((w + κ) * (n : ℤ) * ((n : ℤ) + 1)) * u n)
          ((c : ℤ) + 1) := by
  have he : -(2 * κ) - 2 = 2 * (-κ - 1) := by ring
  rw [twSatTrace_eq_sum C w κ true u hC, ← pairQ_sum_claspEigen_mul, ← mul_assoc, he,
    kinkScalar_zpow_mul_twQSatEval]
  congr 2
  ring

/-- The twisted trace with the positive clasp. -/
theorem twSatTrace_false_eq (C : BraidKnot) (w κ : ℤ) (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (c : ℕ) :
    twSatTrace C (2 * κ) false c =
      (-1) ^ c * kinkScalar c ^ (-(2 * κ) + 2) *
        twQBar (pairQFormula
          (fun n ↦ qParam ^ (-((w + κ) * (n : ℤ) * ((n : ℤ) + 1))) * twQBar (u n))
          ((c : ℤ) + 1)) := by
  have he : -(2 * κ) + 2 = 2 * (-κ + 1) := by ring
  rw [twSatTrace_eq_sum C w κ false u hC, ← pairQ_sum_claspEigen_mul, map_mul, map_mul,
    map_pow, map_neg, map_one, twQBar_X_zpow, ← mul_assoc, he, kinkScalar_zpow_mul_twQSatEval,
    map_sum]
  congr 1
  · congr 1
    ring
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [map_mul, map_mul, twQBar_qParam_zpow, twQBar_twQBar, neg_neg]
    rfl

end AJConjecture
