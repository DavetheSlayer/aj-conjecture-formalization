import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinThickCrossCap
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinPtrTailCyclic
import AJConjecture.SkeinTracePairing
import AJConjecture.SkeinTraceCyclic
import AJConjecture.SkeinWeightPlace

/-!
# A cap moves around a loop; cyclicity of a loop (node RA5.i.3)

In the loop operator `ω_k(Y) = ptr(J_(N,k) (1_N ⊗ Y))`: a cap on the loop strands can be moved
from the end of the operator to its beginning (`ω_(k+2)(cap · G) = ω_k(G · cap)`), and operators
that slide through the twist can be moved cyclically (`ω_k(A B) = ω_k(B A)`).

Route. (N3) `capAt_mul_braidMatrix_thickCross_fst`, `_snd` give
`J_(N,k+2) · (1_N ⊗ cap_j) = (1_N ⊗ cap_j) · J_(N,k)` (the cap passes both crossings of the full
twist). Cyclicity of the partial trace over the closed strands, for operators acting on those
strands only and intertwining the weights: test against every `G'` (`eq_of_forall_qtr_mul_eq`),
rewrite `qtr (ptr Z · G') = qtr (Z · (G' ⊗ 1))` (`qtr_eq_qtr_ptrTail`, `ptrTail_mul_skPlace`) and
use `qtr_mul_comm_of_weight` with the interchange law (the analogue of `knotTrace_capAt_mul` for
the loop). Estimate 120–180 lines.
-/

noncomputable section

namespace AJConjecture

/-- Cyclicity of the partial trace over the last strands, for an operator acting on those
strands only and intertwining the weights. -/
private theorem ptrTail_skPlace_mul_comm_loopCap (N p q : ℕ) (A : SkMat p q)
    (Z : SkMat (N + q) (N + p)) (hA : skWeight p * A = A * skWeight q) :
    ptrTail N (N + p) (skPlace (N + p) (N + q) N A * Z) =
      ptrTail N (N + q) (Z * skPlace (N + p) (N + q) N A) := by
  refine eq_of_forall_qtr_mul_eq N N _ _ fun G ↦ ?_
  have hc := skPlace_mul_skPlace_comm (N + p) (N + p) (N + q) (N + q) 0 N G A (by omega)
    (by omega) (by omega) (by omega) (by omega)
  rw [show N + N - N = N by omega] at hc
  rw [← ptrTail_mul_skPlace N (N + p) (by omega), ← qtr_eq_qtr_ptrTail N (N + p) (by omega),
    ← ptrTail_mul_skPlace N (N + q) (by omega), ← qtr_eq_qtr_ptrTail N (N + q) (by omega),
    Matrix.mul_assoc, qtr_mul_comm_of_weight (N + p) (N + q) _ _
      (skWeight_mul_skPlace _ _ _ A hA), Matrix.mul_assoc, hc, Matrix.mul_assoc]

/-- A cap on the loop strands passes through the full twist. -/
private theorem rjFullTwist_mul_capAt_loopCap (N k j : ℕ) (hj : j ≤ k) :
    rjFullTwist N (k + 2) * capAt (N + k) (N + j) = capAt (N + k) (N + j) * rjFullTwist N k := by
  have h1 := capAt_mul_braidMatrix_thickCross_snd (N + k) N k 0 j true (by omega) hj
  have h2 := capAt_mul_braidMatrix_thickCross_fst (N + k) k N 0 j true (by omega) hj
  simp only [zero_add] at h1 h2
  rw [rjFullTwist, rjFullTwist, braidMatrix_append, braidMatrix_append]
  change braidMatrix (N + k + 2) (thickCross N (k + 2) 0 true) *
    braidMatrix (N + k + 2) (thickCross (k + 2) N 0 true) * capAt (N + k) (N + j) = _
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, ← h1, Matrix.mul_assoc]

/-- A cap on the loop strands moves around the loop. -/
theorem rj_loopWith_capAt_mul (N k j : ℕ) (hj : j ≤ k) (G : SkMat k (k + 2)) :
    rjLoopWith N (k + 2) (capAt k j * G) = rjLoopWith N k (G * capAt k j) := by
  have hcap : skPlace (N + (k + 2)) (N + k) N (capAt k j) = capAt (N + k) (N + j) := by
    rw [capAt, skPlace_skPlace _ _ N j skCap (by omega) (by omega) (by omega) (by omega)]
    rfl
  rw [rjLoopWith, rjLoopWith,
    skPlace_mul (N + (k + 2)) (N + k) (N + (k + 2)) N _ _ (by omega) (by omega) (by omega),
    skPlace_mul (N + k) (N + (k + 2)) (N + k) N _ _ (by omega) (by omega) (by omega), hcap,
    ← Matrix.mul_assoc, rjFullTwist_mul_capAt_loopCap N k j hj, Matrix.mul_assoc, ← hcap,
    ptrTail_skPlace_mul_comm_loopCap N (k + 2) k _ _ (skWeight_mul_capAt k j),
    Matrix.mul_assoc]

/-- Operators on the loop strands that slide through the full twist move cyclically. -/
theorem rj_loopWith_mul_comm (N k : ℕ) (A B : SkMat k k)
    (hA : rjFullTwist N k * skPlace (N + k) (N + k) N A =
      skPlace (N + k) (N + k) N A * rjFullTwist N k)
    (hAw : skWeight k * A = A * skWeight k) :
    rjLoopWith N k (A * B) = rjLoopWith N k (B * A) := by
  rw [rjLoopWith, rjLoopWith, skPlace_mul (N + k) (N + k) (N + k) N _ _ (by omega) rfl rfl,
    skPlace_mul (N + k) (N + k) (N + k) N _ _ (by omega) rfl rfl, ← Matrix.mul_assoc, hA,
    Matrix.mul_assoc, ptrTail_skPlace_mul_comm_loopCap N k k A _ hAw, Matrix.mul_assoc]

end AJConjecture
