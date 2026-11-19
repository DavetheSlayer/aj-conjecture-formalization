import Mathlib
import AJConjecture.SkeinKnotTraceJwStep
import AJConjecture.SkeinFusionComplete
import AJConjecture.SkeinLongKnotJw
import AJConjecture.SkeinLongKnotNest

/-!
# The long knot on the channels of two bundles

For a closed braid `K` and two bundles of `c = n + m` strands running along `K` (the `2c`-cable
cut open), with `Λ(k)` the long knot of the `k`-cable:

* `Λ(2c)` commutes with `f ⊗ f` (`AJConjecture.longKnotOp_commute_jwAt`);
* `Λ(2c) π = π Λ(2n)` for the fusion map `π = (f ⊗ f) · caps · f_{2n}`: the long knot commutes with
  `f ⊗ f`, passes the nest of caps (`AJConjecture.capThick_mul_longKnotOp`) and commutes with
  `f_{2n}`;
* hence `qtr(Λ(2c) Q_n) = qtr(Λ(2n) f_{2n})`, the bracket of the `2n`-cable of `K` with the
projector
  `f_{2n}`: `d Q_n = π ι` (`AJConjecture.fusionProj_mul_fusionIncl`), `π` moves cyclically under the
  trace (`AJConjecture.qtr_mul_comm_of_weight`, `AJConjecture.skWeight_mul_fusionProj`),
  `ι π = d f_{2n}` (`AJConjecture.fusionIncl_mul_fusionProj`) and `d ≠ 0`
  (`AJConjecture.turnbackEigen_ne_zero`); the right-hand side is
  `AJConjecture.knotTrace_eq_qtr_longKnotOp`;
* if moreover `Λ(2n)` acts on the projector `f_{2n}` by a scalar `τ`, then `Λ(2c) Q_n = τ Q_n`.

The trace identity is the form in which the long knot of the companion enters the evaluation of
the band-and-clasp diagram; it needs no hypothesis. That the long knot always acts on the
projector by a scalar is true in all computed cases, but it is a statement of Schur type that
the calculus developed here does not prove, so it is a hypothesis of the last statement.
-/

namespace AJConjecture

/-- The quantum trace is homogeneous. -/
private theorem qtr_smul_longKnotChannel (n : ℕ) (x : RatFunc ℚ) (A : SkMat n n) :
    qtr n (x • A) = x * qtr n A := by
  simp only [qtr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- The long knot of the `2c`-cable commutes with `f ⊗ f`. -/
theorem longKnotOp_commute_twoBundleProj (K : BraidKnot) (c : ℕ) :
    Commute (longKnotOp K (2 * c)) (twoBundleProj c) :=
  (longKnotOp_commute_jwAt K (2 * c) 0 c).mul_right (longKnotOp_commute_jwAt K (2 * c) c c)

/-- The long knot passes through the fusion map `π`. -/
theorem longKnotOp_mul_fusionProj (K : BraidKnot) (n m : ℕ) :
    longKnotOp K (2 * (n + m)) * fusionProj n m = fusionProj n m * longKnotOp K (2 * n) := by
  unfold fusionProj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (longKnotOp_commute_twoBundleProj K (n + m)).eq,
    Matrix.mul_assoc (twoBundleProj (n + m)), ← capThick_mul_longKnotOp K (2 * (n + m)) (2 * n) n m
      (by omega) (by omega), Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, (longKnotOp_commute_jwAt K (2 * n) 0 (2 * n)).eq]

/-- The quantum trace of the long knot on the channel of colour `2n` is the bracket of the
`2n`-cable with the projector `f_{2n}`. -/
theorem qtr_longKnotOp_mul_channelIdem (K : BraidKnot) (n m : ℕ) :
    qtr (2 * (n + m)) (longKnotOp K (2 * (n + m)) * channelIdem (n + m) n) =
      knotTrace K (2 * n) (jwAt (2 * n) 0 (2 * n)) := by
  have hd : claspAlgTurnbackEigen (n + m) m n ≠ 0 := turnbackEigen_ne_zero (n + m) m n (by omega)
  have hQ : channelIdem (n + m) n =
      (claspAlgTurnbackEigen (n + m) m n)⁻¹ • (fusionProj n m * fusionIncl n m) := by
    rw [fusionProj_mul_fusionIncl, smul_smul, inv_mul_cancel₀ hd, one_smul]
  rw [hQ, Matrix.mul_smul, qtr_smul_longKnotChannel, ← Matrix.mul_assoc,
    longKnotOp_mul_fusionProj, Matrix.mul_assoc,
    qtr_mul_comm_of_weight _ _ (fusionProj n m) _ (skWeight_mul_fusionProj n m),
    Matrix.mul_assoc, fusionIncl_mul_fusionProj, Matrix.mul_smul, qtr_smul_longKnotChannel,
    ← mul_assoc, inv_mul_cancel₀ hd, one_mul, knotTrace_eq_qtr_longKnotOp]

end AJConjecture
