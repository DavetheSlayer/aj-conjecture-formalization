import Mathlib
import AJConjecture.SkeinJwCupCap
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinLongKnotCap
import AJConjecture.SkeinLongKnotJw

/-!
# The Chebyshev recursion for projectors on a cabled knot

With `a_{i,j} = Tr_{K,i+j}(f_j ⊗ 1_i)`: `a_{i,j+2} = a_{i+1,j+1} - a_{i,j}`. Wenzl's recursion gives
`f_{j+2} = f_{j+1} + ([j+1]/[j+2]) f_{j+1} e_j f_{j+1}`. The long knot commutes with `f_{j+1}`
(`AJConjecture.longKnotOp_commute_jwAt`) and `f_{j+1}` commutes with the weight
(`AJConjecture.skWeight_mul_jwAt`), so `Tr(f e_j f) = Tr(e_j f)` by
`AJConjecture.knotTrace_eq_qtr_longKnotOp` and the cyclicity of the trace; `e_j = capAt * cupAt`
(`AJConjecture.capAt_mul_cupAt`), the cap moves around the knot
(`AJConjecture.knotTrace_capAt_mul` with `G = cupAt * f`), and closing the last strand of
`f_{j+1}` gives `-([j+2]/[j+1]) f_j` (`AJConjecture.cupAt_mul_jwAt_mul_capAt`).
-/

namespace AJConjecture

/-- The quantum trace is additive. -/
private theorem qtr_add_jwStep (n : ℕ) (A B : SkMat n n) :
    qtr n (A + B) = qtr n A + qtr n B := by
  simp only [qtr, Matrix.mul_add, Matrix.trace_add]

/-- The quantum trace is homogeneous. -/
private theorem qtr_smul_jwStep (n : ℕ) (x : RatFunc ℚ) (A : SkMat n n) :
    qtr n (x • A) = x * qtr n A := by
  simp only [qtr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- The knot trace is linear in the inserted operator. -/
private theorem knotTrace_add_smul_jwStep (K : BraidKnot) (k : ℕ) (x : RatFunc ℚ)
    (Y Z : SkMat k k) :
    knotTrace K k (Y + x • Z) = knotTrace K k Y + x * knotTrace K k Z := by
  simp only [knotTrace_eq_qtr_longKnotOp, Matrix.mul_add, Matrix.mul_smul, qtr_add_jwStep,
    qtr_smul_jwStep]

/-- The knot trace of `f_{j+1} e_j f_{j+1}` is `-([j+2]/[j+1])` times the knot trace of `f_j` on
two strands less. -/
private theorem knotTrace_jwAt_mul_tlGenF_mul_jwAt_jwStep (K : BraidKnot) (k j : ℕ)
    (hj : j ≤ k) :
    knotTrace K (k + 2) (jwAt (k + 2) 0 (j + 1) * tlGenF (k + 2) j * jwAt (k + 2) 0 (j + 1)) =
      -(quantumInt ((j : ℤ) + 2) / quantumInt ((j : ℤ) + 1)) * knotTrace K k (jwAt k 0 j) := by
  have hc := (longKnotOp_commute_jwAt K (k + 2) 0 (j + 1)).eq
  rw [knotTrace_eq_qtr_longKnotOp]
  calc qtr (k + 2) (longKnotOp K (k + 2) *
        (jwAt (k + 2) 0 (j + 1) * tlGenF (k + 2) j * jwAt (k + 2) 0 (j + 1)))
      = qtr (k + 2) (jwAt (k + 2) 0 (j + 1) *
          (longKnotOp K (k + 2) * tlGenF (k + 2) j * jwAt (k + 2) 0 (j + 1))) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc]
        simp only [Matrix.mul_assoc]
    _ = qtr (k + 2) (longKnotOp K (k + 2) * tlGenF (k + 2) j * jwAt (k + 2) 0 (j + 1) *
          jwAt (k + 2) 0 (j + 1)) :=
        qtr_mul_comm_of_weight _ _ _ _ (skWeight_mul_jwAt _ _ _)
    _ = knotTrace K (k + 2) (capAt k j * (cupAt k j * jwAt (k + 2) 0 (j + 1))) := by
        rw [Matrix.mul_assoc (longKnotOp K (k + 2) * tlGenF (k + 2) j), jwAt_mul_self,
          Matrix.mul_assoc, knotTrace_eq_qtr_longKnotOp, ← Matrix.mul_assoc (capAt k j),
          capAt_mul_cupAt k j hj]
    _ = knotTrace K k (cupAt k j * jwAt (k + 2) 0 (j + 1) * capAt k j) :=
        knotTrace_capAt_mul K k j hj _
    _ = -(quantumInt ((j : ℤ) + 2) / quantumInt ((j : ℤ) + 1)) * knotTrace K k (jwAt k 0 j) := by
        rw [cupAt_mul_jwAt_mul_capAt k j hj, knotTrace_eq_qtr_longKnotOp, Matrix.mul_smul,
          qtr_smul_jwStep, ← knotTrace_eq_qtr_longKnotOp]

/-- The recursion `a_{i,j+2} = a_{i+1,j+1} - a_{i,j}` of the projector-coloured cabled knot. -/
theorem knotTrace_jwAt_succ_succ (K : BraidKnot) (k j : ℕ) (hj : j ≤ k) :
    knotTrace K (k + 2) (jwAt (k + 2) 0 (j + 2)) =
      knotTrace K (k + 2) (jwAt (k + 2) 0 (j + 1)) - knotTrace K k (jwAt k 0 j) := by
  have h1 : quantumInt ((j : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h2 : quantumInt ((j : ℤ) + 2) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hw : jwAt (k + 2) 0 (j + 2) = jwAt (k + 2) 0 (j + 1) +
      (quantumInt ((j : ℤ) + 1) / quantumInt ((j : ℤ) + 2)) •
        (jwAt (k + 2) 0 (j + 1) * tlGenF (k + 2) j * jwAt (k + 2) 0 (j + 1)) := by
    rw [jwAt, Nat.zero_add]
  rw [hw, knotTrace_add_smul_jwStep, knotTrace_jwAt_mul_tlGenF_mul_jwAt_jwStep K k j hj]
  field_simp
  ring

end AJConjecture
