import Mathlib
import AJTwist.Quantum.TwQTarget
import AJTwist.Quantum.TwQCramerOp

/-!
# The operators `P_a` for every integer `a`, and the weight operators (Unit Q3)

Source: revision 5, Section 3.3, eq. (physicalrow): `𝒩_a = ∑_i a_i(q, x) Δ R_i`,
`P_a = ∑_i a_i(q, M²) u^i`; "both chiralities give identical coefficients at a fixed `a`".
Section 6.3: `J^z = ∑_i d_i^{[z]} Δ R_i`, `D^{[z]} = ∑_i d_i^{[z]} u^i`.

* `twTransferOp a = twCramerOp (twWindow a) (twTarget a t⁴)` is `P_a` in the library's
  conventions: forward shift, order `d = twWindow a`, coefficients the Cramer numerators (the
  paper's `a_i` times a nonzero function of `(q, x)`). For `a = m ≥ 1` it **is** the library's
  `famTransferOp m` (`twTransferOp_natCast`), so every library theorem on `famTransferOp` applies.
* `twWeightOp d z = twCramerOp d (J^z)` is `D^{[z]}` for the window `d`, with the same
  normalization (the same determinant) as `twTransferOp`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The operator `P_a` of order `twWindow a`, for every integer `a`. -/
def twTransferOp (a : ℤ) : RecOp :=
  twCramerOp (twWindow a) (twTarget a (X ^ 4))

/-- The weight operator `D^{[z]}` of the window `d`: the operator of the target `J^z`. -/
def twWeightOp (d z : ℕ) : RecOp :=
  twCramerOp d (X ^ z)

/-- For `a = m ≥ 1` the operator `P_a` is the library's `famTransferOp m`. -/
theorem twTransferOp_natCast (m : ℕ) (hm : 1 ≤ m) : twTransferOp (m : ℤ) = famTransferOp m := by
  rw [twTransferOp, twWindow_natCast, twTarget_natCast m hm]
  rfl

theorem twTransferOp_zero : twTransferOp 0 = twCramerOp 3 (twZeroTarget (X ^ 4)) := by
  rw [twTransferOp, twWindow_zero, twTarget_zero]

theorem twTransferOp_neg_natCast (b : ℕ) (hb : 1 ≤ b) :
    twTransferOp (-(b : ℤ)) = twCramerOp (2 * b + 2) (twNegTarget b (X ^ 4)) := by
  rw [twTransferOp, twWindow_neg_natCast b hb, twTarget_neg_natCast b hb]

/-- The Cramer identity of `P_a` over every commutative ring:
`∑_i c_i P_i = det · (q^d x)^(|a|+1) 𝒩_a`. -/
theorem sum_twCoeff_mul_twBasisPoly_twTarget {R : Type*} [CommRing R] (a : ℤ) (q : R) :
    ∑ i : Fin (twWindow a + 1),
        C (twCoeff (twWindow a) q (twTarget a q) i) * twBasisPoly (twWindow a) q i =
      C (twDet (twWindow a) q) * twTarget a q :=
  sum_twCoeff_mul_twBasisPoly _ q _ (natDegree_twTarget_le a q)

end AJConjecture
