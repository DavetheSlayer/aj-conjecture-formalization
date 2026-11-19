import Mathlib
import AJConjecture.WitnessPolynomials
import AJConjecture.QAlgSymbolMoebiusExtra
import AJFamily.Quantum.TwistPolyMoebius
import AJTwist.Quantum.TwQTwistPolyNeg
import AJTwist.Factor.TwFMoebiusChain

/-!
# The blocks as stationary pullbacks (TwF)

Source: revision 5, Section 3.4 (`transfer.tex`): `Π_a = (1 - J)(Z + 2) T_a`, and the blocks
`L - 1`, `E`, `B_a`, `C_b` are the pullbacks of `1 - J`, `x (Z + 2) = ζ + 2x`, `x^a T_a`,
`x^b T_(-b)` under `J = (x L + 1)/(L + x)`, `x = M²`; Section 5.1:
`Z_num = (x + 1)² E - 2x (L + x)² = x (L + x)² Z`.

* `twfPullback 1 (1 - J) = (1 - x)(L - 1)`;
* `twfPullback 2 (ζ + 2x) = (x + 1)² E`;
* `twfPullback (2k) (symbolTwist k) = twistPoly k` (the library's `map_moebiusSubst_symbolTwist`);
* `twfPullback (2b - 1) (symbolTwistNeg b) = twistPolyNeg b` (the definition).

With `AJTwist/Factor/TwFMoebiusChain.lean` these turn values, first derivatives and Jacobians of
the blocks at a point `(m₀, l₀)` into those of their sources at `(m₀², J₀)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `(L + x) (1 - J) = (1 - x)(L - 1)`. -/
theorem twfPullback_one_sub_X : twfPullback 1 (1 - X) = C (1 - X ^ 2) * (X - 1) := by
  simp [twfPullback, moebiusSubst, Finset.sum_range_succ, coeff_one, coeff_X]
  ring

/-- `(L + x)² (ζ + 2x) = (x + 1)² E`. -/
theorem twfPullback_symbolZeta_add :
    twfPullback 2 (symbolZeta + C (2 * X)) = C ((X ^ 2 + 1) ^ 2) * extraFactor :=
  map_moebiusSubst_symbolZeta_add

/-- `ζ + 2x` has degree at most `2` in `J`. -/
theorem natDegree_symbolZeta_add_le : (symbolZeta + C (2 * X) : ℤ[X][X]).natDegree ≤ 2 := by
  rw [symbolZeta]
  compute_degree

/-- `B_k` is the stationary pullback of `T̂_k`. -/
theorem twfPullback_symbolTwist (k : ℕ) : twfPullback (2 * k) (symbolTwist k) = twistPoly k :=
  map_moebiusSubst_symbolTwist k

/-- `C_b` is the stationary pullback of `T̂_(-b)`. -/
theorem twfPullback_symbolTwistNeg (b : ℕ) :
    twfPullback (2 * b - 1) (symbolTwistNeg b) = twistPolyNeg b :=
  rfl

end AJConjecture
