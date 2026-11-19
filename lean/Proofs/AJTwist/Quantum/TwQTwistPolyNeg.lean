import Mathlib
import AJFamily.Quantum.TwistPoly
import AJFamily.Quantum.TwistPolyMoebius

/-!
# The cleared twist polynomials `C_b` of negative index (Unit Q3)

Source: revision 5, Section 3.4 (`transfer.tex`, eq. (B)):
`C_k = x^k (L + x)^(2k-1) T_(-k)`, where `T_0 = 1`, `T_1 = Z - 1 + e`, `T_(k+1) = Z T_k - T_(k-1)`
extended to all integers (`T_(-1) = 1 - e = K - J`); Section 5.1 (`operators.tex`, "Retention of
the shift endpoints"): `C_1 = L + x³`, `C_2 = Z_num C_1 - x² (L + x)³`,
`C_(k+1) = Z_num C_k - x² (L + x)⁴ C_(k-1)` for `k ≥ 2`; `C_b` is monic of degree `2b - 1`, has
constant `x^(4b-1)`, and `C_b(x, -x) = x^b (x² - 1)^(2b-1)`.

* `symbolTwistNeg k = x^k T_(-k)` in `ℤ[x][J]`, next to the library's `symbolTwist k = x^k T_k`
  (the same recursion `T̂_(k+2) = ζ T̂_(k+1) - x² T̂_k`, initial values `1`, `x² + 1 - x J`).
* `twistPolyNeg b` is `C_b` in `ℤ[M][L]` (`x = M²`), **defined** as the stationary pullback
  `(L + x)^(2b-1) T̂_(-b)(J(L))`, `J = (x L + 1)/(L + x)`, next to the library's
  `twistPoly k = B_k`. The paper's recurrence and the four properties are theorems; `Z_num` is the
  library's `zetaMoebiusM`. (`twistPolyNeg 0 = 1`; the paper defines `C_b` for `b ≥ 1`.)

This file has the recurrence; the four properties are in `AJTwist.Quantum.TwQTwistPolyNegFacts`.
All statements were checked exactly for `b ≤ 6` (scratch `check_symbol_mod.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `T̂_(-k) = x^k T_(-k)(Z, e)` in `ℤ[x][J]`: `T̂_0 = 1`, `T̂_(-1) = x² + 1 - x J`,
`T̂_(-(k+2)) = ζ T̂_(-(k+1)) - x² T̂_(-k)`. -/
def symbolTwistNeg : ℕ → ℤ[X][X]
  | 0 => 1
  | 1 => C (X ^ 2 + 1) - C X * X
  | k + 2 => symbolZeta * symbolTwistNeg (k + 1) - C (X ^ 2) * symbolTwistNeg k

/-- The cleared twist polynomial `C_b(M, L) = x^b (L + x)^(2b-1) T_(-b)`, `x = M²`: the
stationary pullback of `symbolTwistNeg b`. -/
def twistPolyNeg (b : ℕ) : ℤ[X][X] :=
  (moebiusSubst (2 * b - 1) (symbolTwistNeg b)).map (Polynomial.compRingHom (X ^ 2))

/-- `T̂_(-b)` has degree at most `2b - 1` in `J`. -/
theorem natDegree_symbolTwistNeg_le (b : ℕ) (hb : 1 ≤ b) :
    (symbolTwistNeg b).natDegree ≤ 2 * b - 1 := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    match b, hb, ih with
    | 1, _, _ =>
      rw [symbolTwistNeg]
      compute_degree
    | 2, _, ih =>
      rw [symbolTwistNeg]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le_of_le natDegree_symbolZeta_le (ih 1 (by omega) le_rfl)
      · rw [symbolTwistNeg, mul_one, natDegree_C]
        omega
    | k + 3, _, ih =>
      rw [symbolTwistNeg]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le_of_le natDegree_symbolZeta_le (ih (k + 2) (by omega) (by omega))
          |>.trans (by omega)
      · exact natDegree_C_mul_le _ _ |>.trans
          ((ih (k + 1) (by omega) (by omega)).trans (by omega))

/-- `C_1 = L + x³`. -/
theorem twistPolyNeg_one : twistPolyNeg 1 = X + C (X ^ 6) := by
  rw [twistPolyNeg, symbolTwistNeg, moebiusSubst_sub, moebiusSubst_C_mul,
    show 2 * 1 - 1 = 0 + 1 from rfl, moebiusSubst_X, ← mul_one (C (X ^ 2 + 1)),
    moebiusSubst_C_mul, moebiusSubst_one]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, coe_compRingHom_apply, X_comp,
    pow_zero, mul_one, C_add, C_pow, C_1]
  ring

/-- `C_2 = Z_num C_1 - x² (L + x)³`. -/
theorem twistPolyNeg_two :
    twistPolyNeg 2 = zetaMoebiusM * twistPolyNeg 1 - C (X ^ 4) * (C (X ^ 2) + X) ^ 3 := by
  have h1 : moebiusSubst (2 * 2 - 1) (symbolZeta * symbolTwistNeg 1) =
      symbolZetaMoebius * moebiusSubst (2 * 1 - 1) (symbolTwistNeg 1) := by
    rw [show 2 * 2 - 1 = 2 + (2 * 1 - 1) from rfl,
      moebiusSubst_mul natDegree_symbolZeta_le (natDegree_symbolTwistNeg_le 1 le_rfl),
      moebiusSubst_symbolZeta]
  rw [twistPolyNeg, symbolTwistNeg, moebiusSubst_sub, h1, show symbolTwistNeg 0 = 1 from rfl,
    moebiusSubst_C_mul, moebiusSubst_one]
  simp only [twistPolyNeg, zetaMoebiusM, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    coe_compRingHom_apply, pow_comp, X_comp]
  rw [← pow_mul]

/-- `C_(k+1) = Z_num C_k - x² (L + x)⁴ C_(k-1)` for `k ≥ 2`. -/
theorem twistPolyNeg_add_three (k : ℕ) :
    twistPolyNeg (k + 3) =
      zetaMoebiusM * twistPolyNeg (k + 2) -
        C (X ^ 4) * (C (X ^ 2) + X) ^ 4 * twistPolyNeg (k + 1) := by
  have h1 : moebiusSubst (2 * (k + 3) - 1) (symbolZeta * symbolTwistNeg (k + 2)) =
      symbolZetaMoebius * moebiusSubst (2 * (k + 2) - 1) (symbolTwistNeg (k + 2)) := by
    rw [show 2 * (k + 3) - 1 = 2 + (2 * (k + 2) - 1) by omega,
      moebiusSubst_mul natDegree_symbolZeta_le
        (natDegree_symbolTwistNeg_le (k + 2) (by omega)), moebiusSubst_symbolZeta]
  have h2 : moebiusSubst (2 * (k + 3) - 1) (symbolTwistNeg (k + 1)) =
      moebiusSubst (2 * (k + 1) - 1) (symbolTwistNeg (k + 1)) * (C X + X) ^ 4 := by
    rw [show 2 * (k + 3) - 1 = 2 * (k + 1) - 1 + 4 by omega,
      moebiusSubst_add_degree 4 (natDegree_symbolTwistNeg_le (k + 1) (by omega))]
  rw [twistPolyNeg, symbolTwistNeg, moebiusSubst_sub, moebiusSubst_C_mul, h1, h2]
  simp only [twistPolyNeg, zetaMoebiusM, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    coe_compRingHom_apply, pow_comp, X_comp]
  rw [show ((X : ℤ[X]) ^ 2) ^ 2 = X ^ 4 from (pow_mul X 2 2).symm]
  ring

end AJConjecture
