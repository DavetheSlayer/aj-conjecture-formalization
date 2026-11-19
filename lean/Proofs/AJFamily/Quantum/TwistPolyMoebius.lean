import Mathlib
import AJConjecture.QAlgMoebiusSubstBasic
import AJConjecture.QAlgSymbolZetaMoebius
import AJFamily.Quantum.TwistPoly

/-!
# The twist polynomial as a Möbius substitution

The Möbius substitution of `symbolTwist k` in degree `2k`, after `x = M²`, is `twistPoly k`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `T̂_k` has degree at most `2k` in `J`. -/
theorem natDegree_symbolTwist_le (k : ℕ) : (symbolTwist k).natDegree ≤ 2 * k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [symbolTwist]
    | 1, _ =>
      rw [symbolTwist]
      refine natDegree_sub_le_of_le (natDegree_add_le_of_degree_le natDegree_symbolZeta_le ?_)
        (natDegree_C _).le |>.trans (by norm_num)
      compute_degree
      norm_num
    | k + 2, ih =>
      rw [symbolTwist]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le_of_le natDegree_symbolZeta_le (ih (k + 1) (by omega)) |>.trans
          (by omega)
      · exact natDegree_C_mul_le _ _ |>.trans ((ih k (by omega)).trans (by omega))

/-- The Möbius substitution of `T̂_k` in degree `2k`, after `x = M²`, is `B_k`. -/
theorem map_moebiusSubst_symbolTwist (k : ℕ) :
    (moebiusSubst (2 * k) (symbolTwist k)).map (Polynomial.compRingHom (X ^ 2)) = twistPoly k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [symbolTwist, twistPoly, moebiusSubst_one]
    | 1, _ =>
      rw [symbolTwist, twistPoly, moebiusSubst_sub, moebiusSubst_add, moebiusSubst_symbolZeta,
        moebiusSubst_C_mul, show 2 * 1 = 1 + 1 from rfl, moebiusSubst_X,
        ← mul_one (C (X ^ 2 + 1)), moebiusSubst_C_mul, moebiusSubst_one]
      simp [zetaMoebiusM]
      ring
    | k + 2, ih =>
      rw [symbolTwist, twistPoly, moebiusSubst_sub, moebiusSubst_C_mul,
        show 2 * (k + 2) = 2 + 2 * (k + 1) by ring,
        moebiusSubst_mul natDegree_symbolZeta_le (natDegree_symbolTwist_le (k + 1)),
        moebiusSubst_symbolZeta, show 2 + 2 * (k + 1) = 2 * k + 4 by ring,
        moebiusSubst_add_degree 4 (natDegree_symbolTwist_le k)]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_X, ih (k + 1) (by omega), ih k (by omega)]
      simp [zetaMoebiusM]
      ring

end AJConjecture
