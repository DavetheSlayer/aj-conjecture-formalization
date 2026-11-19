import Mathlib
import AJTwist.Quantum.TwQCramerOp
import AJTwist.Quantum.TwQWindowDet

/-!
# The operator of a nonzero target is not zero

`twCramerOp d T = ∑_k c_(d-k)(t⁴, t^(4d) M²) L^k`, where the `c_i = twCoeff d (t⁴) T i` are
the Cramer numerators of the target `T` in the pole basis of the window `d`.

* `twH_twDet_ne_zero`: the determinant of the pole basis over `ℤ[t]` at `q = t⁴` is not zero
  (its image in `ℚ(t)[x]` is `twDet d qParam` by `map_twDet` and `twTHom_X_pow_four`, which does
  not vanish at `x = q^(d+1)` by `twDet_eval_ne_zero`).
* `twH_twCramerOp_ne_zero`: if `T ≠ 0` has degree at most `d` in `J`, then `twCramerOp d T ≠ 0`.
  If the operator were zero, every coefficient `c_i(t⁴, t^(4d) M²)` would vanish, hence every
  `c_i` (the substitution `x ↦ t^(4d) M²` is injective on `ℤ[t][x]`:
  `Polynomial.comp_eq_zero_iff`, the inner polynomial is not constant), and the Cramer identity
  `∑_i c_i P_i = det · T` (`sum_twCoeff_mul_twBasisPoly`) would give `det · T = 0`.

The manuscript's operators `P_a` are shown nonzero through their symbols; for the operator of
an arbitrary target this elementary argument is used instead.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The determinant of the pole basis of the window `d` over `ℤ[t]`, at `q = t⁴`, is not
zero. -/
theorem twH_twDet_ne_zero (d : ℕ) : twDet d (X ^ 4 : ℤ[X]) ≠ 0 := by
  intro h
  have h1 := map_twDet twTHom d (X ^ 4 : ℤ[X])
  rw [h, Polynomial.map_zero, twTHom_X_pow_four] at h1
  have h2 := twDet_eval_ne_zero d (N := (d : ℤ) + 1) le_rfl
  rw [← h1, eval_zero] at h2
  exact h2 rfl

/-- The coefficients of the operator of a target are the substituted Cramer numerators. -/
private theorem coeff_twCramerOp_cramerNeZero (d : ℕ) (T : ℤ[X][X][X]) (i : Fin (d + 1)) :
    (twCramerOp d T).coeff (i : ℕ) =
      (twCoeff d (X ^ 4 : ℤ[X]) T (Fin.rev i)).comp (C (X ^ (4 * d)) * X ^ 2) := by
  rw [twCramerOp, finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow_self, mul_one]
  · intro k _ hk
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h ↦ hk (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The operator of a nonzero target of degree at most `d` in `J` is not zero. -/
theorem twH_twCramerOp_ne_zero (d : ℕ) {T : ℤ[X][X][X]} (hT : T.natDegree ≤ d) (h0 : T ≠ 0) :
    twCramerOp d T ≠ 0 := by
  intro h
  have hc : ∀ i : Fin (d + 1), twCoeff d (X ^ 4 : ℤ[X]) T i = 0 := by
    intro i
    have h1 := coeff_twCramerOp_cramerNeZero d T (Fin.rev i)
    rw [h, coeff_zero, Fin.rev_rev] at h1
    rcases comp_eq_zero_iff.mp h1.symm with h2 | ⟨_, h2⟩
    · exact h2
    · exfalso
      have h3 := congrArg natDegree h2
      rw [natDegree_C, natDegree_C_mul_X_pow 2 _ (pow_ne_zero _ X_ne_zero)] at h3
      exact two_ne_zero h3
  have hsum := sum_twCoeff_mul_twBasisPoly d (X ^ 4 : ℤ[X]) T hT
  simp only [hc, C_0, zero_mul, Finset.sum_const_zero] at hsum
  rcases mul_eq_zero.mp hsum.symm with h4 | h4
  · exact twH_twDet_ne_zero d (C_eq_zero.mp h4)
  · exact h0 h4

end AJConjecture
