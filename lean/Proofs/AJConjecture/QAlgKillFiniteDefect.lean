import Mathlib
import AJConjecture.QAlgOpApplyFieldBasic

/-!
# Absorbing finitely many exceptional colours

An operator that annihilates a sequence outside finitely many colours annihilates it at every
colour after left multiplication by a nonzero coefficient vanishing at `M = t^(2n)` for the
exceptional colours `n`.
-/

open Polynomial

namespace AJConjecture

/-- The coefficient `t^(2 n⁻) M - t^(2 n⁺)` of `ℤ[t][M]`, which vanishes at the colour `n`. -/
private noncomputable def colourVanishingCoeff (n : ℤ) : Coeff :=
  C (X ^ (2 * (-n).toNat)) * X - C (X ^ (2 * n.toNat))

/-- The coefficient `colourVanishingCoeff n` is not zero. -/
private theorem colourVanishingCoeff_ne_zero (n : ℤ) : colourVanishingCoeff n ≠ 0 := by
  intro h0
  have h1 := congrArg (fun p : Coeff ↦ p.coeff 1) h0
  simp only [colourVanishingCoeff, coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C_succ,
    sub_zero, coeff_zero] at h1
  exact pow_ne_zero _ X_ne_zero h1

/-- The coefficient `colourVanishingCoeff n` vanishes at the colour `n`. -/
private theorem evalAtField_colourVanishingCoeff (n : ℤ) :
    evalAtField n (colourVanishingCoeff n) = 0 := by
  simp only [colourVanishingCoeff, evalAtField, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X, eval₂_pow]
  rw [sub_eq_zero, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ RatFunc.X_ne_zero]
  congr 1
  push_cast
  omega

/-- An annihilator outside a finite set of colours becomes an annihilator of all colours after
multiplication by a nonzero coefficient. -/
theorem exists_C_mul_annihilator_of_outside_finite {f : ℤ → RatFunc ℚ} {Q : RecOp} {N : ℤ}
    (h : ∀ n : ℤ, N ≤ |n| → opApplyField Q f n = 0) :
    ∃ c : Coeff, c ≠ 0 ∧ ∀ n : ℤ, opApplyField (C c * Q) f n = 0 := by
  refine ⟨∏ m ∈ Finset.Icc (-N) N, colourVanishingCoeff m,
    Finset.prod_ne_zero_iff.mpr fun m _ ↦ colourVanishingCoeff_ne_zero m, fun n ↦ ?_⟩
  rw [opApplyField_C_mul_left]
  by_cases hn : N ≤ |n|
  · rw [h n hn, mul_zero]
  · have hmem : n ∈ Finset.Icc (-N) N := by
      rw [Finset.mem_Icc, ← abs_le]
      omega
    rw [map_prod, Finset.prod_eq_zero hmem (evalAtField_colourVanishingCoeff n), zero_mul]

end AJConjecture
