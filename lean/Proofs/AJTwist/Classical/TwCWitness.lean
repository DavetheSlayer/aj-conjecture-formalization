import Mathlib
import AJConjecture.WitnessPolynomials
import AJTwist.Classical.TwCWitnessPos
import AJTwist.Classical.TwCWitnessNeg

/-!
# A zero of `E` off every bound `(L - 1) 𝒫_(k₁) 𝒫_(k₂)`

At `M = 2` and a root `L` of `L² - L + 16` the extra factor `E` vanishes, and neither `L - 1` nor
any `𝒫_k`, `k ∈ ℤ`, does. Hence every bound `twBound k₁ k₂` is nonzero there, and is a nonzero
polynomial. This is the point of `exists_extraFactor_zero_not_famBound_zero`
(`AJFamily.Classical.FamilyPoint`), now for all signed indices and for products.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `E(2, L) = L² - L + 16`. -/
theorem evalPoint_extraFactor_witness (L : ℂ) (hL : L ^ 2 - L + 16 = 0) :
    evalPoint (mapC extraFactor) (2, L) = 0 := by
  simp only [mapC, evalPoint, extraFactor, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_ofNat, eval₂_add, eval₂_sub,
    eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, Polynomial.coe_evalRingHom, eval_add, eval_mul,
    eval_pow, eval_X, eval_sub, eval_one, eval_ofNat]
  linear_combination hL

/-- No filling polynomial `𝒫_k` vanishes at the witness point. -/
theorem evalPoint_twP_witness_ne_zero (L : ℂ) (hL : L ^ 2 - L + 16 = 0) (k : ℤ) :
    evalPoint (mapC (twP k)) (2, L) ≠ 0 := by
  have h0 : evalPoint (mapC (twP 0)) (2, L) ≠ 0 := by
    rw [twP_zero, mapC, Polynomial.map_one, evalPoint, eval₂_one]
    exact one_ne_zero
  obtain ⟨m, rfl | rfl⟩ := k.eq_nat_or_neg
  · obtain _ | n := m
    · exact h0
    · rw [twP_natCast]
      exact evalPoint_twistPoly_witness_ne_zero L hL n
  · obtain _ | n := m
    · exact h0
    · rw [twP_neg_natCast (n + 1) (by omega)]
      exact evalPoint_twistPolyNeg_witness_ne_zero L hL (n + 1) (by omega)

/-- No bound `(L - 1) 𝒫_(k₁) 𝒫_(k₂)` vanishes at the witness point. -/
theorem evalPoint_twBound_witness_ne_zero (L : ℂ) (hL : L ^ 2 - L + 16 = 0) (k₁ k₂ : ℤ) :
    evalPoint (mapC (twBound k₁ k₂)) (2, L) ≠ 0 := by
  have hmul : evalPoint (mapC (twBound k₁ k₂)) (2, L) =
      (L - 1) * evalPoint (mapC (twP k₁)) (2, L) * evalPoint (mapC (twP k₂)) (2, L) := by
    simp only [mapC, evalPoint, twBound, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one]
  rw [hmul]
  refine mul_ne_zero (mul_ne_zero (fun h1 ↦ ?_) (evalPoint_twP_witness_ne_zero L hL k₁))
    (evalPoint_twP_witness_ne_zero L hL k₂)
  have h16 : (16 : ℂ) = 0 := by linear_combination hL - L * h1
  norm_num at h16

/-- The bounds are nonzero polynomials. -/
theorem twBound_ne_zero (k₁ k₂ : ℤ) : twBound k₁ k₂ ≠ 0 := by
  intro h
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = -63 := IsAlgClosed.exists_pow_nat_eq (-63) (by norm_num)
  have hL : ((1 + s) / 2) ^ 2 - (1 + s) / 2 + 16 = 0 := by linear_combination (1 / 4 : ℂ) * hs
  apply evalPoint_twBound_witness_ne_zero _ hL k₁ k₂
  simp only [h, mapC, Polynomial.map_zero, evalPoint, eval₂_zero]

end AJConjecture
