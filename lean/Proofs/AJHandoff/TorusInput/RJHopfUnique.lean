import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinTurnbackEigenBasic

/-!
# The Hopf functionals separate the colours (node RA5.iv.4)

If `∑_(N ∈ S) z_N h_k(N) = 0` for all `k ≥ k₀`, then `z_N = 0` for every `N ∈ S`.

Route. `h_k(N) = (-1)^k [(N+1)(k+1)]/[N+1]`, and
`(t² - t⁻²) [(N+1)(k+1)] = y_k^(N+1) - y_k^(-(N+1))` with `y_k = t^(2(k+1))`. So the Laurent
polynomial `L(y) = ∑_N (z_N/[N+1]) (y^(N+1) - y^(-(N+1)))` vanishes at the infinitely many
distinct points `y_k`, `k ≥ k₀`; multiplied by a power of `y` it is a polynomial over `ℚ(t)` with
infinitely many roots, hence zero (`Polynomial.eq_zero_of_infinite_isRoot`), and its coefficient
at `y^(M+N+1)` is `z_N/[N+1]` (the exponents `N + 1 > 0` are distinct). Alternatively use the
dilated Chebyshev polynomials `Polynomial.Chebyshev.S` evaluated at `y_k + y_k⁻¹`. Estimate
100–160 lines.
-/

noncomputable section

namespace AJConjecture

/-- `k ↦ t^(2(k + k₀ + 1))` is injective. -/
private theorem rj_hopf_point_injective (k₀ : ℕ) :
    Function.Injective fun k : ℕ ↦ (RatFunc.X : RatFunc ℚ) ^ (2 * (k + k₀ + 1)) := by
  intro a b hab
  simp only at hab
  rw [← RatFunc.algebraMap_X, ← map_pow, ← map_pow] at hab
  have h := congrArg Polynomial.natDegree (RatFunc.algebraMap_injective ℚ hab)
  simp only [Polynomial.natDegree_X_pow] at h
  omega

/-- The Hopf term, times `(-1)^k (t² - t⁻²) y^M`, is a difference of two powers of
`y = t^(2(k+1))`. -/
private theorem rj_hopf_term_eq (N k M : ℕ) (hNM : N + 1 ≤ M) (zN : RatFunc ℚ) :
    zN / quantumInt ((N : ℤ) + 1) *
        (((RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1))) ^ (M + N + 1) -
          ((RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1))) ^ (M - N - 1)) =
      (-1) ^ k * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
        (RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1) * M) * (zN * rjHopf N k) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD := claspAlg_ratFuncX_sq_sub_ne_zero
  have hpow : (RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1) * M) *
      (RatFunc.X ^ (2 * (((N : ℤ) + 1) * ((k : ℤ) + 1))) -
        RatFunc.X ^ (-(2 * (((N : ℤ) + 1) * ((k : ℤ) + 1))))) =
      ((RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1))) ^ (M + N + 1) -
        ((RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1))) ^ (M - N - 1) := by
    rw [← pow_mul, ← pow_mul]
    simp only [← zpow_natCast, mul_sub, ← zpow_add₀ hX]
    have hc : ((M - N - 1 : ℕ) : ℤ) = (M : ℤ) - N - 1 := by omega
    push_cast
    rw [hc]
    congr 2 <;> ring
  have hq : quantumInt (((N : ℤ) + 1) * ((k : ℤ) + 1)) =
      (RatFunc.X ^ (2 * (((N : ℤ) + 1) * ((k : ℤ) + 1))) -
        RatFunc.X ^ (-(2 * (((N : ℤ) + 1) * ((k : ℤ) + 1))))) /
        (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) := rfl
  have hN : quantumInt ((N : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h1 : ((-1 : RatFunc ℚ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  rw [← hpow, rjHopf, hq]
  calc _ = ((-1 : RatFunc ℚ) ^ k * (-1) ^ k) * ((RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
        (RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1) * M) * (zN *
          ((RatFunc.X ^ (2 * (((N : ℤ) + 1) * ((k : ℤ) + 1))) -
            RatFunc.X ^ (-(2 * (((N : ℤ) + 1) * ((k : ℤ) + 1))))) /
            (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) / quantumInt ((N : ℤ) + 1)))) := by
        rw [h1, one_mul]
        generalize (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) : RatFunc ℚ) = D at hD ⊢
        field_simp
    _ = _ := by ring

open Polynomial in
/-- The Hopf functionals `k ↦ h_k(N)`, `k ≥ k₀`, are linearly independent. -/
theorem rj_hopf_unique (S : Finset ℕ) (z : ℕ → RatFunc ℚ) (k₀ : ℕ)
    (h : ∀ k, k₀ ≤ k → ∑ N ∈ S, z N * rjHopf N k = 0) : ∀ N ∈ S, z N = 0 := by
  classical
  set M := S.sup id + 1 with hM
  have hlt : ∀ N ∈ S, N + 1 ≤ M := fun N hN ↦ by
    have := Finset.le_sup (f := id) hN
    simp only [id] at this
    omega
  set P : (RatFunc ℚ)[X] := ∑ N ∈ S, C (z N / quantumInt ((N : ℤ) + 1)) *
    (X ^ (M + N + 1) - X ^ (M - N - 1)) with hP
  have hroot : ∀ k, k₀ ≤ k → P.IsRoot ((RatFunc.X : RatFunc ℚ) ^ (2 * (k + 1))) := by
    intro k hk
    rw [IsRoot, hP, eval_finsetSum]
    simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X]
    rw [Finset.sum_congr rfl fun N hN ↦ rj_hopf_term_eq N k M (hlt N hN) (z N), ← Finset.mul_sum,
      h k hk, mul_zero]
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.infinite_of_injective_forall_mem (rj_hopf_point_injective k₀) fun k ↦ ?_
    have := hroot (k + k₀) (by omega)
    simpa [add_assoc] using this
  intro N hN
  have hcoeff : P.coeff (M + N + 1) = z N / quantumInt ((N : ℤ) + 1) := by
    rw [hP, finsetSum_coeff, Finset.sum_eq_single N]
    · simp only [coeff_C_mul, coeff_sub, coeff_X_pow]
      rw [ite_eq_left trivial, ite_eq_right (by omega), sub_zero, mul_one]
    · intro N' hN' hne
      simp only [coeff_C_mul, coeff_sub, coeff_X_pow]
      rw [ite_eq_right (by omega), ite_eq_right (by have := hlt N' hN'; omega), sub_zero, mul_zero]
    · intro h'; exact absurd hN h'
  rw [hP0, coeff_zero, eq_comm, div_eq_zero_iff] at hcoeff
  rcases hcoeff with h' | h'
  · exact h'
  · exact absurd h' (claspAlg_quantumInt_ne_zero (by omega))

end AJConjecture
