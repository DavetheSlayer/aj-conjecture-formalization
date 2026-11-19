import Mathlib
import AJHandoff.LocalTheory.LocSymJetEquation

/-!
# The divided first-jet equation

Substituting the contents `S₀ = μ^b S*`, `R₀ = μ^a R*`, `s = μ^b s*`, `r = μ^a r*`,
`β₀ = μ^(a+b) β*` in the first-jet equation (`opJet0_mul_locJetNumer_add`) gives
`S* (μ^(2b) s* 𝒩(R)) + R* U = μ^(2a+2b) N*` with
`N* = β*² 𝒩(P) - c s* (u ∂_u S*)(r* z ∂_z R* - z r*' R*)`;
the bracket is homogeneous of degree `(2, 2)` in the contents (the terms containing `z μ^a'`
cancel). Port of the library's `content_mul_jetBracket` and `exists_nodeSyzygy_of_content`
(Step 2 of Theorem C), with the constant `2` replaced by `-c`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The bracket `c s (u ∂_u S)(r z ∂_z R - z r' R)` scales by `A² B²` under
`(S, R, s, r) ↦ (B S, A R, B s, A r)`. -/
theorem content_mul_locJetBracket (c : ℂ) (A B r s : ℂ[X]) (Ss Rs : ℂ[X][X]) :
    C (C c * (B * s)) * (X * derivative (C B * Ss)) *
        (C (A * r) * (C X * innerDerivative (C A * Rs)) -
          C (X * derivative (A * r)) * (C A * Rs)) =
      C (A ^ 2 * B ^ 2) *
        (C (C c * s) * (X * derivative Ss) *
          (C r * (C X * innerDerivative Rs) - C (X * derivative r) * Rs)) := by
  rw [innerDerivative_mul, innerDerivative_C, derivative_C_mul, derivative_mul]
  simp only [C_mul, C_add, C_pow]
  ring

/-- The divided first-jet equation `S* (μ^(2b) s* 𝒩(R)) + R* U = μ^(2a+2b) N*`. -/
theorem exists_locNodeSyzygy (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (h : C β * P = oreMul δ.shiftHom S R) (hn : P.natDegree = S.natDegree + R.natDegree)
    {z₀ : ℂ} {a b : ℕ} {βs : ℂ[X]} {Ss Rs : ℂ[X][X]}
    (hR : opJet0 R = C ((X - C z₀) ^ a) * Rs) (hS : opJet0 S = C ((X - C z₀) ^ b) * Ss)
    (hβ : locJet0 β = (X - C z₀) ^ (a + b) * βs) :
    ∃ U : ℂ[X][X],
      Ss * (C ((X - C z₀) ^ (2 * b) * Ss.coeff S.natDegree) * locJetNumer R) + Rs * U =
        C ((X - C z₀) ^ (2 * a + 2 * b)) *
          (C (βs ^ 2) * locJetNumer P -
            C (C δ.c * Ss.coeff S.natDegree) * (X * derivative Ss) *
              (C (Rs.coeff R.natDegree) * (C X * innerDerivative Rs) -
                C (X * derivative (Rs.coeff R.natDegree)) * Rs)) := by
  have key := opJet0_mul_locJetNumer_add δ h hn
  have hRc : (opJet0 R).coeff R.natDegree = (X - C z₀) ^ a * Rs.coeff R.natDegree := by
    rw [hR, coeff_C_mul]
  have hSc : (opJet0 S).coeff S.natDegree = (X - C z₀) ^ b * Ss.coeff S.natDegree := by
    rw [hS, coeff_C_mul]
  rw [hSc, hRc, hS, hR, hβ, content_mul_locJetBracket] at key
  refine ⟨C ((X - C z₀) ^ a) *
    (C ((X - C z₀) ^ a * Rs.coeff R.natDegree) * locJetNumer S +
      C (C δ.c * ((X - C z₀) ^ b * Ss.coeff S.natDegree) *
          (X * derivative ((X - C z₀) ^ a * Rs.coeff R.natDegree))) *
        (X * derivative (C ((X - C z₀) ^ b) * Ss) -
          (S.natDegree : ℂ[X][X]) * (C ((X - C z₀) ^ b) * Ss))), ?_⟩
  simp only [C_mul, C_pow] at key ⊢
  linear_combination key

end AJConjecture
