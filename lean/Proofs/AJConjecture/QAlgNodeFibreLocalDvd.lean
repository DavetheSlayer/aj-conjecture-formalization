import Mathlib
import AJConjecture.QAlgNodeContentSplit
import AJConjecture.QAlgNodeFibreClearDenominators

/-!
# Divisibility in the comparison ring gives divisibility near `M = m₀` of the primitive part

Let `toComparison G ∣ toComparison F`, the fibre of `G` at `M = m₀ ∈ ℂ` not zero, and
`F = μ^a F*` over `ℂ[M][L]` (`μ = M - m₀`; any such decomposition). Then `u L^n F* = G Q` over
`ℂ[M][L]` with `u ∈ ℂ[M]`, `u(m₀) ≠ 0`.

Proof. `c L^n F = G Q₀` over `ℤ` (`exists_C_mul_X_pow_mul_eq_of_toComparison_dvd`); base change.
If `Q₀ = 0` then `F* = 0` and `u = 1`, `Q = 0` will do. Otherwise write the base change of `c`
as `μ^f u`, `u(m₀) ≠ 0`, and that of `Q₀` as `μ^e Q*` with nonzero fibre
(`exists_eq_C_pow_mul_fibre_ne_zero`). Then `μ^(f+a) (u L^n F*) = μ^e (G Q*)` and the fibre of
`G Q*` is not zero, so `u L^n F* = G (μ^(e-f-a) Q*)` (`eq_C_pow_mul_of_C_pow_mul_eq`).
-/

open Polynomial

namespace AJConjecture

/-- A nonzero polynomial is a power of `M - m₀` times a polynomial not vanishing at `m₀`. -/
private theorem exists_eq_pow_mul_eval_ne_zero_localDvd {k : Type*} [Field k] (m₀ : k)
    {c : k[X]} (hc : c ≠ 0) :
    ∃ (f : ℕ) (u : k[X]), c = (X - C m₀) ^ f * u ∧ u.eval m₀ ≠ 0 :=
  ⟨rootMultiplicity m₀ c, c /ₘ (X - C m₀) ^ rootMultiplicity m₀ c,
    (pow_mul_divByMonic_rootMultiplicity_eq c m₀).symm,
    eval_divByMonic_pow_rootMultiplicity_ne_zero m₀ hc⟩

/-- If `G` divides `F` in the comparison ring and the fibre of `G` at `m₀` is not zero, then
`G` divides `u L^n F*` over `ℂ[M][L]` for the primitive part `F*` of `F` at `m₀`, with
`u(m₀) ≠ 0`. -/
theorem exists_local_dvd_of_toComparison_dvd {G F : ℤ[X][X]} {m₀ : ℂ}
    (hdvd : toComparison G ∣ toComparison F)
    (hG : (G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) ≠ 0)
    {a : ℕ} {Fs : ℂ[X][X]}
    (hF : F.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = C ((X - C m₀) ^ a) * Fs) :
    ∃ (u : ℂ[X]) (n : ℕ) (Q : ℂ[X][X]), u.eval m₀ ≠ 0 ∧
      C u * X ^ n * Fs = G.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) * Q := by
  obtain ⟨c, n, Q₀, hc, hcQ⟩ := exists_C_mul_X_pow_mul_eq_of_toComparison_dvd hdvd
  have hbc := congrArg (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) hcQ
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, coe_mapRingHom, hF] at hbc
  have hcC : c.map (Int.castRingHom ℂ) ≠ 0 := fun h0 ↦
    hc (Polynomial.map_injective _ Int.cast_injective (h0.trans (Polynomial.map_zero _).symm))
  obtain ⟨f, u, hfu, hu⟩ := exists_eq_pow_mul_eval_ne_zero_localDvd m₀ hcC
  by_cases hQ0 : Q₀.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = 0
  · refine ⟨1, 0, 0, by rw [eval_one]; exact one_ne_zero, ?_⟩
    rw [hQ0, mul_zero] at hbc
    have h1 : C (c.map (Int.castRingHom ℂ)) * (X : ℂ[X][X]) ^ n ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr hcC) (pow_ne_zero n X_ne_zero)
    have h2 := (mul_eq_zero.mp hbc).resolve_left h1
    have hFs : Fs = 0 := (mul_eq_zero.mp h2).resolve_left
      (C_ne_zero.mpr (pow_ne_zero a (X_sub_C_ne_zero m₀)))
    rw [hFs, mul_zero, mul_zero]
  · obtain ⟨e, Qs, hQs, hQs0⟩ := exists_eq_C_pow_mul_fibre_ne_zero m₀ hQ0
    have key : C ((X - C m₀) ^ (f + a)) * (C u * X ^ n * Fs) =
        C ((X - C m₀) ^ e) * (G.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) * Qs) := by
      rw [hfu, hQs, C_mul] at hbc
      rw [pow_add, C_mul]
      linear_combination hbc
    have hfib : (G.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) * Qs).map
        (Polynomial.evalRingHom m₀) ≠ 0 := by
      rw [Polynomial.map_mul]
      exact mul_ne_zero hG hQs0
    obtain ⟨-, hres⟩ := eq_C_pow_mul_of_C_pow_mul_eq key hfib
    exact ⟨u, n, C ((X - C m₀) ^ (e - (f + a))) * Qs, hu, by rw [hres]; ring⟩

end AJConjecture
