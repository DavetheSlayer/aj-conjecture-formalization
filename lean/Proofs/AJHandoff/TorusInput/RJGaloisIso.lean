import Mathlib
import AJHandoff.TorusInput.RJGaloisTrace
import AJHandoff.TorusInput.RJIsoProjProps

/-!
# The Galois step on the isotypic parts (node RA4.2)

For even `b`, `r ≥ 1`, `s ≥ 1` prime to `r` and `N` in the spectrum:
`qtr(c^s P_N) = ν_N^(s-1) qtr(c P_N)` after the embedding `t ↦ t^r`.

Route. `rj_galois_trace` with `C = c`, `P = P_N`, `w` the weight of `skWeight` (a diagonal
matrix, `qtr m A = trace (skWeight m * A)`), `μ = μ_N`, `ν = ν_N`: the hypotheses are
`rj_isoProj_mul_self`, `rj_cycleMat_mul_isoProj`, `rj_cycleMat_pow_mul_isoProj`,
`skWeight_mul_braidMatrix`, `rj_skWeight_mul_isoProj`, `rjNu_pow` (every `N` in the spectrum is
even when `b` is even), `rjNu_ne_zero`. Estimate 40–70 lines.
-/

noncomputable section

namespace AJConjecture

/-- The Galois step for the cabled cyclic braid on an isotypic part. -/
theorem rj_galois_isoProj (b r s N : ℕ) (hb : Even b) (hr : 1 ≤ r) (hs1 : 1 ≤ s)
    (hs : Nat.Coprime s r) (hN : N ∈ rjSpec b r) :
    rjEmbed r (qtr (b * r) (rjCycleMat b r ^ s * rjIsoProj b r N)) =
      rjNu b r N ^ (s - 1) * rjEmbed r (qtr (b * r) (rjCycleMat b r * rjIsoProj b r N)) := by
  have hNe : Even N := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨n, rfl⟩ := hb
    refine ⟨n * r - j, ?_⟩
    have : 2 * j ≤ (n + n) * r := by
      rw [Finset.mem_range] at *
      omega
    rw [add_mul] at this ⊢
    omega
  simp only [qtr, ← mul_assoc]
  exact rj_galois_trace _ (rjCycleMat b r) (rjIsoProj b r N) hr hs1 hs (rjTwistEigen b r N)
    (rjNu b r N) (rjNu_pow b r N hr hb hNe) (rjNu_ne_zero b r N) (rj_isoProj_mul_self b r N hr hN)
    (rj_cycleMat_mul_isoProj b r N) (rj_cycleMat_pow_mul_isoProj b r N hr hN)
    (skWeight_mul_braidMatrix _ _) (rj_skWeight_mul_isoProj b r N)

end AJConjecture
