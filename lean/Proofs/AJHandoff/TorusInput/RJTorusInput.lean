import Mathlib
import AJHandoff.TorusInput.RJKnotTraceCycle
import AJHandoff.TorusInput.RJGaloisIso
import AJHandoff.TorusInput.RJCycleTrace
import AJHandoff.TorusInput.RJSupportSum
import AJHandoff.TorusInput.RJAssemblyIdentity

/-!
# The torus input in channel form (node RA6.3, top node)

For every admissible pair `(r, s)` and every `n`:
`knotTrace (T(r,s)) (2n) f_(2n) = t^(4(r-1)s n(n+1)) pairQOddColor r s n`.

Route. Put `b = 2n`. `rj_knotTrace_torusPairKnot`; `f_b^{⊗ r} = ∑_N P_N` (`rj_sum_isoProj`),
linearity of `qtr`. Apply the injective `rjEmbed r` (`rjEmbed_injective`); for each `N`,
`rj_galois_isoProj` and `rj_qtr_cycleMat_mul_isoProj` give
`rjEmbed(qtr(c^s P_N)) = ν_N^(s-1) rjEmbed(rjCycleValue b r N)`. Sum with
`rj_sum_cycleValue_mul` (`φ = rjEmbed r`, `g N = ν_N^(s-1)`), `rj_nu_support`, and pull
`rjEmbed` out (`map_sum`, `map_mul`, `map_pow`); the result is `rjEmbed` of the left side of
`rj_assembly_identity` (`b / 2 = n`). `IsTorusPair r s` gives `2 ≤ r` and `s` prime to `r`
(`s ≥ 1`). Estimate 60–100 lines.
-/

noncomputable section

namespace AJConjecture

/-- The quantum trace is additive over finite sums. -/
private theorem rj_qtr_sum_torusInput (m : ℕ) (S : Finset ℕ) (f : ℕ → SkMat m m) :
    qtr m (∑ N ∈ S, f N) = ∑ N ∈ S, qtr m (f N) := by
  simp only [qtr, Matrix.mul_sum, Matrix.trace_sum]

/-- The torus input in channel form, for every admissible pair. -/
theorem rj_knotTrace_torusPair_jw (r s : ℕ) (h : IsTorusPair r s) (n : ℕ) :
    knotTrace (torusPairKnot r s h) (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (((r - 1) * s : ℕ) : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) *
        pairQOddColor r s n := by
  have hr2 : 2 ≤ r := h.1
  have hs1 : 1 ≤ s := by have := h.2.1; omega
  have hcop : Nat.Coprime s r := h.2.2.symm
  have hb : Even (2 * n) := even_two_mul n
  have hn : 2 * n / 2 = n := by omega
  rw [rj_knotTrace_torusPairKnot, ← rj_sum_isoProj, Matrix.mul_sum, rj_qtr_sum_torusInput]
  apply rjEmbed_injective r
  rw [map_sum, Finset.sum_congr rfl fun N hN ↦ by
    rw [rj_galois_isoProj (2 * n) r s N hb (by omega) hs1 hcop hN,
      rj_qtr_cycleMat_mul_isoProj (2 * n) r N hb hr2 hN, mul_comm],
    rj_sum_cycleValue_mul (2 * n) r hb hr2 (rjEmbed r) fun N ↦ rjNu (2 * n) r N ^ (s - 1),
    ← rj_assembly_identity r s n (by omega), map_sum, hn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [rj_nu_support (2 * n) r (by omega), ← map_pow, ← map_mul]
  congr 1
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

end AJConjecture
