import Mathlib
import AJHandoff.TorusInput.RJCycleRelation
import AJHandoff.TorusInput.RJCandidateIdentity
import AJHandoff.TorusInput.RJHopfUnique

/-!
# The trace of the cyclic braid on an isotypic part (node RA5, crux)

For even `b = 2n` and `r ≥ 2`: `qtr(c P_N) = rjCycleValue b r N`, i.e.
`t^(4ri²+4i)[2ri+1]/θ_b` if `N + 1 = |2ri+1|`, `|i| ≤ n`, and `0` otherwise. (This is
`ν_N a_N Δ_N` with `a_N ∈ {0, ±1}` the coefficients of `S_N` in `S_b(T_r)`: Rosso–Jones, Morton.)

Route. For `k ≥ b`, subtract `rj_candidate_relation` from `rj_cycle_relation`
(`min b k = b`) and apply `rj_hopf_unique` to `z_N = qtr(c P_N) - rjCycleValue b r N`. Estimate
30–50 lines.
-/

noncomputable section

namespace AJConjecture

/-- The trace of the cabled cyclic braid on the isotypic part of colour `N`. -/
theorem rj_qtr_cycleMat_mul_isoProj (b r N : ℕ) (hb : Even b) (hr : 2 ≤ r) (hN : N ∈ rjSpec b r) :
    qtr (b * r) (rjCycleMat b r * rjIsoProj b r N) = rjCycleValue b r N := by
  have h := rj_hopf_unique (rjSpec b r)
    (fun M ↦ qtr (b * r) (rjCycleMat b r * rjIsoProj b r M) - rjCycleValue b r M) b
    (fun k hk ↦ by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [rj_cycle_relation b r k (by omega), rj_candidate_relation b r k hb hr hk,
        min_eq_left hk, sub_self]) N hN
  exact sub_eq_zero.mp h

end AJConjecture
