import Mathlib
import AJHandoff.TorusInput.RJMarkovStep
import AJHandoff.TorusInput.RJMarkovEnds

/-!
# The closure of the cyclic braid with its axis is `T(2, 2r)` (node RA5.ii, crux)

`qtr((c f_b^{⊗ r} ⊗ 1_k) J_(br,k) (1 ⊗ f_k)) = θ_b^(r-1) qtr(J_(b,k)^r (f_b ⊗ f_k))`: the
closure of `σ_0 ⋯ σ_(r-2)` cabled by `f_b`, together with its braid axis coloured `f_k`, is the
torus link `T(2, 2r)` coloured `f_b`, `f_k`, the factor `θ_b^(r-1)` being the blackboard framing
`r - 1` of the closed cyclic braid.

Route. `rj_colorTrace_start`, `rj_colorTrace_beta` with `m = r - 1`, `p = 0`, and
`rj_colorTrace_end`. Numerically checked for `r ≤ 4`, `b, k ≤ 2` (design notes). Estimate
20–40 lines.
-/

noncomputable section

namespace AJConjecture

/-- The isotopy `closure(c) ∪ axis ≅ T(2, 2r)` as an identity of quantum traces. -/
theorem rj_axis_isotopy (b r k : ℕ) (hr : 1 ≤ r) :
    qtr (b * r + k) (skPlace (b * r + k) (b * r + k) 0 (rjCycleMat b r * rjColsProj b r) *
        rjFullTwist (b * r) k * jwAt (b * r + k) (b * r) k) =
      kinkScalar b ^ (r - 1) * qtr (b + k) (rjFullTwist b k ^ r * rjBundleProj b k) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [rj_colorTrace_start b k (n + 1) hr, rj_colorTrace_beta b k n 0, Nat.zero_add,
    rj_colorTrace_end b k n, Nat.add_sub_cancel]

end AJConjecture
