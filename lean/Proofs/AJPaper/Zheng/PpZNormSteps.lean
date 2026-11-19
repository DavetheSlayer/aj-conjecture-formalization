import Mathlib
import AJHandoff.Geometry.GeoPhysDefs

/-!
# One-step ratios of Zheng's norm factor `S_{n,i}` (Unit PpZ, node `PpZ_NormSteps`)

Source: H. Zheng, arXiv:math/0508138v4, (3.3). The norm factor
`S_{n,i} = ∏_{j=1}^{n} 4 sin²((i+j)π/N) / (2 sin(jπ/N))` (`geoNormFactor`) has exact one-step
ratios in both indices. They replace the Riemann-sum and Stirling estimates of Zheng's Lemma 3.1:
everything in Lemmas 3.2 and 3.3 is read off from these two identities.

* `ppZ_normFactor_pos`: `S_{n,i} > 0` on the triangle `n + i < N`.
* `ppZ_normFactor_succ_left`: `S_{n+1,i} = S_{n,i} · 4 sin²((i+n+1)π/N) / (2 sin((n+1)π/N))`.
* `ppZ_normFactor_succ_right`: `S_{n,i+1} · sin²((i+1)π/N) = S_{n,i} · sin²((i+n+1)π/N)`
  (the product telescopes; stated without division, so it needs no hypothesis).

Route. `Finset.prod_Icc_succ_top` for the first; for the second, induction on `n` using the first
(or `Finset.prod_div_distrib` and a telescoping product). Positivity: every factor is positive
because `0 < (i+j)π/N < π` and `0 < jπ/N < π` for `1 ≤ j ≤ n`, `n + i < N`.
-/

noncomputable section

namespace AJConjecture

/-- `S_{n,i} > 0` on the triangle `n + i < N`. -/
theorem ppZ_normFactor_pos {N n i : ℕ} (h : n + i < N) : 0 < geoNormFactor N n i := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsin : ∀ m : ℕ, 1 ≤ m → m < N → 0 < Real.sin ((m : ℝ) * Real.pi / N) := by
    intro m hm1 hmN
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    · rw [div_lt_iff₀ hNr]
      have : (m : ℝ) < N := by exact_mod_cast hmN
      nlinarith [Real.pi_pos]
  unfold geoNormFactor
  refine Finset.prod_pos fun j hj ↦ ?_
  rw [Finset.mem_Icc] at hj
  have h1 := hsin (i + j) (by omega) (by omega)
  have h2 := hsin j hj.1 (by omega)
  push_cast at h1
  positivity

/-- One step in `n`: `S_{n+1,i} = S_{n,i} · 4 sin²((i+n+1)π/N) / (2 sin((n+1)π/N))`. -/
theorem ppZ_normFactor_succ_left (N n i : ℕ) :
    geoNormFactor N (n + 1) i = geoNormFactor N n i *
      (4 * Real.sin (((i : ℝ) + n + 1) * Real.pi / N) ^ 2 /
        (2 * Real.sin (((n : ℝ) + 1) * Real.pi / N))) := by
  unfold geoNormFactor
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
  push_cast
  rw [add_assoc (i : ℝ)]

/-- One step in `i`: `S_{n,i+1} · sin²((i+1)π/N) = S_{n,i} · sin²((i+n+1)π/N)`. -/
theorem ppZ_normFactor_succ_right (N n i : ℕ) :
    geoNormFactor N n (i + 1) * Real.sin (((i : ℝ) + 1) * Real.pi / N) ^ 2 =
      geoNormFactor N n i * Real.sin (((i : ℝ) + n + 1) * Real.pi / N) ^ 2 := by
  induction n with
  | zero => simp [geoNormFactor]
  | succ n ih =>
    rw [ppZ_normFactor_succ_left N n (i + 1), ppZ_normFactor_succ_left N n i]
    push_cast
    have e1 : ((i : ℝ) + 1 + n + 1) = (i : ℝ) + (n + 1) + 1 := by ring
    rw [e1]
    linear_combination (4 * Real.sin (((i : ℝ) + (n + 1) + 1) * Real.pi / N) ^ 2 /
      (2 * Real.sin (((n : ℝ) + 1) * Real.pi / N))) * ih

end AJConjecture
