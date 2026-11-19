import Mathlib
import AJTwist.Exist.TwHAdjunction
import AJTwist.Exist.TwHTargetNeZero
import AJTwist.Exist.TwHCramerNeZero

/-!
# From an inner relation to a recurrence of the reduced sequence on the positive tail

Source: revision 5, Section 3.3 (`transfer.tex`, "The row in physical color"), applied to an
arbitrary inner operator instead of `p_a`. Let `u` be any input, `D = pairQCycloCoeff u`,
`F = pairQReducedFormulaEven u`, and suppose `∑_{s ≤ r} ρ_s(q^j) (V^s D)_j = 0` for all `j`,
with `ρ_s ∈ ℤ[t][J]` not all zero. Choose a window `d ≥ 1` with `deg ρ_s + 2s ≤ d` for all
`s ≤ r`, and let `𝒯 = twHTarget d t⁴ r ρ`, `P = twCramerOp d 𝒯`.

* `twH_opApplyField_cramerOp_target`: for every input and every colour `n ≥ 1`, `N = n + d`,
  `(P F)(n) = det(q^N) (q^d q^N)^r ∑_{j<N} G_j(N) ∑_{s ≤ r} ρ_s(q^j) (V^s D)_j`
  (`twQ_opApplyField_cramerOp`, `map_twHTarget` with `twTHom_X_pow_four`,
  `natDegree_twHTarget_le`, `twH_sum_twKernel_mul_target`). There are no boundary terms and no
  condition on the input.
* `twH_exists_tail_annihilator_of_relation`: under the relation the right side vanishes, so
  `P` annihilates `F` at all colours `n ≥ 1`; and `P ≠ 0` (`twHTarget_ne_zero` over the domain
  `ℤ[t]` with `q = t⁴ ≠ 0`, `twH_twCramerOp_ne_zero`). A window: `d = 1 + ∑_{s ≤ r} (deg ρ_s +
  2s)`, or the supremum.

Checked for 22 choices of `(η, r, s, ℓ)` in a prime field and for 5 in exact rationals, with the
Cramer numerators as defined here, at `n = 1, 2, 3` (scratch `H/h03_pipeline.py`):
`(P F)(n) = 0`, the displayed formula, and `P ≠ 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The operator of the cleared target of an inner operator `∑_s ρ_s(J) V^s`, applied to the
reduced sequence of an arbitrary input, at the colours `n ≥ 1`. -/
theorem twH_opApplyField_cramerOp_target (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (ρ : ℕ → ℤ[X][X])
    (hdeg : ∀ s, s ≤ r → (ρ s).natDegree + 2 * s ≤ d) (u : ℕ → RatFunc ℚ) {n : ℤ}
    (hn : 1 ≤ n) :
    opApplyField (twCramerOp d (twHTarget d (X ^ 4 : ℤ[X]) r ρ)) (pairQReducedFormulaEven u) n =
      (twDet d qParam).eval (qParam ^ (n + (d : ℤ))) *
        (qParam ^ d * qParam ^ (n + (d : ℤ))) ^ r *
          ∑ j ∈ Finset.range (n + (d : ℤ)).toNat, twKernel d j (n + d) *
            ∑ s ∈ Finset.range (r + 1), ((ρ s).map twTHom).eval (qParam ^ j) *
              cycloStep^[s] (pairQCycloCoeff u) j := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  have hT : (twHTarget d (X ^ 4 : ℤ[X]) r ρ).natDegree ≤ d := natDegree_twHTarget_le d _ r ρ hdeg
  have h := twH_sum_twKernel_mul_target d hd (N := k + d) (by omega) r
    (fun s ↦ (ρ s).map twTHom) (pairQCycloCoeff u)
  have hcast : ((k + d : ℕ) : ℤ) = (k : ℤ) + d := by push_cast; ring
  have htoNat : ((k : ℤ) + (d : ℤ)).toNat = k + d := by omega
  rw [hcast] at h
  rw [twQ_opApplyField_cramerOp d _ hT u hn, map_twHTarget, twTHom_X_pow_four, htoNat, h,
    mul_assoc]

/-- A nontrivial polynomial relation in `V` for the cyclotomic coefficients of an input gives a
nonzero recurrence operator annihilating its reduced sequence at all colours `n ≥ 1`. -/
theorem twH_exists_tail_annihilator_of_relation (u : ℕ → RatFunc ℚ) (r : ℕ)
    (ρ : ℕ → ℤ[X][X]) (hρ : ∃ s, s ≤ r ∧ ρ s ≠ 0)
    (hrel : ∀ j : ℕ, ∑ s ∈ Finset.range (r + 1), ((ρ s).map twTHom).eval (qParam ^ j) *
      cycloStep^[s] (pairQCycloCoeff u) j = 0) :
    ∃ G : RecOp, G ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n → opApplyField G (pairQReducedFormulaEven u) n = 0 := by
  have hdeg : ∀ s, s ≤ r → (ρ s).natDegree + 2 * s ≤
      1 + ∑ i ∈ Finset.range (r + 1), ((ρ i).natDegree + 2 * i) := by
    intro s hs
    have h := Finset.single_le_sum (f := fun i ↦ (ρ i).natDegree + 2 * i)
      (fun i _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))
    exact h.trans (Nat.le_add_left _ _)
  have hq : (X ^ 4 : ℤ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  refine ⟨twCramerOp _ (twHTarget _ (X ^ 4 : ℤ[X]) r ρ),
    twH_twCramerOp_ne_zero _ (natDegree_twHTarget_le _ _ r ρ hdeg)
      (twHTarget_ne_zero _ hq r ρ hρ), fun n hn ↦ ?_⟩
  rw [twH_opApplyField_cramerOp_target _ (Nat.le_add_right 1 _) r ρ hdeg u hn]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ ↦ ?_)
  rw [hrel j, mul_zero]

end AJConjecture
