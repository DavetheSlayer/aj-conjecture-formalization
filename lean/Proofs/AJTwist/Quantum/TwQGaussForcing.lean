import Mathlib
import AJTwist.Quantum.TwQOuter
import AJTwist.Quantum.TwQInnerForcing
import AJTwist.Quantum.TwQPeriod
import AJHandoff.PairDefs

/-!
# The transfer in the Gaussian-period form (Unit Q4)

Source: revision 5, Section 6.3, eq. (finite-module-force):
`P_a F = -q^(ηm+ℓ) ∑_{i=1}^{4} c_i(q^η) (D^{[0]} G_{p_i}^{(ℓ)} - D^{[1]} G_{p_i - 1}^{(ℓ)})`,
`p_i = ℓ + η λ_i`, with the weight operators `D^{[z]}` (`J^z = ∑_i d_i^{[z]} Δ R_i`). "The
identity uses only the displayed periods and the two pole-basis weight operators." It holds for
every `(η, ℓ)`.

In the Cramer normalization (`twTransferOp a`, `twWeightOp d z` share the determinant of the
pole basis, and `twTransferOp` carries the clearing power `(q^d q^N)^(|a|+1)`), at the colours
`n ≥ 1`: `twQ_gaussForcing`. Route: `twQ_opApplyField_transferOp`, `twQ_defect_eq_periods`,
`twQ_opApplyField_weightOp` (`z = 0, 1`).

`twExp_mem_Icc_true`, `twExp_mem_Icc_false` are the index ranges of Section 6.3: for the
right-handed companion with `ℓ = γ ≥ m` (`a ≤ 0`), `1 ≤ p_i ≤ 2γ - 1`; for the mirror companion
with `ℓ = -γ ≤ -m` (`a ≥ 0`), `1 ≤ -p_i ≤ 2γ - 1`. With `G_0 = 0` and `G_(-c) = -q^c G_c`
(`twPeriod_zero`, `twPeriod_neg`) the periods `G_c`, `1 ≤ c ≤ 2γ`, suffice (eq. (finite-U)).

Checked at random points in the same cases as `twQ_physicalForcing` (scratch
`check_transfer.py`, column `gaussian`).
-/

noncomputable section

namespace AJConjecture

/-- Eq. (finite-module-force): the transfer in terms of the Gaussian periods and the two weight
operators, for every companion sign and every twist. -/
theorem twQ_gaussForcing (η : Bool) (r s : ℕ) (ℓ : ℤ) {n : ℤ} (hn : 1 ≤ n) :
    opApplyField (twTransferOp (twIndex η r s ℓ)) (twReducedEven η r s ℓ) n =
      -(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
        (qParam ^ twWindow (twIndex η r s ℓ) *
          qParam ^ (n + (twWindow (twIndex η r s ℓ) : ℤ))) ^ ((twIndex η r s ℓ).natAbs + 1) *
          ∑ i : Fin 4, twCoef η r s i *
            (opApplyField (twWeightOp (twWindow (twIndex η r s ℓ)) 0)
                (twPeriod ℓ (twExp η r s ℓ i)) n -
              opApplyField (twWeightOp (twWindow (twIndex η r s ℓ)) 1)
                (twPeriod ℓ (twExp η r s ℓ i - 1)) n) := by
  have hF : twReducedEven η r s ℓ = pairQReducedFormulaEven (twInput η r s ℓ) := rfl
  have hP : ∀ c : ℤ, twPeriod ℓ c = pairQReducedFormulaEven (twPeriodInput ℓ c) := fun _ ↦ rfl
  have hd : 1 ≤ twWindow (twIndex η r s ℓ) := by
    rw [twWindow]
    split_ifs <;> omega
  rw [hF, twQ_opApplyField_transferOp _ _ hn, twTransferScalar]
  simp only [hP, twQ_opApplyField_weightOp _ 0 (Nat.zero_le _) _ hn,
    twQ_opApplyField_weightOp _ 1 hd _ hn, twQ_defect_eq_periods, pow_zero, pow_one, mul_one]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- `r + s + 1 ≤ r s` for a torus pair. -/
private theorem add_add_one_le_mul_twQGaussForcing {r s : ℕ} (h : IsTorusPair r s) :
    (r : ℤ) + s + 1 ≤ ((r * s : ℕ) : ℤ) := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 3 := ⟨s - 3, by omega⟩
  have h1 : r' + 2 + (s' + 3) + 1 ≤ (r' + 2) * (s' + 3) := by
    nlinarith [Nat.zero_le (r' * s')]
  exact_mod_cast h1

/-- The exponents `λ_i` are bounded by `r + s` in absolute value. -/
private theorem twLambda_abs_le_twQGaussForcing (r s : ℕ) (i : Fin 4) :
    -((r : ℤ) + s) ≤ twLambda r s i ∧ twLambda r s i ≤ (r : ℤ) + s := by
  fin_cases i <;> simp [twLambda] <;> omega

/-- The index range of Section 6.3 for the right-handed companion with `ℓ ≥ r s` (`a ≤ 0`). -/
theorem twExp_mem_Icc_true {r s : ℕ} (h : IsTorusPair r s) {ℓ : ℤ}
    (hℓ : ((r * s : ℕ) : ℤ) ≤ ℓ) (i : Fin 4) :
    1 ≤ twExp true r s ℓ i ∧ twExp true r s ℓ i ≤ 2 * ℓ - 1 := by
  have h1 := add_add_one_le_mul_twQGaussForcing h
  obtain ⟨h2, h3⟩ := twLambda_abs_le_twQGaussForcing r s i
  rw [twExp, ite_eq_left rfl, one_mul]
  constructor <;> linarith

/-- The index range of Section 6.3 for the mirror companion with `ℓ ≤ -r s` (`a ≥ 0`). -/
theorem twExp_mem_Icc_false {r s : ℕ} (h : IsTorusPair r s) {ℓ : ℤ}
    (hℓ : ℓ ≤ -((r * s : ℕ) : ℤ)) (i : Fin 4) :
    1 ≤ -twExp false r s ℓ i ∧ -twExp false r s ℓ i ≤ -(2 * ℓ) - 1 := by
  have h1 := add_add_one_le_mul_twQGaussForcing h
  obtain ⟨h2, h3⟩ := twLambda_abs_le_twQGaussForcing r s i
  rw [twExp, ite_eq_right Bool.false_ne_true]
  constructor <;> linarith

end AJConjecture
