import Mathlib
import AJConjecture.QAlgCycloBilateralSumCheb
import AJConjecture.QAlgCycloChebLinear
import AJHandoff.TorusQuantum.PairQCycloBilateral
import AJHandoff.TorusQuantum.PairQCycloReindex

/-!
# The defect as a bilateral transform of the forcing

If the odd extension of `u` satisfies `ũ(n+1) = q^(-2m(n+1)) ũ(n) + h(n)` (with `m ≥ 1`), then
`2 e_j = -q 𝔅_j((Q - J)(q^((n+1)(m-1)) + q^((n+1)m)) h)` for every `j` (source Q7/Q8).

Route (the private lemmas `torusCycloDefect_symbol_eq_reindex_symbol` and
`cycloBilateralSum_torusReindex_symbol_eq` of `TorusCycloDefectVanishes`, with `4a = 2m`): apply
`pairQ_cycloBilateralSum_reindex` to `φ(n) = Q^(m-1) + Q^m`. The operator on the left becomes
`s_(m-1) + (1 - qJ) s_m - qJ s_(m+1)` with `s_l = Q^l + q^(-l) Q^(-l)` (field identity); by
`cycloBilateralSum_cheb`, `pairQ_two_mul_cycloCoeff` and `cycloCheb_const_mul` its bilateral
transform against `ũ` is `2 e_j`.
-/

noncomputable section

namespace AJConjecture

/-- The bilateral transform is additive. -/
private theorem cycloBilateralSum_add_pairQDefect (f g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ f n + g n) j = cycloBilateralSum f j + cycloBilateralSum g j := by
  simp only [cycloBilateralSum, mul_add, Finset.sum_add_distrib]

/-- The bilateral transform commutes with multiplication by a constant. -/
private theorem cycloBilateralSum_const_mul_pairQDefect (c : RatFunc ℚ) (f : ℤ → RatFunc ℚ)
    (j : ℕ) :
    cycloBilateralSum (fun n ↦ c * f n) j = c * cycloBilateralSum f j := by
  simp only [cycloBilateralSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  ring

/-- The operator of the re-indexing identity applied to `φ = Q^d + Q^(d+1)`, `m = d + 1`, is
`s_d + (1 - qJ) s_(d+1) - qJ s_(d+2)` with `s_e = Q^e + q^(-e) Q^(-e)`. -/
private theorem pairQCycloDefect_symbol_eq_reindex_symbol (m d : ℕ) (hd : m = d + 1)
    (j : ℕ) (n : ℤ) :
    (1 - qParam * qParam ^ j * qParam ^ n) *
          (qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) +
        qParam ^ (1 - 2 * (m : ℤ)) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(2 * (m : ℤ) * n)) *
          (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ))) =
      (qParam ^ (n * (d : ℤ)) + qParam ^ (-(d : ℤ)) * qParam ^ (-(n * (d : ℤ)))) +
        ((1 - qParam * qParam ^ j) * (qParam ^ (n * ((d + 1 : ℕ) : ℤ)) +
            qParam ^ (-((d + 1 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 1 : ℕ) : ℤ)))) +
          -(qParam * qParam ^ j) * (qParam ^ (n * ((d + 2 : ℕ) : ℤ)) +
            qParam ^ (-((d + 2 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 2 : ℕ) : ℤ))))) := by
  have hq := qParam_ne_zero
  have hQ : qParam ^ n ≠ 0 := zpow_ne_zero n hq
  have h2m : 2 * (m : ℤ) = ((2 * d + 2 : ℕ) : ℤ) := by subst hd; push_cast; ring
  have h1 : qParam ^ (1 - 2 * (m : ℤ)) = (qParam ^ (2 * d + 1))⁻¹ := by
    rw [h2m, ← zpow_natCast, ← zpow_neg,
      show (1 : ℤ) - ((2 * d + 2 : ℕ) : ℤ) = -((2 * d + 1 : ℕ) : ℤ) by push_cast; ring]
  have h2 : qParam ^ (-(2 * (m : ℤ) * n)) = ((qParam ^ n) ^ (2 * d + 2))⁻¹ := by
    rw [h2m, ← zpow_natCast, ← zpow_mul, ← zpow_neg, mul_comm]
  rw [h1, h2]
  simp only [zpow_neg, zpow_mul, zpow_add_one₀ hq, zpow_natCast]
  field_simp
  ring

/-- The bilateral transform of the operator applied to `φ = Q^d + Q^(d+1)` against the odd
extension of `u` is twice the defect combination. -/
private theorem cycloBilateralSum_pairQReindex_symbol_eq (m d : ℕ) (hd : m = d + 1)
    (u : ℕ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ ((1 - qParam * qParam ^ j * qParam ^ n) *
          (qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) +
        qParam ^ (1 - 2 * (m : ℤ)) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(2 * (m : ℤ) * n)) *
          (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ)))) *
        pairQOddExt u n) j =
      2 * (cycloCheb d (pairQCycloCoeff u) j +
        (1 - qParam * qParam ^ j) * cycloCheb (d + 1) (pairQCycloCoeff u) j -
          qParam * qParam ^ j * cycloCheb (d + 2) (pairQCycloCoeff u) j) := by
  have hD : cycloBilateralSum (pairQOddExt u) = fun i ↦ 2 * pairQCycloCoeff u i :=
    funext fun i ↦ (pairQ_two_mul_cycloCoeff u i).symm
  have hfun : (fun n : ℤ ↦ ((1 - qParam * qParam ^ j * qParam ^ n) *
          (qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) +
        qParam ^ (1 - 2 * (m : ℤ)) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(2 * (m : ℤ) * n)) *
          (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ)))) *
        pairQOddExt u n) =
      fun n ↦ (qParam ^ (n * (d : ℤ)) + qParam ^ (-(d : ℤ)) * qParam ^ (-(n * (d : ℤ)))) *
          pairQOddExt u n +
        ((1 - qParam * qParam ^ j) * ((qParam ^ (n * ((d + 1 : ℕ) : ℤ)) +
            qParam ^ (-((d + 1 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 1 : ℕ) : ℤ)))) *
              pairQOddExt u n) +
          -(qParam * qParam ^ j) * ((qParam ^ (n * ((d + 2 : ℕ) : ℤ)) +
            qParam ^ (-((d + 2 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 2 : ℕ) : ℤ)))) *
              pairQOddExt u n)) := by
    funext n
    rw [pairQCycloDefect_symbol_eq_reindex_symbol m d hd j n]
    ring
  rw [hfun, cycloBilateralSum_add_pairQDefect, cycloBilateralSum_add_pairQDefect,
    cycloBilateralSum_const_mul_pairQDefect, cycloBilateralSum_const_mul_pairQDefect]
  rw [cycloBilateralSum_cheb d, cycloBilateralSum_cheb (d + 1), cycloBilateralSum_cheb (d + 2),
    hD, cycloCheb_const_mul, cycloCheb_const_mul, cycloCheb_const_mul]
  ring

/-- The defect as a bilateral transform of the forcing (source Q7/Q8). -/
theorem pairQ_two_mul_cycloDefect (m : ℕ) (hm : 1 ≤ m) (u : ℕ → RatFunc ℚ)
    {h : ℤ → RatFunc ℚ}
    (hrec : ∀ n : ℤ, pairQOddExt u (n + 1) =
      qParam ^ (-(2 * (m : ℤ) * (n + 1))) * pairQOddExt u n + h n)
    (j : ℕ) :
    2 * pairQCycloDefect m u j =
      -qParam * cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
        (qParam ^ ((n + 1) * ((m - 1 : ℕ) : ℤ)) + qParam ^ ((n + 1) * (m : ℤ))) * h n) j := by
  set d := m - 1 with hd_def
  have hd : m = d + 1 := by omega
  have hr := pairQ_cycloBilateralSum_reindex m hrec
    (fun n ↦ qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) j
  beta_reduce at hr
  rw [cycloBilateralSum_pairQReindex_symbol_eq m d hd u j, ← hd] at hr
  rw [pairQCycloDefect, ← hd_def, show m + 1 = d + 2 by omega, hr]

end AJConjecture
