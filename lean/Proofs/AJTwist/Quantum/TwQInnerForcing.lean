import Mathlib
import AJTwist.Quantum.TwQForcingWeight
import AJTwist.Quantum.TwQDefectBilateral
import AJConjecture.QAlgCycloKernelAntisymm

/-!
# The inner equation `p_a D = e` for the twisted input (Unit Q4)

Source: revision 5, Section 3.2, eq. (innerforcing): "This proves the exact inner equation for
every integer `a`: `p_a D = e`, `e_j = ∑_{n=0}^{j} K_{jn} g(n) ℛ_η(Q, J)` … The prefactor is
`-q^a g(n+1)/g(n)` with its `Q`-power put into `A`. The reflected forcing gives a difference
because `K_{jn} g(n)` is odd."

* `twQ_defect_eq_sum`: eq. (innerforcing) for `u = twInput η r s ℓ`, `a = twIndex η r s ℓ`. As in
  the paper the weight is `f = Q^(a-1)` alone: the bilateral sum against
  `(Q - J)(Q'^(a-1) - Q'^a) h` vanishes (re-indexing identity `twQ_cycloBilateralSum_reindex` with
  `φ = Q^(a-1) - Q^a`, whose multiplier is odd under `n ↦ -n-1`), so
  `(p_a D)_j = -q 𝔅_j((Q - J) Q'^(a-1) h)` for every input with forcing `h`; with `twInput_rec`,
  `h = twForcing`, the bilateral sum is folded onto `0 ≤ n ≤ j` by the oddness of the kernel, and
  with `twForcing_eq_sum` and `a + 2ℓ = ηm + ℓ` the summand is `g(n) ℛ_η(q^n, q^j)` termwise.
* `twQ_defect_eq_periods`: the same statement with the inner sums recognized as the cyclotomic
  coefficients of the Gaussian period inputs:
  `g(n) ℛ_η = -q^(ηm+ℓ) ∑_i c_i (w_n^{(ℓ,p_i)} - q^j w_n^{(ℓ,p_i-1)})`.

Checked at random points (scratch `check_transfer.py`, column `inner`; `check_literal.py`).
-/

noncomputable section

namespace AJConjecture

/-- Folding the bilateral transform onto `0 ≤ k ≤ j` by the oddness of the kernel. -/
private theorem cycloBilateralSum_eq_sum_range_innerForcing (ψ : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum ψ j =
      ∑ k ∈ Finset.range (j + 1), cycloBilateralKernel j k * (ψ k - ψ (-(k : ℤ) - 1)) := by
  have hU : Finset.Icc (-((j : ℤ) + 1)) (j : ℤ) =
      Finset.Icc (-((j : ℤ) + 1)) (-1) ∪ Finset.Icc (0 : ℤ) (j : ℤ) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hD : Disjoint (Finset.Icc (-((j : ℤ) + 1)) (-1)) (Finset.Icc (0 : ℤ) (j : ℤ)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rw [Finset.mem_Icc] at h1 h2
    omega
  have hneg : ∑ n ∈ Finset.Icc (-((j : ℤ) + 1)) (-1), cycloBilateralKernel j n * ψ n =
      ∑ k ∈ Finset.range (j + 1), cycloBilateralKernel j k * -ψ (-(k : ℤ) - 1) := by
    refine Finset.sum_nbij' (fun n ↦ (-n - 1).toNat) (fun k ↦ -(k : ℤ) - 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    · intro k _
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
      rw [show (-(-(k : ℤ) - 1) - 1).toNat = k by omega, cycloBilateralKernel_neg_sub_one]
      ring
  have hpos : ∑ n ∈ Finset.Icc (0 : ℤ) (j : ℤ), cycloBilateralKernel j n * ψ n =
      ∑ k ∈ Finset.range (j + 1), cycloBilateralKernel j k * ψ k := by
    refine Finset.sum_nbij' (fun n ↦ n.toNat) (fun k ↦ (k : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    · intro k _
      exact Int.toNat_natCast k
    · intro n hn
      rw [Finset.mem_Icc] at hn
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.1
      rw [Int.toNat_natCast]
  rw [cycloBilateralSum, hU, Finset.sum_union hD, hneg, hpos, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-- An integer power of `q` whose exponent is an integer combination of `na`, `a`, `n`, `1`. -/
private theorem qParam_zpow_eq_of_lin_innerForcing (a n c₁ c₂ c₃ c₄ e : ℤ)
    (h : e = c₁ * (n * a) + c₂ * a + c₃ * n + c₄) :
    qParam ^ e =
      (qParam ^ (n * a)) ^ c₁ * (qParam ^ a) ^ c₂ * (qParam ^ n) ^ c₃ * qParam ^ c₄ := by
  have hq := qParam_ne_zero
  rw [h, zpow_add₀ hq, zpow_add₀ hq, zpow_add₀ hq, mul_comm c₁, mul_comm c₂, mul_comm c₃,
    zpow_mul _ (n * a) c₁, zpow_mul _ a c₂, zpow_mul _ n c₃]

/-- The operator of the re-indexing identity applied to `φ = Q^(a-1) - Q^a` is odd under the
reflection `n ↦ -n - 1`. -/
private theorem reindexSymbol_neg_sub_one_innerForcing (a : ℤ) (j : ℕ) (n : ℤ) :
    (1 - qParam * qParam ^ j * qParam ^ (-n - 1)) *
          (qParam ^ ((-n - 1) * (a - 1)) - qParam ^ ((-n - 1) * a)) +
        qParam ^ (1 - 2 * a) * (qParam ^ (-n - 1) - qParam ^ j) *
          qParam ^ (-(2 * a * (-n - 1))) *
            (qParam ^ ((-n - 1 + 1) * (a - 1)) - qParam ^ ((-n - 1 + 1) * a)) =
      -((1 - qParam * qParam ^ j * qParam ^ n) * (qParam ^ (n * (a - 1)) - qParam ^ (n * a)) +
        qParam ^ (1 - 2 * a) * (qParam ^ n - qParam ^ j) * qParam ^ (-(2 * a * n)) *
          (qParam ^ ((n + 1) * (a - 1)) - qParam ^ ((n + 1) * a))) := by
  have hq := qParam_ne_zero
  have hA : qParam ^ (n * a) ≠ 0 := zpow_ne_zero _ hq
  have hB : qParam ^ a ≠ 0 := zpow_ne_zero _ hq
  have hQ : qParam ^ n ≠ 0 := zpow_ne_zero _ hq
  rw [qParam_zpow_eq_of_lin_innerForcing a n 0 0 (-1) (-1) (-n - 1) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n (-1) (-1) 1 1 ((-n - 1) * (a - 1)) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n (-1) (-1) 0 0 ((-n - 1) * a) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n 0 (-2) 0 1 (1 - 2 * a) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n 2 2 0 0 (-(2 * a * (-n - 1))) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n (-1) 0 1 0 ((-n - 1 + 1) * (a - 1)) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n (-1) 0 0 0 ((-n - 1 + 1) * a) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n 1 0 (-1) 0 (n * (a - 1)) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n (-2) 0 0 0 (-(2 * a * n)) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n 1 1 (-1) (-1) ((n + 1) * (a - 1)) (by ring),
    qParam_zpow_eq_of_lin_innerForcing a n 1 1 0 0 ((n + 1) * a) (by ring)]
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- The bilateral transform of the forcing against `(Q - J)(Q'^(a-1) - Q'^a)` vanishes: the two
weights `f = Q^(a-1)` and `f = Q^a` give the same inner equation. -/
private theorem cycloBilateralSum_forcing_diff_eq_zero_innerForcing (a : ℤ) (u : ℕ → RatFunc ℚ)
    {h : ℤ → RatFunc ℚ}
    (hrec : ∀ n : ℤ, pairQOddExt u (n + 1) =
      qParam ^ (-(2 * a * (n + 1))) * pairQOddExt u n + h n)
    (j : ℕ) :
    -qParam * cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
      (qParam ^ ((n + 1) * (a - 1)) - qParam ^ ((n + 1) * a)) * h n) j = 0 := by
  have hr := twQ_cycloBilateralSum_reindex a hrec
    (fun n ↦ qParam ^ (n * (a - 1)) - qParam ^ (n * a)) j
  beta_reduce at hr
  rw [← hr, cycloBilateralSum_eq_sum_range_innerForcing]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [reindexSymbol_neg_sub_one_innerForcing a j k, pairQOddExt_neg_sub_one, neg_mul_neg,
    sub_self, mul_zero]

/-- The inner equation with the weight `f = Q^(a-1)` of the source: `(p_a D)_j` is the bilateral
transform of `-q (Q - J) Q'^(a-1) h`, `Q' = q^(n+1)`, for every integer `a`. -/
private theorem twDefect_eq_cycloBilateralSum_innerForcing (a : ℤ) (u : ℕ → RatFunc ℚ)
    {h : ℤ → RatFunc ℚ}
    (hrec : ∀ n : ℤ, pairQOddExt u (n + 1) =
      qParam ^ (-(2 * a * (n + 1))) * pairQOddExt u n + h n)
    (j : ℕ) :
    twDefect a u j =
      -qParam * cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
        qParam ^ ((n + 1) * (a - 1)) * h n) j := by
  have h2 := twQ_two_mul_defect a u hrec j
  have h0 := cycloBilateralSum_forcing_diff_eq_zero_innerForcing a u hrec j
  have hs : cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
        (qParam ^ ((n + 1) * (a - 1)) + qParam ^ ((n + 1) * a)) * h n) j +
      cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
        (qParam ^ ((n + 1) * (a - 1)) - qParam ^ ((n + 1) * a)) * h n) j =
      2 * cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
        qParam ^ ((n + 1) * (a - 1)) * h n) j := by
    simp only [cycloBilateralSum]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    ring
  linear_combination (1 / 2 : RatFunc ℚ) * h2 - (1 / 2 : RatFunc ℚ) * h0 - (qParam / 2) * hs

/-- The index `a = η m - ℓ` with the sign written as in the forcing weight. -/
private theorem twIndex_eq_sign_mul_innerForcing (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    twIndex η r s ℓ = (if η then 1 else -1) * ((r : ℤ) * s) - ℓ := by
  cases η <;> simp [twIndex]

/-- The forcing term of the inner equation at the integer `n`:
`-q (Q - J) Q'^(a-1) g(n+1) H_η(q, Q) = -q^(ηm+ℓ) g(n) A(Q, J)`. -/
private theorem forcing_term_eq_innerForcing (η : Bool) (r s : ℕ) (ℓ : ℤ) (j : ℕ) (n : ℤ) :
    -qParam * ((qParam ^ n - qParam ^ j) * qParam ^ ((n + 1) * (twIndex η r s ℓ - 1)) *
        twForcing η r s ℓ n) =
      qParam ^ (ℓ * n * (n + 1)) *
        (-(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
          ∑ i : Fin 4, twCoef η r s i *
            (qParam ^ (twExp η r s ℓ i * n) -
              qParam ^ j * qParam ^ ((twExp η r s ℓ i - 1) * n))) := by
  have hq := qParam_ne_zero
  rw [twForcing_eq_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have k1 : qParam * (qParam ^ ((n + 1) * (twIndex η r s ℓ - 1)) *
        (qParam ^ (ℓ * (n + 1) * (n + 2)) *
          qParam ^ (n * ((if η then 1 else -1) * (twLambda r s i - (r : ℤ) * s))))) =
      qParam ^ (ℓ * n * (n + 1)) *
        (qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ) *
          qParam ^ ((twExp η r s ℓ i - 1) * n)) := by
    rw [← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_one_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
    congr 1
    rw [twIndex_eq_sign_mul_innerForcing, twExp]
    ring
  have k2 : qParam ^ n * qParam ^ ((twExp η r s ℓ i - 1) * n) =
      qParam ^ (twExp η r s ℓ i * n) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  linear_combination (-(twCoef η r s i * (qParam ^ n - qParam ^ j))) * k1 -
    (twCoef η r s i * qParam ^ (ℓ * n * (n + 1)) *
      qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) * k2

/-- The forcing term of the inner equation at the reflected integer `-n - 1`. -/
private theorem forcing_term_neg_sub_one_innerForcing (η : Bool) (r s : ℕ) (ℓ : ℤ) (j : ℕ)
    (n : ℤ) :
    -qParam * ((qParam ^ (-n - 1) - qParam ^ j) *
        qParam ^ ((-n - 1 + 1) * (twIndex η r s ℓ - 1)) * twForcing η r s ℓ (-n - 1)) =
      qParam ^ (ℓ * n * (n + 1)) *
        (-(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
          ∑ i : Fin 4, twCoef η r s i *
            (qParam ^ (-(twExp η r s ℓ i * (n + 1))) -
              qParam ^ j * qParam ^ (-((twExp η r s ℓ i - 1) * (n + 1))))) := by
  rw [forcing_term_eq_innerForcing, show ℓ * (-n - 1) * (-n - 1 + 1) = ℓ * n * (n + 1) by ring]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show twExp η r s ℓ i * (-n - 1) = -(twExp η r s ℓ i * (n + 1)) by ring,
    show (twExp η r s ℓ i - 1) * (-n - 1) = -((twExp η r s ℓ i - 1) * (n + 1)) by ring]

/-- The cyclotomic coefficients as a sum against the bilateral kernel on `0 ≤ k ≤ j`. -/
private theorem pairQCycloCoeff_eq_sum_kernel_innerForcing (u : ℕ → RatFunc ℚ) (j : ℕ) :
    pairQCycloCoeff u j = ∑ k ∈ Finset.range (j + 1), cycloBilateralKernel j k * u k := by
  rw [pairQCycloCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  have hE : (m : ℤ) * ((m : ℤ) + 1) / 2 = ((m * (m + 1) / 2 : ℕ) : ℤ) := by norm_cast
  rw [cycloBilateralKernel, ite_eq_left (by omega),
    show ((j : ℤ) - (m : ℤ)).toNat = j - m by omega,
    show ((j : ℤ) + (m : ℤ) + 1).toNat = j + m + 1 by omega, hE, zpow_natCast, zpow_natCast]
  ring

/-- Eq. (innerforcing): `(p_a D)_j = ∑_{n ≤ j} K_{j,n} g(n) ℛ_η(q^n, q^j)` for the twisted
input, `a = twIndex η r s ℓ`. -/
theorem twQ_defect_eq_sum (η : Bool) (r s : ℕ) (ℓ : ℤ) (j : ℕ) :
    twDefect (twIndex η r s ℓ) (twInput η r s ℓ) j =
      ∑ k ∈ Finset.range (j + 1), cycloBilateralKernel j k *
        (qParam ^ (ℓ * (k : ℤ) * ((k : ℤ) + 1)) * twForcingWeight η r s ℓ k j) := by
  rw [twDefect_eq_cycloBilateralSum_innerForcing _ _ (twInput_rec η r s ℓ) j,
    cycloBilateralSum_eq_sum_range_innerForcing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have e1 := forcing_term_eq_innerForcing η r s ℓ j k
  have e2 := forcing_term_neg_sub_one_innerForcing η r s ℓ j k
  have hw : twForcingWeight η r s ℓ k j =
      -(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
          ∑ i : Fin 4, twCoef η r s i *
            (qParam ^ (twExp η r s ℓ i * k) -
              qParam ^ j * qParam ^ ((twExp η r s ℓ i - 1) * k)) -
        -(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
          ∑ i : Fin 4, twCoef η r s i *
            (qParam ^ (-(twExp η r s ℓ i * ((k : ℤ) + 1))) -
              qParam ^ j * qParam ^ (-((twExp η r s ℓ i - 1) * ((k : ℤ) + 1)))) := by
    rw [twForcingWeight, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hw]
  linear_combination cycloBilateralKernel j k * e1 - cycloBilateralKernel j k * e2

/-- Eq. (innerforcing) in terms of the Gaussian period inputs:
`(p_a D)_j = -q^(ηm+ℓ) ∑_i c_i (D_j(w^{(ℓ, p_i)}) - q^j D_j(w^{(ℓ, p_i - 1)}))`. -/
theorem twQ_defect_eq_periods (η : Bool) (r s : ℕ) (ℓ : ℤ) (j : ℕ) :
    twDefect (twIndex η r s ℓ) (twInput η r s ℓ) j =
      -(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
        ∑ i : Fin 4, twCoef η r s i *
          (pairQCycloCoeff (twPeriodInput ℓ (twExp η r s ℓ i)) j -
            qParam ^ j * pairQCycloCoeff (twPeriodInput ℓ (twExp η r s ℓ i - 1)) j) := by
  rw [twQ_defect_eq_sum]
  simp only [pairQCycloCoeff_eq_sum_kernel_innerForcing, twForcingWeight, twPeriodInput]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end AJConjecture
