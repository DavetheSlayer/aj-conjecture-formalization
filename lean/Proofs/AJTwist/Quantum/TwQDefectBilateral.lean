import Mathlib
import AJConjecture.QAlgCycloBilateralSumCheb
import AJConjecture.QAlgCycloChebLinear
import AJTwist.Quantum.TwQDefect
import AJTwist.Quantum.TwQReindexZ
import AJHandoff.TorusQuantum.PairQCycloBilateral

/-!
# The inner equation for every integer index (Unit Q4)

Source: revision 5, Section 3.2 (`transfer.tex`): "Insert `f(Q) = Q^(a-1)` and
eq. (twistedinner). … Pairing the reflected terms gives the half-interval multiplier as the sum
of this expression at `Q, \hat Q`. … `S_k(Q + \hat Q) = Q^k + \hat Q^k` and `S_(-k) = q^k S_k`. …
This proves the exact inner equation for every integer `a`" (eq. (innerforcing)).

* `twChebZ_bilateral`: the bilateral transform intertwines multiplication by
  `Q^k + q^(-k) Q^(-k)` with `S_k(V)`, for every integer `k` (`cycloBilateralSum_cheb` for
  `k ≥ 0`; for `k < 0` use `Q^k + q^(-k) Q^(-k) = q^(-k) (Q^(-k) + q^k Q^k)`).
* `twQ_two_mul_defect`: apply `twQ_cycloBilateralSum_reindex` to `φ(n) = Q^(a-1) + Q^a`. The
  operator on the left is `s_(a-1) + (1 - qJ) s_a - qJ s_(a+1)`, `s_k = Q^k + q^(-k) Q^(-k)` (a
  field identity valid for every integer `a`), so by `twChebZ_bilateral` and
  `pairQ_two_mul_cycloCoeff`: `2 (p_a D)_j = -q 𝔅_j((Q - J)(Q'^(a-1) + Q'^a) h)`, `Q' = q^(n+1)`.
  For `a = m ≥ 1` this is the library's `pairQ_two_mul_cycloDefect`.

Checked at random points for eleven values of `a` between `-12` and `12` (scratch
`check_inner.py`, column `bilateral`).
-/

noncomputable section

namespace AJConjecture

/-- The bilateral transform is additive. -/
private theorem cycloBilateralSum_add_defectBilateral (f g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ f n + g n) j = cycloBilateralSum f j + cycloBilateralSum g j := by
  simp only [cycloBilateralSum, mul_add, Finset.sum_add_distrib]

/-- The bilateral transform commutes with multiplication by a constant. -/
private theorem cycloBilateralSum_const_mul_defectBilateral (c : RatFunc ℚ)
    (f : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ c * f n) j = c * cycloBilateralSum f j := by
  simp only [cycloBilateralSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  ring

/-- The trace operators of integer index commute with multiplication by a constant. -/
private theorem twChebZ_const_mul_defectBilateral (k : ℤ) (c : RatFunc ℚ) (y : ℕ → RatFunc ℚ)
    (j : ℕ) : twChebZ k (fun i ↦ c * y i) j = c * twChebZ k y j := by
  unfold twChebZ
  split_ifs
  · exact cycloCheb_const_mul _ c y j
  · rw [cycloCheb_const_mul]
    ring

/-- An integer power of `q` whose exponent is an integer combination of `na`, `a`, `n`, `1`. -/
private theorem qParam_zpow_eq_of_lin_defectBilateral (a n c₁ c₂ c₃ c₄ e : ℤ)
    (h : e = c₁ * (n * a) + c₂ * a + c₃ * n + c₄) :
    qParam ^ e =
      (qParam ^ (n * a)) ^ c₁ * (qParam ^ a) ^ c₂ * (qParam ^ n) ^ c₃ * qParam ^ c₄ := by
  have hq := qParam_ne_zero
  rw [h, zpow_add₀ hq, zpow_add₀ hq, zpow_add₀ hq, mul_comm c₁, mul_comm c₂, mul_comm c₃,
    zpow_mul _ (n * a) c₁, zpow_mul _ a c₂, zpow_mul _ n c₃]

/-- The operator of the re-indexing identity applied to `φ = Q^(a-1) + Q^a` is
`s_(a-1) + (1 - qJ) s_a - qJ s_(a+1)` with `s_k = Q^k + q^(-k) Q^(-k)`, for every integer `a`. -/
private theorem twDefect_symbol_eq_reindex_symbol_defectBilateral (a : ℤ) (j : ℕ) (n : ℤ) :
    (1 - qParam * qParam ^ j * qParam ^ n) * (qParam ^ (n * (a - 1)) + qParam ^ (n * a)) +
        qParam ^ (1 - 2 * a) * (qParam ^ n - qParam ^ j) * qParam ^ (-(2 * a * n)) *
          (qParam ^ ((n + 1) * (a - 1)) + qParam ^ ((n + 1) * a)) =
      (qParam ^ (n * (a - 1)) + qParam ^ (-(a - 1)) * qParam ^ (-(n * (a - 1)))) +
        ((1 - qParam * qParam ^ j) *
            (qParam ^ (n * a) + qParam ^ (-a) * qParam ^ (-(n * a))) +
          -(qParam * qParam ^ j) *
            (qParam ^ (n * (a + 1)) + qParam ^ (-(a + 1)) * qParam ^ (-(n * (a + 1))))) := by
  have hq := qParam_ne_zero
  have hA : qParam ^ (n * a) ≠ 0 := zpow_ne_zero _ hq
  have hB : qParam ^ a ≠ 0 := zpow_ne_zero _ hq
  have hQ : qParam ^ n ≠ 0 := zpow_ne_zero _ hq
  rw [qParam_zpow_eq_of_lin_defectBilateral a n 1 0 (-1) 0 (n * (a - 1)) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n 0 (-2) 0 1 (1 - 2 * a) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n (-2) 0 0 0 (-(2 * a * n)) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n 1 1 (-1) (-1) ((n + 1) * (a - 1)) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n 1 1 0 0 ((n + 1) * a) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n 0 (-1) 0 1 (-(a - 1)) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n (-1) 0 1 0 (-(n * (a - 1))) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n 0 (-1) 0 0 (-a) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n (-1) 0 0 0 (-(n * a)) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n 1 0 1 0 (n * (a + 1)) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n 0 (-1) 0 (-1) (-(a + 1)) (by ring),
    qParam_zpow_eq_of_lin_defectBilateral a n (-1) 0 (-1) 0 (-(n * (a + 1))) (by ring)]
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- The bilateral transform intertwines multiplication by `Q^k + q^(-k) Q^(-k)` with `S_k(V)`,
for every integer `k`. -/
theorem twChebZ_bilateral (k : ℤ) (g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum
        (fun n ↦ (qParam ^ (n * k) + qParam ^ (-k) * qParam ^ (-(n * k))) * g n) j =
      twChebZ k (cycloBilateralSum g) j := by
  obtain ⟨d, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [twChebZ_natCast]
    exact cycloBilateralSum_cheb d g j
  · have hq := qParam_ne_zero
    have hfun : (fun n : ℤ ↦ (qParam ^ (n * -(d : ℤ)) +
        qParam ^ (-(-(d : ℤ))) * qParam ^ (-(n * -(d : ℤ)))) * g n) =
        fun n ↦ qParam ^ d * ((qParam ^ (n * (d : ℤ)) +
          qParam ^ (-(d : ℤ)) * qParam ^ (-(n * (d : ℤ)))) * g n) := by
      funext n
      have h1 : qParam ^ d * qParam ^ (-(d : ℤ)) = 1 := by
        rw [← zpow_natCast, ← zpow_add₀ hq, add_neg_cancel, zpow_zero]
      rw [mul_neg, neg_neg, neg_neg, zpow_natCast]
      linear_combination (-(qParam ^ (-(n * (d : ℤ))) * g n)) * h1
    rw [hfun, cycloBilateralSum_const_mul_defectBilateral, cycloBilateralSum_cheb d,
      twChebZ_neg_natCast]

/-- The inner equation: the image of the cyclotomic coefficients under `p_a` is a bilateral
transform of the forcing of the input. -/
theorem twQ_two_mul_defect (a : ℤ) (u : ℕ → RatFunc ℚ) {h : ℤ → RatFunc ℚ}
    (hrec : ∀ n : ℤ, pairQOddExt u (n + 1) =
      qParam ^ (-(2 * a * (n + 1))) * pairQOddExt u n + h n)
    (j : ℕ) :
    2 * twDefect a u j =
      -qParam * cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
        (qParam ^ ((n + 1) * (a - 1)) + qParam ^ ((n + 1) * a)) * h n) j := by
  have hD : cycloBilateralSum (pairQOddExt u) = fun i ↦ 2 * pairQCycloCoeff u i :=
    funext fun i ↦ (pairQ_two_mul_cycloCoeff u i).symm
  have hr := twQ_cycloBilateralSum_reindex a hrec
    (fun n ↦ qParam ^ (n * (a - 1)) + qParam ^ (n * a)) j
  beta_reduce at hr
  rw [← hr]
  have hfun : (fun n : ℤ ↦ ((1 - qParam * qParam ^ j * qParam ^ n) *
          (qParam ^ (n * (a - 1)) + qParam ^ (n * a)) +
        qParam ^ (1 - 2 * a) * (qParam ^ n - qParam ^ j) * qParam ^ (-(2 * a * n)) *
          (qParam ^ ((n + 1) * (a - 1)) + qParam ^ ((n + 1) * a))) * pairQOddExt u n) =
      fun n ↦ (qParam ^ (n * (a - 1)) + qParam ^ (-(a - 1)) * qParam ^ (-(n * (a - 1)))) *
          pairQOddExt u n +
        ((1 - qParam * qParam ^ j) *
            ((qParam ^ (n * a) + qParam ^ (-a) * qParam ^ (-(n * a))) * pairQOddExt u n) +
          -(qParam * qParam ^ j) *
            ((qParam ^ (n * (a + 1)) + qParam ^ (-(a + 1)) * qParam ^ (-(n * (a + 1)))) *
              pairQOddExt u n)) := by
    funext n
    rw [twDefect_symbol_eq_reindex_symbol_defectBilateral a j n]
    ring
  rw [hfun, cycloBilateralSum_add_defectBilateral, cycloBilateralSum_add_defectBilateral,
    cycloBilateralSum_const_mul_defectBilateral, cycloBilateralSum_const_mul_defectBilateral,
    twChebZ_bilateral, twChebZ_bilateral, twChebZ_bilateral, hD,
    twChebZ_const_mul_defectBilateral, twChebZ_const_mul_defectBilateral,
    twChebZ_const_mul_defectBilateral, twDefect]
  ring

end AJConjecture
