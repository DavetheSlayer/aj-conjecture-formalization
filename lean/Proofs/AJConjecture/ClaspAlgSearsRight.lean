import Mathlib
import AJConjecture.ClaspAlgBasic
import AJConjecture.ClaspAlgQVandermonde
import AJConjecture.ClaspAlgQVandermondeDual
import AJConjecture.ClaspAlgSearsMid

/-!
# The Sears transformation, cyclotomic side

With `P_m = (q; q)_m` and `c = n + M`:
`(-1)^n q^(n(n+1)/2) ∑_{m=0}^{M} (-1)^(n+m) q^((n+m)(n+m+1)/2 - c(n+m)) P_(2n+M+1+m) P_(n+m) /
(P_(M-m) P_m P_(2n+1+m)) = q^(c²+2c) Mid(n, M)`.

Route: expand, by the dual `q`-Chu–Vandermonde sum with `x = q^(n+1)`, `y = q^(2n+2)`,
`P_(n+m) / (P_m P_(2n+1+m)) = ∑_{i=0}^{m} (-1)^i q^(i(i-1)/2 + (n+1)i) P_(n+i) / (P_i P_(m-i) P_(2n+1+i))`;
exchange the two summations; the inner sum over `m = i + l` is
`∑_{l=0}^{M-i} (-1)^l q^(l(l+1)/2 - (M-i) l) P_(a+l) / (P_l P_(M-i-l)) = q^((a+1)(M-i)) P_a / P_(M-i)` with
`a = 2n+M+1+i`, the case `C = 0`, `b = q^(a+1)` of the `q`-Chu–Vandermonde sum.

The two sums are `claspAlg_qVandermonde_dual` and `claspAlg_qVandermonde` (stated with natural
exponents `q^(i(i-1)/2)`, `q^((m-k)(m-k-1)/2)`); `(q^(a+1); q)_k = P_(a+k) / P_a` is
`claspAlg_qPochhammer_mul_shift`.
-/

namespace AJConjecture

/-- Twice the triangular number `k(k-1)/2`, as an integer. -/
private theorem claspAlg_searsRight_two_mul_tri (k : ℕ) :
    2 * ((k * (k - 1) / 2 : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
  have h := Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
  have h' : (2 : ℤ) * ((k * (k - 1) / 2 : ℕ) : ℤ) = ((k * (k - 1) : ℕ) : ℤ) := by
    exact_mod_cast h
  rw [h']
  cases k with
  | zero => simp
  | succ k =>
    push_cast
    simp

/-- Twice the triangular number `k(k+1)/2`, as an integer. -/
theorem claspAlg (k : ℕ) :
    2 * ((k * (k + 1) / 2 : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) + 1) := by
  have h := Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd
  exact_mod_cast h

/-- The case `C = 0`, `b = q^(a+1)` of the `q`-Chu–Vandermonde sum, in terms of `(q; q)_m`. -/
private theorem claspAlg_searsRight_innerSum (a K : ℕ) :
    ∑ l ∈ Finset.range (K + 1),
        (-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (a + l) /
          (qPochhammer qParam l * qPochhammer qParam (K - l)) =
      qParam ^ (K * (K - 1) / 2) * qParam ^ ((a + 1) * K) * qPochhammer qParam a /
        qPochhammer qParam K := by
  have hPK := qPochhammer_qParam_ne_zero K
  have h0 : ∀ (x : RatFunc ℚ) (j : ℕ), qPochhammer (0 * x) j = 1 := by
    intro x j
    simp [qPochhammer]
  have hV := claspAlg_qVandermonde K (qParam ^ (a + 1)) 0
  have hprod : ∏ s ∈ Finset.range K, qParam ^ s * (qParam ^ (a + 1) - 0 * qParam ^ s) =
      qParam ^ (K * (K - 1) / 2) * qParam ^ ((a + 1) * K) := by
    simp only [zero_mul, sub_zero]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
      Finset.prod_const, Finset.card_range, ← pow_mul]
  have hterm : ∀ l ∈ Finset.range (K + 1),
      (-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) *
          (qPochhammer qParam K / (qPochhammer qParam l * qPochhammer qParam (K - l))) *
          qPochhammer (0 * qParam ^ l) (K - l) * qPochhammer (qParam ^ (a + 1)) l *
          qPochhammer qParam a =
        qPochhammer qParam K *
          ((-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (a + l) /
            (qPochhammer qParam l * qPochhammer qParam (K - l))) := by
    intro l _
    rw [h0, ← claspAlg_qPochhammer_mul_shift a l]
    ring
  have hsum : (∏ s ∈ Finset.range K, qParam ^ s * (qParam ^ (a + 1) - 0 * qParam ^ s)) *
      qPochhammer qParam a =
        qPochhammer qParam K * ∑ l ∈ Finset.range (K + 1),
          (-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (a + l) /
            (qPochhammer qParam l * qPochhammer qParam (K - l)) := by
    rw [← hV, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hprod] at hsum
  rw [eq_div_iff hPK]
  linear_combination -hsum

/-- The product of the dual `q`-Chu–Vandermonde sum at `x = q^(n+1)`, `y = q^(2n+2)`. -/
private theorem claspAlg_searsRight_prod (n m : ℕ) :
    ∏ s ∈ Finset.range m, (qParam ^ (n + 1) - qParam ^ (2 * n + 1 + 1) * qParam ^ s) =
      qParam ^ ((n + 1) * m) * qPochhammer (qParam ^ (n + 1)) m := by
  induction m with
  | zero => simp [qPochhammer]
  | succ m ih =>
    have hW : qPochhammer (qParam ^ (n + 1)) (m + 1) =
        qPochhammer (qParam ^ (n + 1)) m * (1 - qParam ^ (n + 1) * qParam ^ m) :=
      Finset.prod_range_succ _ _
    rw [Finset.prod_range_succ, ih, hW]
    ring

/-- The expansion of `P_(n+m) / (P_m P_(2n+1+m))` by the dual `q`-Chu–Vandermonde sum. -/
private theorem claspAlg_searsRight_expand (n m : ℕ) :
    ∑ i ∈ Finset.range (m + 1),
        (-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ ((n + 1) * i) * qPochhammer qParam (n + i) /
          (qPochhammer qParam i * qPochhammer qParam (m - i) * qPochhammer qParam (2 * n + 1 + i)) =
      qPochhammer qParam (n + m) / (qPochhammer qParam m * qPochhammer qParam (2 * n + 1 + m)) := by
  have hV := claspAlg_qVandermonde_dual m (qParam ^ (n + 1)) (qParam ^ (2 * n + 1 + 1))
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (-1) ^ i * qParam ^ (i * (i - 1) / 2) *
          (qPochhammer qParam m / (qPochhammer qParam i * qPochhammer qParam (m - i))) *
          qPochhammer (qParam ^ (2 * n + 1 + 1) * qParam ^ i) (m - i) *
          (qParam ^ (2 * n + 1 + 1)) ^ i *
          (qPochhammer (qParam ^ (n + 1)) i * (qParam ^ (n + 1)) ^ (m - i)) *
          qPochhammer qParam n =
        qPochhammer qParam m * qPochhammer qParam (2 * n + 1 + m) * qParam ^ ((n + 1) * m) *
          ((-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ ((n + 1) * i) *
            qPochhammer qParam (n + i) /
            (qPochhammer qParam i * qPochhammer qParam (m - i) *
              qPochhammer qParam (2 * n + 1 + i))) := by
    intro i hi
    obtain ⟨d, rfl⟩ : ∃ d, m = i + d := ⟨m - i, by have := Finset.mem_range.mp hi; omega⟩
    have e : i + d - i = d := by omega
    have hW : qPochhammer qParam (2 * n + 1 + i) *
        qPochhammer (qParam ^ (2 * n + 1 + 1) * qParam ^ i) d =
          qPochhammer qParam (2 * n + 1 + (i + d)) := by
      have h := claspAlg_qPochhammer_mul_shift (2 * n + 1 + i) d
      rw [show qParam ^ (2 * n + 1 + i + 1) = qParam ^ (2 * n + 1 + 1) * qParam ^ i by ring,
        Nat.add_assoc (2 * n + 1) i d] at h
      exact h
    have hx : qPochhammer qParam n * qPochhammer (qParam ^ (n + 1)) i =
        qPochhammer qParam (n + i) := claspAlg_qPochhammer_mul_shift n i
    have h1 := qPochhammer_qParam_ne_zero (2 * n + 1 + i)
    rw [e, ← hW, ← hx]
    field_simp
    ring
  have hsum : (∏ s ∈ Finset.range m, (qParam ^ (n + 1) - qParam ^ (2 * n + 1 + 1) * qParam ^ s)) *
      qPochhammer qParam n =
        qPochhammer qParam m * qPochhammer qParam (2 * n + 1 + m) * qParam ^ ((n + 1) * m) *
          ∑ i ∈ Finset.range (m + 1),
            (-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ ((n + 1) * i) *
              qPochhammer qParam (n + i) /
              (qPochhammer qParam i * qPochhammer qParam (m - i) *
                qPochhammer qParam (2 * n + 1 + i)) := by
    rw [← hV, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hprod := claspAlg_searsRight_prod n m
  have hshift := claspAlg_qPochhammer_mul_shift n m
  have hQ : qParam ^ ((n + 1) * m) ≠ 0 := pow_ne_zero _ qParam_ne_zero
  have hne : qPochhammer qParam m * qPochhammer qParam (2 * n + 1 + m) ≠ 0 :=
    mul_ne_zero (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _)
  rw [eq_div_iff hne]
  refine mul_left_cancel₀ hQ ?_
  linear_combination -hsum + qPochhammer qParam n * hprod + qParam ^ ((n + 1) * m) * hshift

/-- The double summand: the term of index `i` of the expansion of the `m`-th term of the
cyclotomic side. -/
private noncomputable def claspAlgSearsRightTerm (n M i m : ℕ) : RatFunc ℚ :=
  (-1) ^ n * qParam ^ (n * (n + 1) / 2) *
      ((-1) ^ (n + m) *
        qParam ^ ((((n + m) * (n + m + 1) / 2 : ℕ) : ℤ) - ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
        (qPochhammer qParam (2 * n + M + 1 + m) / qPochhammer qParam (M - m))) *
    ((-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ ((n + 1) * i) * qPochhammer qParam (n + i) /
      (qPochhammer qParam i * qPochhammer qParam (m - i) * qPochhammer qParam (2 * n + 1 + i)))

/-- One term of the cyclotomic side is a sum of double summands. -/
private theorem claspAlg_searsRight_outer (n M m : ℕ) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) *
        ((-1) ^ (n + m) *
          qParam ^ ((((n + m) * (n + m + 1) / 2 : ℕ) : ℤ) -
            ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
          qPochhammer qParam (2 * n + M + 1 + m) * qPochhammer qParam (n + m) /
          (qPochhammer qParam (M - m) * qPochhammer qParam m *
            qPochhammer qParam (2 * n + 1 + m))) =
      ∑ i ∈ Finset.range (m + 1), claspAlgSearsRightTerm n M i m := by
  unfold claspAlgSearsRightTerm
  rw [← Finset.mul_sum, claspAlg_searsRight_expand n m]
  ring

/-- The powers of `q` in a double summand, with `M = i + l + r`. -/
private theorem claspAlg_searsRight_pow_term (n i l r : ℕ) :
    qParam ^ (n * (n + 1) / 2) *
        qParam ^ ((((n + (i + l)) * (n + (i + l) + 1) / 2 : ℕ) : ℤ) -
          ((n + (i + l + r) : ℕ) : ℤ) * ((n + (i + l) : ℕ) : ℤ)) *
        qParam ^ (i * (i - 1) / 2) * qParam ^ ((n + 1) * i) =
      qParam ^ (((n * (n + 1) / 2 : ℕ) : ℤ) + (((n + i) * (n + i + 1) / 2 : ℕ) : ℤ) -
          ((n + (i + l + r) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) + ((i * (i - 1) / 2 : ℕ) : ℤ) +
          (((n + 1) * i : ℕ) : ℤ) - (((l + r) * (l + r - 1) / 2 : ℕ) : ℤ)) *
        qParam ^ (r * (r - 1) / 2) := by
  have hq := qParam_ne_zero
  have g1 := claspAlg (n + (i + l))
  have g2 := claspAlg (n + i)
  have h3 := claspAlg_searsRight_two_mul_tri (l + r)
  have h4 := claspAlg_searsRight_two_mul_tri r
  rw [← zpow_natCast qParam (n * (n + 1) / 2), ← zpow_natCast qParam (i * (i - 1) / 2),
    ← zpow_natCast qParam ((n + 1) * i), ← zpow_natCast qParam (r * (r - 1) / 2),
    ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul] at g1 g2 h3 ⊢
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  linear_combination g1 - g2 + h3 - h4

/-- The rational identity that puts a double summand in the form of a term of the inner sum. -/
private theorem claspAlg_searsRight_term_algebra
    (sn si sl Qn E Ti Qi Et Tr Pal Pr Pni Pi Pl PAi : RatFunc ℚ)
    (hsn : sn * sn = 1) (hsi : si * si = 1) (hpow : Qn * E * Ti * Qi = Et * Tr) :
    sn * Qn * (sn * (si * sl) * E * (Pal / Pr)) * (si * Ti * Qi * Pni / (Pi * Pl * PAi)) =
      Et * Pni / (Pi * PAi) * (sl * Tr * Pal / (Pl * Pr)) := by
  have key : sn * Qn * (sn * (si * sl) * E * (Pal / Pr)) * (si * Ti * Qi * Pni / (Pi * Pl * PAi)) =
      (sn * sn) * (si * si) * (Qn * E * Ti * Qi) * (sl * Pal * Pni / (Pr * Pi * Pl * PAi)) := by
    ring
  rw [key, hsn, hsi, hpow]
  ring

/-- A double summand with `m = i + l`, `M = i + l + r`, as a term of the inner sum. -/
private theorem claspAlgSearsRightTerm_eq (n i l r : ℕ) :
    claspAlgSearsRightTerm n (i + l + r) i (i + l) =
      qParam ^ (((n * (n + 1) / 2 : ℕ) : ℤ) + (((n + i) * (n + i + 1) / 2 : ℕ) : ℤ) -
            ((n + (i + l + r) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) + ((i * (i - 1) / 2 : ℕ) : ℤ) +
            (((n + 1) * i : ℕ) : ℤ) - (((l + r) * (l + r - 1) / 2 : ℕ) : ℤ)) *
          qPochhammer qParam (n + i) / (qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i)) *
        ((-1) ^ l * qParam ^ (r * (r - 1) / 2) *
          qPochhammer qParam (2 * n + (i + l + r) + 1 + (i + l)) /
          (qPochhammer qParam l * qPochhammer qParam r)) := by
  have hsn : (-1 : RatFunc ℚ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hsi : (-1 : RatFunc ℚ) ^ i * (-1) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  unfold claspAlgSearsRightTerm
  rw [show i + l + r - (i + l) = r by omega, show i + l - i = l by omega,
    pow_add (-1 : RatFunc ℚ) n (i + l), pow_add (-1 : RatFunc ℚ) i l]
  exact claspAlg_searsRight_term_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsn hsi
    (claspAlg_searsRight_pow_term n i l r)

/-- The powers of `q` after the inner summation, with `M = i + K`. -/
private theorem claspAlg_searsRight_pow_final (n i K : ℕ) :
    qParam ^ (((n * (n + 1) / 2 : ℕ) : ℤ) + (((n + i) * (n + i + 1) / 2 : ℕ) : ℤ) -
          ((n + (i + K) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) + ((i * (i - 1) / 2 : ℕ) : ℤ) +
          (((n + 1) * i : ℕ) : ℤ) - ((K * (K - 1) / 2 : ℕ) : ℤ)) *
        (qParam ^ (K * (K - 1) / 2) * qParam ^ ((2 * n + (i + K) + 1 + i + 1) * K)) =
      qParam ^ ((n + (i + K)) ^ 2 + 2 * (n + (i + K))) *
        qParam ^ (-(((n + (i + K) + 1) * (n + i) : ℕ) : ℤ)) := by
  have hq := qParam_ne_zero
  have g0 := claspAlg n
  have g2 := claspAlg (n + i)
  have h2 := claspAlg_searsRight_two_mul_tri i
  rw [← zpow_natCast qParam (K * (K - 1) / 2),
    ← zpow_natCast qParam ((2 * n + (i + K) + 1 + i + 1) * K),
    ← zpow_natCast qParam ((n + (i + K)) ^ 2 + 2 * (n + (i + K))), ← zpow_add₀ hq, ← zpow_add₀ hq,
    ← zpow_add₀ hq]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at g2 ⊢
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  linear_combination g0 + g2 + h2

/-- The inner sum of the double sum is a term of the middle sum. -/
private theorem claspAlg_searsRight_inner (n i K : ℕ) :
    ∑ l ∈ Finset.range (K + 1), claspAlgSearsRightTerm n (i + K) i (i + l) =
      qParam ^ ((n + (i + K)) ^ 2 + 2 * (n + (i + K))) *
        (qParam ^ (-(((n + (i + K) + 1) * (n + i) : ℕ) : ℤ)) *
          qPochhammer qParam (2 * n + (i + K) + 1 + i) * qPochhammer qParam (n + i) /
          (qPochhammer qParam (i + K - i) * qPochhammer qParam i *
            qPochhammer qParam (2 * n + 1 + i))) := by
  have hterm : ∀ l ∈ Finset.range (K + 1), claspAlgSearsRightTerm n (i + K) i (i + l) =
      qParam ^ (((n * (n + 1) / 2 : ℕ) : ℤ) + (((n + i) * (n + i + 1) / 2 : ℕ) : ℤ) -
            ((n + (i + K) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) + ((i * (i - 1) / 2 : ℕ) : ℤ) +
            (((n + 1) * i : ℕ) : ℤ) - ((K * (K - 1) / 2 : ℕ) : ℤ)) *
          qPochhammer qParam (n + i) / (qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i)) *
        ((-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) *
          qPochhammer qParam (2 * n + (i + K) + 1 + i + l) /
          (qPochhammer qParam l * qPochhammer qParam (K - l))) := by
    intro l hl
    obtain ⟨r, rfl⟩ : ∃ r, K = l + r := ⟨K - l, by have := Finset.mem_range.mp hl; omega⟩
    rw [show l + r - l = r by omega, show i + (l + r) = i + l + r by omega,
      show 2 * n + (i + l + r) + 1 + i + l = 2 * n + (i + l + r) + 1 + (i + l) by omega]
    exact claspAlgSearsRightTerm_eq n i l r
  have hf := claspAlg_searsRight_pow_final n i K
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    claspAlg_searsRight_innerSum (2 * n + (i + K) + 1 + i) K, show i + K - i = K by omega]
  linear_combination (qPochhammer qParam (2 * n + (i + K) + 1 + i) * qPochhammer qParam (n + i) /
    (qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i) * qPochhammer qParam K)) * hf

/-- The cyclotomic side of the clasp identity is the middle term of the Sears transformation. -/
theorem claspAlg_searsRight (n M : ℕ) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) *
        ∑ m ∈ Finset.range (M + 1),
          (-1) ^ (n + m) *
            qParam ^ ((((n + m) * (n + m + 1) / 2 : ℕ) : ℤ) -
              ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
            qPochhammer qParam (2 * n + M + 1 + m) * qPochhammer qParam (n + m) /
            (qPochhammer qParam (M - m) * qPochhammer qParam m *
              qPochhammer qParam (2 * n + 1 + m)) =
      qParam ^ ((n + M) ^ 2 + 2 * (n + M)) * claspAlgSearsMid n M := by
  have hswap : ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (m + 1),
      claspAlgSearsRightTerm n M i m =
        ∑ i ∈ Finset.range (M + 1), ∑ m ∈ Finset.Ico i (M + 1),
          claspAlgSearsRightTerm n M i m := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (M + 1) _).symm
  rw [Finset.mul_sum, claspAlgSearsMid, Finset.mul_sum,
    Finset.sum_congr rfl fun m _ ↦ claspAlg_searsRight_outer n M m, hswap]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.sum_Ico_eq_sum_range]
  obtain ⟨K, rfl⟩ : ∃ K, M = i + K := ⟨M - i, by have := Finset.mem_range.mp hi; omega⟩
  rw [show i + K + 1 - i = K + 1 by omega]
  exact claspAlg_searsRight_inner n i K

end AJConjecture
