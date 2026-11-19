import Mathlib
import AJConjecture.ClaspAlgSearsRight
import AJConjecture.ClaspAlgBasic
import AJConjecture.ClaspAlgQVandermonde
import AJConjecture.ClaspAlgQVandermondeDual
import AJConjecture.ClaspAlgSearsMid

/-!
# The Sears transformation, turnback side

With `P_m = (q; q)_m` and `c = n + M`:
`P_M P_(2n+M+1) ∑_{m=0}^{M} q^((n+m)² - 2c(n+m)) P_(n+m) / (P_(M-m)² P_m P_(2n+1+m)) = q^c Mid(n, M)`.

Route: for `m ≤ M` expand, by the dual `q`-Chu–Vandermonde sum with `x = q^(2n+M+2)`,
`y = q^(2n+2)`,
`(-1)^m q^(m(m-1)/2) P_M P_(2n+1+M) / (P_(M-m) P_m P_(2n+1+m)) =
∑_{i=0}^{m} (-1)^i q^(i(i-1)/2 + M(m-i)) P_(2n+1+M+i) / (P_i P_(m-i) P_(2n+1+i))`;
exchange the two summations; the inner sum over `m = i + l` is
`∑_{l=0}^{M-i} (-1)^l q^(l(l+1)/2 - (M-i) l) P_(n+i+l) / (P_l P_(M-i-l)) = q^((n+i+1)(M-i)) P_(n+i) / P_(M-i)`,
the case `C = 0`, `b = q^(n+i+1)` of the `q`-Chu–Vandermonde sum.

The two sums are `claspAlg_qVandermonde_dual` and `claspAlg_qVandermonde` (stated with natural
exponents `q^(i(i-1)/2)`, `q^((m-k)(m-k-1)/2)`); `(q^(a+1); q)_k = P_(a+k) / P_a` is
`claspAlg_qPochhammer_mul_shift`.
-/

namespace AJConjecture

/-- Twice the triangular number `k(k-1)/2`, as an integer. -/
private theorem claspAlg_searsLeft_two_mul_tri (k : ℕ) :
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

/-- The case `C = 0`, `b = q^(a+1)` of the `q`-Chu–Vandermonde sum, in terms of `(q; q)_m`. -/
private theorem claspAlg_searsLeft_innerSum (a K : ℕ) :
    ∑ l ∈ Finset.range (K + 1),
        (-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (a + l) /
          (qPochhammer qParam l * qPochhammer qParam (K - l)) =
      qParam ^ (K * (K - 1) / 2) * qParam ^ ((a + 1) * K) * qPochhammer qParam a /
        qPochhammer qParam K := by
  have hPa := qPochhammer_qParam_ne_zero a
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

/-- The product of the dual `q`-Chu–Vandermonde sum at `x = q^(A+M+1)`, `y = q^(A+1)`. -/
private theorem claspAlg_searsLeft_prod (A M m : ℕ) (hm : m ≤ M) :
    (∏ s ∈ Finset.range m, (qParam ^ (A + M + 1) - qParam ^ (A + 1) * qParam ^ s)) *
        qPochhammer qParam (M - m) =
      (-1) ^ m * qParam ^ ((A + 1) * m) * qParam ^ (m * (m - 1) / 2) * qPochhammer qParam M := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨r, rfl⟩ : ∃ r, M = m + 1 + r := ⟨M - (m + 1), by omega⟩
    have ih' := ih (by omega)
    have e1 : m + 1 + r - m = r + 1 := by omega
    have e2 : m + 1 + r - (m + 1) = r := by omega
    have hP : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
      Finset.prod_range_succ _ _
    have hT : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := Nat.triangle_succ m
    have hfac : qParam ^ (A + (m + 1 + r) + 1) - qParam ^ (A + 1) * qParam ^ m =
        -(qParam ^ (A + 1) * qParam ^ m) * (1 - qParam * qParam ^ r) := by
      ring
    rw [e1, hP] at ih'
    rw [Finset.prod_range_succ, e2, hT, hfac]
    linear_combination (-(qParam ^ (A + 1) * qParam ^ m)) * ih'

/-- The expansion of `1 / (P_(M-m) P_m P_(A+m))` by the dual `q`-Chu–Vandermonde sum. -/
private theorem claspAlg_searsLeft_expand (A M m : ℕ) (hm : m ≤ M) :
    ∑ i ∈ Finset.range (m + 1),
        (-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ (M * (m - i)) *
          qPochhammer qParam (A + M + i) /
          (qPochhammer qParam i * qPochhammer qParam (m - i) * qPochhammer qParam (A + i)) =
      (-1) ^ m * qParam ^ (m * (m - 1) / 2) * qPochhammer qParam M * qPochhammer qParam (A + M) /
        (qPochhammer qParam (M - m) * qPochhammer qParam m * qPochhammer qParam (A + m)) := by
  have hV := claspAlg_qVandermonde_dual m (qParam ^ (A + M + 1)) (qParam ^ (A + 1))
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (-1) ^ i * qParam ^ (i * (i - 1) / 2) *
          (qPochhammer qParam m / (qPochhammer qParam i * qPochhammer qParam (m - i))) *
          qPochhammer (qParam ^ (A + 1) * qParam ^ i) (m - i) * (qParam ^ (A + 1)) ^ i *
          (qPochhammer (qParam ^ (A + M + 1)) i * (qParam ^ (A + M + 1)) ^ (m - i)) *
          qPochhammer qParam (A + M) =
        qPochhammer qParam m * qPochhammer qParam (A + m) * qParam ^ ((A + 1) * m) *
          ((-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ (M * (m - i)) *
            qPochhammer qParam (A + M + i) /
            (qPochhammer qParam i * qPochhammer qParam (m - i) * qPochhammer qParam (A + i))) := by
    intro i hi
    obtain ⟨d, rfl⟩ : ∃ d, m = i + d := ⟨m - i, by have := Finset.mem_range.mp hi; omega⟩
    have e : i + d - i = d := by omega
    have hW : qPochhammer qParam (A + i) * qPochhammer (qParam ^ (A + 1) * qParam ^ i) d =
        qPochhammer qParam (A + (i + d)) := by
      have h := claspAlg_qPochhammer_mul_shift (A + i) d
      rw [show qParam ^ (A + i + 1) = qParam ^ (A + 1) * qParam ^ i by ring,
        Nat.add_assoc A i d] at h
      exact h
    have hx : qPochhammer qParam (A + M) * qPochhammer (qParam ^ (A + M + 1)) i =
        qPochhammer qParam (A + M + i) := claspAlg_qPochhammer_mul_shift (A + M) i
    have h1 := qPochhammer_qParam_ne_zero (A + i)
    rw [e, ← hW, ← hx]
    field_simp
    ring
  have hsum : (∏ s ∈ Finset.range m, (qParam ^ (A + M + 1) - qParam ^ (A + 1) * qParam ^ s)) *
      qPochhammer qParam (A + M) =
        qPochhammer qParam m * qPochhammer qParam (A + m) * qParam ^ ((A + 1) * m) *
          ∑ i ∈ Finset.range (m + 1),
            (-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ (M * (m - i)) *
              qPochhammer qParam (A + M + i) /
              (qPochhammer qParam i * qPochhammer qParam (m - i) * qPochhammer qParam (A + i)) := by
    rw [← hV, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hprod := claspAlg_searsLeft_prod A M m hm
  have hQ : qParam ^ ((A + 1) * m) ≠ 0 := pow_ne_zero _ qParam_ne_zero
  have hne : qPochhammer qParam (M - m) * qPochhammer qParam m * qPochhammer qParam (A + m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _))
      (qPochhammer_qParam_ne_zero _)
  rw [eq_div_iff hne]
  refine mul_left_cancel₀ hQ ?_
  linear_combination (-qPochhammer qParam (M - m)) * hsum + qPochhammer qParam (A + M) * hprod

/-- The double summand: the term of index `i` of the expansion of the `m`-th term of the turnback
side. -/
private noncomputable def claspAlgSearsLeftTerm (n M i m : ℕ) : RatFunc ℚ :=
  qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
      (qPochhammer qParam (n + m) / qPochhammer qParam (M - m)) *
      ((-1) ^ m * (qParam ^ (m * (m - 1) / 2))⁻¹) *
    ((-1) ^ i * qParam ^ (i * (i - 1) / 2) * qParam ^ (M * (m - i)) *
      qPochhammer qParam (2 * n + 1 + M + i) /
      (qPochhammer qParam i * qPochhammer qParam (m - i) * qPochhammer qParam (2 * n + 1 + i)))

/-- The rational identity behind the expansion of one term of the turnback side. -/
private theorem claspAlg_searsLeft_outer_algebra (E Pn Pd PM PA Pm PAm s T Tinv : RatFunc ℚ)
    (hs : s * s = 1) (hT : Tinv * T = 1) :
    PM * PA * (E * Pn / (Pd ^ 2 * Pm * PAm)) =
      E * (Pn / Pd) * (s * Tinv) * (s * T * PM * PA / (Pd * Pm * PAm)) := by
  have key : E * (Pn / Pd) * (s * Tinv) * (s * T * PM * PA / (Pd * Pm * PAm)) =
      (s * s) * (Tinv * T) * (PM * PA * (E * Pn / (Pd ^ 2 * Pm * PAm))) := by
    ring
  rw [key, hs, hT]
  ring

/-- One term of the turnback side is a sum of double summands. -/
private theorem claspAlg_searsLeft_outer (n M m : ℕ) (hm : m ≤ M) :
    qPochhammer qParam M * qPochhammer qParam (2 * n + M + 1) *
        (qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
          qPochhammer qParam (n + m) /
          (qPochhammer qParam (M - m) ^ 2 * qPochhammer qParam m *
            qPochhammer qParam (2 * n + 1 + m))) =
      ∑ i ∈ Finset.range (m + 1), claspAlgSearsLeftTerm n M i m := by
  have hs : (-1 : RatFunc ℚ) ^ m * (-1) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hT : (qParam ^ (m * (m - 1) / 2))⁻¹ * qParam ^ (m * (m - 1) / 2) = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ qParam_ne_zero)
  unfold claspAlgSearsLeftTerm
  rw [← Finset.mul_sum, claspAlg_searsLeft_expand (2 * n + 1) M m hm,
    show 2 * n + M + 1 = 2 * n + 1 + M by omega]
  exact claspAlg_searsLeft_outer_algebra _ _ _ _ _ _ _ _ _ _ hs hT

/-- The powers of `q` in a double summand, with `M = i + l + r`. -/
private theorem claspAlg_searsLeft_pow_term (n i l r : ℕ) :
    qParam ^ (((n + (i + l) : ℕ) : ℤ) ^ 2 -
          2 * ((n + (i + l + r) : ℕ) : ℤ) * ((n + (i + l) : ℕ) : ℤ)) *
        (qParam ^ ((i + l) * (i + l - 1) / 2))⁻¹ * qParam ^ (i * (i - 1) / 2) *
        qParam ^ ((i + l + r) * l) =
      qParam ^ (((n + i : ℕ) : ℤ) ^ 2 - 2 * ((n + (i + l + r) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) -
          (((l + r) * (l + r - 1) / 2 : ℕ) : ℤ)) * qParam ^ (r * (r - 1) / 2) := by
  have hq := qParam_ne_zero
  have h1 := claspAlg_searsLeft_two_mul_tri (i + l)
  have h2 := claspAlg_searsLeft_two_mul_tri i
  have h3 := claspAlg_searsLeft_two_mul_tri (l + r)
  have h4 := claspAlg_searsLeft_two_mul_tri r
  rw [← zpow_natCast qParam ((i + l) * (i + l - 1) / 2), ← zpow_natCast qParam (i * (i - 1) / 2),
    ← zpow_natCast qParam ((i + l + r) * l), ← zpow_natCast qParam (r * (r - 1) / 2), ← zpow_neg,
    ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul] at h1 h3 ⊢
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  linear_combination -h1 + h2 + h3 - h4

/-- The rational identity that puts a double summand in the form of a term of the inner sum. -/
private theorem claspAlg_searsLeft_term_algebra
    (E Til Ti QMl Et Tr si sl Pnil Pr PAMi Pi Pl PAi : RatFunc ℚ)
    (hs : si * si = 1) (hpow : E * Til⁻¹ * Ti * QMl = Et * Tr) :
    E * (Pnil / Pr) * (si * sl * Til⁻¹) * (si * Ti * QMl * PAMi / (Pi * Pl * PAi)) =
      Et * PAMi / (Pi * PAi) * (sl * Tr * Pnil / (Pl * Pr)) := by
  have key : E * (Pnil / Pr) * (si * sl * Til⁻¹) * (si * Ti * QMl * PAMi / (Pi * Pl * PAi)) =
      (si * si) * (E * Til⁻¹ * Ti * QMl) * (sl * Pnil * PAMi / (Pr * Pi * Pl * PAi)) := by
    ring
  rw [key, hs, hpow]
  ring

/-- A double summand with `m = i + l`, `M = i + l + r`, as a term of the inner sum. -/
private theorem claspAlgSearsLeftTerm_eq (n i l r : ℕ) :
    claspAlgSearsLeftTerm n (i + l + r) i (i + l) =
      qParam ^ (((n + i : ℕ) : ℤ) ^ 2 - 2 * ((n + (i + l + r) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) -
            (((l + r) * (l + r - 1) / 2 : ℕ) : ℤ)) *
          qPochhammer qParam (2 * n + 1 + (i + l + r) + i) /
          (qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i)) *
        ((-1) ^ l * qParam ^ (r * (r - 1) / 2) * qPochhammer qParam (n + (i + l)) /
          (qPochhammer qParam l * qPochhammer qParam r)) := by
  have hs : (-1 : RatFunc ℚ) ^ i * (-1) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  unfold claspAlgSearsLeftTerm
  rw [show i + l + r - (i + l) = r by omega, show i + l - i = l by omega,
    pow_add (-1 : RatFunc ℚ) i l]
  exact claspAlg_searsLeft_term_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
    (claspAlg_searsLeft_pow_term n i l r)

/-- The powers of `q` after the inner summation, with `M = i + K`. -/
private theorem claspAlg_searsLeft_pow_final (n i K : ℕ) :
    qParam ^ (((n + i : ℕ) : ℤ) ^ 2 - 2 * ((n + (i + K) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) -
          ((K * (K - 1) / 2 : ℕ) : ℤ)) *
        (qParam ^ (K * (K - 1) / 2) * qParam ^ ((n + i + 1) * K)) =
      qParam ^ (n + (i + K)) * qParam ^ (-(((n + (i + K) + 1) * (n + i) : ℕ) : ℤ)) := by
  have hq := qParam_ne_zero
  rw [← zpow_natCast qParam (K * (K - 1) / 2), ← zpow_natCast qParam ((n + i + 1) * K),
    ← zpow_natCast qParam (n + (i + K)), ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- The inner sum of the double sum is a term of the middle sum. -/
private theorem claspAlg_searsLeft_inner (n i K : ℕ) :
    ∑ l ∈ Finset.range (K + 1), claspAlgSearsLeftTerm n (i + K) i (i + l) =
      qParam ^ (n + (i + K)) *
        (qParam ^ (-(((n + (i + K) + 1) * (n + i) : ℕ) : ℤ)) *
          qPochhammer qParam (2 * n + (i + K) + 1 + i) * qPochhammer qParam (n + i) /
          (qPochhammer qParam (i + K - i) * qPochhammer qParam i *
            qPochhammer qParam (2 * n + 1 + i))) := by
  have hterm : ∀ l ∈ Finset.range (K + 1), claspAlgSearsLeftTerm n (i + K) i (i + l) =
      qParam ^ (((n + i : ℕ) : ℤ) ^ 2 - 2 * ((n + (i + K) : ℕ) : ℤ) * ((n + i : ℕ) : ℤ) -
            ((K * (K - 1) / 2 : ℕ) : ℤ)) *
          qPochhammer qParam (2 * n + 1 + (i + K) + i) /
          (qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i)) *
        ((-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (n + i + l) /
          (qPochhammer qParam l * qPochhammer qParam (K - l))) := by
    intro l hl
    obtain ⟨r, rfl⟩ : ∃ r, K = l + r := ⟨K - l, by have := Finset.mem_range.mp hl; omega⟩
    rw [show l + r - l = r by omega, show i + (l + r) = i + l + r by omega,
      show n + i + l = n + (i + l) by omega]
    exact claspAlgSearsLeftTerm_eq n i l r
  have hf := claspAlg_searsLeft_pow_final n i K
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, claspAlg_searsLeft_innerSum (n + i) K,
    show i + K - i = K by omega, show 2 * n + (i + K) + 1 + i = 2 * n + 1 + (i + K) + i by omega]
  linear_combination (qPochhammer qParam (2 * n + 1 + (i + K) + i) * qPochhammer qParam (n + i) /
    (qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i) * qPochhammer qParam K)) * hf

/-- The turnback side of the clasp identity is the middle term of the Sears transformation. -/
theorem claspAlg_searsLeft (n M : ℕ) :
    qPochhammer qParam M * qPochhammer qParam (2 * n + M + 1) *
        ∑ m ∈ Finset.range (M + 1),
          qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
            qPochhammer qParam (n + m) /
            (qPochhammer qParam (M - m) ^ 2 * qPochhammer qParam m *
              qPochhammer qParam (2 * n + 1 + m)) =
      qParam ^ (n + M) * claspAlgSearsMid n M := by
  have hswap : ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (m + 1),
      claspAlgSearsLeftTerm n M i m =
        ∑ i ∈ Finset.range (M + 1), ∑ m ∈ Finset.Ico i (M + 1),
          claspAlgSearsLeftTerm n M i m := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (M + 1) _).symm
  rw [Finset.mul_sum, claspAlgSearsMid, Finset.mul_sum,
    Finset.sum_congr rfl fun m hm ↦
      claspAlg_searsLeft_outer n M m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), hswap]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.sum_Ico_eq_sum_range]
  obtain ⟨K, rfl⟩ : ∃ K, M = i + K := ⟨M - i, by have := Finset.mem_range.mp hi; omega⟩
  rw [show i + K + 1 - i = K + 1 by omega]
  exact claspAlg_searsLeft_inner n i K

end AJConjecture
