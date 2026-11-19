import Mathlib
import AJConjecture.ClaspAlgSearsMid
import AJConjecture.ClaspAlgQVandermonde
import AJConjecture.ClaspAlgBasic

/-!
# The coefficient-extraction convolution is the Sears middle term (G-KERNEL, crux)

With `P_m = (q;q)_m`, `c = n + M`:
`∑_{i=0}^{M} q^{-(c+1)(n+i)} P_{n+i} P_{n+M-i} / (P_n P_i P_{M-i}) = Mid(n, M)`,
where `Mid(n, M) = ∑_{i=0}^{M} q^{-(c+1)(n+i)} P_{c+1+n+i} P_{n+i} / (P_{M-i} P_i P_{2n+1+i})` is
the library's `claspAlgSearsMid`, already identified with the clasp coefficient
(`claspAlgCoeff_eq_searsMid`). Checked exactly at `t = 3/2` for `n, M ≤ 3`.

Route. After the common factor `q^{-(c+1)(n+i)} P_{n+i}/(P_i P_{M-i})` the two sides differ by
`P_{n+M-i}/P_n = (q^{n+1}; q)_{M-i}` versus `P_{c+1+n+i}/P_{2n+1+i} = (q^{2n+2+i}; q)_M`. Expand
`(q^{2n+2+i}; q)_M` by the `q`-binomial convolution
`(ab; q)_M = ∑_k [M, k]_q b^k (a; q)_k (b; q)_{M-k}` with `a = q^{n+1}`, `b = q^{n+1+i}`
(`geo_qPochhammer_mul_eq_sum`, induction on `M` with the `q`-Pascal rule) and exchange the two
summations. The inner sum over `i` is
`∑_{i=0}^{M} q^{-(A+1)i} P_{A+i} / (P_i P_{M-i}) = q^{-(A+1)M} P_A / P_M`, `A = n + M - k`, the case
`a = 0`, `b = q^{A+1}` of the same convolution, read backwards. The result is the left-hand side
read backwards (`i ↦ M - k`).
-/

noncomputable section

namespace AJConjecture

/-- The `q`-Pascal rule `[j+r+2, j+1] = [j+r+1, j+1] + q^{r+1} [j+r+1, j]` in terms of
`P_m = (q; q)_m`. -/
private theorem geo_qBinom_pascal (j r : ℕ) :
    qPochhammer qParam (j + 1 + r + 1) /
        (qPochhammer qParam (j + 1) * qPochhammer qParam (r + 1)) =
      qPochhammer qParam (j + 1 + r) / (qPochhammer qParam (j + 1) * qPochhammer qParam r) +
        qParam ^ (r + 1) * (qPochhammer qParam (j + 1 + r) /
          (qPochhammer qParam j * qPochhammer qParam (r + 1))) := by
  have hm : qPochhammer qParam (j + 1 + r + 1) =
      qPochhammer qParam (j + 1 + r) * (1 - qParam * qParam ^ (j + 1 + r)) :=
    Finset.prod_range_succ _ _
  have hj : qPochhammer qParam (j + 1) = qPochhammer qParam j * (1 - qParam * qParam ^ j) :=
    Finset.prod_range_succ _ _
  have hr : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
    Finset.prod_range_succ _ _
  have h1 := qPochhammer_qParam_ne_zero j
  have h2 := qPochhammer_qParam_ne_zero r
  have h3 := claspAlg_one_sub_qParam_mul_pow_ne_zero j
  have h4 := claspAlg_one_sub_qParam_mul_pow_ne_zero r
  rw [hm, hj, hr]
  field_simp
  ring

/-- The summand `[M, k]_q b^k (a; q)_k (b; q)_{M-k}` of the `q`-binomial convolution. -/
private def geoConvTerm (a b : RatFunc ℚ) (M k : ℕ) : RatFunc ℚ :=
  qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k)) * b ^ k *
    qPochhammer a k * qPochhammer b (M - k)

/-- Multiplication of a summand by `1 - ab q^M` splits it into the two pieces of the next row. -/
private theorem geoConvTerm_mul (a b : RatFunc ℚ) (M k : ℕ) (hk : k ≤ M) :
    geoConvTerm a b M k * (1 - a * b * qParam ^ M) =
      qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k)) * b ^ k *
          qPochhammer a k * qPochhammer b (M + 1 - k) +
        qParam ^ (M - k) *
          (qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k))) *
          b ^ (k + 1) * qPochhammer a (k + 1) * qPochhammer b (M - k) := by
  have hb : qPochhammer b (M + 1 - k) = qPochhammer b (M - k) * (1 - b * qParam ^ (M - k)) := by
    rw [show M + 1 - k = M - k + 1 by omega]
    exact Finset.prod_range_succ _ _
  have ha : qPochhammer a (k + 1) = qPochhammer a k * (1 - a * qParam ^ k) :=
    Finset.prod_range_succ _ _
  have hq : qParam ^ M = qParam ^ (M - k) * qParam ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hb, ha, hq, geoConvTerm]
  ring

/-- The interior coefficients of the next row (the `q`-Pascal rule). -/
private theorem geoConvTerm_succ_succ (a b : RatFunc ℚ) (M j : ℕ) (hj : j < M) :
    geoConvTerm a b (M + 1) (j + 1) =
      qPochhammer qParam M / (qPochhammer qParam (j + 1) * qPochhammer qParam (M - (j + 1))) *
          b ^ (j + 1) * qPochhammer a (j + 1) * qPochhammer b (M + 1 - (j + 1)) +
        qParam ^ (M - j) *
          (qPochhammer qParam M / (qPochhammer qParam j * qPochhammer qParam (M - j))) *
          b ^ (j + 1) * qPochhammer a (j + 1) * qPochhammer b (M - j) := by
  obtain ⟨r, rfl⟩ : ∃ r, M = j + 1 + r := ⟨M - (j + 1), by omega⟩
  have e1 : j + 1 + r + 1 - (j + 1) = r + 1 := by omega
  have e2 : j + 1 + r - (j + 1) = r := by omega
  have e3 : j + 1 + r - j = r + 1 := by omega
  rw [geoConvTerm, e1, e2, e3, geo_qBinom_pascal j r]
  ring

/-- The `q`-binomial convolution `(ab; q)_M = ∑_k [M, k]_q b^k (a; q)_k (b; q)_{M-k}`. -/
theorem geo_qPochhammer_mul_eq_sum (a b : RatFunc ℚ) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1),
        qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k)) * b ^ k *
          qPochhammer a k * qPochhammer b (M - k) =
      qPochhammer (a * b) M := by
  change ∑ k ∈ Finset.range (M + 1), geoConvTerm a b M k = _
  induction M with
  | zero =>
    simp [geoConvTerm, qPochhammer]
  | succ M ih =>
    have hP0 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
    have hab : qPochhammer (a * b) (M + 1) = qPochhammer (a * b) M * (1 - a * b * qParam ^ M) :=
      Finset.prod_range_succ _ _
    rw [hab, ← ih, Finset.sum_mul,
      Finset.sum_congr rfl fun k hk ↦
        geoConvTerm_mul a b M k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
      Finset.sum_add_distrib, Finset.sum_range_succ', Finset.sum_range_succ,
      Finset.sum_range_succ' (fun k ↦ qPochhammer qParam M /
        (qPochhammer qParam k * qPochhammer qParam (M - k)) * b ^ k *
          qPochhammer a k * qPochhammer b (M + 1 - k)),
      Finset.sum_range_succ (fun k ↦ qParam ^ (M - k) *
          (qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k))) *
          b ^ (k + 1) * qPochhammer a (k + 1) * qPochhammer b (M - k)),
      Finset.sum_congr rfl fun j hj ↦ geoConvTerm_succ_succ a b M j (Finset.mem_range.mp hj),
      Finset.sum_add_distrib]
    simp only [geoConvTerm, Nat.sub_self, Nat.sub_zero, hP0, pow_zero, mul_one, one_mul,
      div_self (qPochhammer_qParam_ne_zero _)]
    ring

/-- The inner sum `∑_{i=0}^{M} q^{-(A+1)i} P_{A+i} / (P_i P_{M-i}) = q^{-(A+1)M} P_A / P_M`: the
convolution at `a = 0`, `b = q^{A+1}`, read backwards. -/
private theorem geo_conv_innerSum (A M : ℕ) :
    ∑ i ∈ Finset.range (M + 1),
        qParam ^ (-(((A + 1) * i : ℕ) : ℤ)) * qPochhammer qParam (A + i) /
          (qPochhammer qParam i * qPochhammer qParam (M - i)) =
      qParam ^ (-(((A + 1) * M : ℕ) : ℤ)) * qPochhammer qParam A / qPochhammer qParam M := by
  have h0 : ∀ k, qPochhammer 0 k = 1 := fun k ↦ by simp [qPochhammer]
  have hE := geo_qPochhammer_mul_eq_sum 0 (qParam ^ (A + 1)) M
  rw [zero_mul, h0, ← Finset.sum_range_reflect] at hE
  have hterm : ∀ i ∈ Finset.range (M + 1),
      qParam ^ (-(((A + 1) * i : ℕ) : ℤ)) * qPochhammer qParam (A + i) /
          (qPochhammer qParam i * qPochhammer qParam (M - i)) =
        qParam ^ (-(((A + 1) * M : ℕ) : ℤ)) * qPochhammer qParam A / qPochhammer qParam M *
          (qPochhammer qParam M /
              (qPochhammer qParam (M + 1 - 1 - i) *
                qPochhammer qParam (M - (M + 1 - 1 - i))) *
            (qParam ^ (A + 1)) ^ (M + 1 - 1 - i) * qPochhammer 0 (M + 1 - 1 - i) *
            qPochhammer (qParam ^ (A + 1)) (M - (M + 1 - 1 - i))) := by
    intro i hi
    have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : M + 1 - 1 - i = M - i := by omega
    have e2 : M - (M - i) = i := by omega
    have hpow : qParam ^ (-(((A + 1) * i : ℕ) : ℤ)) =
        qParam ^ (-(((A + 1) * M : ℕ) : ℤ)) * (qParam ^ (A + 1)) ^ (M - i) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ qParam_ne_zero]
      congr 1
      push_cast [Nat.cast_sub hi']
      ring
    rw [e1, e2, h0, hpow, ← claspAlg_qPochhammer_mul_shift A i]
    have := qPochhammer_qParam_ne_zero A
    have := qPochhammer_qParam_ne_zero M
    have := qPochhammer_qParam_ne_zero i
    have := qPochhammer_qParam_ne_zero (M - i)
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hE, mul_one]

/-- One summand of the Sears middle term, expanded by the `q`-binomial convolution with
`a = q^{n+1}`, `b = q^{n+1+i}`. -/
private theorem geo_searsMid_term_expand (n M i : ℕ) :
    qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ)) * qPochhammer qParam (2 * n + M + 1 + i) *
        qPochhammer qParam (n + i) /
        (qPochhammer qParam (M - i) * qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i)) =
      ∑ k ∈ Finset.range (M + 1),
        qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ) + (((n + i + 1) * k : ℕ) : ℤ)) *
          (qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k))) *
          (qPochhammer qParam (n + k) / qPochhammer qParam n) *
          (qPochhammer qParam (n + i + (M - k)) /
            (qPochhammer qParam (M - i) * qPochhammer qParam i)) := by
  have hE := geo_qPochhammer_mul_eq_sum (qParam ^ (n + 1)) (qParam ^ (n + i + 1)) M
  have hab : qParam ^ (n + 1) * qParam ^ (n + i + 1) = qParam ^ (2 * n + 1 + i + 1) := by
    rw [← pow_add]
    congr 1
    ring
  have hP : qPochhammer qParam (2 * n + M + 1 + i) =
      qPochhammer qParam (2 * n + 1 + i) * qPochhammer (qParam ^ (2 * n + 1 + i + 1)) M := by
    rw [claspAlg_qPochhammer_mul_shift]
    congr 1
    ring
  rw [hab] at hE
  have h1 := qPochhammer_qParam_ne_zero (2 * n + 1 + i)
  have hL : qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ)) *
        qPochhammer qParam (2 * n + M + 1 + i) * qPochhammer qParam (n + i) /
        (qPochhammer qParam (M - i) * qPochhammer qParam i *
          qPochhammer qParam (2 * n + 1 + i)) =
      qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ)) * qPochhammer qParam (n + i) /
          (qPochhammer qParam (M - i) * qPochhammer qParam i) *
        qPochhammer (qParam ^ (2 * n + 1 + i + 1)) M := by
    rw [hP]
    field_simp
  rw [hL, ← hE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [zpow_add₀ qParam_ne_zero, zpow_natCast, pow_mul, ← claspAlg_qPochhammer_mul_shift n k,
    ← claspAlg_qPochhammer_mul_shift (n + i) (M - k)]
  have := qPochhammer_qParam_ne_zero n
  have := qPochhammer_qParam_ne_zero i
  have := qPochhammer_qParam_ne_zero (M - i)
  field_simp

/-- The coefficient-extraction convolution equals the Sears middle term. -/
theorem geo_claspConv_eq_searsMid (n M : ℕ) :
    ∑ i ∈ Finset.range (M + 1),
        qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ)) * qPochhammer qParam (n + i) *
          qPochhammer qParam (n + M - i) /
          (qPochhammer qParam n * qPochhammer qParam i * qPochhammer qParam (M - i)) =
      claspAlgSearsMid n M := by
  rw [claspAlgSearsMid, Finset.sum_congr rfl fun i _ ↦ geo_searsMid_term_expand n M i,
    Finset.sum_comm, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hinner := geo_conv_innerSum (n + M - k) M
  have hterm : ∀ i ∈ Finset.range (M + 1),
      qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ) + (((n + i + 1) * k : ℕ) : ℤ)) *
          (qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k))) *
          (qPochhammer qParam (n + k) / qPochhammer qParam n) *
          (qPochhammer qParam (n + i + (M - k)) /
            (qPochhammer qParam (M - i) * qPochhammer qParam i)) =
        qParam ^ (-(((n + M + 1) * n : ℕ) : ℤ) + (((n + 1) * k : ℕ) : ℤ)) *
          (qPochhammer qParam M / (qPochhammer qParam k * qPochhammer qParam (M - k))) *
          (qPochhammer qParam (n + k) / qPochhammer qParam n) *
          (qParam ^ (-(((n + M - k + 1) * i : ℕ) : ℤ)) * qPochhammer qParam (n + M - k + i) /
            (qPochhammer qParam i * qPochhammer qParam (M - i))) := by
    intro i _
    have e1 : n + i + (M - k) = n + M - k + i := by omega
    have hpow : qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ) + (((n + i + 1) * k : ℕ) : ℤ)) =
        qParam ^ (-(((n + M + 1) * n : ℕ) : ℤ) + (((n + 1) * k : ℕ) : ℤ)) *
          qParam ^ (-(((n + M - k + 1) * i : ℕ) : ℤ)) := by
      rw [← zpow_add₀ qParam_ne_zero]
      congr 1
      push_cast [Nat.cast_sub (le_add_left hk')]
      ring
    rw [e1, hpow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hinner]
  have e2 : M + 1 - 1 - k = M - k := by omega
  have e3 : n + (M - k) = n + M - k := by omega
  have e4 : n + M - (M - k) = n + k := by omega
  have e5 : M - (M - k) = k := by omega
  have hpow : qParam ^ (-(((n + M + 1) * (n + (M - k)) : ℕ) : ℤ)) =
      qParam ^ (-(((n + M + 1) * n : ℕ) : ℤ) + (((n + 1) * k : ℕ) : ℤ)) *
        qParam ^ (-(((n + M - k + 1) * M : ℕ) : ℤ)) := by
    rw [← zpow_add₀ qParam_ne_zero]
    congr 1
    push_cast [Nat.cast_sub hk', Nat.cast_sub (le_add_left hk')]
    ring
  rw [e2, e4, e5, hpow, e3]
  have := qPochhammer_qParam_ne_zero n
  have := qPochhammer_qParam_ne_zero k
  have := qPochhammer_qParam_ne_zero M
  have := qPochhammer_qParam_ne_zero (M - k)
  field_simp

end AJConjecture
