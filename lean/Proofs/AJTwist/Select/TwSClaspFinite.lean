import Mathlib
import AJConjecture.ClaspAlgClaspEigenCoeff
import AJConjecture.QAlgQBinomial
import AJHandoff.TorusQuantum.PairQFormulaBasic

/-!
# The clasp form of the finite transform

Source: eq. (claspfinite) of `transfer.tex` and eq. (coefficient-kernel) of `selection.tex`
(revision 5). For an input `w` and `θ ∈ {0, 1}`,
`Y_{θ,N}(w) = (1 - q) / (1 - X) ∑_{i + n < N} X^i (-1)^(θ n) q^(θ n(n+1)/2) w_n
  (q^(i+1); q)_n (X q^(-i-n); q)_n / (q; q)_n` at `X = q^N`.

* `twsY θ w N` is `Y_{θ,N}(w)` (`θ = false`: `θ = 0`; `θ = true`: `θ = 1`).
* `tws_claspAlgCoeff_eq_twsZheng` (crux): `∑_{j=n}^{N-1} C_j(N) K_{j,n} = β_{N,n}` with Zheng's
  coefficient `β_{N,n}` of eq. (claspfinite). The paper obtains the equivalence of the two forms
  from the literature (Zheng's and Habiro's formulas for the Whitehead link); here it is a
  terminating `q`-series identity. By `claspAlgCoeff_eq_searsMid` it is equivalent to, with
  `P_k = (q; q)_k`, `M = N - 1 - n`,
  `∑_{i=0}^{M} q^(-N i) P_(n+i) P_(M+n-i) / (P_i P_(M-i) P_n) =
   ∑_{i=0}^{M} q^(-N i) P_(2n+M+1+i) P_(n+i) / (P_(M-i) P_i P_(2n+1+i))`.
* `tws_reducedFormula_eq_twsY`: the triangular transform of the library (eq. (universalbailey))
  is the clasp form, `F_N = q^(N-1) Y_{0,N}(u)` for every input `u`
  (`pairQ_quantumInt_mul_reducedFormula`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The factor `(-1)^(θ n) q^(θ n(n+1)/2)`. -/
def twsTheta (θ : Bool) (n : ℕ) : RatFunc ℚ :=
  if θ then (-1) ^ n * qParam ^ (n * (n + 1) / 2) else 1

/-- The finite kernel sum `Y_{θ,N}(w)` of eq. (coefficient-kernel), evaluated at `X = q^N`. -/
def twsY (θ : Bool) (w : ℕ → RatFunc ℚ) (N : ℕ) : RatFunc ℚ :=
  (1 - qParam) / (1 - qParam ^ N) *
    ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
      qParam ^ (N * i) * (twsTheta θ n * w n) *
        (qPochhammer (qParam ^ (i + 1)) n * qPochhammer (qParam ^ (N - i - n)) n /
          qPochhammer qParam n)

/-- Zheng's coefficient `β_{N,n}` of eq. (claspfinite), with the `i`-sum reversed: the coefficient
of `w_n` in `q^(N-1) Y_{0,N}(w)`. -/
def twsZheng (N n : ℕ) : RatFunc ℚ :=
  qParam ^ (N - 1) * ((1 - qParam) / (1 - qParam ^ N)) *
    ∑ i ∈ Finset.range (N - n), qParam ^ (N * i) *
      (qPochhammer (qParam ^ (i + 1)) n * qPochhammer (qParam ^ (N - i - n)) n /
        qPochhammer qParam n)

/-- Twice the triangular number `k(k-1)/2`, as an integer. -/
private theorem two_mul_tri_twsClaspFinite (k : ℕ) :
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

/-- `(q^(-M); q)_m q^(M m) P_(M-m) = (-1)^m q^(m(m-1)/2) P_M` for `m ≤ M`. -/
private theorem qPochhammer_inv_pow_twsClaspFinite (M m : ℕ) (hm : m ≤ M) :
    qPochhammer (qParam ^ M)⁻¹ m * (qParam ^ M) ^ m * qPochhammer qParam (M - m) =
      (-1) ^ m * qParam ^ (m * (m - 1) / 2) * qPochhammer qParam M := by
  induction m with
  | zero => simp [qPochhammer]
  | succ m ih =>
    obtain ⟨r, rfl⟩ : ∃ r, M = m + 1 + r := ⟨M - (m + 1), by omega⟩
    have ih' := ih (by omega)
    have e1 : m + 1 + r - m = r + 1 := by omega
    have e2 : m + 1 + r - (m + 1) = r := by omega
    have hP : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
      Finset.prod_range_succ _ _
    have hZ : qPochhammer (qParam ^ (m + 1 + r))⁻¹ (m + 1) =
        qPochhammer (qParam ^ (m + 1 + r))⁻¹ m * (1 - (qParam ^ (m + 1 + r))⁻¹ * qParam ^ m) :=
      Finset.prod_range_succ _ _
    have hT : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := Nat.triangle_succ m
    have hne : qParam ^ (m + 1 + r) ≠ 0 := pow_ne_zero _ qParam_ne_zero
    have hfac : (1 - (qParam ^ (m + 1 + r))⁻¹ * qParam ^ m) * qParam ^ (m + 1 + r) =
        -qParam ^ m * (1 - qParam * qParam ^ r) := by
      rw [sub_mul, mul_right_comm, inv_mul_cancel₀ hne]
      ring
    rw [e1, hP] at ih'
    rw [hZ, e2, hT, pow_succ (qParam ^ (m + 1 + r)) m]
    linear_combination (-qParam ^ m) * ih' +
      (qPochhammer (qParam ^ (m + 1 + r))⁻¹ m * (qParam ^ (m + 1 + r)) ^ m *
        qPochhammer qParam r) * hfac

/-- The expansion of `1 / (P_m P_(M-m))` by the `q`-binomial theorem at `z = q^(-M)`. -/
private theorem sum_qBinomial_inv_pow_twsClaspFinite (M m : ℕ) (hm : m ≤ M) :
    ∑ j ∈ Finset.range (m + 1),
        (-1) ^ j * qParam ^ (j * (j - 1) / 2) * ((qParam ^ M)⁻¹) ^ j /
          (qPochhammer qParam j * qPochhammer qParam (m - j)) =
      (-1) ^ m * qParam ^ (m * (m - 1) / 2) * ((qParam ^ M)⁻¹) ^ m * qPochhammer qParam M /
        (qPochhammer qParam m * qPochhammer qParam (M - m)) := by
  have hB := sum_qBinomial_eq_qPochhammer m (qParam ^ M)⁻¹
  have hP := qPochhammer_inv_pow_twsClaspFinite M m hm
  have hsum : qPochhammer qParam m * ∑ j ∈ Finset.range (m + 1),
      (-1) ^ j * qParam ^ (j * (j - 1) / 2) * ((qParam ^ M)⁻¹) ^ j /
        (qPochhammer qParam j * qPochhammer qParam (m - j)) = qPochhammer (qParam ^ M)⁻¹ m := by
    rw [← hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hz : ((qParam ^ M)⁻¹) ^ m * (qParam ^ M) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ qParam_ne_zero), one_pow]
  have hne : qPochhammer qParam m * qPochhammer qParam (M - m) ≠ 0 :=
    mul_ne_zero (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _)
  rw [eq_div_iff hne]
  linear_combination qPochhammer qParam (M - m) * hsum + ((qParam ^ M)⁻¹) ^ m * hP -
    (qPochhammer (qParam ^ M)⁻¹ m * qPochhammer qParam (M - m)) * hz

/-- The double summand: the term of index `j` of the expansion of the `m`-th term of the turnback
side of the Sears transformation by the `q`-binomial theorem. -/
private def doubleTerm_twsClaspFinite (n M j m : ℕ) : RatFunc ℚ :=
  qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
      (qPochhammer qParam (n + m) /
        (qPochhammer qParam (M - m) * qPochhammer qParam (2 * n + 1 + m))) *
      ((-1) ^ m * (qParam ^ (m * (m - 1) / 2))⁻¹ * (qParam ^ M) ^ m) *
    ((-1) ^ j * qParam ^ (j * (j - 1) / 2) * ((qParam ^ M)⁻¹) ^ j /
      (qPochhammer qParam j * qPochhammer qParam (m - j)))

/-- The rational identity behind the expansion of a term of the turnback side. -/
private theorem outer_algebra_twsClaspFinite (E Pnm Pd PM Pm PAm s T Tinv Qm zm : RatFunc ℚ)
    (hs : s * s = 1) (hT : Tinv * T = 1) (hz : zm * Qm = 1) :
    PM * (E * Pnm / (Pd ^ 2 * Pm * PAm)) =
      E * (Pnm / (Pd * PAm)) * (s * Tinv * Qm) * (s * T * zm * PM / (Pm * Pd)) := by
  have key : E * (Pnm / (Pd * PAm)) * (s * Tinv * Qm) * (s * T * zm * PM / (Pm * Pd)) =
      (s * s) * (Tinv * T) * (zm * Qm) * (PM * (E * Pnm / (Pd ^ 2 * Pm * PAm))) := by
    ring
  rw [key, hs, hT, hz]
  ring

/-- One term of the turnback side is a sum of double summands. -/
private theorem doubleTerm_outer_twsClaspFinite (n M m : ℕ) (hm : m ≤ M) :
    qPochhammer qParam M *
        (qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
          qPochhammer qParam (n + m) /
          (qPochhammer qParam (M - m) ^ 2 * qPochhammer qParam m *
            qPochhammer qParam (2 * n + 1 + m))) =
      ∑ j ∈ Finset.range (m + 1), doubleTerm_twsClaspFinite n M j m := by
  have hs : (-1 : RatFunc ℚ) ^ m * (-1) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hT : (qParam ^ (m * (m - 1) / 2))⁻¹ * qParam ^ (m * (m - 1) / 2) = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ qParam_ne_zero)
  have hz : ((qParam ^ M)⁻¹) ^ m * (qParam ^ M) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ qParam_ne_zero), one_pow]
  unfold doubleTerm_twsClaspFinite
  rw [← Finset.mul_sum, sum_qBinomial_inv_pow_twsClaspFinite M m hm]
  exact outer_algebra_twsClaspFinite _ _ _ _ _ _ _ _ _ _ _ hs hT hz

/-- The powers of `q` in a double summand, with `M = j + l + r`. -/
private theorem pow_term_twsClaspFinite (n j l r : ℕ) :
    qParam ^ (((n + (j + l) : ℕ) : ℤ) ^ 2 -
          2 * ((n + (j + l + r) : ℕ) : ℤ) * ((n + (j + l) : ℕ) : ℤ)) *
        (qParam ^ ((j + l) * (j + l - 1) / 2))⁻¹ * (qParam ^ (j + l + r)) ^ (j + l) *
        qParam ^ (j * (j - 1) / 2) * ((qParam ^ (j + l + r))⁻¹) ^ j =
      qParam ^ (((n + j : ℕ) : ℤ) ^ 2 - 2 * ((n + (j + l + r) : ℕ) : ℤ) * ((n + j : ℕ) : ℤ) -
          (((l + r) * (l + r - 1) / 2 : ℕ) : ℤ)) * qParam ^ (r * (r - 1) / 2) := by
  have hq := qParam_ne_zero
  have h1 := two_mul_tri_twsClaspFinite (j + l)
  have h2 := two_mul_tri_twsClaspFinite j
  have h3 := two_mul_tri_twsClaspFinite (l + r)
  have h4 := two_mul_tri_twsClaspFinite r
  rw [inv_pow, ← pow_mul, ← pow_mul, ← zpow_natCast qParam ((j + l) * (j + l - 1) / 2),
    ← zpow_natCast qParam (j * (j - 1) / 2), ← zpow_natCast qParam ((j + l + r) * (j + l)),
    ← zpow_natCast qParam ((j + l + r) * j), ← zpow_natCast qParam (r * (r - 1) / 2), ← zpow_neg,
    ← zpow_neg, ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul] at h1 h3 ⊢
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  linear_combination -h1 + h2 + h3 - h4

/-- The rational identity that puts a double summand in the form of a term of the inner sum. -/
private theorem term_algebra_twsClaspFinite
    (E Tjl QMm Tj zj Et Tr sj sl Pnm Pr PAm Pj Pl : RatFunc ℚ)
    (hs : sj * sj = 1) (hpow : E * Tjl⁻¹ * QMm * Tj * zj = Et * Tr) :
    E * (Pnm / (Pr * PAm)) * (sj * sl * Tjl⁻¹ * QMm) * (sj * Tj * zj / (Pj * Pl)) =
      Et / Pj * (sl * Tr * Pnm / (Pl * Pr * PAm)) := by
  have key : E * (Pnm / (Pr * PAm)) * (sj * sl * Tjl⁻¹ * QMm) * (sj * Tj * zj / (Pj * Pl)) =
      (sj * sj) * (E * Tjl⁻¹ * QMm * Tj * zj) * (sl * Pnm / (Pr * PAm * Pj * Pl)) := by
    ring
  rw [key, hs, hpow]
  ring

/-- A double summand with `m = j + l`, `M = j + l + r`, as a term of the inner sum. -/
private theorem doubleTerm_eq_twsClaspFinite (n j l r : ℕ) :
    doubleTerm_twsClaspFinite n (j + l + r) j (j + l) =
      qParam ^ (((n + j : ℕ) : ℤ) ^ 2 - 2 * ((n + (j + l + r) : ℕ) : ℤ) * ((n + j : ℕ) : ℤ) -
            (((l + r) * (l + r - 1) / 2 : ℕ) : ℤ)) / qPochhammer qParam j *
        ((-1) ^ l * qParam ^ (r * (r - 1) / 2) * qPochhammer qParam (n + (j + l)) /
          (qPochhammer qParam l * qPochhammer qParam r *
            qPochhammer qParam (2 * n + 1 + (j + l)))) := by
  have hs : (-1 : RatFunc ℚ) ^ j * (-1) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  unfold doubleTerm_twsClaspFinite
  rw [show j + l + r - (j + l) = r by omega, show j + l - j = l by omega,
    pow_add (-1 : RatFunc ℚ) j l]
  exact term_algebra_twsClaspFinite _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
    (pow_term_twsClaspFinite n j l r)

/-- The product of the `q`-Chu–Vandermonde sum at `b = q^(n+j+1)`, `C = q^(2n+j+2)`. -/
private theorem qVandermonde_prod_twsClaspFinite (n j K : ℕ) :
    ∏ s ∈ Finset.range K,
        qParam ^ s * (qParam ^ (n + j + 1) - qParam ^ (2 * n + 1 + j + 1) * qParam ^ s) =
      qParam ^ (K * (K - 1) / 2) * qParam ^ ((n + j + 1) * K) *
        qPochhammer (qParam ^ (n + 1)) K := by
  induction K with
  | zero => simp [qPochhammer]
  | succ K ih =>
    have hW : qPochhammer (qParam ^ (n + 1)) (K + 1) =
        qPochhammer (qParam ^ (n + 1)) K * (1 - qParam ^ (n + 1) * qParam ^ K) :=
      Finset.prod_range_succ _ _
    have hT : (K + 1) * (K + 1 - 1) / 2 = K * (K - 1) / 2 + K := Nat.triangle_succ K
    rw [Finset.prod_range_succ, ih, hW, hT]
    ring

/-- The `q`-Chu–Vandermonde sum at `b = q^(n+j+1)`, `C = q^(2n+j+2)`, in terms of `(q; q)_m`. -/
private theorem qVandermonde_innerSum_twsClaspFinite (n j K : ℕ) :
    ∑ l ∈ Finset.range (K + 1),
        (-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (n + j + l) /
          (qPochhammer qParam l * qPochhammer qParam (K - l) *
            qPochhammer qParam (2 * n + 1 + j + l)) =
      qParam ^ (K * (K - 1) / 2) * qParam ^ ((n + j + 1) * K) * qPochhammer qParam (n + K) *
          qPochhammer qParam (n + j) /
        (qPochhammer qParam n * qPochhammer qParam K *
          qPochhammer qParam (2 * n + 1 + j + K)) := by
  have hV := claspAlg_qVandermonde K (qParam ^ (n + j + 1)) (qParam ^ (2 * n + 1 + j + 1))
  have hterm : ∀ l ∈ Finset.range (K + 1),
      (-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) *
          (qPochhammer qParam K / (qPochhammer qParam l * qPochhammer qParam (K - l))) *
          qPochhammer (qParam ^ (2 * n + 1 + j + 1) * qParam ^ l) (K - l) *
          qPochhammer (qParam ^ (n + j + 1)) l * qPochhammer qParam (n + j) =
        qPochhammer qParam K * qPochhammer qParam (2 * n + 1 + j + K) *
          ((-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (n + j + l) /
            (qPochhammer qParam l * qPochhammer qParam (K - l) *
              qPochhammer qParam (2 * n + 1 + j + l))) := by
    intro l hl
    obtain ⟨d, rfl⟩ : ∃ d, K = l + d := ⟨K - l, by have := Finset.mem_range.mp hl; omega⟩
    have e : l + d - l = d := by omega
    have hW : qPochhammer qParam (2 * n + 1 + j + l) *
        qPochhammer (qParam ^ (2 * n + 1 + j + 1) * qParam ^ l) d =
          qPochhammer qParam (2 * n + 1 + j + (l + d)) := by
      have h := claspAlg_qPochhammer_mul_shift (2 * n + 1 + j + l) d
      rw [show qParam ^ (2 * n + 1 + j + l + 1) = qParam ^ (2 * n + 1 + j + 1) * qParam ^ l by ring,
        Nat.add_assoc (2 * n + 1 + j) l d] at h
      exact h
    have hx : qPochhammer qParam (n + j) * qPochhammer (qParam ^ (n + j + 1)) l =
        qPochhammer qParam (n + j + l) := claspAlg_qPochhammer_mul_shift (n + j) l
    have h1 := qPochhammer_qParam_ne_zero (2 * n + 1 + j + l)
    rw [e, ← hW, ← hx]
    field_simp
  have hsum : (∏ s ∈ Finset.range K,
      qParam ^ s * (qParam ^ (n + j + 1) - qParam ^ (2 * n + 1 + j + 1) * qParam ^ s)) *
      qPochhammer qParam (n + j) =
        qPochhammer qParam K * qPochhammer qParam (2 * n + 1 + j + K) *
          ∑ l ∈ Finset.range (K + 1),
            (-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (n + j + l) /
              (qPochhammer qParam l * qPochhammer qParam (K - l) *
                qPochhammer qParam (2 * n + 1 + j + l)) := by
    rw [← hV, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hshift := claspAlg_qPochhammer_mul_shift n K
  have hne : qPochhammer qParam n * qPochhammer qParam K *
      qPochhammer qParam (2 * n + 1 + j + K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _))
      (qPochhammer_qParam_ne_zero _)
  rw [qVandermonde_prod_twsClaspFinite] at hsum
  rw [eq_div_iff hne]
  linear_combination (-qPochhammer qParam n) * hsum +
    (qParam ^ (K * (K - 1) / 2) * qParam ^ ((n + j + 1) * K) * qPochhammer qParam (n + j)) * hshift

/-- The powers of `q` after the inner summation, with `M = j + K`. -/
private theorem pow_final_twsClaspFinite (n j K : ℕ) :
    qParam ^ (((n + j : ℕ) : ℤ) ^ 2 - 2 * ((n + (j + K) : ℕ) : ℤ) * ((n + j : ℕ) : ℤ) -
          ((K * (K - 1) / 2 : ℕ) : ℤ)) *
        (qParam ^ (K * (K - 1) / 2) * qParam ^ ((n + j + 1) * K)) =
      qParam ^ (((j + K : ℕ) : ℤ) - (n : ℤ) * ((n + (j + K) : ℕ) : ℤ) -
        ((n + (j + K) + 1 : ℕ) : ℤ) * (j : ℤ)) := by
  have hq := qParam_ne_zero
  rw [← zpow_natCast qParam (K * (K - 1) / 2), ← zpow_natCast qParam ((n + j + 1) * K),
    ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- The inner sum of the double sum is a term of Zheng's sum. -/
private theorem doubleTerm_inner_twsClaspFinite (n j K : ℕ) :
    ∑ l ∈ Finset.range (K + 1), doubleTerm_twsClaspFinite n (j + K) j (j + l) =
      qParam ^ (((j + K : ℕ) : ℤ) - (n : ℤ) * ((n + (j + K) : ℕ) : ℤ) -
          ((n + (j + K) + 1 : ℕ) : ℤ) * (j : ℤ)) *
        qPochhammer qParam (n + K) * qPochhammer qParam (n + j) /
        (qPochhammer qParam n * qPochhammer qParam K * qPochhammer qParam j *
          qPochhammer qParam (2 * n + 1 + (j + K))) := by
  have hterm : ∀ l ∈ Finset.range (K + 1), doubleTerm_twsClaspFinite n (j + K) j (j + l) =
      qParam ^ (((n + j : ℕ) : ℤ) ^ 2 - 2 * ((n + (j + K) : ℕ) : ℤ) * ((n + j : ℕ) : ℤ) -
            ((K * (K - 1) / 2 : ℕ) : ℤ)) / qPochhammer qParam j *
        ((-1) ^ l * qParam ^ ((K - l) * (K - l - 1) / 2) * qPochhammer qParam (n + j + l) /
          (qPochhammer qParam l * qPochhammer qParam (K - l) *
            qPochhammer qParam (2 * n + 1 + j + l))) := by
    intro l hl
    obtain ⟨r, rfl⟩ : ∃ r, K = l + r := ⟨K - l, by have := Finset.mem_range.mp hl; omega⟩
    rw [show l + r - l = r by omega, show j + (l + r) = j + l + r by omega,
      show n + j + l = n + (j + l) by omega, show 2 * n + 1 + j + l = 2 * n + 1 + (j + l) by omega]
    exact doubleTerm_eq_twsClaspFinite n j l r
  have hf := pow_final_twsClaspFinite n j K
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, qVandermonde_innerSum_twsClaspFinite n j K,
    show 2 * n + 1 + (j + K) = 2 * n + 1 + j + K by omega]
  linear_combination (qPochhammer qParam (n + K) * qPochhammer qParam (n + j) /
    (qPochhammer qParam n * qPochhammer qParam K * qPochhammer qParam j *
      qPochhammer qParam (2 * n + 1 + j + K))) * hf

/-- The turnback side of the Sears transformation is Zheng's sum (Gasper–Rahman (III.7)). -/
private theorem searsLeft_eq_zheng_twsClaspFinite (n M : ℕ) :
    qPochhammer qParam M *
        ∑ m ∈ Finset.range (M + 1),
          qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
            qPochhammer qParam (n + m) /
            (qPochhammer qParam (M - m) ^ 2 * qPochhammer qParam m *
              qPochhammer qParam (2 * n + 1 + m)) =
      ∑ j ∈ Finset.range (M + 1),
        qParam ^ (((M : ℕ) : ℤ) - (n : ℤ) * ((n + M : ℕ) : ℤ) -
            ((n + M + 1 : ℕ) : ℤ) * (j : ℤ)) *
          qPochhammer qParam (n + (M - j)) * qPochhammer qParam (n + j) /
          (qPochhammer qParam n * qPochhammer qParam (M - j) * qPochhammer qParam j *
            qPochhammer qParam (2 * n + 1 + M)) := by
  have hswap : ∑ m ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (m + 1),
      doubleTerm_twsClaspFinite n M j m =
        ∑ j ∈ Finset.range (M + 1), ∑ m ∈ Finset.Ico j (M + 1),
          doubleTerm_twsClaspFinite n M j m := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (M + 1) _).symm
  rw [Finset.mul_sum,
    Finset.sum_congr rfl fun m hm ↦
      doubleTerm_outer_twsClaspFinite n M m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), hswap]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.sum_Ico_eq_sum_range]
  obtain ⟨K, rfl⟩ : ∃ K, M = j + K := ⟨M - j, by have := Finset.mem_range.mp hj; omega⟩
  rw [show j + K + 1 - j = K + 1 by omega, show j + K - j = K by omega]
  exact doubleTerm_inner_twsClaspFinite n j K

/-- Zheng's coefficient at `N = n + M + 1` in terms of `(q; q)_m`. -/
private theorem twsZheng_eq_sum_twsClaspFinite (n M : ℕ) :
    twsZheng (n + M + 1) n =
      qParam ^ (n + M) * ((1 - qParam) / (1 - qParam ^ (n + M + 1))) *
        ∑ i ∈ Finset.range (M + 1), qParam ^ ((n + M + 1) * i) *
          (qPochhammer qParam (n + i) * qPochhammer qParam (n + (M - i)) /
            (qPochhammer qParam i * qPochhammer qParam (M - i) * qPochhammer qParam n)) := by
  rw [twsZheng, show n + M + 1 - 1 = n + M by omega, show n + M + 1 - n = M + 1 by omega]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by have := Finset.mem_range.mp hi; omega⟩
  have h1 := claspAlg_qPochhammer_mul_shift i n
  have h2 := claspAlg_qPochhammer_mul_shift d n
  have hi0 := qPochhammer_qParam_ne_zero i
  have hd0 := qPochhammer_qParam_ne_zero d
  have hn0 := qPochhammer_qParam_ne_zero n
  rw [show n + (i + d) + 1 - i - n = d + 1 by omega, show i + d - i = d by omega,
    show n + i = i + n by omega, show n + d = d + n by omega, ← h1, ← h2]
  field_simp

/-- The reflected term of the transformed sum is a term of Zheng's sum. -/
private theorem reflect_term_twsClaspFinite (n i d : ℕ) :
    qParam ^ (((i + d : ℕ) : ℤ) - (n : ℤ) * ((n + (i + d) : ℕ) : ℤ) -
          ((n + (i + d) + 1 : ℕ) : ℤ) * (d : ℤ)) *
        qPochhammer qParam (n + i) * qPochhammer qParam (n + d) /
        (qPochhammer qParam n * qPochhammer qParam i * qPochhammer qParam d *
          qPochhammer qParam (2 * n + 1 + (i + d))) =
      qParam ^ (-(((n + (i + d)) ^ 2 : ℕ) : ℤ)) / qPochhammer qParam (2 * n + 1 + (i + d)) *
        (qParam ^ ((n + (i + d) + 1) * i) *
          (qPochhammer qParam (n + i) * qPochhammer qParam (n + d) /
            (qPochhammer qParam i * qPochhammer qParam d * qPochhammer qParam n))) := by
  have hq := qParam_ne_zero
  have hpow : qParam ^ (((i + d : ℕ) : ℤ) - (n : ℤ) * ((n + (i + d) : ℕ) : ℤ) -
      ((n + (i + d) + 1 : ℕ) : ℤ) * (d : ℤ)) =
        qParam ^ (-(((n + (i + d)) ^ 2 : ℕ) : ℤ)) * qParam ^ ((n + (i + d) + 1) * i) := by
    rw [← zpow_natCast qParam ((n + (i + d) + 1) * i), ← zpow_add₀ hq]
    congr 1
    push_cast
    ring
  rw [hpow]
  ring

/-- The turnback side of the Sears transformation as Zheng's sum, with the `i`-sum reversed. -/
private theorem searsLeft_eq_zheng_reflect_twsClaspFinite (n M : ℕ) :
    qPochhammer qParam M *
        ∑ m ∈ Finset.range (M + 1),
          qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
            qPochhammer qParam (n + m) /
            (qPochhammer qParam (M - m) ^ 2 * qPochhammer qParam m *
              qPochhammer qParam (2 * n + 1 + m)) =
      qParam ^ (-(((n + M) ^ 2 : ℕ) : ℤ)) / qPochhammer qParam (2 * n + 1 + M) *
        ∑ i ∈ Finset.range (M + 1), qParam ^ ((n + M + 1) * i) *
          (qPochhammer qParam (n + i) * qPochhammer qParam (n + (M - i)) /
            (qPochhammer qParam i * qPochhammer qParam (M - i) * qPochhammer qParam n)) := by
  rw [searsLeft_eq_zheng_twsClaspFinite, ← Finset.sum_range_reflect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by have := Finset.mem_range.mp hi; omega⟩
  rw [show i + d + 1 - 1 - i = d by omega, show i + d - d = i by omega,
    show i + d - i = d by omega]
  exact reflect_term_twsClaspFinite n i d

/-- The clasp coefficient of the library is Zheng's coefficient:
`[N] ∑_{j=n}^{N-1} C_j(N) K_{j,n} = [N] β_{N,n}` for `n < N`. Route: with `M = N - 1 - n`,
`∑_i q^(-N i) (q^(i+1); q)_n (q^(N-i-n); q)_n / (q; q)_n` is
`(q; q)_(M+n) / (q; q)_M` times the terminating `₂φ₁(q^(-M), q^(n+1); q^(-M-n); q, q^(-M-2n-1))`;
Gasper–Rahman (III.7) (one `q`-Chu–Vandermonde expansion, exchange of the two sums, and the
`q`-binomial theorem) turns it into `₃φ₂(q^(-M), q^(-M), q^(n+1); q^(2n+2), 0; q, q)`, the form
of the clasp eigenvalue `claspAlgClaspEigen (N - 1) n`
(`claspAlgClaspEigen_eq_searsMid`, `claspAlgClaspEigen_eq_claspAlgCoeff`). -/
theorem tws_claspAlgCoeff_eq_twsZheng {N n : ℕ} (hn : n < N) :
    claspAlgCoeff N n = quantumInt N * twsZheng N n := by
  obtain ⟨M, rfl⟩ : ∃ M, N = n + M + 1 := ⟨N - n - 1, by omega⟩
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 := claspAlgCoeff_eq_searsMid (n + M) n (by omega)
  have h2 := claspAlg_searsLeft n M
  have h3 := searsLeft_eq_zheng_reflect_twsClaspFinite n M
  have hQ := claspAlg_quantumInt_mul_one_sub_qParam ((n + M + 1 : ℕ) : ℤ)
  have hqN : (1 : RatFunc ℚ) - qParam ^ (n + M + 1) ≠ 0 := by
    have h := one_sub_qParam_zpow_ne_zero (n := ((n + M + 1 : ℕ) : ℤ)) (by omega)
    rwa [zpow_natCast] at h
  have hPA := qPochhammer_qParam_ne_zero (2 * n + 1 + M)
  have hqc : qParam ^ (n + M) ≠ 0 := pow_ne_zero _ qParam_ne_zero
  have hpow : (RatFunc.X : RatFunc ℚ) ^ (4 * ((n + M : ℕ) : ℤ) ^ 2 + 6 * ((n + M : ℕ) : ℤ)) *
      qParam ^ (-(((n + M) ^ 2 : ℕ) : ℤ)) =
        RatFunc.X ^ (2 - 2 * ((n + M + 1 : ℕ) : ℤ)) * (qParam ^ (n + M) * qParam ^ (n + M)) := by
    rw [claspAlg_qParam_zpow, claspAlg_qParam_pow, ← zpow_add₀ hX, ← zpow_add₀ hX,
      ← zpow_add₀ hX]
    congr 1
    push_cast
    ring
  rw [zpow_natCast] at hQ
  rw [show n + M - n = M by omega] at h1
  rw [show 2 * n + M + 1 = 2 * n + 1 + M by omega, mul_right_comm, h3] at h2
  rw [h1, twsZheng_eq_sum_twsClaspFinite]
  refine mul_left_cancel₀ hqc ?_
  have hQ' : quantumInt ((n + M + 1 : ℕ) : ℤ) * ((1 - qParam) / (1 - qParam ^ (n + M + 1))) =
      RatFunc.X ^ (2 - 2 * ((n + M + 1 : ℕ) : ℤ)) := by
    rw [← mul_div_assoc, hQ, mul_div_assoc, div_self hqN, mul_one]
  have h2' : qParam ^ (n + M) * claspAlgSearsMid n M =
      qParam ^ (-(((n + M) ^ 2 : ℕ) : ℤ)) *
        ∑ i ∈ Finset.range (M + 1), qParam ^ ((n + M + 1) * i) *
          (qPochhammer qParam (n + i) * qPochhammer qParam (n + (M - i)) /
            (qPochhammer qParam i * qPochhammer qParam (M - i) * qPochhammer qParam n)) := by
    rw [← h2, div_mul_eq_mul_div, div_mul_cancel₀ _ hPA]
  linear_combination
    (RatFunc.X : RatFunc ℚ) ^ (4 * ((n + M : ℕ) : ℤ) ^ 2 + 6 * ((n + M : ℕ) : ℤ)) * h2' +
    (∑ i ∈ Finset.range (M + 1), qParam ^ ((n + M + 1) * i) *
          (qPochhammer qParam (n + i) * qPochhammer qParam (n + (M - i)) /
            (qPochhammer qParam i * qPochhammer qParam (M - i) * qPochhammer qParam n))) * hpow -
    (qParam ^ (n + M) * qParam ^ (n + M) *
      ∑ i ∈ Finset.range (M + 1), qParam ^ ((n + M + 1) * i) *
          (qPochhammer qParam (n + i) * qPochhammer qParam (n + (M - i)) /
            (qPochhammer qParam i * qPochhammer qParam (M - i) * qPochhammer qParam n))) * hQ'

/-- The triangular finite transform is the clasp form: `F_N = q^(N-1) Y_{0,N}(u)`. -/
theorem tws_reducedFormula_eq_twsY (u : ℕ → RatFunc ℚ) {N : ℕ} (hN : 1 ≤ N) :
    pairQReducedFormula u N = qParam ^ (N - 1) * twsY false u N := by
  have hQ : quantumInt (N : ℤ) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  refine mul_left_cancel₀ hQ ?_
  rw [pairQ_quantumInt_mul_reducedFormula,
    Finset.sum_congr rfl fun n hn ↦ by
      rw [tws_claspAlgCoeff_eq_twsZheng (Finset.mem_range.mp hn)]]
  simp only [twsY, twsZheng, twsTheta, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Bool.false_eq_true, ite_false]
  ring

end AJConjecture
