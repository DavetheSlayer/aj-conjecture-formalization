import Mathlib
import AJHandoff.PairDefs
import AJHandoff.TorusQuantum.PairQFormula
import AJConjecture.ClaspAlgBasic
import AJConjecture.QAlgQParamBasic

/-!
# The colour-2 value of the satellite formula determines the pair

`pairQFormula_two_injective`: for admissible pairs, the value at colour `2` of the satellite
formula `pairQFormula (pairQOddColor r s)` determines `(r, s)`. Route (as
`torusWhiteheadFormula_two_injective` for `r = 2`): `u_0 = 1`, and the colour-2 value is
`[2] (1 + C_1(2) D_1)` with `D_1` affine in `u_1` with nonzero coefficient, so it determines
`u_1 = q^(-2rs) (1 + q^(rs+r) [2s+1] - q^(rs-r) [2s-1])`; as a Laurent polynomial in `q` (or `t`)
its lowest degree is `-2rs` (from the term `1`) and its highest degree is `r + s - rs`, both
attained by a single monomial, so `u_1` determines `rs` and `r + s`, hence `(r, s)` with `r < s`.
Checked by computer (sympy, outside the formal development): no collision among the 22
admissible pairs with `r ≤ 6`, `s ≤ 11`.
-/

open Polynomial

namespace AJConjecture

/-- The colour `u_0` of `T(r, s)` is `1`. -/
private theorem pairQOddColor_zero_jonesTwo (r s : ℕ) : pairQOddColor r s 0 = 1 := by
  simp only [pairQOddColor, quantumInt, Nat.cast_zero, neg_zero, Finset.Icc_self,
    Finset.sum_singleton, mul_zero, zero_add, zpow_zero, one_mul, mul_one]
  exact div_self claspAlg_ratFuncX_sq_sub_ne_zero

/-- The reduced formula at `N = 2` of an input sequence with `u_0 = 1`. -/
private theorem pairQReducedFormula_two {u : ℕ → RatFunc ℚ} (hu : u 0 = 1) :
    pairQReducedFormula u 2 =
      qParam * (1 + qParam ^ 2 + (1 - qParam) * u 1) / (1 + qParam) := by
  have hq := qParam_ne_zero
  have h1 : 1 - qParam ≠ 0 := by simpa using one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
  have h2 : 1 - qParam ^ 2 ≠ 0 := by
    simpa using one_sub_qParam_zpow_ne_zero (n := 2) two_ne_zero
  have h3 : 1 - qParam ^ 3 ≠ 0 := by
    simpa using one_sub_qParam_zpow_ne_zero (n := 3) three_ne_zero
  have hp : 1 + qParam ≠ 0 := by
    intro h
    apply h2
    linear_combination (1 - qParam) * h
  simp only [pairQReducedFormula, pairQCycloCoeff, cyclotomicKernel, qPochhammer,
    Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, hu]
  norm_num [Finset.Icc_self]
  field_simp
  ring

/-- `[-n] = -[n]`. -/
private theorem quantumInt_neg_pairK (n : ℤ) : quantumInt (-n) = -quantumInt n := by
  simp only [quantumInt, mul_neg, neg_neg, ← neg_div, neg_sub]

/-- `[2n+1] (1 - q) q^n = 1 - q^(2n+1)`. -/
private theorem quantumInt_odd_mul_pairK (n : ℕ) :
    quantumInt (2 * (n : ℤ) + 1) * (1 - qParam) * qParam ^ n = 1 - qParam ^ (2 * n + 1) := by
  rw [claspAlg_quantumInt_mul_one_sub_qParam]
  have hX : (RatFunc.X : RatFunc ℚ) ^ (2 - 2 * (2 * (n : ℤ) + 1)) * qParam ^ n = 1 := by
    rw [← zpow_natCast qParam n, claspAlg_qParam_zpow, ← zpow_add₀ RatFunc.X_ne_zero]
    ring_nf
    exact zpow_zero _
  rw [show qParam ^ (2 * (n : ℤ) + 1) = qParam ^ (2 * n + 1) by
    rw [← zpow_natCast]; push_cast; rfl]
  linear_combination (1 - qParam ^ (2 * n + 1)) * hX

/-- The six-term polynomial `q^t (q^s - q^(s+1) + q^(m+r) - q^(m+r+2s+1) - q^(m-r+1) +
q^(m-r+2s))`, written in the variable `X` with `q = X⁴`. -/
private noncomputable def pairKJonesPoly (t m r s : ℕ) : ℚ[X] :=
  X ^ (4 * (t + s)) - X ^ (4 * (t + s + 1)) + X ^ (4 * (t + m + r)) -
    X ^ (4 * (t + m + r + 2 * s + 1)) - X ^ (4 * (t + m - r + 1)) + X ^ (4 * (t + m - r + 2 * s))

private theorem algebraMap_X_pow_four_mul (e : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ) ((X : ℚ[X]) ^ (4 * e)) = qParam ^ e := by
  rw [map_pow, RatFunc.algebraMap_X, qParam, pow_mul]

/-- `q^(t + 2rs + s) (1 - q) u_1 = pairKJonesPoly t (rs) r s`. -/
private theorem pairQOddColor_one_poly {r s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    qParam ^ (t + 2 * (r * s) + s) * ((1 - qParam) * pairQOddColor r s 1) =
      algebraMap ℚ[X] (RatFunc ℚ) (pairKJonesPoly t (r * s) r s) := by
  have hIcc : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hq := qParam_ne_zero
  have e1 : qParam ^ (-((r : ℤ) * ((s' + 1 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) * (((1 : ℕ) : ℤ) + 1))) =
      (qParam ^ (2 * (r * (s' + 1))))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast]
    push_cast
    ring_nf
  have e2 : qParam ^ ((r : ℤ) * (-1) * (((s' + 1 : ℕ) : ℤ) * (-1) + 1)) =
      qParam ^ (r * (s' + 1) - r) := by
    rw [← zpow_natCast, Nat.cast_sub (Nat.le_mul_of_pos_right r (by omega))]
    push_cast
    ring_nf
  have e3 : qParam ^ ((r : ℤ) * 1 * (((s' + 1 : ℕ) : ℤ) * 1 + 1)) =
      qParam ^ (r * (s' + 1) + r) := by
    rw [← zpow_natCast]
    push_cast
    ring_nf
  have e4 : quantumInt (2 * ((s' + 1 : ℕ) : ℤ) * (-1) + 1) = -quantumInt (2 * (s' : ℤ) + 1) := by
    rw [← quantumInt_neg_pairK]
    push_cast
    ring_nf
  have e5 : quantumInt (2 * ((s' + 1 : ℕ) : ℤ) * 1 + 1) =
      quantumInt (2 * ((s' + 1 : ℕ) : ℤ) + 1) := by
    ring_nf
  have e6 : quantumInt (2 * ((s' + 1 : ℕ) : ℤ) * 0 + 1) = 1 := by
    simp only [mul_zero, zero_add, quantumInt, mul_one]
    exact div_self claspAlg_ratFuncX_sq_sub_ne_zero
  rw [pairQOddColor, hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, e1, e2, e3, e4, e5, mul_zero, zero_mul, zpow_zero, one_mul, e6]
  have hA := quantumInt_odd_mul_pairK (s' + 1)
  have hB := quantumInt_odd_mul_pairK s'
  have hle : r ≤ r * (s' + 1) := Nat.le_mul_of_pos_right r (by omega)
  obtain ⟨c, hc⟩ : ∃ c, r * (s' + 1) = r + c := ⟨r * (s' + 1) - r, by omega⟩
  simp only [pairKJonesPoly, map_add, map_sub, algebraMap_X_pow_four_mul]
  rw [hc] at hle ⊢
  rw [show r + c - r = c by omega, show t + (r + c) - r + 1 = t + c + 1 by omega,
    show t + (r + c) - r + 2 * (s' + 1) = t + c + 2 * (s' + 1) by omega]
  have hinv : (qParam ^ (2 * (r + c)))⁻¹ * qParam ^ (2 * (r + c)) = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ hq)
  linear_combination (qParam ^ (t + (s' + 1)) * (1 - qParam) *
      (-(qParam ^ c * quantumInt (2 * (s' : ℤ) + 1)) + 1 +
        qParam ^ (r + c + r) * quantumInt (2 * ((s' + 1 : ℕ) : ℤ) + 1))) * hinv -
    qParam ^ (t + c + 1) * hB + qParam ^ (t + (r + c) + r) * hA

private theorem coeff_pairKJonesPoly (t m r s n : ℕ) :
    (pairKJonesPoly t m r s).coeff n =
      (if n = 4 * (t + s) then 1 else 0) - (if n = 4 * (t + s + 1) then 1 else 0) +
        (if n = 4 * (t + m + r) then 1 else 0) -
        (if n = 4 * (t + m + r + 2 * s + 1) then 1 else 0) -
        (if n = 4 * (t + m - r + 1) then 1 else 0) +
        (if n = 4 * (t + m - r + 2 * s) then 1 else 0) := by
  simp only [pairKJonesPoly, coeff_add, coeff_sub, coeff_X_pow]

/-- Two admissible pairs whose six-term polynomials agree (after the normalising shifts) have the
same product and the same sum. -/
private theorem mul_eq_and_add_eq_of_pairKJonesPoly {r s r' s' : ℕ} (h : IsTorusPair r s)
    (h' : IsTorusPair r' s')
    (hP : pairKJonesPoly (2 * (r' * s') + s') (r * s) r s =
      pairKJonesPoly (2 * (r * s) + s) (r' * s') r' s') :
    r * s = r' * s' ∧ r + s = r' + s' := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨hr', hrs', -⟩ := h'
  have hm : r + s + 1 ≤ r * s := by nlinarith
  have hm' : r' + s' + 1 ≤ r' * s' := by nlinarith
  generalize r * s = m at hm hP
  generalize r' * s' = m' at hm' hP
  have hlow : m = m' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hc := congrArg (fun p : ℚ[X] ↦ p.coeff (4 * (2 * m + s + s'))) hP
      simp only [coeff_pairKJonesPoly] at hc
      simp (disch := omega) only [ite_eq_right] at hc
      norm_num at hc
    · have hc := congrArg (fun p : ℚ[X] ↦ p.coeff (4 * (2 * m' + s' + s))) hP
      simp only [coeff_pairKJonesPoly] at hc
      simp (disch := omega) only [ite_eq_right] at hc
      norm_num at hc
  subst hlow
  refine ⟨rfl, ?_⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hc := congrArg (fun p : ℚ[X] ↦ p.coeff (4 * (2 * m + s + m + r' + 2 * s' + 1))) hP
    simp only [coeff_pairKJonesPoly] at hc
    simp (disch := omega) only [ite_eq_right] at hc
    norm_num at hc
  · have hc := congrArg (fun p : ℚ[X] ↦ p.coeff (4 * (2 * m + s' + m + r + 2 * s + 1))) hP
    simp only [coeff_pairKJonesPoly] at hc
    simp (disch := omega) only [ite_eq_right] at hc
    norm_num at hc

/-- The colour-2 value of the satellite formula of `T(r, s)` determines the admissible pair. -/
theorem pairQFormula_two_injective {r s r' s' : ℕ} (h : IsTorusPair r s) (h' : IsTorusPair r' s')
    (heq : pairQFormula (pairQOddColor r s) 2 = pairQFormula (pairQOddColor r' s') 2) :
    r = r' ∧ s = s' := by
  have hq := qParam_ne_zero
  have hF : pairQReducedFormula (pairQOddColor r s) 2 =
      pairQReducedFormula (pairQOddColor r' s') 2 := by
    have h2 : quantumInt 2 ≠ 0 := claspAlg_quantumInt_ne_zero (by norm_num)
    have ht : (2 : ℤ).toNat = 2 := rfl
    simp only [pairQFormula, show (0 : ℤ) < 2 by norm_num, ite_true, ht] at heq
    exact mul_left_cancel₀ h2 heq
  have hp : 1 + qParam ≠ 0 := by
    have h2 : 1 - qParam ^ 2 ≠ 0 := by
      simpa using one_sub_qParam_zpow_ne_zero (n := 2) two_ne_zero
    intro h0
    apply h2
    linear_combination (1 - qParam) * h0
  rw [pairQReducedFormula_two (pairQOddColor_zero_jonesTwo r s),
    pairQReducedFormula_two (pairQOddColor_zero_jonesTwo r' s'), div_left_inj₀ hp] at hF
  have hV : (1 - qParam) * pairQOddColor r s 1 = (1 - qParam) * pairQOddColor r' s' 1 :=
    add_left_cancel (mul_left_cancel₀ hq hF)
  have hs : 1 ≤ s := by have := h.1; have := h.2.1; omega
  have hs' : 1 ≤ s' := by have := h'.1; have := h'.2.1; omega
  have hP := pairQOddColor_one_poly (r := r) hs (2 * (r' * s') + s')
  rw [hV, show 2 * (r' * s') + s' + 2 * (r * s) + s = 2 * (r * s) + s + 2 * (r' * s') + s' by
    ring, pairQOddColor_one_poly (r := r') hs'] at hP
  obtain ⟨hmul, hadd⟩ := mul_eq_and_add_eq_of_pairKJonesPoly h h'
    (RatFunc.algebraMap_injective ℚ hP).symm
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨hr', hrs', -⟩ := h'
  have key : ((s : ℤ) - s') * ((r : ℤ) - s') = 0 := by
    have h1 : (r' : ℤ) = r + s - s' := by omega
    have h2 : (r : ℤ) * s = r' * s' := by exact_mod_cast hmul
    rw [h1] at h2
    linear_combination h2
  rcases mul_eq_zero.mp key with h0 | h0 <;> omega

end AJConjecture
