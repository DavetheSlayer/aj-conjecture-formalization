import Mathlib
import AJTwist.Select.TwSClaspFinite
import AJTwist.Select.TwSInvert

/-!
# The normalized inversion of the finite transform

Source: Section 6.4 of `selection.tex` (revision 5): with `(𝓑 F)_N = q^(N(N-1)) F_N(t⁻¹)`,
"the prefactor in (claspfinite) contributes `q^(-N(N-1)) (1 - q) / (1 - X)` after inversion, and
the ratio of Pochhammers contributes `(-1)^n q^(-n N + n(n+1)/2)` times the ratio in
(coefficient-kernel); the inverted summand monomial contributes `X^i q^(N n)`. Thus
`(𝓑 F)_N = Y_{1,N}(v(q⁻¹))` on the entire finite support."

Proof: `tws_reducedFormula_eq_twsY`, then termwise
`(q⁻¹; q⁻¹)_k = (-1)^k q^(-k(k+1)/2) (q; q)_k` for the three Pochhammer symbols and
`1 - q^(-N) = -q^(-N) (1 - q^N)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `twsInv` inverts `q = t⁴`. -/
private theorem twsInv_qParam_twsInvFormula : twsInv qParam = qParam⁻¹ := by
  rw [qParam, map_pow, twsInv_X, inv_pow]

/-- The inverted Pochhammer symbol: `(q^(-a); q⁻¹)_n q^(n a + n(n-1)/2) = (-1)^n (q^a; q)_n`. -/
private theorem twsInv_qPochhammer_twsInvFormula (a n : ℕ) :
    twsInv (qPochhammer (qParam ^ a) n) * qParam ^ (n * a + n * (n - 1) / 2) =
      (-1) ^ n * qPochhammer (qParam ^ a) n := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    have hP : qPochhammer (qParam ^ a) (n + 1) =
        qPochhammer (qParam ^ a) n * (1 - qParam ^ a * qParam ^ n) :=
      Finset.prod_range_succ _ _
    have hT : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := Nat.triangle_succ n
    have hne : qParam ^ a * qParam ^ n ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ qParam_ne_zero) (pow_ne_zero _ qParam_ne_zero)
    have hfac : (1 - qParam⁻¹ ^ a * qParam⁻¹ ^ n) * (qParam ^ a * qParam ^ n) =
        -(1 - qParam ^ a * qParam ^ n) := by
      rw [inv_pow, inv_pow, sub_mul, ← mul_inv, inv_mul_cancel₀ hne]
      ring
    have he : qParam ^ ((n + 1) * a + (n * (n - 1) / 2 + n)) =
        qParam ^ (n * a + n * (n - 1) / 2) * (qParam ^ a * qParam ^ n) := by
      ring
    rw [hP, hT, he, map_mul, map_sub, map_one, map_mul, map_pow, map_pow,
      twsInv_qParam_twsInvFormula]
    linear_combination ((1 - qParam⁻¹ ^ a * qParam⁻¹ ^ n) * (qParam ^ a * qParam ^ n)) * ih +
      ((-1) ^ n * qPochhammer (qParam ^ a) n) * hfac

/-- The inverted summand of the clasp form is the reflected summand of `Y_{1,N}`. -/
private theorem inv_term_twsInvFormula (w : RatFunc ℚ) (n i k : ℕ) :
    qParam ^ ((n + i + k + 1) * (n + i + k)) *
        (qParam⁻¹ ^ ((n + i + k + 1) * i) * w *
          (twsInv (qPochhammer (qParam ^ (i + 1)) n) * twsInv (qPochhammer (qParam ^ (k + 1)) n) /
            twsInv (qPochhammer qParam n))) =
      qParam ^ ((n + i + k + 1) * k) * ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * w) *
        (qPochhammer (qParam ^ (k + 1)) n * qPochhammer (qParam ^ (i + 1)) n /
          qPochhammer qParam n) := by
  have hq0 : qParam ≠ 0 := qParam_ne_zero
  have hA := twsInv_qPochhammer_twsInvFormula (i + 1) n
  have hB := twsInv_qPochhammer_twsInvFormula (k + 1) n
  have hD := twsInv_qPochhammer_twsInvFormula 1 n
  rw [pow_one] at hD
  have hT1 : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
    have h := Nat.triangle_succ n
    rwa [Nat.add_sub_cancel, mul_comm] at h
  have hT2 : n * (n - 1) / 2 + n * (n - 1) / 2 + n = n * n := by
    have h := Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd
    have h' : n * (n - 1) + n = n * n := by
      cases n with
      | zero => rfl
      | succ m =>
        rw [Nat.add_sub_cancel]
        ring
    omega
  rw [hT1]
  generalize n * (n - 1) / 2 = t at hA hB hD hT2 ⊢
  have hsgn : ((-1 : RatFunc ℚ) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hPD : qPochhammer qParam n ≠ 0 := qPochhammer_qParam_ne_zero n
  have hD0 : twsInv (qPochhammer qParam n) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hD
    exact mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) hPD hD.symm
  generalize twsInv (qPochhammer (qParam ^ (i + 1)) n) = A at hA ⊢
  generalize twsInv (qPochhammer (qParam ^ (k + 1)) n) = B at hB ⊢
  generalize twsInv (qPochhammer qParam n) = D at hD hD0 ⊢
  generalize qPochhammer (qParam ^ (i + 1)) n = PA at hA ⊢
  generalize qPochhammer (qParam ^ (k + 1)) n = PB at hB ⊢
  generalize qPochhammer qParam n = PD at hD hPD ⊢
  generalize ((-1 : RatFunc ℚ) ^ n) = σ at hA hB hD hsgn ⊢
  have hXY : A * B / D * (qParam ^ (n * (i + k + 1)) * qParam ^ t) = σ * (PB * PA / PD) := by
    rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff hD0 hPD]
    linear_combination (-(A * B * (qParam ^ (n * (i + k + 1)) * qParam ^ t) * PD)) * hsgn +
      σ * (-(A * B * (qParam ^ (n * (i + k + 1)) * qParam ^ t)) * hD +
        D * (B * qParam ^ (n * (k + 1) + t) * hA + σ * PA * hB) + D * PA * PB * hsgn)
  have hE : qParam ^ ((n + i + k + 1) * (n + i + k)) * qParam⁻¹ ^ ((n + i + k + 1) * i) =
      qParam ^ ((n + i + k + 1) * k) * qParam ^ (t + t + n) * qParam ^ (n * (i + k + 1)) := by
    rw [hT2, inv_pow, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hq0)]
    ring
  linear_combination (w * (A * B / D)) * hE +
    (qParam ^ ((n + i + k + 1) * k) * qParam ^ (t + n) * w) * hXY

/-- The normalized inversion of the finite transform: `q^(N(N-1)) F_N(t⁻¹) = Y_{1,N}` of the
inverted input. -/
theorem tws_inv_reducedFormula (u : ℕ → RatFunc ℚ) {N : ℕ} (hN : 1 ≤ N) :
    qParam ^ (N * (N - 1)) * twsInv (pairQReducedFormula u N) =
      twsY true (fun n ↦ twsInv (u n)) N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [tws_reducedFormula_eq_twsY u hN, Nat.add_sub_cancel]
  simp only [twsY, twsTheta, Bool.false_eq_true, ↓reduceIte, map_mul, map_div₀, map_sub, map_one,
    map_sum, map_pow, twsInv_qParam_twsInvFormula, one_mul]
  have hpre : qParam⁻¹ ^ M * ((1 - qParam⁻¹) / (1 - qParam⁻¹ ^ (M + 1))) =
      (1 - qParam) / (1 - qParam ^ (M + 1)) := by
    have hq0 : qParam ≠ 0 := qParam_ne_zero
    have hne : (1 : RatFunc ℚ) - qParam ^ (M + 1) ≠ 0 := by
      have h := one_sub_qParam_zpow_ne_zero (n := ((M + 1 : ℕ) : ℤ)) (by omega)
      rwa [zpow_natCast] at h
    have hne' : qParam ^ (M + 1) - 1 ≠ 0 := fun h ↦ hne (by rw [← neg_sub, h, neg_zero])
    rw [inv_pow, inv_pow]
    field_simp
    ring
  rw [← mul_assoc (qParam⁻¹ ^ M), hpre, mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Finset.mul_sum]
  refine Eq.trans ?_ (Finset.sum_range_reflect _ _)
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hn hi
  obtain ⟨k, rfl⟩ : ∃ k, M = n + i + k := ⟨M - n - i, by omega⟩
  have e1 : n + i + k + 1 - n - 1 - i = k := by omega
  have e2 : n + i + k + 1 - i - n = k + 1 := by omega
  have e3 : n + i + k + 1 - k - n = i + 1 := by omega
  rw [e1, e2, e3]
  exact inv_term_twsInvFormula (twsInv (u n)) n i k

end AJConjecture
