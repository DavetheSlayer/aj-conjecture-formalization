import Mathlib
import AJConjecture.QAlgCycloKernelMoments
import AJHandoff.TorusQuantum.PairQOddColorRec
import AJHandoff.TorusQuantum.PairQCycloDefectReindex

/-!
# The defect of `T(r, s)` vanishes from `j = r + s + 1` on

`pairQCycloDefect_eq_zero`: with `u = pairQOddColor r s` and `m = rs`, `e_j = 0` for every
`j ≥ r + s + 1` (source: "(Q5) kills the forcing for `j ≥ c = r + s + 1`").

Route (as `torusCycloDefect_eq_zero`). By `pairQ_two_mul_cycloDefect` with the recurrence
`pairQOddColor_rec`, `2 e_j` is `-q` times the bilateral transform of
`(Q - J)(Q^(m-1) q^(m-1) + Q^m q^m) h_(r,s)`, a combination with constant coefficients of
`Q^l h_(r,s)(Q)`, `l ∈ {m-1, m, m+1}`. Each `Q^l h_(r,s)` is a combination of the four
monomials `Q^(l+b)`, `b ∈ {r+s-m, r-s-m, s-r-m, -(r+s+m)}` (the exponents of `pairQForcing`), and
`|l + b| ≤ r + s + 1 ≤ j` for all twelve; the moments vanish by `cycloBilateralSum_zpow_eq_zero`.
-/

noncomputable section

namespace AJConjecture

/-- The bilateral transform is additive. -/
private theorem cycloBilateralSum_add_pairQVanish (f g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ f n + g n) j = cycloBilateralSum f j + cycloBilateralSum g j := by
  simp only [cycloBilateralSum, mul_add, Finset.sum_add_distrib]

/-- The bilateral transform commutes with multiplication by a constant. -/
private theorem cycloBilateralSum_const_mul_pairQVanish (c : RatFunc ℚ) (f : ℤ → RatFunc ℚ)
    (j : ℕ) :
    cycloBilateralSum (fun n ↦ c * f n) j = c * cycloBilateralSum f j := by
  simp only [cycloBilateralSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  ring

/-- The product of a monomial `Q^k` with the forcing term of `T(r, s)`, as a combination of
four monomials `Q^(k + b)`. -/
private theorem zpow_mul_pairQForcing_eq_monomials (r s : ℕ) (k n : ℤ) :
    qParam ^ (n * k) * pairQForcing r s n =
      RatFunc.X ^ (4 * ((r : ℤ) + s - r * s) + 2) /
          (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
          qParam ^ (n * (k + ((r : ℤ) + s - r * s))) +
        (-(RatFunc.X ^ (4 * ((r : ℤ) - s - r * s) - 2) /
            (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) *
            qParam ^ (n * (k + ((r : ℤ) - s - r * s))) +
          (-(RatFunc.X ^ (4 * ((s : ℤ) - r - r * s) - 2) /
              (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) *
              qParam ^ (n * (k + ((s : ℤ) - r - r * s))) +
            RatFunc.X ^ (-4 * ((r : ℤ) + s + r * s) + 2) /
                (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
              qParam ^ (n * (k - ((r : ℤ) + s + r * s))))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have key : ∀ e c b : ℤ, 4 * (n * k) + e = c + 4 * (n * b) →
      RatFunc.X ^ (4 * (n * k)) * RatFunc.X ^ e =
        (RatFunc.X ^ c : RatFunc ℚ) * RatFunc.X ^ (4 * (n * b)) := by
    intro e c b h
    rw [← zpow_add₀ hX, ← zpow_add₀ hX, h]
  have h1 := key (4 * ((r : ℤ) + s - r * s) * (n + 1) + 2) (4 * ((r : ℤ) + s - r * s) + 2)
    (k + ((r : ℤ) + s - r * s)) (by ring)
  have h2 := key (4 * ((r : ℤ) - s - r * s) * (n + 1) - 2) (4 * ((r : ℤ) - s - r * s) - 2)
    (k + ((r : ℤ) - s - r * s)) (by ring)
  have h3 := key (4 * ((s : ℤ) - r - r * s) * (n + 1) - 2) (4 * ((s : ℤ) - r - r * s) - 2)
    (k + ((s : ℤ) - r - r * s)) (by ring)
  have h4 := key (-4 * ((r : ℤ) + s + r * s) * (n + 1) + 2) (-4 * ((r : ℤ) + s + r * s) + 2)
    (k - ((r : ℤ) + s + r * s)) (by ring)
  simp only [qParam_zpow_eq_ratFuncX_zpow, pairQForcing]
  linear_combination (h1 - h2 - h3 + h4) / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))

/-- The bilateral transform of `Q^k h_(r,s)(Q)` vanishes when all four shifted exponents are at
most `j` in absolute value. -/
private theorem cycloBilateralSum_zpow_mul_pairQForcing_eq_zero (r s : ℕ) {j : ℕ} {k : ℤ}
    (h1 : |k + ((r : ℤ) + s - r * s)| ≤ (j : ℤ)) (h2 : |k + ((r : ℤ) - s - r * s)| ≤ (j : ℤ))
    (h3 : |k + ((s : ℤ) - r - r * s)| ≤ (j : ℤ)) (h4 : |k - ((r : ℤ) + s + r * s)| ≤ (j : ℤ)) :
    cycloBilateralSum (fun n ↦ qParam ^ (n * k) * pairQForcing r s n) j = 0 := by
  simp only [zpow_mul_pairQForcing_eq_monomials]
  rw [cycloBilateralSum_add_pairQVanish, cycloBilateralSum_add_pairQVanish,
    cycloBilateralSum_add_pairQVanish, cycloBilateralSum_const_mul_pairQVanish,
    cycloBilateralSum_const_mul_pairQVanish, cycloBilateralSum_const_mul_pairQVanish,
    cycloBilateralSum_const_mul_pairQVanish, cycloBilateralSum_zpow_eq_zero h1,
    cycloBilateralSum_zpow_eq_zero h2, cycloBilateralSum_zpow_eq_zero h3,
    cycloBilateralSum_zpow_eq_zero h4]
  simp only [mul_zero, add_zero]

/-- The bilateral transform of `Q^k h_(r,s)(Q)` vanishes for `rs - 1 ≤ k ≤ rs + 1` and
`j ≥ r + s + 1`. -/
private theorem cycloBilateralSum_zpow_mul_pairQForcing_eq_zero_of_window (r s : ℕ) {j : ℕ}
    (hj : r + s + 1 ≤ j) {k : ℤ} (hlo : (r : ℤ) * s - 1 ≤ k) (hhi : k ≤ (r : ℤ) * s + 1) :
    cycloBilateralSum (fun n ↦ qParam ^ (n * k) * pairQForcing r s n) j = 0 := by
  have hj' : (r : ℤ) + s + 1 ≤ j := by exact_mod_cast hj
  generalize hM : (r : ℤ) * s = M at hlo hhi
  refine cycloBilateralSum_zpow_mul_pairQForcing_eq_zero r s ?_ ?_ ?_ ?_ <;>
    rw [hM, abs_le] <;> constructor <;> omega

/-- The forcing side of the re-indexing identity for `φ = Q^d + Q^(d+1)`, `d + 1 = rs`,
vanishes for `j ≥ r + s + 1`. -/
private theorem cycloBilateralSum_pairQDefect_forcing_eq_zero (r s m d : ℕ) (hd : m = d + 1)
    (hm : (m : ℤ) = r * s) {j : ℕ} (hj : r + s + 1 ≤ j) :
    cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
      (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * (m : ℤ))) *
        pairQForcing r s n) j = 0 := by
  subst hd
  have hq := qParam_ne_zero
  have hd' : (d : ℤ) = r * s - 1 := by push_cast at hm; omega
  have hfun : (fun n : ℤ ↦ (qParam ^ n - qParam ^ j) *
      (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ))) *
        pairQForcing r s n) =
      fun n ↦ qParam ^ (d + 1) * (qParam ^ (n * ((d + 2 : ℕ) : ℤ)) * pairQForcing r s n) +
        ((qParam ^ d - qParam ^ j * qParam ^ (d + 1)) *
            (qParam ^ (n * ((d + 1 : ℕ) : ℤ)) * pairQForcing r s n) +
          -(qParam ^ j * qParam ^ d) * (qParam ^ (n * (d : ℤ)) * pairQForcing r s n)) := by
    funext n
    simp only [zpow_mul, zpow_add_one₀ hq, zpow_natCast]
    ring
  rw [hfun, cycloBilateralSum_add_pairQVanish, cycloBilateralSum_add_pairQVanish,
    cycloBilateralSum_const_mul_pairQVanish, cycloBilateralSum_const_mul_pairQVanish,
    cycloBilateralSum_const_mul_pairQVanish,
    cycloBilateralSum_zpow_mul_pairQForcing_eq_zero_of_window r s hj (by push_cast; omega)
      (by push_cast; omega),
    cycloBilateralSum_zpow_mul_pairQForcing_eq_zero_of_window r s hj (by push_cast; omega)
      (by push_cast; omega),
    cycloBilateralSum_zpow_mul_pairQForcing_eq_zero_of_window r s hj (by omega) (by omega)]
  simp only [mul_zero, add_zero]

/-- The defect of `T(r, s)` vanishes from `j = r + s + 1` on. -/
theorem pairQCycloDefect_eq_zero (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) {j : ℕ}
    (hj : r + s + 1 ≤ j) : pairQCycloDefect (r * s) (pairQOddColor r s) j = 0 := by
  have hm : 1 ≤ r * s := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hrec : ∀ n : ℤ, pairQOddExt (pairQOddColor r s) (n + 1) =
      qParam ^ (-(2 * ((r * s : ℕ) : ℤ) * (n + 1))) * pairQOddExt (pairQOddColor r s) n +
        pairQForcing r s n := by
    intro n
    rw [pairQOddColor_rec r s n, Nat.cast_mul]
  have h2 := pairQ_two_mul_cycloDefect (r * s) hm (pairQOddColor r s) hrec j
  rw [cycloBilateralSum_pairQDefect_forcing_eq_zero r s (r * s) (r * s - 1) (by omega)
    (by push_cast; ring) hj, mul_zero] at h2
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

end AJConjecture
