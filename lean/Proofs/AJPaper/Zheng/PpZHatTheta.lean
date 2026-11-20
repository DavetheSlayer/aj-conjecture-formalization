import Mathlib
import AJHandoff.Geometry.GeoZhEq516
import AJPaper.Zheng.PpZThetaSum

/-!
# `Ĥ_n` and `q∂_q Ĥ_n` in terms of the theta sums (Unit PpZ, node `PpZ_HatTheta`)

Source: Zheng, (4.1), (5.2); the library's `geoHatInput`, `geoHatInputDeriv`.

With `v_n = -4an(n+1) - (a²+4)/(4a)` and `s = e^{πi/N}`:
* `ppZ_hatInput_eq_theta`: `Ĥ_n(s) = e^{πi v_n/N} Θ`;
* `ppZ_hatInputDeriv_eq_theta`: `q∂_q Ĥ_n = ½ e^{πi v_n/N} (v_n Θ + Θ₂/(4a))`.

Route. `Ĥ_n(s) = ∑_{|k|≤n} (s^{u_k^+} - s^{u_k^-})` with integer exponents
`u_k^± = -4an(n+1) + 2ak(2k+1) ± (4k+1)` (`zpow_add₀`, `geoHalfRoot N ≠ 0`), and
`(4ak + a ± 2)²/(4a) = 4ak² + 2ak ± 4k ± 1 + (a²+4)/(4a)`, so
`s^{u_k^±} = e^{πi u_k^±/N} = e^{πi v_n/N} G(4ak + a ± 2)` (`Complex.exp_int_mul`,
`← Complex.exp_add`, `field_simp; ring` on the exponents; `a, N ≠ 0`). For the derivative:
`(s/2) d/ds s^u = (u/2) s^u` (`hasDerivAt_zpow`, as in `geoZh_norm_hatInputDeriv_le` of
`GeoZhEq516`), and `u_k^± = v_n + m²/(4a)` with `m = 4ak + a ± 2`.
Checked numerically (`kt.py`, errors `< 10⁻¹⁰` relative to `N^{5/2}`).
-/

noncomputable section

namespace AJConjecture

/-- `s^u = e^{πi v_n/N} G(m)` and `u = v_n + m²/(4a)` when `4au = 4a v_n + m²`. -/
private theorem halfRoot_zpow_ppZHatTheta (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) (u m : ℤ)
    (h : 4 * (a : ℤ) * u = -(16 * (a : ℤ) ^ 2 * n * (n + 1)) - ((a : ℤ) ^ 2 + 4) + m ^ 2) :
    geoHalfRoot N ^ u =
        Complex.exp (Real.pi * Complex.I *
          (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N) * ppZG a N m ∧
      (u : ℂ) = -(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a) +
        (m : ℂ) ^ 2 / (4 * a) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hc : 4 * (a : ℂ) * u =
      -(16 * (a : ℂ) ^ 2 * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) + (m : ℂ) ^ 2 := by
    exact_mod_cast h
  have hu : (u : ℂ) = -(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a) +
      (m : ℂ) ^ 2 / (4 * a) := by
    field_simp
    linear_combination hc
  refine ⟨?_, hu⟩
  rw [geoHalfRoot, ← Complex.exp_int_mul, ppZG, ← Complex.exp_add, hu]
  congr 1
  field_simp

/-- `Ĥ_n(s) = ∑_{|k| ≤ n} (s^{u_k^+} - s^{u_k^-})` for `s ≠ 0`. -/
private theorem hatInput_eq_sum_ppZHatTheta (a n : ℕ) {s : ℂ} (hs : s ≠ 0) :
    geoHatInput a n s = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      (s ^ (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) + (4 * k + 1)) -
        s ^ (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) - (4 * k + 1))) := by
  rw [geoHatInput, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 : s ^ (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) + (4 * k + 1)) =
      s ^ (-(4 * (a : ℤ) * n * (n + 1))) * (s ^ (2 * (a : ℤ) * k * (2 * k + 1)) *
        s ^ (4 * k + 1)) := by
    rw [zpow_add₀ hs, zpow_add₀ hs, mul_assoc]
  have h2 : s ^ (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) - (4 * k + 1)) =
      s ^ (-(4 * (a : ℤ) * n * (n + 1))) * (s ^ (2 * (a : ℤ) * k * (2 * k + 1)) *
        s ^ (-(4 * k + 1))) := by
    rw [sub_eq_add_neg, zpow_add₀ hs, zpow_add₀ hs, mul_assoc]
  rw [h1, h2]
  ring

/-- `geoHalfRoot N ≠ 0`. -/
private theorem halfRoot_ne_zero_ppZHatTheta (N : ℕ) : geoHalfRoot N ≠ 0 :=
  Complex.exp_ne_zero _

/-- `Ĥ_n(e^{πi/N}) = e^{πi v_n/N} Θ`, `v_n = -4an(n+1) - (a²+4)/(4a)`. -/
theorem ppZ_hatInput_eq_theta (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    geoHatInput a n (geoHalfRoot N) =
      Complex.exp (Real.pi * Complex.I *
        (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N) * ppZTheta a N n := by
  rw [hatInput_eq_sum_ppZHatTheta a n (halfRoot_ne_zero_ppZHatTheta N), ppZTheta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [(halfRoot_zpow_ppZHatTheta a N n ha hN _ (4 * a * k + a + 2) (by ring)).1,
    (halfRoot_zpow_ppZHatTheta a N n ha hN _ (4 * a * k + a - 2) (by ring)).1]
  exact (mul_sub _ _ _).symm

/-- `q∂_q Ĥ_n = ½ e^{πi v_n/N} (v_n Θ + Θ₂/(4a))`. -/
theorem ppZ_hatInputDeriv_eq_theta (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    geoHatInputDeriv a n N =
      1 / 2 * Complex.exp (Real.pi * Complex.I *
          (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N) *
        ((-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) * ppZTheta a N n +
          ppZThetaTwo a N n / (4 * a)) := by
  have hs : geoHalfRoot N ≠ 0 := halfRoot_ne_zero_ppZHatTheta N
  have hev : geoHatInput a n =ᶠ[nhds (geoHalfRoot N)] fun s ↦
      ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (s ^ (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) + (4 * k + 1)) -
          s ^ (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) - (4 * k + 1))) :=
    (isOpen_ne.eventually_mem hs).mono fun t ht ↦ hatInput_eq_sum_ppZHatTheta a n ht
  have hd := HasDerivAt.fun_sum (u := Finset.Icc (-(n : ℤ)) n) fun k _ ↦
    (hasDerivAt_zpow (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) + (4 * k + 1))
      (geoHalfRoot N) (Or.inl hs)).fun_sub
    (hasDerivAt_zpow (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) - (4 * k + 1))
      (geoHalfRoot N) (Or.inl hs))
  rw [geoHatInputDeriv, hev.deriv_eq, hd.deriv, ppZTheta, ppZThetaTwo, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain ⟨h1, h1'⟩ := halfRoot_zpow_ppZHatTheta a N n ha hN
    (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) + (4 * k + 1))
    (4 * a * k + a + 2) (by ring)
  obtain ⟨h2, h2'⟩ := halfRoot_zpow_ppZHatTheta a N n ha hN
    (-(4 * (a : ℤ) * n * (n + 1)) + 2 * (a : ℤ) * k * (2 * k + 1) - (4 * k + 1))
    (4 * a * k + a - 2) (by ring)
  rw [zpow_sub_one₀ hs, zpow_sub_one₀ hs, h1, h2, h1', h2']
  field_simp
  ring

end AJConjecture
