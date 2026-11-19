import Mathlib
import AJHandoff.Geometry.GeoPhysDefs

/-!
# Proposition 4.1: the reduced sum over `a`-th roots of unity (Unit PpZ, node `PpZ_P41Defs`)

Source: H. Zheng, arXiv:math/0508138v4, Proposition 4.1 and (4.17), for `(p, q) = (a, 2)`.

`A⁺_{a,2}(N, 1) = ∑_{j=1}^{2a-1} e^{-Nj²πi/(4a)} j² sin(jπ/a) sin(jπ/2)` is, up to a unit, the sum

  `R(u) = ∑_{m<a} w_m ζ_a^{u E(m)}`,  `w_m = (a - 1 - 2m)(-1)^m`,  `E(m) = -j(Nj + 4)`, `j = 2m+1`,

with `ζ_a = e^{2πi/a}` and `8u ≡ 1 (mod a)` (`ppZ_zhengA_eq_conjSum`, next node). Only `a`-th roots
of unity and integer weights occur, so the Galois and Fourier arguments of the following nodes
are finite and elementary.

This file: the definitions (`ppZRoot`, `ppZWeight`, `ppZExp`, `ppZConjSum`) and the basic
properties of `ζ_a^r`.
-/

noncomputable section

namespace AJConjecture

/-- `ζ_a^r = exp(2πi r/a)`. -/
def ppZRoot (a : ℕ) (r : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * r / a)

/-- The weight `w_m = (a - 1 - 2m)(-1)^m`. -/
def ppZWeight (a m : ℕ) : ℤ := ((a : ℤ) - 1 - 2 * m) * (-1) ^ m

/-- The exponent `E(m) = -j(Nj + 4)`, `j = 2m + 1`. -/
def ppZExp (N : ℤ) (m : ℕ) : ℤ := -((2 * (m : ℤ) + 1) * (N * (2 * m + 1) + 4))

/-- The conjugate sums `R(u) = ∑_{m<a} w_m ζ_a^{u E(m)}`. -/
def ppZConjSum (a : ℕ) (N u : ℤ) : ℂ :=
  ∑ m ∈ Finset.range a, (ppZWeight a m : ℂ) * ppZRoot a (u * ppZExp N m)

/-- `ζ_a^{r+s} = ζ_a^r ζ_a^s`. -/
theorem ppZRoot_add (a : ℕ) (r s : ℤ) : ppZRoot a (r + s) = ppZRoot a r * ppZRoot a s := by
  simp only [ppZRoot, Int.cast_add, ← Complex.exp_add]
  congr 1
  ring

/-- `ζ_a^{ur} = (ζ_a^u)^r`. -/
theorem ppZRoot_mul (a : ℕ) (u r : ℤ) : ppZRoot a (u * r) = ppZRoot a u ^ r := by
  simp only [ppZRoot, Int.cast_mul, ← Complex.exp_int_mul]
  congr 1
  ring

/-- `ζ_a^r` depends only on `r mod a`. -/
theorem ppZRoot_eq_of_modEq {a : ℕ} (ha : 1 ≤ a) {r s : ℤ} (h : r ≡ s [ZMOD (a : ℤ)]) :
    ppZRoot a r = ppZRoot a s := by
  obtain ⟨k, hk⟩ := h.symm.dvd
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hr : r = s + a * k := by linarith
  have hexp : 2 * Real.pi * Complex.I * ((s + a * k : ℤ) : ℂ) / a =
      2 * Real.pi * Complex.I * (s : ℂ) / a + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [hr, ppZRoot, ppZRoot, hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `‖ζ_a^r‖ = 1`. -/
theorem ppZRoot_norm (a : ℕ) (r : ℤ) : ‖ppZRoot a r‖ = 1 := by
  have hexp : 2 * Real.pi * Complex.I * (r : ℂ) / a =
      ((2 * Real.pi * r / a : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ppZRoot, hexp, Complex.norm_exp_ofReal_mul_I]

/-- For `u` coprime to `a`, `ζ_a^u` is a primitive `a`-th root of unity. -/
theorem ppZRoot_isPrimitiveRoot {a : ℕ} (ha : 1 ≤ a) {u : ℤ} (hu : IsCoprime u (a : ℤ)) :
    IsPrimitiveRoot (ppZRoot a u) a := by
  have h1 : IsPrimitiveRoot (ppZRoot a 1) a := by
    have h := Complex.isPrimitiveRoot_exp a (by omega)
    simpa [ppZRoot] using h
  have h2 := h1.zpow_of_gcd_eq_one u (Int.isCoprime_iff_gcd_eq_one.mp hu)
  rwa [← ppZRoot_mul, one_mul] at h2

end AJConjecture
