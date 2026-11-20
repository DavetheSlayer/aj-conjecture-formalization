import Mathlib
import AJHandoff.Geometry.GeoPhysDefs

/-!
# The partial theta sums of `T(a, 2)` at `q = e^{2πi/N}` (Unit PpZ, node `PpZ_ThetaSum`)

Source: Zheng, (4.1) (Morton's formula) for `(p, q) = (a, 2)` and odd colour `c = 2n + 1`.

With `G(m) = e^{πi m²/(4aN)}` (`ppZG`):
* `ppZTheta a N n = ∑_{|k| ≤ n} (G(4ak + a + 2) - G(4ak + a - 2))`;
* `ppZThetaTwo a N n`: the same sum with weights `m²`.
The exponents of `Ĥ_n` are `u_k^± = v_n + (4ak + a ± 2)²/(4a)`, `v_n = -4an(n+1) - (a²+4)/(4a)`,
so `Ĥ_n(e^{πi/N}) = e^{πi v_n/N} Θ` and `q∂_q Ĥ_n = ½ e^{πi v_n/N}(v_n Θ + Θ₂/(4a))` (next node).

`ppZ_cosh_mul_sum`: the generating identity behind (5.5)–(5.6),
`cosh(az) ∑_{|k| ≤ n} (cosh((4ak+a+2)z) - cosh((4ak+a-2)z)) = sinh(2z) sinh(2a(2n+1)z)`.
Route: `cosh(x+2z') - cosh(x-2z') = 2 sinh x sinh 2z'`-type product formulas
(`Complex.cosh_add`, `Complex.sinh_add`): the difference is `2 sinh((4ak+a)z) sinh(2z)`, and
`2 cosh(az) sinh((4ak+a)z) = sinh((4ak+2a)z) + sinh(4akz)`; `∑_{|k|≤n} sinh(4akz) = 0` (odd in
`k`) and `∑_{|k|≤n} sinh(2a(2k+1)z) = sinh(2a(2n+1)z)` (the terms `k` and `-k-1` cancel).
Induction on `n` (`Finset.sum_Icc`-splitting as in `geoZh_hatInput_succ`) is the simplest proof.
-/

noncomputable section

namespace AJConjecture

/-- `G(m) = e^{πi m²/(4aN)}`. -/
def ppZG (a N : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (m : ℂ) ^ 2 / (4 * a * N))

/-- `Θ = ∑_{|k| ≤ n} (G(4ak + a + 2) - G(4ak + a - 2))`. -/
def ppZTheta (a N n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
    (ppZG a N (4 * a * k + a + 2) - ppZG a N (4 * a * k + a - 2))

/-- `Θ₂ = ∑_{|k| ≤ n} ((4ak+a+2)² G(4ak + a + 2) - (4ak+a-2)² G(4ak + a - 2))`. -/
def ppZThetaTwo (a N n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
    (((4 * a * k + a + 2 : ℤ) : ℂ) ^ 2 * ppZG a N (4 * a * k + a + 2) -
      ((4 * a * k + a - 2 : ℤ) : ℂ) ^ 2 * ppZG a N (4 * a * k + a - 2))

/-- `cosh(az) ∑_{|k|≤n} (cosh((4ak+a+2)z) - cosh((4ak+a-2)z)) = sinh(2z) sinh(2a(2n+1)z)`. -/
theorem ppZ_cosh_mul_sum (a n : ℕ) (z : ℂ) :
    Complex.cosh (a * z) * ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (Complex.cosh (((4 * a * k + a + 2 : ℤ) : ℂ) * z) -
          Complex.cosh (((4 * a * k + a - 2 : ℤ) : ℂ) * z)) =
      Complex.sinh (2 * z) * Complex.sinh (2 * a * (2 * n + 1) * z) := by
  induction n with
  | zero =>
    have e1 : (((4 * a * (0 : ℤ) + a + 2 : ℤ) : ℂ)) * z = a * z + 2 * z := by
      push_cast
      ring
    have e2 : (((4 * a * (0 : ℤ) + a - 2 : ℤ) : ℂ)) * z = a * z - 2 * z := by
      push_cast
      ring
    have e3 : 2 * (a : ℂ) * (2 * ((0 : ℕ) : ℂ) + 1) * z = a * z + a * z := by
      push_cast
      ring
    simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton]
    rw [e1, e2]
    rw [Nat.cast_zero] at e3
    rw [e3, Complex.cosh_add, Complex.cosh_sub, Complex.sinh_add]
    ring
  | succ n ih =>
    have hsplit : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1) =
        {-((n : ℤ) + 1), (n : ℤ) + 1} ∪ Finset.Icc (-(n : ℤ)) n := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hdisj : Disjoint ({-((n : ℤ) + 1), (n : ℤ) + 1} : Finset ℤ)
        (Finset.Icc (-(n : ℤ)) n) := by
      rw [Finset.disjoint_left]
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [Finset.mem_Icc]
      omega
    have e1 : (((4 * a * (-((n : ℤ) + 1)) + a + 2 : ℤ) : ℂ)) * z =
        -(4 * a * (n + 1) * z) + a * z + 2 * z := by
      push_cast
      ring
    have e2 : (((4 * a * (-((n : ℤ) + 1)) + a - 2 : ℤ) : ℂ)) * z =
        -(4 * a * (n + 1) * z) + a * z - 2 * z := by
      push_cast
      ring
    have e3 : (((4 * a * ((n : ℤ) + 1) + a + 2 : ℤ) : ℂ)) * z =
        4 * a * (n + 1) * z + a * z + 2 * z := by
      push_cast
      ring
    have e4 : (((4 * a * ((n : ℤ) + 1) + a - 2 : ℤ) : ℂ)) * z =
        4 * a * (n + 1) * z + a * z - 2 * z := by
      push_cast
      ring
    have e5 : 2 * (a : ℂ) * (2 * ((n + 1 : ℕ) : ℂ) + 1) * z =
        4 * a * (n + 1) * z + (a * z + a * z) := by
      push_cast
      ring
    have e6 : 2 * (a : ℂ) * (2 * (n : ℂ) + 1) * z = 4 * a * (n + 1) * z - (a * z + a * z) := by
      ring
    rw [e6] at ih
    rw [e5, Nat.cast_add, Nat.cast_one]
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_pair (by omega), mul_add, ih, e1, e2, e3, e4]
    simp only [Complex.cosh_add, Complex.cosh_sub, Complex.sinh_add, Complex.sinh_sub,
      Complex.cosh_neg, Complex.sinh_neg]
    ring

end AJConjecture
