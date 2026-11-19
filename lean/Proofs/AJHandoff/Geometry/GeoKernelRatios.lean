import Mathlib

/-!
# The formal critical equations of the homogeneous kernel (G-KERNEL)

The summand of the coefficient-extraction kernel on the homogeneous companion channel
`v_n = q^{-2an(n+1)}` is, at `q = s²` and `x = q^N`,

  `τ(N, n, z) = s^{2N² - N - 1} z^{-N} (z/x)ⁿ (q;q)_n / ((z;q)_{n+1} (z/x;q)_{n+1}) · v_n`

(`geoKernelTerm`; `z^{-N}` performs the extraction of `[z^{N-1}]` against `dz/z`). Its `q`-shift
ratios in `n`, `z` and `N` are exact rational functions `R_Q, R_z, R_x` of `(s, x, Q, z)`,
`Q = q^n` (`geoRatioQ`, `geoRatioZ`, `geoRatioX`). Their values at `s = 1` are the exponentiated
partial derivatives of the formal dilogarithmic action `S_a` of the source (stationary_bridge):
`d Li₂(v)/d log v = -log(1 - v)` turns each `q`-Pochhammer `(c;q)_n` into the ratio factor
`1 - c Q`. So the formal exponentiated critical equations are `R_Q(1) = R_z(1) = 1`, and the
outer shift is `L = R_x(1)`; with `y = zQ` they read

  `y(1 - Q) = Q^{4a+1}(1 - y)(x - y)`, `xQ(1 - y)(x - y) = (Q - y)(xQ - y)`,
  `L = x² Q (x - y)/(y(xQ - y))`.

Route. Ratios: cancel the common factors of the two `q`-Pochhammer products
(`Finset.prod_range_succ`, `Finset.prod_range_succ'`) and the monomials. The equivalences at
`s = 1` are `field_simp` with the stated nonvanishing.
-/

noncomputable section

namespace AJConjecture

/-- The complex `q`-Pochhammer symbol `(c; q)_m = ∏_{s<m} (1 - c q^s)`. -/
def geoPochC (q c : ℂ) (m : ℕ) : ℂ :=
  ∏ k ∈ Finset.range m, (1 - c * q ^ k)

/-- The homogeneous summand of the coefficient-extraction kernel at `q = s²`, `x = q^N`. -/
def geoKernelTerm (a : ℕ) (s : ℂ) (N n : ℕ) (z : ℂ) : ℂ :=
  s ^ (2 * (N : ℤ) ^ 2 - N - 1) * z ^ (-(N : ℤ)) * (z / s ^ (2 * N)) ^ n *
    geoPochC (s ^ 2) (s ^ 2) n /
      (geoPochC (s ^ 2) z (n + 1) * geoPochC (s ^ 2) (z / s ^ (2 * N)) (n + 1)) *
    (s ^ 2) ^ (-(2 * (a : ℤ) * n * (n + 1)))

/-- The ratio of the `n`-shift: `(z/x)(1 - qQ)/((1 - zqQ)(1 - zqQ/x)) (qQ)^{-4a}`. -/
def geoRatioQ (a : ℕ) (s x Q z : ℂ) : ℂ :=
  z / x * (1 - s ^ 2 * Q) / ((1 - z * s ^ 2 * Q) * (1 - z * s ^ 2 * Q / x)) *
    (s ^ 2 * Q) ^ (-(4 * (a : ℤ)))

/-- The ratio of the `z`-shift `z ↦ qz`: `x⁻¹ Q (1 - z)(1 - z/x)/((1 - zqQ)(1 - zqQ/x))`. -/
def geoRatioZ (s x Q z : ℂ) : ℂ :=
  x⁻¹ * Q * (1 - z) * (1 - z / x) / ((1 - z * s ^ 2 * Q) * (1 - z * s ^ 2 * Q / x))

/-- The ratio of the colour shift `N ↦ N + 1`: `x² s z⁻¹ Q⁻¹ (1 - zQ/x)/(1 - z/(qx))`. -/
def geoRatioX (s x Q z : ℂ) : ℂ :=
  x ^ 2 * s * z⁻¹ * Q⁻¹ * (1 - z * Q / x) / (1 - z / (s ^ 2 * x))

/-- The last factor of a complex `q`-Pochhammer symbol. -/
private theorem geoPochC_succ (q c : ℂ) (m : ℕ) :
    geoPochC q c (m + 1) = geoPochC q c m * (1 - c * q ^ m) :=
  Finset.prod_range_succ _ _

/-- The first factor of a complex `q`-Pochhammer symbol. -/
private theorem geoPochC_succ_left (q c : ℂ) (m : ℕ) :
    geoPochC q c (m + 1) = (1 - c) * geoPochC q (c * q) m := by
  unfold geoPochC
  rw [Finset.prod_range_succ', pow_zero, mul_one, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  ring

/-- A complex `q`-Pochhammer symbol with nonzero factors is nonzero. -/
private theorem geoPochC_ne_zero {q c : ℂ} {m : ℕ} (h : ∀ k < m, 1 - c * q ^ k ≠ 0) :
    geoPochC q c m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k hk ↦ h k (Finset.mem_range.mp hk)

/-- The rational identity behind the `n`-shift. -/
private theorem geo_shiftQ_algebra (K zN w z P Pz Pw q1 E F : ℂ) (n : ℕ) (hPz : Pz ≠ 0)
    (hPw : Pw ≠ 0) (h2 : 1 - w * q1 ≠ 0) :
    K * zN * w ^ (n + 1) * (P * (1 - q1)) / (Pz * (1 - z * q1) * (Pw * (1 - w * q1))) * (E * F) =
      w * (1 - q1) / ((1 - z * q1) * (1 - w * q1)) * F * (K * zN * w ^ n * P / (Pz * Pw) * E) := by
  rw [pow_succ]
  field_simp

/-- The rational identity behind the `z`-shift. -/
private theorem geo_shiftZ_algebra (K xi zN Q w z P Pz Pw q1 E : ℂ) (n : ℕ) (hPz : Pz ≠ 0)
    (hPw : Pw ≠ 0) (h1 : 1 - z * q1 ≠ 0) (h3 : 1 - z ≠ 0) (h4 : 1 - w ≠ 0) :
    K * (xi * zN) * (Q * w ^ n) * P /
        (Pz * (1 - z * q1) / (1 - z) * (Pw * (1 - w * q1) / (1 - w))) * E =
      xi * Q * (1 - z) * (1 - w) / ((1 - z * q1) * (1 - w * q1)) *
        (K * zN * w ^ n * P / (Pz * Pw) * E) := by
  field_simp

/-- The rational identity behind the colour shift. -/
private theorem geo_shiftX_algebra (K S4 zN zi Q w P Pz Pw q1 E : ℂ) (n : ℕ) (hPz : Pz ≠ 0)
    (hPw : Pw ≠ 0) (h1 : 1 - w ≠ 0) (h2 : 1 - w * q1 ≠ 0) (hQ : Q ≠ 0) :
    K * S4 * (zN * zi) * w ^ n * P / (Pz * ((1 - w) * Pw / (1 - w * q1))) * E =
      S4 * zi * Q⁻¹ * (1 - w * q1) / (1 - w) * (K * zN * (w ^ n * Q) * P / (Pz * Pw) * E) := by
  field_simp

/-- The three exact shift identities of the kernel summand. -/
theorem geo_kernelTerm_shifts (a : ℕ) {s z : ℂ} (N n : ℕ) (hs : s ≠ 0) (hz : z ≠ 0)
    (hgen : ∀ m ≤ n + 1, 1 - z * (s ^ 2) ^ m ≠ 0 ∧ 1 - z * (s ^ 2) ^ m / s ^ (2 * N) ≠ 0)
    (hgen' : 1 - z / (s ^ 2 * s ^ (2 * N)) ≠ 0) :
    geoKernelTerm a s N (n + 1) z =
        geoRatioQ a s (s ^ (2 * N)) (s ^ (2 * n)) z * geoKernelTerm a s N n z ∧
      geoKernelTerm a s N n (s ^ 2 * z) =
        geoRatioZ s (s ^ (2 * N)) (s ^ (2 * n)) z * geoKernelTerm a s N n z ∧
      geoKernelTerm a s (N + 1) n z =
        geoRatioX s (s ^ (2 * N)) (s ^ (2 * n)) z * geoKernelTerm a s N n z := by
  have hz1 : ∀ k < n + 2, 1 - z * (s ^ 2) ^ k ≠ 0 := fun k hk ↦ (hgen k (by omega)).1
  have hz2 : ∀ k < n + 2, 1 - z / s ^ (2 * N) * (s ^ 2) ^ k ≠ 0 := fun k hk ↦ by
    rw [div_mul_eq_mul_div]
    exact (hgen k (by omega)).2
  have hA := geoPochC_ne_zero (q := s ^ 2) (m := n + 1) fun k hk ↦ hz1 k (by omega)
  have hB := geoPochC_ne_zero (q := s ^ 2) (m := n + 1) fun k hk ↦ hz2 k (by omega)
  have hA1 := hz1 (n + 1) (by omega)
  have hB1 := hz2 (n + 1) (by omega)
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  refine ⟨?_, ?_, ?_⟩
  · have hpow : (s ^ 2) ^ (-(2 * (a : ℤ) * ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) + 1))) =
        (s ^ 2) ^ (-(2 * (a : ℤ) * (n : ℤ) * ((n : ℤ) + 1))) *
          ((s ^ 2) ^ (n + 1)) ^ (-(4 * (a : ℤ))) := by
      rw [← zpow_natCast (s ^ 2) (n + 1), ← zpow_mul, ← zpow_add₀ hs2]
      congr 1
      push_cast
      ring
    have hP : geoPochC (s ^ 2) (s ^ 2) (n + 1) =
        geoPochC (s ^ 2) (s ^ 2) n * (1 - (s ^ 2) ^ (n + 1)) := by
      rw [geoPochC_succ, ← pow_succ']
    have eR : geoRatioQ a s (s ^ (2 * N)) (s ^ (2 * n)) z =
        z / s ^ (2 * N) * (1 - (s ^ 2) ^ (n + 1)) /
            ((1 - z * (s ^ 2) ^ (n + 1)) * (1 - z / s ^ (2 * N) * (s ^ 2) ^ (n + 1))) *
          ((s ^ 2) ^ (n + 1)) ^ (-(4 * (a : ℤ))) := by
      have hQ : (s ^ 2) ^ (n + 1) = s ^ 2 * s ^ (2 * n) := by ring
      rw [hQ, geoRatioQ]
      ring
    rw [eR, geoKernelTerm, geoKernelTerm, hpow, hP, geoPochC_succ _ z (n + 1),
      geoPochC_succ _ (z / s ^ (2 * N)) (n + 1)]
    exact geo_shiftQ_algebra _ _ _ _ _ _ _ _ _ _ n hA hB hB1
  · have hc : ∀ c : ℂ, (1 - c) * geoPochC (s ^ 2) (c * s ^ 2) (n + 1) =
        geoPochC (s ^ 2) c (n + 1) * (1 - c * (s ^ 2) ^ (n + 1)) := fun c ↦ by
      rw [← geoPochC_succ, geoPochC_succ_left _ c (n + 1)]
    have h0a : 1 - z ≠ 0 := by simpa using hz1 0 (by omega)
    have h0b : 1 - z / s ^ (2 * N) ≠ 0 := by simpa using hz2 0 (by omega)
    have hA' : geoPochC (s ^ 2) (s ^ 2 * z) (n + 1) =
        geoPochC (s ^ 2) z (n + 1) * (1 - z * (s ^ 2) ^ (n + 1)) / (1 - z) := by
      rw [eq_div_iff h0a, ← hc, mul_comm z]
      ring
    have hB' : geoPochC (s ^ 2) (s ^ 2 * z / s ^ (2 * N)) (n + 1) =
        geoPochC (s ^ 2) (z / s ^ (2 * N)) (n + 1) *
          (1 - z / s ^ (2 * N) * (s ^ 2) ^ (n + 1)) / (1 - z / s ^ (2 * N)) := by
      rw [eq_div_iff h0b, ← hc, show s ^ 2 * z / s ^ (2 * N) = z / s ^ (2 * N) * s ^ 2 by ring]
      ring
    have hzpow : (s ^ 2 * z) ^ (-(N : ℤ)) = (s ^ (2 * N))⁻¹ * z ^ (-(N : ℤ)) := by
      rw [mul_zpow, zpow_neg, zpow_natCast, ← pow_mul]
    have hwpow : (s ^ 2 * z / s ^ (2 * N)) ^ n = s ^ (2 * n) * (z / s ^ (2 * N)) ^ n := by
      rw [mul_div_assoc, mul_pow, ← pow_mul]
    have eZ : geoRatioZ s (s ^ (2 * N)) (s ^ (2 * n)) z =
        (s ^ (2 * N))⁻¹ * s ^ (2 * n) * (1 - z) * (1 - z / s ^ (2 * N)) /
          ((1 - z * (s ^ 2) ^ (n + 1)) * (1 - z / s ^ (2 * N) * (s ^ 2) ^ (n + 1))) := by
      rw [geoRatioZ]
      ring
    rw [eZ, geoKernelTerm, geoKernelTerm, hA', hB', hzpow, hwpow]
    exact geo_shiftZ_algebra _ _ _ _ _ _ _ _ _ _ _ n hA hB hA1 h0a h0b
  · have hw : z / s ^ (2 * N) = z / s ^ (2 * (N + 1)) * s ^ 2 := by
      field_simp
      ring
    have hc' : (1 - z / s ^ (2 * (N + 1))) *
        geoPochC (s ^ 2) (z / s ^ (2 * (N + 1)) * s ^ 2) (n + 1) =
        geoPochC (s ^ 2) (z / s ^ (2 * (N + 1))) (n + 1) *
          (1 - z / s ^ (2 * (N + 1)) * (s ^ 2) ^ (n + 1)) := by
      rw [← geoPochC_succ, geoPochC_succ_left _ (z / s ^ (2 * (N + 1))) (n + 1)]
    have h1 : 1 - z / s ^ (2 * (N + 1)) ≠ 0 := by
      rwa [show s ^ (2 * (N + 1)) = s ^ 2 * s ^ (2 * N) by ring]
    have h2 : 1 - z / s ^ (2 * (N + 1)) * (s ^ 2) ^ (n + 1) ≠ 0 := by
      have := hz2 n (by omega)
      rwa [hw, mul_assoc, ← pow_succ'] at this
    have hB' : geoPochC (s ^ 2) (z / s ^ (2 * (N + 1))) (n + 1) =
        (1 - z / s ^ (2 * (N + 1))) * geoPochC (s ^ 2) (z / s ^ (2 * (N + 1)) * s ^ 2) (n + 1) /
          (1 - z / s ^ (2 * (N + 1)) * (s ^ 2) ^ (n + 1)) := by
      rw [eq_div_iff h2, hc']
    have hpow : s ^ (2 * ((N + 1 : ℕ) : ℤ) ^ 2 - ((N + 1 : ℕ) : ℤ) - 1) =
        s ^ (2 * (N : ℤ) ^ 2 - N - 1) * s ^ (4 * N + 1) := by
      rw [← zpow_natCast s (4 * N + 1), ← zpow_add₀ hs]
      congr 1
      push_cast
      ring
    have hzpow : z ^ (-((N + 1 : ℕ) : ℤ)) = z ^ (-(N : ℤ)) * z⁻¹ := by
      rw [← zpow_neg_one, ← zpow_add₀ hz]
      congr 1
      push_cast
      ring
    have eX : geoRatioX s (s ^ (2 * N)) (s ^ (2 * n)) z =
        s ^ (4 * N + 1) * z⁻¹ * ((s ^ 2) ^ n)⁻¹ *
          (1 - z / s ^ (2 * (N + 1)) * (s ^ 2) ^ (n + 1)) / (1 - z / s ^ (2 * (N + 1))) := by
      rw [geoRatioX, show s ^ 2 * s ^ (2 * N) = s ^ (2 * (N + 1)) by ring,
        show z * s ^ (2 * n) / s ^ (2 * N) = z / s ^ (2 * (N + 1)) * (s ^ 2) ^ (n + 1) by
          field_simp
          ring]
      ring
    have hB2 := hB
    rw [hw] at hB2
    rw [eX, geoKernelTerm, geoKernelTerm, hB', hpow, hzpow, hw, mul_pow]
    exact geo_shiftX_algebra _ _ _ _ _ _ _ _ _ _ _ n hA hB2 h1 h2 (pow_ne_zero n hs2)

set_option linter.unusedVariables false in
/-- At `s = 1` the ratios are the source's exponentiated critical equations, with `y = zQ`. -/
theorem geo_critical_equations (a : ℕ) {x Q z : ℂ} (hx : x ≠ 0) (hQ : Q ≠ 0) (hz : z ≠ 0)
    (h1 : 1 - z * Q ≠ 0) (h2 : x - z * Q ≠ 0) (h3 : x - z ≠ 0) (h4 : x * Q - z * Q ≠ 0) :
    (geoRatioQ a 1 x Q z = 1 ↔
        z * Q * (1 - Q) = Q ^ (4 * a + 1) * (1 - z * Q) * (x - z * Q)) ∧
      (geoRatioZ 1 x Q z = 1 ↔
        x * Q * (1 - z * Q) * (x - z * Q) - (Q - z * Q) * (x * Q - z * Q) = 0) ∧
      geoRatioX 1 x Q z = x ^ 2 * Q * (x - z * Q) / (z * Q * (x * Q - z * Q)) := by
  have hQa : (Q : ℂ) ^ (-(4 * (a : ℤ))) = (Q ^ (4 * a))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast]
    push_cast
    rfl
  have eQ : geoRatioQ a 1 x Q z =
      z * Q * (1 - Q) / (Q ^ (4 * a + 1) * (1 - z * Q) * (x - z * Q)) := by
    simp only [geoRatioQ, one_pow, one_mul]
    rw [hQa]
    field_simp
    ring
  have eZ : geoRatioZ 1 x Q z = Q * (1 - z) * (x - z) / (x * (1 - z * Q) * (x - z * Q)) := by
    simp only [geoRatioZ, one_pow]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [eQ, div_eq_one_iff_eq (by positivity)]
  · rw [eZ, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hx h1) h2)]
    constructor
    · intro h
      linear_combination (-Q) * h
    · intro h
      have h' : Q * (x * (1 - z * Q) * (x - z * Q) - Q * (1 - z) * (x - z)) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hQ
      · linear_combination -h''
  · simp only [geoRatioX, one_pow, one_mul, mul_one]
    field_simp

end AJConjecture
