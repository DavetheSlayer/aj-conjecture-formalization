import Mathlib
import AJPaper.Zheng.PpZP41Prog
import AJPaper.Zheng.PpZP41Geom

/-!
# The restricted sum does not vanish (Unit PpZ, node `PpZ_P41Sum`)

Source: Zheng, (4.24)–(4.25) and the last lines of the proof of Proposition 4.1.

`ppZ_restricted_sum_ne_zero`: for odd `a ≥ 3`,
`∑_{m<a, β ∣ j, α ∣ Nj+2} w_m ζ_a^{a_c E(m)} ≠ 0` (`j = 2m + 1`).

Route. Let `j₁`, `T = a/(αβ)` be as in `ppZ_restricted_progression`, `j = j₁ + 2αβ t`.
* `ppZ_restricted_summand`: since `β ∣ j` and `p' ∣ N`, `E(m) = -4j - Nj² ≡ -4j (mod a_N)`
  (`a_N = β p'` divides `N j²`), hence `ζ_a^{a_c E(m)} = ζ_a^{-4 a_c j}`
  (`ppZRoot_eq_of_modEq`, `a = a_N a_c`), and `ζ_a^{-8 a_c αβ} = ζ_{p'}^{-8α}`. Also
  `(-1)^m = (-1)^{(j₁-1)/2} (-1)^t` (`αβ` odd). So the summand is
  `(-1)^{(j₁-1)/2} ζ_a^{-4 a_c j₁} · (a - j₁ - 2αβ t) · ϱ^t`, `ϱ = -ζ_{p'}^{-8α}`.
* `ϱ^T = -1` (`T` odd, `p' ∣ T`), `ϱ ≠ 1` (`ζ_{p'}^{-8α}` has odd order), `|ϱ| = 1`; apply
  `ppZ_arithGeom_ne_zero` with `c₀ = a - j₁`, `d = 2αβ`, `dT = 2a`: `2c₀ - dT + d = 2(αβ - j₁)`.
* If `j₁ = αβ` and `ϱ = -1`: `ϱ = -1` means `p' ∣ 8α`, so `p' = 1` (`p'` is odd and coprime to
  `α`), i.e. no prime of `a` divides `N`; then `β = 1`, `j₁ = α`, and `α ∣ Nα + 2` gives `α ∣ 2`,
  `α = 1`; but `α = 1` with `p' = 1` forces `a = 1`, against `3 ≤ a`.

Checked numerically for 32 values of `a ≤ 1125` and all/many `N`: closed form to `7·10⁻¹¹`,
`min |sum| = 0.25` (`p41.py`).
-/

noncomputable section

namespace AJConjecture

/-- `ζ_a^d = 1` exactly when `a ∣ d`. -/
private theorem root_eq_one_iff_P41Sum {a : ℕ} (ha : 1 ≤ a) (d : ℤ) :
    ppZRoot a d = 1 ↔ (a : ℤ) ∣ d := by
  have h1 : IsPrimitiveRoot (ppZRoot a 1) a := ppZRoot_isPrimitiveRoot ha isCoprime_one_left
  rw [← h1.zpow_eq_one_iff_dvd, ← ppZRoot_mul, one_mul]

/-- `ζ_{bc}^{bx} = ζ_c^x`. -/
private theorem root_scale_P41Sum {a b c : ℕ} (ha : 1 ≤ a) (h : a = b * c) (x : ℤ) :
    ppZRoot a ((b : ℤ) * x) = ppZRoot c x := by
  subst h
  have hb : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    rintro rfl
    simp at ha)
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    rintro rfl
    simp at ha)
  rw [ppZRoot, ppZRoot]
  congr 1
  push_cast
  field_simp

/-- `a = a_c β p'`. -/
private theorem eq_partC_beta_rad_P41Sum (a : ℕ) (ha : 1 ≤ a) (N : ℤ) :
    a = ppZPartC a N * ppZBeta a N * ppZRad a N := by
  have h := ppZPartN_mul_partC a ha N
  rw [← ppZBeta_mul_rad] at h
  conv_lhs => rw [← h]
  ring

/-- `α T = a_c p'` for `T = a/(αβ)`. -/
private theorem alpha_mul_quot_P41Sum (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) :
    ppZAlpha a N * (a / (ppZAlpha a N * ppZBeta a N)) = ppZPartC a N * ppZRad a N := by
  have hdvd := (ppZ_alpha_beta_quot a ha hodd N).1
  have hβpos : 0 < ppZBeta a N := by
    refine Nat.pos_of_ne_zero fun h ↦ ?_
    rw [h, mul_zero, zero_dvd_iff] at hdvd
    omega
  refine Nat.eq_of_mul_eq_mul_left hβpos ?_
  calc ppZBeta a N * (ppZAlpha a N * (a / (ppZAlpha a N * ppZBeta a N)))
      = ppZAlpha a N * ppZBeta a N * (a / (ppZAlpha a N * ppZBeta a N)) := by ring
    _ = a := Nat.mul_div_cancel' hdvd
    _ = ppZPartC a N * ppZBeta a N * ppZRad a N := eq_partC_beta_rad_P41Sum a ha N
    _ = ppZBeta a N * (ppZPartC a N * ppZRad a N) := by ring

/-- `p'` is odd and positive. -/
private theorem rad_odd_P41Sum (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) :
    Odd (ppZRad a N) :=
  hodd.of_dvd_nat (Dvd.intro_left _ (eq_partC_beta_rad_P41Sum a ha N).symm)

/-- `ϱ^T = -1` for `ϱ = -ζ_{p'}^{-8α}`, `T = a/(αβ)`. -/
private theorem rho_pow_P41Sum (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) :
    (-ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ)))) ^ (a / (ppZAlpha a N * ppZBeta a N)) =
      -1 := by
  have hT := (ppZ_alpha_beta_quot a ha hodd N).2.1
  have h := alpha_mul_quot_P41Sum a ha hodd N
  have h' : ((ppZAlpha a N : ℕ) : ℤ) * ((a / (ppZAlpha a N * ppZBeta a N) : ℕ) : ℤ) =
      (ppZPartC a N : ℤ) * (ppZRad a N : ℤ) := by exact_mod_cast h
  rw [hT.neg_pow, ← zpow_natCast, ← ppZRoot_mul,
    (root_eq_one_iff_P41Sum (rad_odd_P41Sum a ha hodd N).pos _).mpr]
  exact ⟨-(8 * (ppZPartC a N : ℤ)), by linear_combination (-8 : ℤ) * h'⟩

/-- `ϱ ≠ 1` for `ϱ = -ζ_{p'}^{-8α}`. -/
private theorem rho_ne_one_P41Sum (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) :
    -ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ))) ≠ 1 := by
  intro h
  have hpodd := rad_odd_P41Sum a ha hodd N
  have hx : ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ))) = -1 := by
    rw [← h, neg_neg]
  have hpow : ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ))) ^ ppZRad a N = 1 := by
    rw [← zpow_natCast, ← ppZRoot_mul, root_eq_one_iff_P41Sum hpodd.pos]
    exact dvd_mul_left _ _
  rw [hx, hpodd.neg_one_pow] at hpow
  norm_num at hpow

/-- The degenerate case `j₁ = αβ`, `ϱ = -1` does not occur for `a ≥ 3`. -/
private theorem degenerate_false_P41Sum (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) (N : ℤ)
    (h1 : ((ppZAlpha a N : ℕ) : ℤ) ∣ N * ((ppZAlpha a N * ppZBeta a N : ℕ) : ℤ) + 2)
    (h2 : ((ppZRad a N : ℕ) : ℤ) ∣ -(8 * (ppZAlpha a N : ℤ))) : False := by
  have ha1 : 1 ≤ a := by omega
  have hαodd : Odd (ppZAlpha a N) :=
    hodd.of_dvd_nat ((Dvd.intro _ rfl).trans (ppZ_alpha_beta_quot a ha1 hodd N).1)
  have hα2 : ppZAlpha a N ∣ 2 := by
    have h : ((ppZAlpha a N : ℕ) : ℤ) ∣ 2 :=
      (dvd_add_right ⟨N * (ppZBeta a N : ℤ), by push_cast; ring⟩).mp h1
    exact_mod_cast h
  have hα1 : ppZAlpha a N = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.mpr hαodd) hα2
  have hp8 : ppZRad a N ∣ 2 ^ 3 := by
    rw [hα1, dvd_neg] at h2
    exact_mod_cast h2
  have hp1 : ppZRad a N = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr (rad_odd_P41Sum a ha1 hodd N))) hp8
  obtain ⟨ℓ, hℓ, hℓa⟩ := Nat.exists_prime_and_dvd (show a ≠ 1 by omega)
  have hmem : ℓ ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hℓ, hℓa, by omega⟩
  by_cases hN : (ℓ : ℤ) ∣ N
  · have h : ℓ ∣ ppZRad a N :=
      Finset.dvd_prod_of_mem (fun ℓ : ℕ ↦ ℓ) (Finset.mem_filter.mpr ⟨hmem, hN⟩)
    rw [hp1] at h
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h)
  · have h : ℓ ^ ((a.factorization ℓ + 1) / 2) ∣ ppZAlpha a N :=
      Finset.dvd_prod_of_mem (fun ℓ : ℕ ↦ ℓ ^ ((a.factorization ℓ + 1) / 2))
        (Finset.mem_filter.mpr ⟨hmem, hN⟩)
    rw [hα1] at h
    have he : (a.factorization ℓ + 1) / 2 ≠ 0 := by
      have := hℓ.factorization_pos_of_dvd (by omega) hℓa
      omega
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp ((dvd_pow_self ℓ he).trans h))

/-- The summand along the progression `2m + 1 = j₁ + 2αβ t`. -/
theorem ppZ_restricted_summand (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) {j₁ t m : ℕ}
    (hj₁ : Odd j₁) (hβ : ((ppZBeta a N : ℕ) : ℤ) ∣ (j₁ : ℤ))
    (hm : 2 * m + 1 = j₁ + 2 * (ppZAlpha a N * ppZBeta a N) * t) :
    (ppZWeight a m : ℂ) * ppZRoot a ((ppZPartC a N : ℤ) * ppZExp N m) =
      (-1) ^ ((j₁ - 1) / 2) * ppZRoot a (-(4 * (ppZPartC a N : ℤ) * j₁)) *
        ((((a : ℝ) - j₁ : ℝ) : ℂ) - ((2 * (ppZAlpha a N * ppZBeta a N) : ℕ) : ℝ) * t) *
        (-ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ)))) ^ t := by
  obtain ⟨c, hc⟩ := id hj₁
  have hM : Odd (ppZAlpha a N * ppZBeta a N) :=
    hodd.of_dvd_nat (ppZ_alpha_beta_quot a ha hodd N).1
  have hmc : m = c + ppZAlpha a N * ppZBeta a N * t := by
    rw [hc] at hm
    linarith
  have hjc : (j₁ - 1) / 2 = c := by omega
  have hw : (ppZWeight a m : ℂ) = (-1) ^ c *
      ((((a : ℝ) - j₁ : ℝ) : ℂ) - ((2 * (ppZAlpha a N * ppZBeta a N) : ℕ) : ℝ) * t) *
      (-1) ^ t := by
    rw [ppZWeight, hmc, pow_add, pow_mul, hM.neg_one_pow, hc]
    push_cast
    ring
  have hj : 2 * (m : ℤ) + 1 = j₁ + 2 * ((ppZAlpha a N : ℤ) * (ppZBeta a N : ℤ)) * t := by
    exact_mod_cast hm
  have hβj : ((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1 := by
    rw [hj]
    exact dvd_add hβ ⟨2 * (ppZAlpha a N : ℤ) * t, by ring⟩
  have hN' : ((ppZPartN a N : ℕ) : ℤ) ∣ (2 * (m : ℤ) + 1) * N := by
    rw [← ppZBeta_mul_rad, Nat.cast_mul]
    exact mul_dvd_mul hβj (ppZRad_dvd a N)
  have haZ : (a : ℤ) = (ppZPartN a N : ℤ) * (ppZPartC a N : ℤ) := by
    exact_mod_cast (ppZPartN_mul_partC a ha N).symm
  have hmod : (ppZPartC a N : ℤ) * ppZExp N m ≡ -(4 * (ppZPartC a N : ℤ) * j₁) +
      ((ppZPartC a N * ppZBeta a N : ℕ) : ℤ) * (-(8 * (ppZAlpha a N : ℤ)) * t) [ZMOD (a : ℤ)] := by
    obtain ⟨q, hq⟩ := hN'
    rw [Int.modEq_iff_dvd, haZ]
    refine ⟨q * (2 * (m : ℤ) + 1), ?_⟩
    rw [ppZExp]
    push_cast
    linear_combination ((ppZPartC a N : ℤ) * (2 * (m : ℤ) + 1)) * hq +
      4 * (ppZPartC a N : ℤ) * hj
  have hroot : ppZRoot a ((ppZPartC a N : ℤ) * ppZExp N m) =
      ppZRoot a (-(4 * (ppZPartC a N : ℤ) * j₁)) *
        ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ))) ^ t := by
    rw [ppZRoot_eq_of_modEq ha hmod, ppZRoot_add,
      root_scale_P41Sum ha (eq_partC_beta_rad_P41Sum a ha N), ppZRoot_mul, zpow_natCast]
  rw [hw, hroot, hjc, neg_pow (ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ)))) t]
  ring

/-- The restricted sum as an arithmetic–geometric sum along the progression. -/
private theorem restricted_sum_eq_P41Sum (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) {j₁ : ℕ}
    (hj₁ : Odd j₁) (hlt : j₁ < 2 * (ppZAlpha a N * ppZBeta a N))
    (hβ : ((ppZBeta a N : ℕ) : ℤ) ∣ (j₁ : ℤ))
    (hiff : ∀ m : ℕ, m < a →
      ((((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1 ∧
          ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2) ↔
        ∃ t : ℕ, t < a / (ppZAlpha a N * ppZBeta a N) ∧
          2 * m + 1 = j₁ + 2 * (ppZAlpha a N * ppZBeta a N) * t)) :
    (∑ m ∈ Finset.range a,
      if ((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1 ∧
          ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2 then
        (ppZWeight a m : ℂ) * ppZRoot a ((ppZPartC a N : ℤ) * ppZExp N m)
      else 0) =
      (-1) ^ ((j₁ - 1) / 2) * ppZRoot a (-(4 * (ppZPartC a N : ℤ) * j₁)) *
        ∑ t ∈ Finset.range (a / (ppZAlpha a N * ppZBeta a N)),
          ((((a : ℝ) - j₁ : ℝ) : ℂ) - ((2 * (ppZAlpha a N * ppZBeta a N) : ℕ) : ℝ) * t) *
            (-ppZRoot (ppZRad a N) (-(8 * (ppZAlpha a N : ℤ)))) ^ t := by
  obtain ⟨c, hc⟩ := id hj₁
  have hdvd := (ppZ_alpha_beta_quot a ha hodd N).1
  have hMpos : 0 < ppZAlpha a N * ppZBeta a N := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hm2 : ∀ t : ℕ, 2 * (c + ppZAlpha a N * ppZBeta a N * t) + 1 =
      j₁ + 2 * (ppZAlpha a N * ppZBeta a N) * t := by
    intro t
    rw [hc]
    ring
  rw [← Finset.sum_filter, Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun t _ ↦ c + ppZAlpha a N * ppZBeta a N * t) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_range] at ht
    have h1 : ppZAlpha a N * ppZBeta a N * t + ppZAlpha a N * ppZBeta a N ≤ a :=
      calc ppZAlpha a N * ppZBeta a N * t + ppZAlpha a N * ppZBeta a N
          = ppZAlpha a N * ppZBeta a N * (t + 1) := by ring
        _ ≤ ppZAlpha a N * ppZBeta a N * (a / (ppZAlpha a N * ppZBeta a N)) :=
          Nat.mul_le_mul_left _ ht
        _ = a := Nat.mul_div_cancel' hdvd
    have hlt' : c + ppZAlpha a N * ppZBeta a N * t < a := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt', (hiff _ hlt').mpr ⟨t, ht, hm2 t⟩⟩
  · intro t _ t' _ h
    exact Nat.eq_of_mul_eq_mul_left hMpos (Nat.add_left_cancel h)
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨t, ht, hmt⟩ := (hiff m hm.1).mp hm.2
    refine ⟨t, Finset.mem_range.mpr ht, ?_⟩
    have := hm2 t
    omega
  · intro t _
    rw [ppZ_restricted_summand a ha hodd N hj₁ hβ (hm2 t)]
    ring

/-- The restricted sum is nonzero for odd `a ≥ 3`. -/
theorem ppZ_restricted_sum_ne_zero (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) (N : ℤ) :
    (∑ m ∈ Finset.range a,
      if ((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1 ∧
          ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2 then
        (ppZWeight a m : ℂ) * ppZRoot a ((ppZPartC a N : ℤ) * ppZExp N m)
      else 0) ≠ 0 := by
  have ha1 : 1 ≤ a := by omega
  obtain ⟨j₁, hj₁, hlt, hβ, hα, hiff⟩ := ppZ_restricted_progression a ha1 hodd N
  have hdvd := (ppZ_alpha_beta_quot a ha1 hodd N).1
  have hMpos : 0 < ppZAlpha a N * ppZBeta a N := Nat.pos_of_dvd_of_pos hdvd (by omega)
  rw [restricted_sum_eq_P41Sum a ha1 hodd N hj₁ hlt hβ hiff]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _)) ?_
  refine ppZ_arithGeom_ne_zero _ (by rw [norm_neg, ppZRoot_norm]) (rho_ne_one_P41Sum a ha1 hodd N)
    (rho_pow_P41Sum a ha1 hodd N) (Nat.cast_ne_zero.mpr (by omega)) ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hMT : ((ppZAlpha a N * ppZBeta a N : ℕ) : ℝ) *
      ((a / (ppZAlpha a N * ppZBeta a N) : ℕ) : ℝ) = a := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  have hj : j₁ = ppZAlpha a N * ppZBeta a N := by
    have h : (j₁ : ℝ) = ((ppZAlpha a N * ppZBeta a N : ℕ) : ℝ) := by
      push_cast at h1 hMT ⊢
      linarith
    exact_mod_cast h
  have h3 : ((ppZRad a N : ℕ) : ℤ) ∣ -(8 * (ppZAlpha a N : ℤ)) :=
    (root_eq_one_iff_P41Sum (rad_odd_P41Sum a ha1 hodd N).pos _).mp (neg_injective h2)
  rw [hj] at hα
  exact degenerate_false_P41Sum a ha hodd N hα h3

end AJConjecture
