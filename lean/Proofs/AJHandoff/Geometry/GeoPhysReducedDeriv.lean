import Mathlib
import AJHandoff.Geometry.GeoPhysDefs

/-!
# Logarithmic derivatives of Zheng's clasp summand (G-PHYS)

The summand `c_{n,i}(t) = t^m ∏_{r=1}^{n} (1 - t^{4(i+r)})(1 - t^{4(N-i-r)})/(1 - t^{4r})`,
`m = 4N² - 2N - 2 - 4N(n+i)`, has derivative `(4/t₀)(m/4 + ∑_r (β_{i+r} + β_{N-i-r} - β_r)) c(t₀)`
at every `t₀ ≠ 0` with `t₀^{4k} ≠ 1` for `1 ≤ k < N`, where `β_k = k/(1 - q₀^{-k})`, `q₀ = t₀⁴`
(`geo_hasDerivAt_claspSummand`). All statements are in "logarithmic" form
`HasDerivAt f (α · f t₀) t₀`, which is closed under products and quotients.
-/

noncomputable section

namespace AJConjecture

/-- Logarithmic derivatives add over finite products. -/
theorem geo_hasDerivAt_finset_prod_logDeriv {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (α : ι → ℂ) {t₀ : ℂ} (h : ∀ j ∈ s, HasDerivAt (f j) (α j * f j t₀) t₀) :
    HasDerivAt (fun t ↦ ∏ j ∈ s, f j t) ((∑ j ∈ s, α j) * ∏ j ∈ s, f j t₀) t₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const t₀ (1 : ℂ)
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj, Finset.sum_insert hj]
    have hm := (h j (Finset.mem_insert_self j s)).mul
      (ih fun k hk ↦ h k (Finset.mem_insert_of_mem hk))
    convert hm using 1
    ring

/-- Logarithmic derivative of a quotient. -/
theorem geo_hasDerivAt_div_logDeriv {f g : ℂ → ℂ} {α γ t₀ : ℂ}
    (hf : HasDerivAt f (α * f t₀) t₀) (hg : HasDerivAt g (γ * g t₀) t₀) (hg0 : g t₀ ≠ 0) :
    HasDerivAt (fun t ↦ f t / g t) ((α - γ) * (f t₀ / g t₀)) t₀ := by
  convert hf.div hg hg0 using 1
  field_simp

/-- Logarithmic derivative of a product of two functions. -/
theorem geo_hasDerivAt_mul_logDeriv {f g : ℂ → ℂ} {α γ t₀ : ℂ}
    (hf : HasDerivAt f (α * f t₀) t₀) (hg : HasDerivAt g (γ * g t₀) t₀) :
    HasDerivAt (fun t ↦ f t * g t) ((α + γ) * (f t₀ * g t₀)) t₀ := by
  convert hf.mul hg using 1
  ring

/-- Logarithmic derivative of an integer power. -/
theorem geo_hasDerivAt_zpow_logDeriv {t₀ : ℂ} (ht₀ : t₀ ≠ 0) (m : ℤ) :
    HasDerivAt (fun t ↦ t ^ m) (4 / t₀ * ((m : ℂ) / 4) * t₀ ^ m) t₀ := by
  convert hasDerivAt_zpow m t₀ (Or.inl ht₀) using 1
  rw [zpow_sub_one₀ ht₀]
  field_simp

/-- Logarithmic derivative of `1 - t^{4k}`, with `β_k = k/(1 - q₀^{-k})`. -/
theorem geo_hasDerivAt_one_sub_pow_logDeriv {t₀ : ℂ} (ht₀ : t₀ ≠ 0) (k : ℕ)
    (hk : (t₀ ^ 4) ^ k ≠ 1) :
    HasDerivAt (fun t ↦ 1 - t ^ (4 * k))
      (4 / t₀ * ((k : ℂ) / (1 - (t₀ ^ 4) ^ (-(k : ℤ)))) * (1 - t₀ ^ (4 * k))) t₀ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
    rcases k with _ | k
    · simp at hk
    · omega⟩
  have hw : (t₀ ^ 4) ^ (j + 1) - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hw0 : (t₀ ^ 4) ^ (j + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ ht₀)
  convert ((hasDerivAt_pow (4 * (j + 1)) t₀).const_sub 1) using 1
  rw [zpow_neg, zpow_natCast, show 4 * (j + 1) - 1 = 4 * j + 3 by omega,
    show 1 - ((t₀ ^ 4) ^ (j + 1))⁻¹ = ((t₀ ^ 4) ^ (j + 1) - 1) / (t₀ ^ 4) ^ (j + 1) by
      field_simp]
  rw [pow_mul] at *
  field_simp
  push_cast
  ring

/-- `β_k = k/(1 - q^{-k})`, the logarithmic `q`-derivative of `1 - q^k`. -/
def geoBeta (q : ℂ) (k : ℕ) : ℂ :=
  (k : ℂ) / (1 - q ^ (-(k : ℤ)))

/-- Zheng's clasp summand `t^m ∏_{r=1}^{n} (1 - t^{4(i+r)})(1 - t^{4(N-i-r)})/(1 - t^{4r})`. -/
def geoClaspSummand (N n i : ℕ) (t : ℂ) : ℂ :=
  t ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i)) *
    ∏ r ∈ Finset.Icc 1 n,
      ((1 - t ^ (4 * (i + r))) * (1 - t ^ (4 * (N - i - r))) / (1 - t ^ (4 * r)))

/-- The logarithmic derivative of Zheng's clasp summand. -/
theorem geo_hasDerivAt_claspSummand {N n i : ℕ} (h : n + i < N) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    (hq : ∀ k ∈ Finset.Icc 1 (N - 1), (t₀ ^ 4) ^ k ≠ 1) :
    HasDerivAt (geoClaspSummand N n i)
      (4 / t₀ * ((((4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i) : ℤ)) : ℂ) / 4 +
        ∑ r ∈ Finset.Icc 1 n,
          (geoBeta (t₀ ^ 4) (i + r) + geoBeta (t₀ ^ 4) (N - i - r) - geoBeta (t₀ ^ 4) r)) *
        geoClaspSummand N n i t₀) t₀ := by
  have hfac : ∀ r ∈ Finset.Icc 1 n,
      HasDerivAt (fun t ↦ (1 - t ^ (4 * (i + r))) * (1 - t ^ (4 * (N - i - r))) /
          (1 - t ^ (4 * r)))
        (4 / t₀ * (geoBeta (t₀ ^ 4) (i + r) + geoBeta (t₀ ^ 4) (N - i - r) -
            geoBeta (t₀ ^ 4) r) *
          ((1 - t₀ ^ (4 * (i + r))) * (1 - t₀ ^ (4 * (N - i - r))) / (1 - t₀ ^ (4 * r)))) t₀ := by
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    have h1 := geo_hasDerivAt_one_sub_pow_logDeriv ht₀ (i + r)
      (hq _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    have h2 := geo_hasDerivAt_one_sub_pow_logDeriv ht₀ (N - i - r)
      (hq _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    have h3r := hq r (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h3 := geo_hasDerivAt_one_sub_pow_logDeriv ht₀ r h3r
    have hne : 1 - t₀ ^ (4 * r) ≠ 0 := by
      rw [pow_mul]
      exact sub_ne_zero.mpr (Ne.symm h3r)
    convert geo_hasDerivAt_div_logDeriv (geo_hasDerivAt_mul_logDeriv h1 h2) h3 hne using 1
    simp only [geoBeta]
    ring
  have hprod := geo_hasDerivAt_finset_prod_logDeriv _ _ _ hfac
  refine (geo_hasDerivAt_mul_logDeriv (geo_hasDerivAt_zpow_logDeriv ht₀
    (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i))) hprod).congr_deriv ?_
  rw [← Finset.mul_sum, geoClaspSummand]
  ring

end AJConjecture
