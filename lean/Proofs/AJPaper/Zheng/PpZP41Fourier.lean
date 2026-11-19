import Mathlib
import AJPaper.Zheng.PpZP41Defs

/-!
# Functions on `ℤ/a` with Fourier support on the units (Unit PpZ, node `PpZ_P41Fourier`)

Source: this replaces Zheng's Lemmas 4.2 and 4.3 (traces to `K(ζ_α)`, and linear relations among
`α`-th roots of unity) by finite Fourier analysis.

`PpZUnitSupported a Φ`: `Φ : ℤ → ℂ` is `a`-periodic and, for every prime `ℓ ∣ a`, its sums over
the cosets of `(a/ℓ)ℤ` vanish: `∑_{s<ℓ} Φ(r + s·a/ℓ) = 0` for all `r`.

`ppZ_unitSupported_expansion`: such a `Φ` is a linear combination of the characters
`r ↦ ζ_a^{ur}` with `u` coprime to `a`.

Route. Fourier inversion on `ZMod a` (`ZMod.dft`, `ZMod.dft_dft`, or directly: with
`Φ̂(v) = ∑_{r<a} Φ(r) ζ_a^{-vr}` one has `Φ(r) = a⁻¹ ∑_{v<a} Φ̂(v) ζ_a^{vr}`, from
`∑_{v<a} ζ_a^{v(r-r')} = a·[r ≡ r']`). If `gcd(v, a) > 1` pick a prime `ℓ ∣ gcd(v, a)`; then
`ζ_a^{-v(r + s·a/ℓ)} = ζ_a^{-vr}`, and grouping `r` into cosets of `(a/ℓ)ℤ/a` gives
`ℓ · Φ̂(v) = ∑_{r<a} ζ_a^{-vr} ∑_{s<ℓ} Φ(r + s·a/ℓ) = 0`. Take `φ u = Φ̂(u)/a`.
-/

noncomputable section

namespace AJConjecture

/-- `Φ` is `a`-periodic and its sums over the cosets of `(a/ℓ)ℤ` vanish for every prime `ℓ ∣ a`
(equivalently: the Fourier transform of `Φ` on `ℤ/a` is supported on the units). -/
def PpZUnitSupported (a : ℕ) (Φ : ℤ → ℂ) : Prop :=
  (∀ r : ℤ, Φ (r + a) = Φ r) ∧
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a → ∀ r : ℤ,
      ∑ s ∈ Finset.range ℓ, Φ (r + (s : ℤ) * ((a / ℓ : ℕ) : ℤ)) = 0

/-- A function with period `a` takes equal values at integers congruent modulo `a`. -/
private theorem apply_eq_of_modEq_P41Fourier {a : ℕ} {F : ℤ → ℂ} (hF : ∀ r : ℤ, F (r + a) = F r)
    {r s : ℤ} (h : r ≡ s [ZMOD (a : ℤ)]) : F r = F s := by
  obtain ⟨k, hk⟩ := h.symm.dvd
  have hp : Function.Periodic F (a : ℤ) := hF
  have hr : r = s + k * a := by linarith
  rw [hr]
  exact hp.int_mul k s

/-- The sum of a function with period `a` over a full period does not change under a shift. -/
private theorem sum_range_shift_P41Fourier {a : ℕ} {F : ℤ → ℂ} (hF : ∀ r : ℤ, F (r + a) = F r)
    (t : ℕ) : ∑ r ∈ Finset.range a, F ((r : ℤ) + t) = ∑ r ∈ Finset.range a, F r := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun r : ℕ ↦ F ((r : ℤ) + t)) a
    have h2 := Finset.sum_range_succ' (fun r : ℕ ↦ F ((r : ℤ) + t)) a
    have h3 : F ((a : ℤ) + t) = F (((0 : ℕ) : ℤ) + t) := by
      rw [add_comm (a : ℤ), hF, Nat.cast_zero, zero_add]
    have h4 : ∀ r : ℕ, F ((r : ℤ) + ((t + 1 : ℕ) : ℤ)) = F (((r + 1 : ℕ) : ℤ) + t) := by
      intro r
      congr 1
      push_cast
      ring
    simp only [h4]
    rw [h1, h3] at h2
    exact (add_right_cancel h2).symm

/-- `ζ_a^d = 1` exactly when `a ∣ d`. -/
private theorem root_eq_one_iff_P41Fourier {a : ℕ} (ha : 1 ≤ a) (d : ℤ) :
    ppZRoot a d = 1 ↔ (a : ℤ) ∣ d := by
  have h1 : IsPrimitiveRoot (ppZRoot a 1) a := ppZRoot_isPrimitiveRoot ha isCoprime_one_left
  rw [← h1.zpow_eq_one_iff_dvd, ← ppZRoot_mul, one_mul]

/-- Orthogonality: `∑_{v<a} ζ_a^{vd} = a·[a ∣ d]`. -/
private theorem sum_root_P41Fourier {a : ℕ} (ha : 1 ≤ a) (d : ℤ) :
    ∑ v ∈ Finset.range a, ppZRoot a ((v : ℤ) * d) = if (a : ℤ) ∣ d then (a : ℂ) else 0 := by
  have hpow : ∀ v : ℕ, ppZRoot a ((v : ℤ) * d) = ppZRoot a d ^ v := by
    intro v
    rw [mul_comm, ppZRoot_mul, zpow_natCast]
  simp only [hpow]
  split_ifs with hd
  · rw [(root_eq_one_iff_P41Fourier ha d).mpr hd]
    simp
  · have hne : ppZRoot a d ≠ 1 := fun h ↦ hd ((root_eq_one_iff_P41Fourier ha d).mp h)
    rw [geom_sum_eq hne, ← hpow, (root_eq_one_iff_P41Fourier ha _).mpr (dvd_mul_right _ _),
      sub_self, zero_div]

/-- The finite Fourier transform `Φ̂(v) = ∑_{r<a} Φ(r) ζ_a^{-vr}`. -/
private def fourierCoeff_P41Fourier (a : ℕ) (Φ : ℤ → ℂ) (v : ℕ) : ℂ :=
  ∑ r ∈ Finset.range a, Φ r * ppZRoot a (-((v : ℤ) * r))

/-- Fourier inversion: `∑_{v<a} Φ̂(v) ζ_a^{vr} = a Φ(r)`. -/
private theorem fourier_inversion_P41Fourier {a : ℕ} (ha : 1 ≤ a) {Φ : ℤ → ℂ}
    (hΦ : ∀ r : ℤ, Φ (r + a) = Φ r) (r : ℤ) :
    ∑ v ∈ Finset.range a, fourierCoeff_P41Fourier a Φ v * ppZRoot a ((v : ℤ) * r) =
      (a : ℂ) * Φ r := by
  have ha' : (a : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hterm : ∀ v r' : ℕ, Φ r' * ppZRoot a (-((v : ℤ) * r')) * ppZRoot a ((v : ℤ) * r) =
      Φ r' * ppZRoot a ((v : ℤ) * (r - r')) := by
    intro v r'
    rw [mul_assoc, ← ppZRoot_add]
    congr 2
    ring
  simp only [fourierCoeff_P41Fourier, Finset.sum_mul, hterm]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_root_P41Fourier ha]
  have hmem : (r % (a : ℤ)).toNat ∈ Finset.range a := by
    have := Int.emod_lt_of_pos r (by omega : (0 : ℤ) < a)
    have := Int.emod_nonneg r ha'
    rw [Finset.mem_range]
    omega
  have hcast : (((r % (a : ℤ)).toNat : ℕ) : ℤ) = r % (a : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg r ha')
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · have hd : (a : ℤ) ∣ r - r % (a : ℤ) := Int.modEq_iff_dvd.mp (Int.mod_modEq r a)
    simp only [hcast, hd, ↓reduceIte]
    rw [mul_comm]
    congr 1
    exact apply_eq_of_modEq_P41Fourier hΦ (Int.mod_modEq r a)
  · intro r' hr' hne
    suffices hnd : ¬ (a : ℤ) ∣ r - r' by simp only [hnd, ↓reduceIte, mul_zero]
    intro hdvd
    apply hne
    have h1 : r % (a : ℤ) = (r' : ℤ) % (a : ℤ) := (Int.emod_emod_of_dvd r (dvd_refl _)).symm.trans
      ((Int.emod_emod_of_dvd r (dvd_refl _)).trans ((Int.modEq_iff_dvd.mpr hdvd).symm))
    have h2 : (r' : ℤ) % (a : ℤ) = r' :=
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast Finset.mem_range.mp hr')
    omega

/-- The Fourier coefficient at `v` vanishes when a prime `ℓ` divides both `v` and `a`. -/
private theorem fourierCoeff_eq_zero_P41Fourier {a : ℕ} {Φ : ℤ → ℂ}
    (h : PpZUnitSupported a Φ) (ha : 1 ≤ a) {ℓ v : ℕ} (hℓ : ℓ.Prime) (hℓa : ℓ ∣ a) (hℓv : ℓ ∣ v) :
    fourierCoeff_P41Fourier a Φ v = 0 := by
  obtain ⟨hΦ, hcoset⟩ := h
  set F : ℤ → ℂ := fun r ↦ Φ r * ppZRoot a (-((v : ℤ) * r)) with hF
  have hFper : ∀ r : ℤ, F (r + a) = F r := by
    intro r
    simp only [hF, hΦ]
    congr 1
    refine ppZRoot_eq_of_modEq ha (Int.modEq_iff_dvd.mpr ⟨v, ?_⟩)
    ring
  have hshift : ∀ s : ℕ, ∑ r ∈ Finset.range a, F ((r : ℤ) + (s : ℤ) * ((a / ℓ : ℕ) : ℤ)) =
      fourierCoeff_P41Fourier a Φ v := by
    intro s
    have := sum_range_shift_P41Fourier hFper (s * (a / ℓ))
    rw [Nat.cast_mul] at this
    exact this
  have hroot : ∀ (r : ℤ) (s : ℕ), ppZRoot a (-((v : ℤ) * (r + (s : ℤ) * ((a / ℓ : ℕ) : ℤ)))) =
      ppZRoot a (-((v : ℤ) * r)) := by
    intro r s
    obtain ⟨v', rfl⟩ := hℓv
    refine ppZRoot_eq_of_modEq ha (Int.modEq_iff_dvd.mpr ⟨v' * s, ?_⟩)
    have hmul : ((ℓ : ℕ) : ℤ) * ((a / ℓ : ℕ) : ℤ) = a := by
      exact_mod_cast Nat.mul_div_cancel' hℓa
    simp only [Nat.cast_mul]
    linear_combination ((v' : ℤ) * s) * hmul
  have hsum : (ℓ : ℂ) * fourierCoeff_P41Fourier a Φ v = 0 := by
    rw [← nsmul_eq_mul, ← Finset.card_range ℓ, ← Finset.sum_const,
      ← Finset.sum_congr rfl fun s _ ↦ hshift s, Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ ↦ ?_
    simp only [hF, hroot, ← Finset.sum_mul, hcoset ℓ hℓ hℓa, zero_mul]
  exact (mul_eq_zero.mp hsum).resolve_left (Nat.cast_ne_zero.mpr hℓ.ne_zero)

/-- A unit-supported function is a combination of the characters `r ↦ ζ_a^{ur}`, `gcd(u, a) = 1`. -/
theorem ppZ_unitSupported_expansion (a : ℕ) (ha : 1 ≤ a) (Φ : ℤ → ℂ)
    (h : PpZUnitSupported a Φ) :
    ∃ φ : ℕ → ℂ, ∀ r : ℤ, Φ r =
      ∑ u ∈ (Finset.range a).filter (fun u ↦ Nat.Coprime u a),
        φ u * ppZRoot a ((u : ℤ) * r) := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨fun u ↦ fourierCoeff_P41Fourier a Φ u / a, fun r ↦ ?_⟩
  rw [Finset.sum_filter_of_ne]
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div, fourier_inversion_P41Fourier ha h.1]
    field_simp
  · intro v _ hne
    by_contra hcop
    obtain ⟨ℓ, hℓ, hℓv, hℓa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    exact hne (by simp only [fourierCoeff_eq_zero_P41Fourier h ha hℓ hℓa hℓv, zero_div, zero_mul])

end AJConjecture
