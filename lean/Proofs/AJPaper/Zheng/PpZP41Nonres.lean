import Mathlib

/-!
# A class that the quadratic exponent never reaches (Unit PpZ, node `PpZ_P41Nonres`)

Source: Zheng, Lemma 4.4 ("the congruence `x² ≡ -kNα^{l-1} mod α^l` has no solution for some
`0 < k < α`").

* `ppZ_exists_nonresidue_shift`: for an odd prime `ℓ ∤ N` there is `k` with
  `ℓ ∤ y² + Nk` for all `y` (take `-Nk` a quadratic non-residue mod `ℓ`:
  `FiniteField.exists_nonsquare` in `ZMod ℓ`, `ringChar (ZMod ℓ) = ℓ ≠ 2`, and `N` is a unit).
* `ppZ_not_pow_dvd_sq_add`: then `ℓ^e ∤ y² + N k ℓ^{e-1}` for all `y`, `e ≥ 1`. Indeed, if
  `ℓ^e ∣ y² + Nkℓ^{e-1}` then `ℓ^{e-1} ∣ y²`. If `ℓ^e ∣ y²`, then `ℓ ∣ Nk`, against the choice of
  `k` at `y = 0`. Otherwise the `ℓ`-adic valuation of `y²` is exactly `e - 1`, so `e - 1` is even,
  `y = ℓ^{(e-1)/2} y'`, and `ℓ ∣ y'² + Nk`: contradiction.
-/

noncomputable section

namespace AJConjecture

/-- For an odd prime `ℓ ∤ N` there is `k` such that `y² + Nk` is never divisible by `ℓ`. -/
theorem ppZ_exists_nonresidue_shift {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) {N : ℤ}
    (hN : ¬ (ℓ : ℤ) ∣ N) : ∃ k : ℤ, ∀ y : ℤ, ¬ (ℓ : ℤ) ∣ y ^ 2 + N * k := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod ℓ) (by rwa [ZMod.ringChar_zmod_n])
  have hN' : (N : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((-c / (N : ZMod ℓ)).val : ℤ), fun y hy ↦ hc ⟨(y : ZMod ℓ), ?_⟩⟩
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr hy
  have hmul : (N : ZMod ℓ) * (-c / (N : ZMod ℓ)) = -c := by field_simp
  push_cast at h
  rw [ZMod.natCast_zmod_val, hmul] at h
  linear_combination -h

/-- If `ℓ ∤ y² + Nk` for all `y`, then `ℓ^e ∤ y² + N k ℓ^{e-1}` for all `y`. -/
theorem ppZ_not_pow_dvd_sq_add {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e) {N k : ℤ}
    (hk : ∀ y : ℤ, ¬ (ℓ : ℤ) ∣ y ^ 2 + N * k) (y : ℤ) :
    ¬ ((ℓ : ℤ) ^ e ∣ y ^ 2 + N * k * (ℓ : ℤ) ^ (e - 1)) := by
  induction e using Nat.strong_induction_on generalizing y with
  | _ e ih =>
  intro h
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  obtain rfl | he1 := eq_or_lt_of_le he
  · rw [pow_one, Nat.sub_self, pow_zero, mul_one] at h
    exact hk y h
  have hy : (ℓ : ℤ) ∣ y := by
    have h1 : (ℓ : ℤ) ∣ y ^ 2 + N * k * (ℓ : ℤ) ^ (e - 1) := (dvd_pow_self _ (by omega)).trans h
    have h2 : (ℓ : ℤ) ∣ N * k * (ℓ : ℤ) ^ (e - 1) :=
      Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    exact hp.dvd_of_dvd_pow ((dvd_add_left h2).mp h1)
  obtain ⟨y', rfl⟩ := hy
  obtain rfl | he2 := eq_or_lt_of_le (show 2 ≤ e from he1)
  · apply hk 0
    have h3 : (ℓ : ℤ) ^ 2 ∣ ((ℓ : ℤ) * y') ^ 2 := ⟨y' ^ 2, by ring⟩
    have h4 : (ℓ : ℤ) * (ℓ : ℤ) ∣ N * k * (ℓ : ℤ) := by
      have := (dvd_add_right h3).mp h
      rwa [pow_two, show 2 - 1 = 1 from rfl, pow_one] at this
    have h5 := (mul_dvd_mul_iff_right hp.ne_zero).mp h4
    rwa [zero_pow two_ne_zero, zero_add]
  · refine ih (e - 2) (by omega) (by omega) y' ?_
    have h3 : (ℓ : ℤ) ^ 2 * (ℓ : ℤ) ^ (e - 2) ∣
        (ℓ : ℤ) ^ 2 * (y' ^ 2 + N * k * (ℓ : ℤ) ^ (e - 2 - 1)) := by
      convert h using 1
      · rw [← pow_add]
        congr 1
        omega
      · have he3 : e - 1 = (e - 2 - 1) + 2 := by omega
        rw [he3, pow_add]
        ring
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hp.ne_zero)).mp h3

end AJConjecture
