import Mathlib
import AJPaper.Zheng.PpZP41Arith

/-!
# Divisibility by `α` and `β` (Unit PpZ, node `PpZ_P41Arith2`)

Source: Zheng, (4.20)–(4.22).

* `ppZAlpha_dvd_iff`: `α ∣ y ↔ ∀ ℓ ∤ N, ℓ^{e_ℓ} ∣ y²` (`ℓ^e ∣ y² ↔ ℓ^{⌈e/2⌉} ∣ y`, by valuations:
  `padicValInt` or `Nat.Prime.pow_dvd_iff_le_factorization` on `y.natAbs`; the factors
  `ℓ^{⌈e/2⌉}` are pairwise coprime, `Finset.prod_dvd_of_coprime` / `Nat.Coprime.prod_dvd`).
* `ppZBeta_dvd_iff`: `β ∣ y ↔ ∀ ℓ ∣ N, ℓ^{e_ℓ - 1} ∣ y`.
* `ppZBeta_dvd_exp_iff`: for odd `a`, `β ∣ E(m) ↔ β ∣ 2m + 1`: `E(m) = -j(Nj + 4)` and, for a
  prime `ℓ ∣ N` of the odd number `a`, `ℓ ∤ Nj + 4`, so `ℓ^{e-1} ∣ j(Nj+4) ↔ ℓ^{e-1} ∣ j`.
* `ppZ_alpha_beta_quot`: `αβ ∣ a`, the quotient `T = a/(αβ)` is odd, `gcd(α, β) = 1`.
-/

noncomputable section

namespace AJConjecture

/-- Divisibility by a product of prime powers (distinct primes) is divisibility by each. -/
private theorem prod_prime_pow_dvd_iff_P41Arith2 (s : Finset ℕ) (hs : ∀ ℓ ∈ s, ℓ.Prime)
    (f : ℕ → ℕ) (y : ℤ) :
    ((∏ ℓ ∈ s, ℓ ^ f ℓ : ℕ) : ℤ) ∣ y ↔ ∀ ℓ ∈ s, (ℓ : ℤ) ^ f ℓ ∣ y := by
  simp only [Nat.cast_prod, Nat.cast_pow]
  refine ⟨fun h ℓ hℓ ↦ (Finset.dvd_prod_of_mem _ hℓ).trans h,
    fun h ↦ Finset.prod_dvd_of_coprime (fun p hp q hq hpq ↦ ?_) h⟩
  refine IsCoprime.pow (Nat.isCoprime_iff_coprime.mpr ?_)
  exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq

/-- `ℓ^e ∣ y² ↔ ℓ^{⌈e/2⌉} ∣ y` for a prime `ℓ`. -/
private theorem prime_pow_dvd_sq_iff_P41Arith2 {ℓ : ℕ} (hℓ : ℓ.Prime) (e : ℕ) (y : ℤ) :
    (ℓ : ℤ) ^ e ∣ y ^ 2 ↔ (ℓ : ℤ) ^ ((e + 1) / 2) ∣ y := by
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  constructor
  · intro h
    rw [pow_dvd_iff_le_emultiplicity, emultiplicity_pow hp] at h
    rw [pow_dvd_iff_le_emultiplicity]
    generalize emultiplicity (ℓ : ℤ) y = m at h ⊢
    induction m using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      norm_cast at h ⊢
      omega
  · intro h
    refine dvd_trans (pow_dvd_pow _ (by omega : e ≤ (e + 1) / 2 * 2)) ?_
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd h 2

/-- `α ∣ a_c`. -/
theorem ppZAlpha_dvd_partC (a : ℕ) (N : ℤ) : ppZAlpha a N ∣ ppZPartC a N := by
  refine Finset.prod_dvd_prod_of_dvd _ _ fun ℓ _ ↦ pow_dvd_pow _ (by omega)

/-- `α ∣ y ↔ ℓ^{e_ℓ} ∣ y²` for every prime `ℓ ∣ a`, `ℓ ∤ N`. -/
theorem ppZAlpha_dvd_iff (a : ℕ) (N y : ℤ) :
    ((ppZAlpha a N : ℕ) : ℤ) ∣ y ↔
      ∀ ℓ ∈ a.primeFactors, ¬ (ℓ : ℤ) ∣ N → (ℓ : ℤ) ^ a.factorization ℓ ∣ y ^ 2 := by
  rw [ppZAlpha, prod_prime_pow_dvd_iff_P41Arith2 _
    (fun ℓ hℓ ↦ Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hℓ).1)]
  simp only [Finset.mem_filter, and_imp]
  refine forall₃_congr fun ℓ hℓ _ ↦ ?_
  rw [prime_pow_dvd_sq_iff_P41Arith2 (Nat.prime_of_mem_primeFactors hℓ)]

/-- `β ∣ y ↔ ℓ^{e_ℓ - 1} ∣ y` for every prime `ℓ ∣ a`, `ℓ ∣ N`. -/
theorem ppZBeta_dvd_iff (a : ℕ) (N y : ℤ) :
    ((ppZBeta a N : ℕ) : ℤ) ∣ y ↔
      ∀ ℓ ∈ a.primeFactors, (ℓ : ℤ) ∣ N → (ℓ : ℤ) ^ (a.factorization ℓ - 1) ∣ y := by
  rw [ppZBeta, prod_prime_pow_dvd_iff_P41Arith2 _
    (fun ℓ hℓ ↦ Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hℓ).1)]
  simp only [Finset.mem_filter, and_imp]

/-- For odd `a`: `β ∣ E(m) ↔ β ∣ 2m + 1`. -/
theorem ppZBeta_dvd_exp_iff (a : ℕ) (hodd : Odd a) (N : ℤ) (m : ℕ) :
    ((ppZBeta a N : ℕ) : ℤ) ∣ ppZExp N m ↔ ((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1 := by
  rw [ppZBeta_dvd_iff, ppZBeta_dvd_iff]
  refine forall₃_congr fun ℓ hℓ hℓN ↦ ?_
  obtain ⟨hp, hdvd, -⟩ := Nat.mem_primeFactors.mp hℓ
  have hcop : IsCoprime ((ℓ : ℤ) ^ (a.factorization ℓ - 1)) (N * (2 * (m : ℤ) + 1) + 4) := by
    refine IsCoprime.pow_left
      ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr fun h ↦ ?_)
    have h4 : (ℓ : ℤ) ∣ 4 := (dvd_add_right (hℓN.mul_right _)).mp h
    have h4' : ℓ ∣ 2 ^ 2 := by exact_mod_cast h4
    have h2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4')
    subst h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  rw [ppZExp, dvd_neg]
  exact ⟨fun h ↦ hcop.dvd_of_dvd_mul_right h, fun h ↦ h.mul_right _⟩

/-- `αβ ∣ a`, the quotient `a/(αβ)` is odd, and `gcd(α, β) = 1`. -/
theorem ppZ_alpha_beta_quot (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) :
    ppZAlpha a N * ppZBeta a N ∣ a ∧ Odd (a / (ppZAlpha a N * ppZBeta a N)) ∧
      Nat.Coprime (ppZAlpha a N) (ppZBeta a N) := by
  have hα := ppZAlpha_dvd_partC a N
  have hβ : ppZBeta a N ∣ ppZPartN a N := ⟨_, (ppZBeta_mul_rad a N).symm⟩
  have hmul : ppZAlpha a N * ppZBeta a N ∣ a := by
    have h := mul_dvd_mul hα hβ
    rwa [mul_comm (ppZPartC a N), ppZPartN_mul_partC a ha N] at h
  refine ⟨hmul, ?_, ((ppZPartN_coprime_partC a N).symm.coprime_dvd_left hα).coprime_dvd_right hβ⟩
  have h := Nat.div_mul_cancel hmul
  rw [← h] at hodd
  exact (Nat.odd_mul.mp hodd).1

end AJConjecture
