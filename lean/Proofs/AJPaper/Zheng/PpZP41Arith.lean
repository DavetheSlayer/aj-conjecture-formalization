import Mathlib
import AJPaper.Zheng.PpZP41Defs

/-!
# The arithmetic data of the reduction (Unit PpZ, node `PpZ_P41Arith`)

Source: Zheng, (4.16) and (4.20). Write `a = ∏ ℓ^{e_ℓ}` and split the primes of `a` into those
dividing `N` (Zheng's `β_i`) and those not dividing `N` (Zheng's `α_i`):

* `ppZPartN a N = ∏_{ℓ ∣ N} ℓ^{e_ℓ}`, `ppZPartC a N = ∏_{ℓ ∤ N} ℓ^{e_ℓ}` (so `a = a_N a_c`);
* `ppZAlpha a N = ∏_{ℓ ∤ N} ℓ^{⌈e_ℓ/2⌉}` (Zheng's `α`);
* `ppZBeta a N = ∏_{ℓ ∣ N} ℓ^{e_ℓ - 1}` (Zheng's `β`), `ppZRad a N = ∏_{ℓ ∣ N} ℓ` (Zheng's `p'`).

Route. `Nat.factorization_prod_pow_eq_self`, `Finset.prod_filter_mul_prod_filter_not`,
`Nat.Coprime.prod_left/right`, `Nat.Prime.dvd_of_dvd_pow`; for `ppZRad_dvd` a product of distinct
primes each dividing `N` divides `N` (`Finset.prod_primes_dvd` or `Nat.prod_primeFactors_dvd`
after reducing to `N.natAbs`; for `N = 0` trivial).
-/

noncomputable section

namespace AJConjecture

/-- The part of `a` supported on the primes dividing `N`. -/
def ppZPartN (a : ℕ) (N : ℤ) : ℕ :=
  ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ (ℓ : ℤ) ∣ N), ℓ ^ a.factorization ℓ

/-- The part of `a` supported on the primes not dividing `N`. -/
def ppZPartC (a : ℕ) (N : ℤ) : ℕ :=
  ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N), ℓ ^ a.factorization ℓ

/-- Zheng's `α = ∏_{ℓ ∤ N} ℓ^{⌈e_ℓ/2⌉}`. -/
def ppZAlpha (a : ℕ) (N : ℤ) : ℕ :=
  ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N), ℓ ^ ((a.factorization ℓ + 1) / 2)

/-- Zheng's `β = ∏_{ℓ ∣ N} ℓ^{e_ℓ - 1}`. -/
def ppZBeta (a : ℕ) (N : ℤ) : ℕ :=
  ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ (ℓ : ℤ) ∣ N), ℓ ^ (a.factorization ℓ - 1)

/-- Zheng's `p' = ∏_{ℓ ∣ N} ℓ`. -/
def ppZRad (a : ℕ) (N : ℤ) : ℕ :=
  ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ (ℓ : ℤ) ∣ N), ℓ

/-- `a = a_N · a_c`. -/
theorem ppZPartN_mul_partC (a : ℕ) (ha : 1 ≤ a) (N : ℤ) : ppZPartN a N * ppZPartC a N = a := by
  have ha0 : a ≠ 0 := by omega
  rw [ppZPartN, ppZPartC, Finset.prod_filter_mul_prod_filter_not,
    ← Nat.prod_factorization_eq_prod_primeFactors]
  exact Nat.prod_factorization_pow_eq_self ha0

/-- `a_N` and `a_c` are coprime. -/
theorem ppZPartN_coprime_partC (a : ℕ) (N : ℤ) : Nat.Coprime (ppZPartN a N) (ppZPartC a N) := by
  refine Nat.Coprime.prod_left fun p hp ↦ Nat.Coprime.prod_right fun q hq ↦ ?_
  rw [Finset.mem_filter] at hp hq
  refine Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1)
    (Nat.prime_of_mem_primeFactors hq.1)).mpr ?_)
  rintro rfl
  exact hq.2 hp.2

/-- `a_N = β · p'`. -/
theorem ppZBeta_mul_rad (a : ℕ) (N : ℤ) : ppZBeta a N * ppZRad a N = ppZPartN a N := by
  rw [ppZBeta, ppZRad, ppZPartN, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ℓ hℓ ↦ ?_
  obtain ⟨hp, hdvd, ha0⟩ := Nat.mem_primeFactors.mp (Finset.mem_filter.mp hℓ).1
  have hpos : 0 < a.factorization ℓ := hp.factorization_pos_of_dvd ha0 hdvd
  rw [← pow_succ, Nat.sub_add_cancel hpos]

/-- `p' ∣ N`. -/
theorem ppZRad_dvd (a : ℕ) (N : ℤ) : ((ppZRad a N : ℕ) : ℤ) ∣ N := by
  rw [Int.natCast_dvd, ppZRad]
  refine Finset.prod_primes_dvd _ (fun ℓ hℓ ↦ ?_) (fun ℓ hℓ ↦ ?_)
  · exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hℓ).1).prime
  · exact Int.natCast_dvd.mp (Finset.mem_filter.mp hℓ).2

/-- `N` is coprime to `a_c`. -/
theorem ppZPartC_isCoprime (a : ℕ) (N : ℤ) : IsCoprime N ((ppZPartC a N : ℕ) : ℤ) := by
  rw [ppZPartC, Nat.cast_prod]
  refine IsCoprime.prod_right fun ℓ hℓ ↦ ?_
  rw [Finset.mem_filter] at hℓ
  rw [Nat.cast_pow]
  refine IsCoprime.pow_right (IsCoprime.symm ?_)
  exact (Nat.prime_iff_prime_int.mp
    (Nat.prime_of_mem_primeFactors hℓ.1)).irreducible.coprime_iff_not_dvd.mpr hℓ.2

end AJConjecture
