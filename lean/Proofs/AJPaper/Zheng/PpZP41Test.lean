import Mathlib
import AJPaper.Zheng.PpZP41Fourier
import AJPaper.Zheng.PpZP41Arith2

/-!
# The test function (Unit PpZ, node `PpZ_P41Test`)

Source: Zheng, Lemma 4.4 and (4.21)–(4.22), in one step for all primes of `a`.

For a choice `k : ℕ → ℤ` (one shift per prime) put, for `r ∈ ℤ`,

  `Φ(r) = [β ∣ r] ζ_a^{a_c r} · ∏_{ℓ ∣ a, ℓ ∤ N} ([ℓ^e ∣ Nr - 4] - [ℓ^e ∣ N(r - k_ℓ ℓ^{e-1}) - 4])`

(`ppZTest`). `ppZTest_unitSupported`: `Φ` is unit-supported, for every choice of `k`.

Route. Periodicity: every condition depends on `r` modulo a divisor of `a`, and
`ζ_a^{a_c (r+a)} = ζ_a^{a_c r}`. Coset sums along `d = a/ℓ₀`, `ℓ₀ ∣ a` prime:
* the factor `[β ∣ r]` is constant on `r + dℤ` (`β ∣ d`), and so is each factor of the product
  belonging to a prime `ℓ ≠ ℓ₀` (`ℓ^{e_ℓ} ∣ d`); pull them out (`Finset.mul_prod_erase`).
* If `ℓ₀ ∣ N`: the whole product is constant, and `∑_{s<ℓ₀} ζ_a^{a_c s d} = 0` because
  `ζ_a^{a_c d} = e^{2πi a_c/ℓ₀}` is a primitive `ℓ₀`-th root of unity (`ℓ₀ ∤ a_c`).
* If `ℓ₀ ∤ N`: `ζ_a^{a_c s d} = 1` (`ℓ₀ ∣ a_c`), and `d ≡ ℓ₀^{e-1}·unit (mod ℓ₀^e)`, so `r + sd`
  runs once through the residues `≡ r (mod ℓ₀^{e-1})` modulo `ℓ₀^e`. As `N` is a unit mod `ℓ₀`,
  each of the two indicators equals `1` for exactly one `s` if `ℓ₀^{e-1} ∣ Nr - 4`, and for none
  otherwise (the same condition for both, since the shift is a multiple of `ℓ₀^{e-1}`); the
  difference sums to `0`.

Checked numerically (`p41.py`: all coset sums `< 2·10⁻¹⁵` for 32 values of `a ≤ 1125`).
-/

noncomputable section

namespace AJConjecture

/-- The test function `Φ` of the reduction (depending on a shift `k ℓ` for every prime `ℓ`). -/
def ppZTest (a : ℕ) (N : ℤ) (k : ℕ → ℤ) (r : ℤ) : ℂ :=
  (if ((ppZBeta a N : ℕ) : ℤ) ∣ r then ppZRoot a ((ppZPartC a N : ℤ) * r) else 0) *
    ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N),
      ((if (ℓ : ℤ) ^ a.factorization ℓ ∣ N * r - 4 then (1 : ℂ) else 0) -
        (if (ℓ : ℤ) ^ a.factorization ℓ ∣
            N * (r - k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) - 4 then (1 : ℂ) else 0))

/-- The factor of the test function belonging to the prime `ℓ`. -/
private def factor_P41Test (a : ℕ) (N : ℤ) (k : ℕ → ℤ) (ℓ : ℕ) (r : ℤ) : ℂ :=
  (if (ℓ : ℤ) ^ a.factorization ℓ ∣ N * r - 4 then (1 : ℂ) else 0) -
    (if (ℓ : ℤ) ^ a.factorization ℓ ∣
        N * (r - k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) - 4 then (1 : ℂ) else 0)

/-- The factor `[β ∣ r] ζ_a^{a_c r}` of the test function. -/
private def prefactor_P41Test (a : ℕ) (N : ℤ) (r : ℤ) : ℂ :=
  if ((ppZBeta a N : ℕ) : ℤ) ∣ r then ppZRoot a ((ppZPartC a N : ℤ) * r) else 0

/-- The test function as the product of its prefactor and its prime factors. -/
private theorem test_eq_P41Test (a : ℕ) (N : ℤ) (k : ℕ → ℤ) (r : ℤ) :
    ppZTest a N k r = prefactor_P41Test a N r *
      ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N), factor_P41Test a N k ℓ r :=
  rfl

/-- `ζ_a^d = 1` exactly when `a ∣ d`. -/
private theorem root_eq_one_iff_P41Test {a : ℕ} (ha : 1 ≤ a) (d : ℤ) :
    ppZRoot a d = 1 ↔ (a : ℤ) ∣ d := by
  have h1 : IsPrimitiveRoot (ppZRoot a 1) a := ppZRoot_isPrimitiveRoot ha isCoprime_one_left
  rw [← h1.zpow_eq_one_iff_dvd, ← ppZRoot_mul, one_mul]

/-- The factor of `ℓ` is invariant under shifts by multiples of `ℓ^{e_ℓ}`. -/
private theorem factor_add_P41Test (a : ℕ) (N : ℤ) (k : ℕ → ℤ) (ℓ : ℕ) {d : ℤ}
    (hd : (ℓ : ℤ) ^ a.factorization ℓ ∣ d) (r : ℤ) :
    factor_P41Test a N k ℓ (r + d) = factor_P41Test a N k ℓ r := by
  have h1 : N * (r + d) - 4 = N * r - 4 + N * d := by ring
  have h2 : N * (r + d - k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) - 4 =
      N * (r - k ℓ * (ℓ : ℤ) ^ (a.factorization ℓ - 1)) - 4 + N * d := by ring
  simp only [factor_P41Test, h1, h2, dvd_add_left (hd.mul_left N)]

/-- The prefactor under a shift by a multiple of `β`. -/
private theorem prefactor_add_P41Test (a : ℕ) (N : ℤ) {d : ℤ}
    (hd : ((ppZBeta a N : ℕ) : ℤ) ∣ d) (r : ℤ) :
    prefactor_P41Test a N (r + d) =
      prefactor_P41Test a N r * ppZRoot a ((ppZPartC a N : ℤ) * d) := by
  simp only [prefactor_P41Test, dvd_add_left hd, mul_add, ppZRoot_add]
  split_ifs
  · rfl
  · rw [zero_mul]

/-- Exactly one `s < ℓ` solves `A + c s ≡ 0 (mod ℓ)` when `ℓ ∤ c`. -/
private theorem sum_prime_indicator_P41Test {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℤ}
    (hc : ¬ (ℓ : ℤ) ∣ c) (A : ℤ) :
    ∑ s ∈ Finset.range ℓ, (if (ℓ : ℤ) ∣ A + c * (s : ℤ) then (1 : ℂ) else 0) = 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hc' : (c : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hiff : ∀ s : ℕ, (ℓ : ℤ) ∣ A + c * (s : ℤ) ↔ (s : ZMod ℓ) = -(A : ZMod ℓ) / c := by
    intro s
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, eq_div_iff hc']
    push_cast
    constructor <;> intro h <;> linear_combination h
  simp only [hiff]
  rw [Finset.sum_eq_single_of_mem (-(A : ZMod ℓ) / c).val (Finset.mem_range.mpr (ZMod.val_lt _))]
  · rw [ite_eq_left (ZMod.natCast_zmod_val _)]
  · intro s hs hne
    rw [ite_eq_right]
    intro h
    apply hne
    rw [← h, ZMod.val_natCast_of_lt (Finset.mem_range.mp hs)]

/-- The number of `s < ℓ` with `ℓ^e ∣ A + s c ℓ^{e-1}` is `[ℓ^{e-1} ∣ A]` when `ℓ ∤ c`. -/
private theorem sum_pow_indicator_P41Test {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e) {c : ℤ}
    (hc : ¬ (ℓ : ℤ) ∣ c) (A : ℤ) :
    ∑ s ∈ Finset.range ℓ,
        (if (ℓ : ℤ) ^ e ∣ A + (s : ℤ) * (c * (ℓ : ℤ) ^ (e - 1)) then (1 : ℂ) else 0) =
      if (ℓ : ℤ) ^ (e - 1) ∣ A then 1 else 0 := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hℓ.ne_zero
  have hpow : (ℓ : ℤ) ^ e = (ℓ : ℤ) ^ (e - 1) * ℓ := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  split_ifs with hA
  · obtain ⟨A', rfl⟩ := hA
    have hiff : ∀ s : ℕ, (ℓ : ℤ) ^ e ∣ (ℓ : ℤ) ^ (e - 1) * A' + (s : ℤ) * (c * (ℓ : ℤ) ^ (e - 1)) ↔
        (ℓ : ℤ) ∣ A' + c * (s : ℤ) := by
      intro s
      rw [hpow, show (ℓ : ℤ) ^ (e - 1) * A' + (s : ℤ) * (c * (ℓ : ℤ) ^ (e - 1)) =
        (ℓ : ℤ) ^ (e - 1) * (A' + c * (s : ℤ)) by ring, mul_dvd_mul_iff_left (pow_ne_zero _ hℓ0)]
    simp only [hiff]
    exact sum_prime_indicator_P41Test hℓ hc A'
  · refine Finset.sum_eq_zero fun s _ ↦ ite_eq_right fun h ↦ hA ?_
    have h1 : (ℓ : ℤ) ^ (e - 1) ∣ A + (s : ℤ) * (c * (ℓ : ℤ) ^ (e - 1)) :=
      (Dvd.intro _ hpow.symm).trans h
    exact (dvd_add_left ((dvd_mul_left _ c).mul_left _)).mp h1

/-- `ℓ^{e_ℓ} ∣ a/ℓ₀` for primes `ℓ ≠ ℓ₀` of `a`. -/
private theorem pow_dvd_div_P41Test {a ℓ ℓ₀ : ℕ} (hℓ : ℓ.Prime) (hℓ₀ : ℓ₀.Prime) (hℓ₀a : ℓ₀ ∣ a)
    (hne : ℓ ≠ ℓ₀) : ℓ ^ a.factorization ℓ ∣ a / ℓ₀ :=
  Nat.dvd_div_of_mul_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ₀ hℓ).mpr hne.symm)) hℓ₀a
    (Nat.ordProj_dvd a ℓ))

/-- `ℓ^{e_ℓ - 1} ∣ a/ℓ₀` for every prime `ℓ` of `a`. -/
private theorem pow_pred_dvd_div_P41Test {a ℓ ℓ₀ : ℕ} (hℓ : ℓ ∈ a.primeFactors) (hℓ₀ : ℓ₀.Prime)
    (hℓ₀a : ℓ₀ ∣ a) : ℓ ^ (a.factorization ℓ - 1) ∣ a / ℓ₀ := by
  obtain ⟨hp, hdvd, ha0⟩ := Nat.mem_primeFactors.mp hℓ
  by_cases hne : ℓ = ℓ₀
  · subst hne
    refine Nat.dvd_div_of_mul_dvd ?_
    rw [← pow_succ', Nat.sub_add_cancel (hp.factorization_pos_of_dvd ha0 hdvd)]
    exact Nat.ordProj_dvd a ℓ
  · exact (pow_dvd_pow _ (Nat.sub_le _ _)).trans (pow_dvd_div_P41Test hp hℓ₀ hℓ₀a hne)

/-- `β ∣ a/ℓ₀` for every prime `ℓ₀` of `a`. -/
private theorem beta_dvd_div_P41Test (a : ℕ) (N : ℤ) {ℓ₀ : ℕ} (hℓ₀ : ℓ₀.Prime) (hℓ₀a : ℓ₀ ∣ a) :
    ((ppZBeta a N : ℕ) : ℤ) ∣ ((a / ℓ₀ : ℕ) : ℤ) := by
  rw [ppZBeta_dvd_iff]
  intro ℓ hℓ _
  exact_mod_cast pow_pred_dvd_div_P41Test hℓ hℓ₀ hℓ₀a

/-- The test function has period `a`. -/
private theorem test_periodic_P41Test (a : ℕ) (ha : 1 ≤ a) (N : ℤ) (k : ℕ → ℤ) (r : ℤ) :
    ppZTest a N k (r + a) = ppZTest a N k r := by
  have hβ : ((ppZBeta a N : ℕ) : ℤ) ∣ (a : ℤ) := by
    rw [ppZBeta_dvd_iff]
    intro ℓ _ _
    exact_mod_cast (pow_dvd_pow ℓ (Nat.sub_le _ _)).trans (Nat.ordProj_dvd a ℓ)
  rw [test_eq_P41Test, test_eq_P41Test, prefactor_add_P41Test a N hβ,
    (root_eq_one_iff_P41Test ha _).mpr (dvd_mul_left _ _), mul_one]
  congr 1
  refine Finset.prod_congr rfl fun ℓ _ ↦ factor_add_P41Test a N k ℓ ?_ r
  exact_mod_cast Nat.ordProj_dvd a ℓ

/-- The coset sums along `a/ℓ₀` vanish when `ℓ₀ ∣ N`. -/
private theorem coset_sum_of_dvd_P41Test (a : ℕ) (ha : 1 ≤ a) (N : ℤ) (k : ℕ → ℤ) {ℓ₀ : ℕ}
    (hℓ₀ : ℓ₀.Prime) (hℓ₀a : ℓ₀ ∣ a) (hN : (ℓ₀ : ℤ) ∣ N) (r : ℤ) :
    ∑ s ∈ Finset.range ℓ₀, ppZTest a N k (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) = 0 := by
  have hmul : (ℓ₀ : ℤ) * ((a / ℓ₀ : ℕ) : ℤ) = a := by exact_mod_cast Nat.mul_div_cancel' hℓ₀a
  have ha0 : (a : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hterm : ∀ s : ℕ, ppZTest a N k (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) =
      ppZTest a N k r * ppZRoot a ((ppZPartC a N : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) ^ s := by
    intro s
    have hprod : ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N),
        factor_P41Test a N k ℓ (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) =
        ∏ ℓ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N), factor_P41Test a N k ℓ r := by
      refine Finset.prod_congr rfl fun ℓ hℓ ↦ factor_add_P41Test a N k ℓ (Dvd.dvd.mul_left ?_ _) r
      rw [Finset.mem_filter] at hℓ
      have hne : ℓ ≠ ℓ₀ := by
        rintro rfl
        exact hℓ.2 hN
      exact_mod_cast pow_dvd_div_P41Test (Nat.prime_of_mem_primeFactors hℓ.1) hℓ₀ hℓ₀a hne
    have hroot : ppZRoot a ((ppZPartC a N : ℤ) * ((s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ))) =
        ppZRoot a ((ppZPartC a N : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) ^ s := by
      rw [← zpow_natCast, ← ppZRoot_mul]
      congr 1
      ring
    rw [test_eq_P41Test, test_eq_P41Test, hprod, prefactor_add_P41Test a N
      ((beta_dvd_div_P41Test a N hℓ₀ hℓ₀a).mul_left _), hroot]
    ring
  simp only [hterm, ← Finset.mul_sum]
  have hx1 : ppZRoot a ((ppZPartC a N : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) ≠ 1 := by
    rw [Ne, root_eq_one_iff_P41Test ha]
    intro h
    have hd0 : ((a / ℓ₀ : ℕ) : ℤ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      exact ha0 hmul.symm
    rw [← hmul, mul_comm (ℓ₀ : ℤ), mul_comm ((ppZPartC a N : ℕ) : ℤ),
      mul_dvd_mul_iff_left hd0] at h
    exact (Nat.prime_iff_prime_int.mp hℓ₀).not_isUnit
      ((ppZPartC_isCoprime a N).isUnit_of_dvd' hN h)
  have hxp : ppZRoot a ((ppZPartC a N : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) ^ ℓ₀ = 1 := by
    rw [← zpow_natCast, ← ppZRoot_mul, root_eq_one_iff_P41Test ha]
    exact ⟨ppZPartC a N, by rw [← hmul]; ring⟩
  rw [geom_sum_eq hx1, hxp, sub_self, zero_div, mul_zero]

/-- The sum of the factor of `ℓ₀` over a coset of `(a/ℓ₀)ℤ` vanishes when `ℓ₀ ∤ N`. -/
private theorem factor_coset_sum_P41Test (a : ℕ) (N : ℤ) (k : ℕ → ℤ) {ℓ₀ : ℕ}
    (hℓ₀ : ℓ₀ ∈ a.primeFactors) (hN : ¬ (ℓ₀ : ℤ) ∣ N) (r : ℤ) :
    ∑ s ∈ Finset.range ℓ₀, factor_P41Test a N k ℓ₀ (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) = 0 := by
  obtain ⟨hp, hdvd, ha0⟩ := Nat.mem_primeFactors.mp hℓ₀
  have he : 1 ≤ a.factorization ℓ₀ := hp.factorization_pos_of_dvd ha0 hdvd
  have hdiv : a / ℓ₀ = a / ℓ₀ ^ a.factorization ℓ₀ * ℓ₀ ^ (a.factorization ℓ₀ - 1) := by
    refine Nat.div_eq_of_eq_mul_right hp.pos ?_
    rw [mul_comm (a / _), ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]
    exact (Nat.ordProj_mul_ordCompl_eq_self a ℓ₀).symm
  have hc : ¬ (ℓ₀ : ℤ) ∣ N * ((a / ℓ₀ ^ a.factorization ℓ₀ : ℕ) : ℤ) := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
    · exact hN h
    · exact Nat.not_dvd_ordCompl hp ha0 (Int.natCast_dvd_natCast.mp h)
  have hcast : ((a / ℓ₀ : ℕ) : ℤ) = ((a / ℓ₀ ^ a.factorization ℓ₀ : ℕ) : ℤ) *
      (ℓ₀ : ℤ) ^ (a.factorization ℓ₀ - 1) := by
    conv_lhs => rw [hdiv]
    push_cast
    ring
  have h1 : ∀ s : ℕ, N * (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) - 4 = (N * r - 4) + (s : ℤ) *
      (N * ((a / ℓ₀ ^ a.factorization ℓ₀ : ℕ) : ℤ) * (ℓ₀ : ℤ) ^ (a.factorization ℓ₀ - 1)) := by
    intro s
    rw [hcast]
    ring
  have h2 : ∀ s : ℕ, N * (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ) -
      k ℓ₀ * (ℓ₀ : ℤ) ^ (a.factorization ℓ₀ - 1)) - 4 =
      (N * (r - k ℓ₀ * (ℓ₀ : ℤ) ^ (a.factorization ℓ₀ - 1)) - 4) + (s : ℤ) *
      (N * ((a / ℓ₀ ^ a.factorization ℓ₀ : ℕ) : ℤ) * (ℓ₀ : ℤ) ^ (a.factorization ℓ₀ - 1)) := by
    intro s
    rw [hcast]
    ring
  have h3 : N * (r - k ℓ₀ * (ℓ₀ : ℤ) ^ (a.factorization ℓ₀ - 1)) - 4 =
      N * r - 4 + (ℓ₀ : ℤ) ^ (a.factorization ℓ₀ - 1) * (-(N * k ℓ₀)) := by ring
  simp only [factor_P41Test, h1, h2, Finset.sum_sub_distrib,
    sum_pow_indicator_P41Test hp he hc]
  simp only [h3, dvd_add_left (dvd_mul_right _ _), sub_self]

/-- The coset sums along `a/ℓ₀` vanish when `ℓ₀ ∤ N`. -/
private theorem coset_sum_of_not_dvd_P41Test (a : ℕ) (ha : 1 ≤ a) (N : ℤ) (k : ℕ → ℤ) {ℓ₀ : ℕ}
    (hℓ₀ : ℓ₀.Prime) (hℓ₀a : ℓ₀ ∣ a) (hN : ¬ (ℓ₀ : ℤ) ∣ N) (r : ℤ) :
    ∑ s ∈ Finset.range ℓ₀, ppZTest a N k (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) = 0 := by
  have hmem : ℓ₀ ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hℓ₀, hℓ₀a, by omega⟩
  have hmemC : ℓ₀ ∈ a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N) :=
    Finset.mem_filter.mpr ⟨hmem, hN⟩
  have hmul : (ℓ₀ : ℤ) * ((a / ℓ₀ : ℕ) : ℤ) = a := by exact_mod_cast Nat.mul_div_cancel' hℓ₀a
  have hℓC : ℓ₀ ∣ ppZPartC a N :=
    (dvd_pow_self ℓ₀ (hℓ₀.factorization_pos_of_dvd (by omega) hℓ₀a).ne').trans
      (Finset.dvd_prod_of_mem _ hmemC)
  have hterm : ∀ s : ℕ, ppZTest a N k (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) =
      prefactor_P41Test a N r *
        (∏ ℓ ∈ (a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N)).erase ℓ₀,
          factor_P41Test a N k ℓ r) *
        factor_P41Test a N k ℓ₀ (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) := by
    intro s
    have hprod : ∏ ℓ ∈ (a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N)).erase ℓ₀,
        factor_P41Test a N k ℓ (r + (s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ)) =
        ∏ ℓ ∈ (a.primeFactors.filter (fun ℓ : ℕ ↦ ¬ (ℓ : ℤ) ∣ N)).erase ℓ₀,
          factor_P41Test a N k ℓ r := by
      refine Finset.prod_congr rfl fun ℓ hℓ ↦ factor_add_P41Test a N k ℓ (Dvd.dvd.mul_left ?_ _) r
      rw [Finset.mem_erase, Finset.mem_filter] at hℓ
      exact_mod_cast pow_dvd_div_P41Test (Nat.prime_of_mem_primeFactors hℓ.2.1) hℓ₀ hℓ₀a hℓ.1
    have hroot : ppZRoot a ((ppZPartC a N : ℤ) * ((s : ℤ) * ((a / ℓ₀ : ℕ) : ℤ))) = 1 := by
      rw [root_eq_one_iff_P41Test ha]
      obtain ⟨c, hc⟩ := hℓC
      refine ⟨c * s, ?_⟩
      rw [hc, ← hmul]
      push_cast
      ring
    rw [test_eq_P41Test, ← Finset.mul_prod_erase _ _ hmemC, hprod, prefactor_add_P41Test a N
      ((beta_dvd_div_P41Test a N hℓ₀ hℓ₀a).mul_left _), hroot]
    ring
  simp only [hterm, ← Finset.mul_sum, factor_coset_sum_P41Test a N k hmem hN, mul_zero]

/-- The test function is unit-supported. -/
theorem ppZTest_unitSupported (a : ℕ) (ha : 1 ≤ a) (N : ℤ) (k : ℕ → ℤ) :
    PpZUnitSupported a (ppZTest a N k) := by
  refine ⟨test_periodic_P41Test a ha N k, fun ℓ₀ hℓ₀ hℓ₀a r ↦ ?_⟩
  by_cases hN : (ℓ₀ : ℤ) ∣ N
  · exact coset_sum_of_dvd_P41Test a ha N k hℓ₀ hℓ₀a hN r
  · exact coset_sum_of_not_dvd_P41Test a ha N k hℓ₀ hℓ₀a hN r

end AJConjecture
