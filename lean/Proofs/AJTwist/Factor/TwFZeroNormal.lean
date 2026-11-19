import Mathlib
import AJTwist.Quantum.TwQCramerOp
import AJTwist.Factor.TwFRiccatiNormal
import AJTwist.Factor.TwFRiccati
import AJTwist.Factor.TwFZeroEvenDefs

/-!
# The normal form of a solution of the Riccati equation of `P_0` over `ℚ(t)[x]` (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`), eq. (riccati-normal):
`r_0 = c(q) x^μ ∏_{k ∈ ℤ} (x - q^k)^{n_k} σ(g)/g`; "The companion and inverse are integral and
invertible at every finite nonzero prime of `ℚ(q)[x]` outside the orbit of `x - 1`. Indeed the
possible finite nonzero poles in eq. (zero-coeff), after monic division and inversion, are at
`1, q, q², q³`."

Forward convention, variable `x`, shift `τ : x ↦ q x`, `q = t⁴`, constants `k = ℚ(t)`
(`twTHom : ℤ[t] → ℚ(t)`). The end coefficients of `twfZeroOpX` are
`p₀ = -t⁴⁴ x² ℓ₀ ℓ₂` and `p₃ = t²⁸ ℓ₁ ℓ₃`, with `ℓ_j = twfLin j = t^(4j) x - 1`
(`b_3(q, q³x) = -q¹¹ x² (x - 1)(q² x - 1)`, `b_0(q, q³x) = q⁷ (q x - 1)(q³ x - 1)`).

`twf_zero_normalForm`: if `(e₀, e₁)` solves the Riccati equation of `twfZeroOpX`, then with
`ρ = -e₀/e₁` there are `c ∈ ℚ(t)^×`, `μ ≤ 2`, `ε_j ≤ 1` and `g ≠ 0` in `ℚ(t)[x]` such that
`p₃ · (-e₀) τ(g) = (c x^μ ∏_{j<4} ℓ_j^{ε_j}) · τ²(e₁) g`, i.e.
`ρ = (c x^μ ∏_j ℓ_j^{ε_j}/p₃) · h/τ(h)` with `h = g/(e₁ τ e₁)`.

Route: `twf_riccati_normalForm` over `k[X]` with `τ = twfTau` (injective: `q ≠ 0`), `n = -e₀`,
`e = e₁` mapped by `twfIota` (`oreRiccati_map`, unfolding `oreRiccati` at `d = 3`; the
coefficients of `twfZeroOpX` are read with `Finset.sum_range_succ`/`Fin.sum_univ_four`): it gives
`A B = p₀ p₃` up to the common nonzero factor, so `A` divides
`-t⁷² x² ℓ₀ ℓ₁ ℓ₂ ℓ₃`, a unit times a product of the primes `x` (twice) and `ℓ_0, …, ℓ_3`,
pairwise non-associated in `ℚ(t)[x]` because `1, q, q², q³` are distinct (`q = t⁴` is
transcendental); a divisor of a product of primes is a unit times a sub-product
(`UniqueFactorizationMonoid`, or prime by prime: if `π` is prime and `A ∣ π N` then `A ∣ N` or
`A = π A'` with `A' ∣ N`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficient map `ℤ[t][x] → ℚ(t)[x]`. -/
def twfIota : Coeff →+* (RatFunc ℚ)[X] := Polynomial.mapRingHom twTHom

/-- The shift `x ↦ t⁴ x` of `ℚ(t)[x]`. -/
def twfTau : (RatFunc ℚ)[X] →+* (RatFunc ℚ)[X] :=
  Polynomial.compRingHom (C (twTHom (X ^ 4)) * X)

/-- The linear forms `ℓ_j = t^(4j) x - 1` of `ℤ[t][x]`. -/
def twfLin (j : ℕ) : Coeff := C (X ^ (4 * j)) * X - 1

theorem twfIota_twfShiftX (c : Coeff) : twfIota (twfShiftX c) = twfTau (twfIota c) := by
  change (c.comp (C (X ^ 4) * X)).map twTHom = (c.map twTHom).comp (C (twTHom (X ^ 4)) * X)
  rw [map_comp, Polynomial.map_mul, map_C, map_X]

/-- The end coefficients of the explicit operator in the variable `x`. -/
theorem coeff_twfZeroOpX_ends :
    twfZeroOpX.coeff 0 = -(C (X ^ 44) * X ^ 2 * twfLin 0 * twfLin 2) ∧
      twfZeroOpX.coeff 3 = C (X ^ 28) * twfLin 1 * twfLin 3 := by
  have hc : ∀ k : Fin 4, twfZeroOpX.coeff (k : ℕ) =
      (twZeroB (X ^ 4 : ℤ[X]) (Fin.rev k)).comp (C (X ^ 12) * X) := by
    intro k
    rw [twfZeroOpX, finsetSum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one]
    · intro j _ hj
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h ↦ hj (Fin.ext h.symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have h0 := hc 0
  have h3 := hc 3
  simp only [Fin.val_zero, show ((3 : Fin 4) : ℕ) = 3 from rfl] at h0 h3
  rw [h0, h3]
  simp only [twZeroB, twfLin, show Fin.rev (0 : Fin 4) = 3 from rfl,
    show Fin.rev (3 : Fin 4) = 0 from rfl, Matrix.cons_val_zero, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_comp, sub_comp, neg_comp, pow_comp, C_comp,
    X_comp, one_comp, C_pow]
  constructor <;> ring

/-- The coefficient map `ℤ[t] → ℚ(t)` is injective. -/
private theorem twTHom_injective_twfZeroNormal : Function.Injective twTHom := by
  have h : twTHom =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [twTHom]
    · simp [twTHom, RatFunc.algebraMap_X]
  rw [h, RingHom.coe_comp, coe_mapRingHom]
  exact (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)

/-- The coefficient map `ℤ[t][x] → ℚ(t)[x]` is injective. -/
private theorem twfIota_injective_twfZeroNormal : Function.Injective twfIota :=
  Polynomial.map_injective _ twTHom_injective_twfZeroNormal

/-- The shift `x ↦ t⁴ x` of `ℚ(t)[x]` is injective. -/
private theorem twfTau_injective_twfZeroNormal : Function.Injective twfTau := by
  have ha : twTHom (X ^ 4) ≠ 0 :=
    (map_ne_zero_iff twTHom twTHom_injective_twfZeroNormal).mpr (pow_ne_zero 4 X_ne_zero)
  intro p q h
  ext n
  have hn := congrArg (fun r : (RatFunc ℚ)[X] ↦ r.coeff n) h
  change (p.comp (C (twTHom (X ^ 4)) * X)).coeff n = (q.comp (C (twTHom (X ^ 4)) * X)).coeff n
    at hn
  rw [comp_C_mul_X_coeff, comp_C_mul_X_coeff] at hn
  exact mul_right_cancel₀ (pow_ne_zero n ha) hn

/-- The images of the linear forms `ℓ_j` are prime in `ℚ(t)[x]`. -/
private theorem prime_twfIota_twfLin_twfZeroNormal (j : ℕ) : Prime (twfIota (twfLin j)) := by
  have ha : twTHom (X ^ (4 * j)) ≠ 0 :=
    (map_ne_zero_iff twTHom twTHom_injective_twfZeroNormal).mpr (pow_ne_zero _ X_ne_zero)
  have hL : twfIota (twfLin j) = C (twTHom (X ^ (4 * j))) * X - 1 := by
    change (C (X ^ (4 * j)) * X - 1 : Coeff).map twTHom = _
    rw [Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, Polynomial.map_one]
  have hdeg : (twfIota (twfLin j)).degree = 1 := by
    rw [hL, degree_sub_eq_left_of_degree_lt, degree_C_mul_X ha]
    rw [degree_C_mul_X ha, degree_one]
    exact zero_lt_one
  exact (irreducible_of_degree_eq_one hdeg).prime

/-- A divisor of `π N`, `π` prime, is `π^ε A'` with `ε ≤ 1` and `A' ∣ N`. -/
private theorem exists_pow_mul_of_dvd_prime_mul_twfZeroNormal {K : Type*} [Field K]
    {π A N : K[X]} (hπ : Prime π) (h : A ∣ π * N) :
    ∃ (ε : ℕ) (A' : K[X]), ε ≤ 1 ∧ A = π ^ ε * A' ∧ A' ∣ N := by
  by_cases hA : π ∣ A
  · obtain ⟨A', rfl⟩ := hA
    exact ⟨1, A', le_rfl, by rw [pow_one], (mul_dvd_mul_iff_left hπ.ne_zero).mp h⟩
  · obtain ⟨q, hq⟩ := h
    obtain ⟨q', rfl⟩ := (hπ.dvd_or_dvd ⟨N, hq.symm⟩).resolve_left hA
    refine ⟨0, A, zero_le_one, by rw [pow_zero, one_mul], ⟨q', mul_left_cancel₀ hπ.ne_zero ?_⟩⟩
    rw [hq]
    ring

/-- A divisor of a unit times `x² ℓ₀ ℓ₁ ℓ₂ ℓ₃` (all prime) is a unit times a sub-product. -/
private theorem exists_normal_divisor_twfZeroNormal {K : Type*} [Field K]
    {x l₀ l₁ l₂ l₃ u A : K[X]} (hx : Prime x) (h₀ : Prime l₀) (h₁ : Prime l₁) (h₂ : Prime l₂)
    (h₃ : Prime l₃) (hu : IsUnit u) (h : A ∣ x * (x * (l₀ * (l₁ * (l₂ * (l₃ * u)))))) :
    ∃ (μ ε₀ ε₁ ε₂ ε₃ : ℕ) (v : K[X]), IsUnit v ∧ μ ≤ 2 ∧ ε₀ ≤ 1 ∧ ε₁ ≤ 1 ∧ ε₂ ≤ 1 ∧ ε₃ ≤ 1 ∧
      A = v * x ^ μ * (l₀ ^ ε₀ * l₁ ^ ε₁ * l₂ ^ ε₂ * l₃ ^ ε₃) := by
  obtain ⟨a, A₁, ha, rfl, hA₁⟩ := exists_pow_mul_of_dvd_prime_mul_twfZeroNormal hx h
  obtain ⟨b, A₂, hb, rfl, hA₂⟩ := exists_pow_mul_of_dvd_prime_mul_twfZeroNormal hx hA₁
  obtain ⟨ε₀, A₃, hε₀, rfl, hA₃⟩ := exists_pow_mul_of_dvd_prime_mul_twfZeroNormal h₀ hA₂
  obtain ⟨ε₁, A₄, hε₁, rfl, hA₄⟩ := exists_pow_mul_of_dvd_prime_mul_twfZeroNormal h₁ hA₃
  obtain ⟨ε₂, A₅, hε₂, rfl, hA₅⟩ := exists_pow_mul_of_dvd_prime_mul_twfZeroNormal h₂ hA₄
  obtain ⟨ε₃, A₆, hε₃, rfl, hA₆⟩ := exists_pow_mul_of_dvd_prime_mul_twfZeroNormal h₃ hA₅
  refine ⟨a + b, ε₀, ε₁, ε₂, ε₃, A₆, isUnit_of_dvd_unit hA₆ hu, by omega, hε₀, hε₁, hε₂, hε₃, ?_⟩
  ring

/-- The product of the end coefficients is a unit times `x² ℓ₀ ℓ₁ ℓ₂ ℓ₃` in `ℚ(t)[x]`. -/
private theorem twfIota_ends_mul_twfZeroNormal :
    ∃ u : (RatFunc ℚ)[X], IsUnit u ∧
      twfIota (twfZeroOpX.coeff 0) * twfIota (twfZeroOpX.coeff 3) =
        X * (X * (twfIota (twfLin 0) * (twfIota (twfLin 1) * (twfIota (twfLin 2) *
          (twfIota (twfLin 3) * u))))) := by
  have hC : ∀ a : ℤ[X], twfIota (C a) = C (twTHom a) := fun a ↦ Polynomial.map_C twTHom
  have hX : twfIota X = X := Polynomial.map_X twTHom
  have hne : twTHom (X ^ 44) * twTHom (X ^ 28) ≠ 0 :=
    mul_ne_zero
      ((map_ne_zero_iff twTHom twTHom_injective_twfZeroNormal).mpr (pow_ne_zero _ X_ne_zero))
      ((map_ne_zero_iff twTHom twTHom_injective_twfZeroNormal).mpr (pow_ne_zero _ X_ne_zero))
  refine ⟨-C (twTHom (X ^ 44) * twTHom (X ^ 28)),
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hne)).neg, ?_⟩
  rw [coeff_twfZeroOpX_ends.1, coeff_twfZeroOpX_ends.2]
  simp only [map_neg, map_mul, map_pow, hC, hX]
  ring

/-- The normal form of a solution of the Riccati equation of `P_0` over `ℚ(t)[x]`. -/
theorem twf_zero_normalForm {e₀ e₁ : Coeff} (he₀ : e₀ ≠ 0) (he₁ : e₁ ≠ 0)
    (hric : oreRiccati twfShiftX 3 twfZeroOpX e₀ e₁ = 0) :
    ∃ (c : RatFunc ℚ) (μ : ℕ) (ε : Fin 4 → ℕ) (g : (RatFunc ℚ)[X]),
      c ≠ 0 ∧ g ≠ 0 ∧ μ ≤ 2 ∧ (∀ j, ε j ≤ 1) ∧
      twfIota (-e₀ * (C (X ^ 28) * twfLin 1 * twfLin 3)) * twfTau g =
        C c * X ^ μ * (∏ j : Fin 4, twfIota (twfLin j) ^ ε j) *
          twfIota (twfShiftX (twfShiftX e₁)) * g := by
  have hn0 : -twfIota e₀ ≠ 0 :=
    neg_ne_zero.mpr ((map_ne_zero_iff twfIota twfIota_injective_twfZeroNormal).mpr he₀)
  have he0 : twfIota e₁ ≠ 0 :=
    (map_ne_zero_iff twfIota twfIota_injective_twfZeroNormal).mpr he₁
  have hric' := congrArg twfIota hric
  rw [oreRiccati_map twfIota twfShiftX twfTau twfIota_twfShiftX, map_zero] at hric'
  simp only [oreRiccati, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, Finset.prod_Ico_eq_prod_range, Nat.sub_self, Nat.add_zero,
    Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Function.iterate_succ_apply,
    Function.iterate_zero_apply, coeff_map] at hric'
  obtain ⟨A, B, g, hg, hA, hB⟩ := twf_riccati_normalForm twfTau twfTau_injective_twfZeroNormal
    (twfIota (twfZeroOpX.coeff 0)) (twfIota (twfZeroOpX.coeff 1))
    (twfIota (twfZeroOpX.coeff 2)) (twfIota (twfZeroOpX.coeff 3)) (n := -twfIota e₀)
    (e := twfIota e₁) he0 (by linear_combination hric')
  have hτg : twfTau g ≠ 0 := (map_ne_zero_iff twfTau twfTau_injective_twfZeroNormal).mpr hg
  have hττe : twfTau (twfTau (twfIota e₁)) ≠ 0 :=
    (map_ne_zero_iff twfTau twfTau_injective_twfZeroNormal).mpr
      ((map_ne_zero_iff twfTau twfTau_injective_twfZeroNormal).mpr he0)
  have hw : twfTau (twfTau (twfIota e₁)) * g * (-twfIota e₀ * twfTau g) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hττe hg) (mul_ne_zero hn0 hτg)
  have hAB : A * B = twfIota (twfZeroOpX.coeff 0) * twfIota (twfZeroOpX.coeff 3) := by
    refine mul_right_cancel₀ hw ?_
    linear_combination (-(twfIota (twfZeroOpX.coeff 0) * (twfTau (twfTau (twfIota e₁)) * g))) * hA
      - A * (twfTau (twfTau (twfIota e₁)) * g) * hB
  obtain ⟨u, hu, hprod⟩ := twfIota_ends_mul_twfZeroNormal
  obtain ⟨μ, ε₀, ε₁, ε₂, ε₃, v, hv, hμ, hε₀, hε₁, hε₂, hε₃, hAeq⟩ :=
    exists_normal_divisor_twfZeroNormal prime_X (prime_twfIota_twfLin_twfZeroNormal 0)
      (prime_twfIota_twfLin_twfZeroNormal 1) (prime_twfIota_twfLin_twfZeroNormal 2)
      (prime_twfIota_twfLin_twfZeroNormal 3) hu (hprod ▸ Dvd.intro B hAB)
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hv
  refine ⟨c, μ, ![ε₀, ε₁, ε₂, ε₃], g, hc.ne_zero, hg, hμ, ?_, ?_⟩
  · intro j
    fin_cases j
    exacts [hε₀, hε₁, hε₂, hε₃]
  · rw [Fin.prod_univ_four, twfIota_twfShiftX, twfIota_twfShiftX, map_mul, map_neg,
      ← coeff_twfZeroOpX_ends.2]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hAeq] at hA
    linear_combination hA

end AJConjecture
