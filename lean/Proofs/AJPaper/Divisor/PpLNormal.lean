import Mathlib
import AJTwist.Factor.TwFRiccatiNormal
import AJPaper.Divisor.PpLAdjoint

/-!
# The normal form of a solution of the Riccati equation of the adjoint over `ℚ(t)[x]` (Unit
PpL, node `PpL_Normal`)

Source: Section 5.6 of the paper (`operators.tex`), eq. (riccati-normal):
`r_0 = c(q) x^μ ∏_k (x - q^k)^{n_k} σ(g)/g`. Mirror of `AJTwist/Factor/TwFZeroNormal.lean` for
the adjoint. The generic normal form `twf_riccati_normalForm` is reused as it is.

The end coefficients of the adjoint are `p†_0 = t²⁸ ℓ₁ ℓ₃` and `p†_3 = -t⁶⁸ x² ℓ₃ ℓ₅`
(`coeff_pplAdjOpX_explicit`), with `ℓ_j = twfLin j = t^(4j) x - 1`, so
`p†_0 p†_3 = -t⁹⁶ x² ℓ₁ ℓ₃² ℓ₅`: against the template (`-t⁷² x² ℓ₀ ℓ₁ ℓ₂ ℓ₃`) the linear form
`ℓ₃` occurs twice. The list of the linear forms with multiplicity is `pplIdx = (1, 3, 3, 5)`.

`ppl_adjoint_normalForm`: if `(e₀, e₁)` solves the Riccati equation of `pplAdjOpX`, there are
`c ∈ ℚ(t)^×`, `μ ≤ 2`, `ε_j ≤ 1` (`j < 4`) and `g ≠ 0` in `ℚ(t)[x]` with
`e₀ · t⁶⁸ x² ℓ₃ ℓ₅ · τ(g) = c x^μ ∏_{j<4} ℓ_{pplIdx j}^{ε_j} · τ²(e₁) g`
(`p†_3 · (-e₀) τ(g) = A · τ²(e₁) g` with `A` a divisor of `p†_0 p†_3`).

Route: as in the template. `twf_riccati_normalForm twfTau` with `n = -twfIota e₀`,
`e = twfIota e₁` (`oreRiccati_map twfIota twfShiftX twfTau twfIota_twfShiftX`, unfold
`oreRiccati` at `d = 3`) gives `A B = p†_0 p†_3`; the product of the ends is
`x · x · ℓ₁ · ℓ₃ · ℓ₃ · ℓ₅ · u` with `u = -t⁹⁶` a unit; the template's private lemmas
`exists_pow_mul_of_dvd_prime_mul_twfZeroNormal` and `exists_normal_divisor_twfZeroNormal` (a
divisor of a unit times a product of six primes is a unit times a sub-product) do not need the
primes to be distinct and apply with `l₁ = l₂ = ℓ₃`; `twfIota (twfLin j)` is prime (degree one).

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The indices `j` of the linear forms `ℓ_j = t^(4j) x - 1` in the product
`p†_0 p†_3 = -t⁹⁶ x² ℓ₁ ℓ₃² ℓ₅` of the end coefficients of the adjoint, with multiplicity. -/
def pplIdx : Fin 4 → ℕ := ![1, 3, 3, 5]

/-- The coefficient map `ℤ[t] → ℚ(t)` is injective. -/
private theorem twTHom_injective_pplNormal : Function.Injective twTHom := by
  have h : twTHom =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [twTHom]
    · simp [twTHom, RatFunc.algebraMap_X]
  rw [h, RingHom.coe_comp, coe_mapRingHom]
  exact (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)

/-- The coefficient map `ℤ[t][x] → ℚ(t)[x]` is injective. -/
private theorem twfIota_injective_pplNormal : Function.Injective twfIota :=
  Polynomial.map_injective _ twTHom_injective_pplNormal

/-- The shift `x ↦ t⁴ x` of `ℚ(t)[x]` is injective. -/
private theorem twfTau_injective_pplNormal : Function.Injective twfTau := by
  have ha : twTHom (X ^ 4) ≠ 0 :=
    (map_ne_zero_iff twTHom twTHom_injective_pplNormal).mpr (pow_ne_zero 4 X_ne_zero)
  intro p q h
  ext n
  have hn := congrArg (fun r : (RatFunc ℚ)[X] ↦ r.coeff n) h
  change (p.comp (C (twTHom (X ^ 4)) * X)).coeff n = (q.comp (C (twTHom (X ^ 4)) * X)).coeff n
    at hn
  rw [comp_C_mul_X_coeff, comp_C_mul_X_coeff] at hn
  exact mul_right_cancel₀ (pow_ne_zero n ha) hn

/-- The images of the linear forms `ℓ_j` are prime in `ℚ(t)[x]`. -/
private theorem prime_twfIota_twfLin_pplNormal (j : ℕ) : Prime (twfIota (twfLin j)) := by
  have ha : twTHom (X ^ (4 * j)) ≠ 0 :=
    (map_ne_zero_iff twTHom twTHom_injective_pplNormal).mpr (pow_ne_zero _ X_ne_zero)
  have hL : twfIota (twfLin j) = C (twTHom (X ^ (4 * j))) * X - 1 := by
    change (C (X ^ (4 * j)) * X - 1 : Coeff).map twTHom = _
    rw [Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, Polynomial.map_one]
  have hdeg : (twfIota (twfLin j)).degree = 1 := by
    rw [hL, degree_sub_eq_left_of_degree_lt, degree_C_mul_X ha]
    rw [degree_C_mul_X ha, degree_one]
    exact zero_lt_one
  exact (irreducible_of_degree_eq_one hdeg).prime

/-- A divisor of `π N`, `π` prime, is `π^ε A'` with `ε ≤ 1` and `A' ∣ N`. -/
private theorem exists_pow_mul_of_dvd_prime_mul_pplNormal {K : Type*} [Field K]
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

/-- A divisor of a unit times `x² l₀ l₁ l₂ l₃` (all prime, not necessarily distinct) is a unit
times a sub-product. -/
private theorem exists_normal_divisor_pplNormal {K : Type*} [Field K]
    {x l₀ l₁ l₂ l₃ u A : K[X]} (hx : Prime x) (h₀ : Prime l₀) (h₁ : Prime l₁) (h₂ : Prime l₂)
    (h₃ : Prime l₃) (hu : IsUnit u) (h : A ∣ x * (x * (l₀ * (l₁ * (l₂ * (l₃ * u)))))) :
    ∃ (μ ε₀ ε₁ ε₂ ε₃ : ℕ) (v : K[X]), IsUnit v ∧ μ ≤ 2 ∧ ε₀ ≤ 1 ∧ ε₁ ≤ 1 ∧ ε₂ ≤ 1 ∧ ε₃ ≤ 1 ∧
      A = v * x ^ μ * (l₀ ^ ε₀ * l₁ ^ ε₁ * l₂ ^ ε₂ * l₃ ^ ε₃) := by
  obtain ⟨a, A₁, ha, rfl, hA₁⟩ := exists_pow_mul_of_dvd_prime_mul_pplNormal hx h
  obtain ⟨b, A₂, hb, rfl, hA₂⟩ := exists_pow_mul_of_dvd_prime_mul_pplNormal hx hA₁
  obtain ⟨ε₀, A₃, hε₀, rfl, hA₃⟩ := exists_pow_mul_of_dvd_prime_mul_pplNormal h₀ hA₂
  obtain ⟨ε₁, A₄, hε₁, rfl, hA₄⟩ := exists_pow_mul_of_dvd_prime_mul_pplNormal h₁ hA₃
  obtain ⟨ε₂, A₅, hε₂, rfl, hA₅⟩ := exists_pow_mul_of_dvd_prime_mul_pplNormal h₂ hA₄
  obtain ⟨ε₃, A₆, hε₃, rfl, hA₆⟩ := exists_pow_mul_of_dvd_prime_mul_pplNormal h₃ hA₅
  refine ⟨a + b, ε₀, ε₁, ε₂, ε₃, A₆, isUnit_of_dvd_unit hA₆ hu, by omega, hε₀, hε₁, hε₂, hε₃, ?_⟩
  ring

/-- The product of the end coefficients of the adjoint is a unit times `x² ℓ₁ ℓ₃² ℓ₅` in
`ℚ(t)[x]`. -/
private theorem twfIota_ends_mul_pplNormal :
    ∃ u : (RatFunc ℚ)[X], IsUnit u ∧
      twfIota (pplAdjOpX.coeff 0) * twfIota (pplAdjOpX.coeff 3) =
        X * (X * (twfIota (twfLin 1) * (twfIota (twfLin 3) * (twfIota (twfLin 3) *
          (twfIota (twfLin 5) * u))))) := by
  have hC : ∀ a : ℤ[X], twfIota (C a) = C (twTHom a) := fun a ↦ Polynomial.map_C twTHom
  have hX : twfIota X = X := Polynomial.map_X twTHom
  have hne : twTHom (X ^ 28) * twTHom (X ^ 68) ≠ 0 :=
    mul_ne_zero
      ((map_ne_zero_iff twTHom twTHom_injective_pplNormal).mpr (pow_ne_zero _ X_ne_zero))
      ((map_ne_zero_iff twTHom twTHom_injective_pplNormal).mpr (pow_ne_zero _ X_ne_zero))
  refine ⟨-C (twTHom (X ^ 28) * twTHom (X ^ 68)),
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hne)).neg, ?_⟩
  rw [coeff_pplAdjOpX_explicit.1, coeff_pplAdjOpX_explicit.2.2.2]
  simp only [map_neg, map_mul, map_pow, hC, hX]
  ring

/-- The normal form of a solution of the Riccati equation of the adjoint of `P_0` over
`ℚ(t)[x]`. -/
theorem ppl_adjoint_normalForm {e₀ e₁ : Coeff} (he₀ : e₀ ≠ 0) (he₁ : e₁ ≠ 0)
    (hric : oreRiccati twfShiftX 3 pplAdjOpX e₀ e₁ = 0) :
    ∃ (c : RatFunc ℚ) (μ : ℕ) (ε : Fin 4 → ℕ) (g : (RatFunc ℚ)[X]),
      c ≠ 0 ∧ g ≠ 0 ∧ μ ≤ 2 ∧ (∀ j, ε j ≤ 1) ∧
      twfIota (e₀ * (C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5)) * twfTau g =
        C c * X ^ μ * (∏ j : Fin 4, twfIota (twfLin (pplIdx j)) ^ ε j) *
          twfIota (twfShiftX (twfShiftX e₁)) * g := by
  have hn0 : -twfIota e₀ ≠ 0 :=
    neg_ne_zero.mpr ((map_ne_zero_iff twfIota twfIota_injective_pplNormal).mpr he₀)
  have he0 : twfIota e₁ ≠ 0 :=
    (map_ne_zero_iff twfIota twfIota_injective_pplNormal).mpr he₁
  have hric' := congrArg twfIota hric
  rw [oreRiccati_map twfIota twfShiftX twfTau twfIota_twfShiftX, map_zero] at hric'
  simp only [oreRiccati, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, Finset.prod_Ico_eq_prod_range, Nat.sub_self, Nat.add_zero,
    Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Function.iterate_succ_apply,
    Function.iterate_zero_apply, coeff_map] at hric'
  obtain ⟨A, B, g, hg, hA, hB⟩ := twf_riccati_normalForm twfTau twfTau_injective_pplNormal
    (twfIota (pplAdjOpX.coeff 0)) (twfIota (pplAdjOpX.coeff 1))
    (twfIota (pplAdjOpX.coeff 2)) (twfIota (pplAdjOpX.coeff 3)) (n := -twfIota e₀)
    (e := twfIota e₁) he0 (by linear_combination hric')
  have hτg : twfTau g ≠ 0 := (map_ne_zero_iff twfTau twfTau_injective_pplNormal).mpr hg
  have hττe : twfTau (twfTau (twfIota e₁)) ≠ 0 :=
    (map_ne_zero_iff twfTau twfTau_injective_pplNormal).mpr
      ((map_ne_zero_iff twfTau twfTau_injective_pplNormal).mpr he0)
  have hw : twfTau (twfTau (twfIota e₁)) * g * (-twfIota e₀ * twfTau g) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hττe hg) (mul_ne_zero hn0 hτg)
  have hAB : A * B = twfIota (pplAdjOpX.coeff 0) * twfIota (pplAdjOpX.coeff 3) := by
    refine mul_right_cancel₀ hw ?_
    linear_combination (-(twfIota (pplAdjOpX.coeff 0) * (twfTau (twfTau (twfIota e₁)) * g))) * hA
      - A * (twfTau (twfTau (twfIota e₁)) * g) * hB
  obtain ⟨u, hu, hprod⟩ := twfIota_ends_mul_pplNormal
  obtain ⟨μ, ε₀, ε₁, ε₂, ε₃, v, hv, hμ, hε₀, hε₁, hε₂, hε₃, hAeq⟩ :=
    exists_normal_divisor_pplNormal prime_X (prime_twfIota_twfLin_pplNormal 1)
      (prime_twfIota_twfLin_pplNormal 3) (prime_twfIota_twfLin_pplNormal 3)
      (prime_twfIota_twfLin_pplNormal 5) hu (hprod ▸ Dvd.intro B hAB)
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hv
  refine ⟨c, μ, ![ε₀, ε₁, ε₂, ε₃], g, hc.ne_zero, hg, hμ, ?_, ?_⟩
  · intro j
    fin_cases j
    exacts [hε₀, hε₁, hε₂, hε₃]
  · have h3 : twfIota (pplAdjOpX.coeff 3) =
        -twfIota (C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5) := by
      rw [coeff_pplAdjOpX_explicit.2.2.2, map_neg]
    rw [Fin.prod_univ_four, twfIota_twfShiftX, twfIota_twfShiftX, map_mul]
    simp only [pplIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hAeq, h3] at hA
    linear_combination hA

end AJConjecture
