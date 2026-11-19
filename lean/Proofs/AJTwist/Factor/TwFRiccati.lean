import Mathlib
import AJConjecture.QAlgOreMul
import AJConjecture.QAlgOreMulBasic
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgOrePseudoDivision

/-!
# Right factors of order one and the Riccati polynomial (TwF, unit F4, generic)

Source: revision 5, Section 5.6 (`operators.tex`, "First-order right divisors at `a = 0`"):
"Suppose `u - r_0` is a right divisor … The equation is
`b_0 + b_1 r_0 + b_2 r_0 σ(r_0) + b_3 r_0 σ(r_0) σ²(r_0) = 0`."

For a commutative ring `A` with an endomorphism `σ` and `P = ∑_k p_k L^k` of degree at most `d`,
`oreRiccati σ d P r₀ r₁ = ∑_{k ≤ d} p_k ∏_{i<k} σ^i(-r₀) ∏_{k ≤ i < d} σ^i(r₁)` is the Riccati
equation of `P` at `ρ = -r₀/r₁`, cleared of denominators (`ρ σ(ρ) ⋯ σ^(k-1)(ρ)` times
`∏_{i<d} σ^i(r₁)`). It is additive in `P`, commutes with left multiplication by coefficients
and with homomorphisms intertwining the shifts, and is homogeneous in `(r₀, r₁)`.

* `oreRiccati_oreMul_linear`: it vanishes on every left multiple `S ⋆ (r₁ L + r₀)`.
* `oreRiccati_eq_zero_of_pseudoFactor`: a right pseudo-factor `R` of degree one of `P` gives a
  solution `(R.coeff 0, R.coeff 1)`.
* `exists_pseudoFactor_of_oreRiccati_eq_zero`: conversely, over a domain with injective `σ`, a
  solution with `r₁ ≠ 0` gives the right pseudo-factor `r₁ L + r₀`
  (`exists_C_mul_eq_oreMul_add`: the remainder is a constant `c`, and
  `oreRiccati σ d (C c) r₀ r₁ = c ∏_{i<d} σ^i(r₁)`).

Route for `oreRiccati_oreMul_linear`: by additivity reduce to `S = monomial j s`, `j < d`; then
`S ⋆ (r₁ L + r₀) = s σ^j(r₁) L^(j+1) + s σ^j(r₀) L^j` and the two terms cancel:
`∏_{i<j+1} σ^i(-r₀) ∏_{j+1 ≤ i<d} σ^i(r₁) · σ^j(r₁) +
  ∏_{i<j} σ^i(-r₀) ∏_{j ≤ i<d} σ^i(r₁) · σ^j(r₀) = 0`.
Checked on random examples (scratch `check_zero2.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The cleared Riccati polynomial of `P` (of degree at most `d`) at `ρ = -r₀/r₁`:
`∑_{k ≤ d} p_k ∏_{i<k} σ^i(-r₀) ∏_{k ≤ i<d} σ^i(r₁)`. -/
def oreRiccati {A : Type*} [CommRing A] (σ : A →+* A) (d : ℕ) (P : A[X]) (r₀ r₁ : A) : A :=
  ∑ k ∈ Finset.range (d + 1),
    P.coeff k * (∏ i ∈ Finset.range k, σ^[i] (-r₀)) * ∏ i ∈ Finset.Ico k d, σ^[i] r₁

theorem oreRiccati_add {A : Type*} [CommRing A] (σ : A →+* A) (d : ℕ) (P Q : A[X])
    (r₀ r₁ : A) :
    oreRiccati σ d (P + Q) r₀ r₁ = oreRiccati σ d P r₀ r₁ + oreRiccati σ d Q r₀ r₁ := by
  simp only [oreRiccati, coeff_add, add_mul, Finset.sum_add_distrib]

theorem oreRiccati_C_mul {A : Type*} [CommRing A] (σ : A →+* A) (d : ℕ) (β : A) (P : A[X])
    (r₀ r₁ : A) : oreRiccati σ d (C β * P) r₀ r₁ = β * oreRiccati σ d P r₀ r₁ := by
  simp only [oreRiccati, coeff_C_mul, Finset.mul_sum, mul_assoc]

/-- The Riccati polynomial commutes with homomorphisms intertwining the shifts. -/
theorem oreRiccati_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A)
    (τ : B →+* B) (hf : ∀ a, f (σ a) = τ (f a)) (d : ℕ) (P : A[X]) (r₀ r₁ : A) :
    f (oreRiccati σ d P r₀ r₁) = oreRiccati τ d (P.map f) (f r₀) (f r₁) := by
  have hit : ∀ (i : ℕ) (a : A), f (σ^[i] a) = τ^[i] (f a) := by
    intro i
    induction i with
    | zero => intro a; rfl
    | succ i ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hf, ih]
  simp only [oreRiccati, map_sum, map_mul, map_prod, hit, coeff_map, map_neg]

/-- The Riccati polynomial is homogeneous in `(r₀, r₁)`. -/
theorem oreRiccati_mul_left {A : Type*} [CommRing A] (σ : A →+* A) (d : ℕ) (P : A[X])
    (γ r₀ r₁ : A) :
    oreRiccati σ d P (γ * r₀) (γ * r₁) =
      (∏ i ∈ Finset.range d, σ^[i] γ) * oreRiccati σ d P r₀ r₁ := by
  unfold oreRiccati
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← Finset.prod_range_mul_prod_Ico (fun i ↦ σ^[i] γ) hk']
  simp only [← mul_neg, iterate_map_mul, Finset.prod_mul_distrib]
  ring

/-- The Ore product with `0` on the left is `0`. -/
private theorem oreMul_zero_left_riccati {A : Type*} [Semiring A] (σ : A →+* A) (Q : A[X]) :
    oreMul σ 0 Q = 0 := by
  unfold oreMul
  exact Polynomial.sum_zero_index _

/-- The Ore product is additive over finite sums in its left argument. -/
private theorem oreMul_sum_left_riccati {A : Type*} [Semiring A] (σ : A →+* A) {ι : Type*}
    (s : Finset ι) (f : ι → A[X]) (Q : A[X]) :
    oreMul σ (∑ j ∈ s, f j) Q = ∑ j ∈ s, oreMul σ (f j) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, oreMul_zero_left_riccati]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, oreMul_add_left, ih]

/-- The Riccati polynomial of `0` is `0`. -/
private theorem oreRiccati_zero_riccati {A : Type*} [CommRing A] (σ : A →+* A) (d : ℕ)
    (r₀ r₁ : A) : oreRiccati σ d 0 r₀ r₁ = 0 := by
  simp only [oreRiccati, coeff_zero, zero_mul, Finset.sum_const_zero]

/-- The Riccati polynomial is additive over finite sums. -/
private theorem oreRiccati_sum_riccati {A : Type*} [CommRing A] (σ : A →+* A) (d : ℕ)
    {ι : Type*} (s : Finset ι) (f : ι → A[X]) (r₀ r₁ : A) :
    oreRiccati σ d (∑ j ∈ s, f j) r₀ r₁ = ∑ j ∈ s, oreRiccati σ d (f j) r₀ r₁ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, oreRiccati_zero_riccati]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, oreRiccati_add, ih]

/-- The Riccati polynomial of a monomial of degree at most `d`. -/
private theorem oreRiccati_monomial_riccati {A : Type*} [CommRing A] (σ : A →+* A) {d k : ℕ}
    (hk : k ≤ d) (c r₀ r₁ : A) :
    oreRiccati σ d (monomial k c) r₀ r₁ =
      c * (∏ i ∈ Finset.range k, σ^[i] (-r₀)) * ∏ i ∈ Finset.Ico k d, σ^[i] r₁ := by
  unfold oreRiccati
  rw [Finset.sum_eq_single k]
  · rw [coeff_monomial_same]
  · intro j _ hj
    rw [coeff_monomial_of_ne _ hj, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h

/-- The Riccati polynomial of a left multiple of `r₁ L + r₀` vanishes at `(r₀, r₁)`. -/
theorem oreRiccati_oreMul_linear {A : Type*} [CommRing A] (σ : A →+* A) (d : ℕ) (S : A[X])
    (hS : S.natDegree < d) (r₀ r₁ : A) :
    oreRiccati σ d (oreMul σ S (C r₁ * X + C r₀)) r₀ r₁ = 0 := by
  rw [S.as_sum_range' d hS, oreMul_sum_left_riccati, oreRiccati_sum_riccati]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have hj' : j < d := Finset.mem_range.mp hj
  rw [C_mul_X_eq_monomial, ← monomial_zero_left (a := r₀), oreMul_add_right,
    oreMul_monomial_monomial, oreMul_monomial_monomial, oreRiccati_add,
    oreRiccati_monomial_riccati σ (by omega), add_zero, oreRiccati_monomial_riccati σ hj'.le,
    Finset.prod_range_succ, Finset.prod_eq_prod_Ico_succ_bot hj', iterate_map_neg]
  ring

/-- Over a domain, the Riccati polynomial of a left multiple of `r₁ L + r₀` of degree at most
`d` vanishes at `(r₀, r₁)`. -/
private theorem oreRiccati_oreMul_linear_of_natDegree_le_riccati {A : Type*} [CommRing A]
    [IsDomain A] {σ : A →+* A} (hσ : Function.Injective σ) {d : ℕ} {S : A[X]} {r₀ r₁ : A}
    (hr₁ : r₁ ≠ 0) (hdeg : (oreMul σ S (C r₁ * X + C r₀)).natDegree ≤ d) :
    oreRiccati σ d (oreMul σ S (C r₁ * X + C r₀)) r₀ r₁ = 0 := by
  by_cases hS : S = 0
  · rw [hS, oreMul_zero_left_riccati, oreRiccati_zero_riccati]
  · have hG : (C r₁ * X + C r₀ : A[X]) ≠ 0 := fun h0 ↦ by
      have := congrArg (fun p : A[X] ↦ p.coeff 1) h0
      simp only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C_succ, add_zero,
        coeff_zero] at this
      exact hr₁ this
    have hGdeg : (C r₁ * X + C r₀ : A[X]).natDegree = 1 := natDegree_linear hr₁
    rw [natDegree_oreMul hσ hS hG, hGdeg] at hdeg
    exact oreRiccati_oreMul_linear σ d S (by omega) r₀ r₁

/-- A right pseudo-factor of degree one gives a solution of the Riccati equation. -/
theorem oreRiccati_eq_zero_of_pseudoFactor {A : Type*} [CommRing A] [IsDomain A]
    {σ : A →+* A} (hσ : Function.Injective σ) {d : ℕ} {P S R : A[X]} {β : A} (hβ : β ≠ 0)
    (h : C β * P = oreMul σ S R) (hR : R.natDegree = 1) (hP : P.natDegree ≤ d) :
    oreRiccati σ d P (R.coeff 0) (R.coeff 1) = 0 := by
  have hReq : R = C (R.coeff 1) * X + C (R.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one hR.le
  have hr₁ : R.coeff 1 ≠ 0 := by
    intro h0
    rw [h0, C_0, zero_mul, zero_add] at hReq
    rw [hReq, natDegree_C] at hR
    exact zero_ne_one hR
  have hdeg : (oreMul σ S (C (R.coeff 1) * X + C (R.coeff 0))).natDegree ≤ d := by
    rw [← hReq, ← h]
    exact (natDegree_C_mul_le _ _).trans hP
  have h0 := oreRiccati_oreMul_linear_of_natDegree_le_riccati hσ hr₁ hdeg
  rw [← hReq, ← h, oreRiccati_C_mul] at h0
  exact (mul_eq_zero.mp h0).resolve_left hβ

/-- A solution of the Riccati equation with `r₁ ≠ 0` gives the right pseudo-factor
`r₁ L + r₀`. -/
theorem exists_pseudoFactor_of_oreRiccati_eq_zero {A : Type*} [CommRing A] [IsDomain A]
    {σ : A →+* A} (hσ : Function.Injective σ) {d : ℕ} {P : A[X]} (hP : P.natDegree ≤ d)
    {r₀ r₁ : A} (hr₁ : r₁ ≠ 0) (h : oreRiccati σ d P r₀ r₁ = 0) :
    ∃ β : A, β ≠ 0 ∧ ∃ S : A[X], C β * P = oreMul σ S (C r₁ * X + C r₀) := by
  have hGdeg : (C r₁ * X + C r₀ : A[X]).natDegree = 1 := natDegree_linear hr₁
  have hG : (C r₁ * X + C r₀ : A[X]) ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hGdeg
    exact zero_ne_one hGdeg
  obtain ⟨β, hβ, S, R, hSR, hRdeg⟩ := exists_C_mul_eq_oreMul_add hσ P hG
  have hR0 : R.natDegree = 0 := by
    by_cases hR : R = 0
    · rw [hR, natDegree_zero]
    · rw [degree_eq_natDegree hR, degree_eq_natDegree hG, hGdeg] at hRdeg
      exact Nat.lt_one_iff.mp (by exact_mod_cast hRdeg)
  obtain ⟨c, hc⟩ : ∃ c, R = C c := ⟨R.coeff 0, eq_C_of_natDegree_eq_zero hR0⟩
  have hdeg : (oreMul σ S (C r₁ * X + C r₀)).natDegree ≤ d := by
    have : oreMul σ S (C r₁ * X + C r₀) = C β * P - C c := by rw [hSR, hc]; ring
    rw [this]
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hP) ?_)
    rw [natDegree_C]
    exact Nat.zero_le d
  have h0 := oreRiccati_oreMul_linear_of_natDegree_le_riccati hσ hr₁ hdeg
  have h1 : oreRiccati σ d (C β * P) r₀ r₁ =
      oreRiccati σ d (oreMul σ S (C r₁ * X + C r₀)) r₀ r₁ + oreRiccati σ d (C c) r₀ r₁ := by
    rw [hSR, hc, oreRiccati_add]
  rw [oreRiccati_C_mul, h, mul_zero, h0, zero_add, ← monomial_zero_left,
    oreRiccati_monomial_riccati σ (Nat.zero_le d), Finset.prod_range_zero, mul_one,
    ← Finset.range_eq_Ico] at h1
  have hprod : ∏ i ∈ Finset.range d, σ^[i] r₁ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ h0 ↦ hr₁ (hσ.iterate i (by rw [h0, iterate_map_zero]))
  have hc0 : c = 0 := (mul_eq_zero.mp h1.symm).resolve_right hprod
  refine ⟨β, hβ, S, ?_⟩
  rw [hSR, hc, hc0, C_0, add_zero]

end AJConjecture
