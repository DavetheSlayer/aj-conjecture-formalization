import Mathlib
import AJHandoff.LocalTheory.LocBasic

/-!
# The `h`-jets of `ℂ[[h]][z]`

For `f ∈ ℂ[[h]][z]` write `f = f₀ + h f₁ + O(h²)` with `f₀, f₁ ∈ ℂ[z]`. The reduction `f ↦ f₀` is
a ring homomorphism; `f ↦ f₁` obeys the Leibniz rule, and the shift `σ(z) = Q z`,
`Q = 1 + c h + O(h²)`, acts on jets by `σ^i(f)₀ = f₀`, `σ^i(f)₁ = f₁ + i c z f₀'`. This is the only
place where the shift enters the first-order calculus; the source writes it as
`σ^i f = f + h i δ f + …`, `δ = c z d/dz`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The reduction `f ↦ f(0, z)` of `f ∈ ℂ[[h]][z]`. -/
def locJet0 : LocPoly →+* ℂ[X] := Polynomial.mapRingHom PowerSeries.constantCoeff

/-- The first `h`-jet `f ↦ (∂f/∂h)(0, z)` of `f ∈ ℂ[[h]][z]`. -/
def locJet1 (f : LocPoly) : ℂ[X] := f.sum fun e a ↦ monomial e (PowerSeries.coeff 1 a)

/-- The coefficients of the reduction. -/
private theorem coeff_locJet0_aux (f : LocPoly) (n : ℕ) :
    (locJet0 f).coeff n = PowerSeries.constantCoeff (f.coeff n) := by
  simp only [locJet0, coe_mapRingHom, coeff_map]

/-- The coefficients of the first jet. -/
private theorem coeff_locJet1_aux (f : LocPoly) (n : ℕ) :
    (locJet1 f).coeff n = PowerSeries.coeff 1 (f.coeff n) := by
  rw [locJet1, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · rw [coeff_monomial_same]
  · intro b _ hb
    rw [coeff_monomial_of_ne _ hb.symm]
  · intro h
    rw [Polynomial.notMem_support_iff.1 h, map_zero, monomial_zero_right, coeff_zero]

/-- The iterated shift is the substitution `z ↦ Q^i z`. -/
private theorem shiftHom_iterate_eq_comp_aux (δ : LocDilation) (i : ℕ) (f : LocPoly) :
    δ.shiftHom^[i] f = f.comp (C ((δ.Q : PowerSeries ℂ) ^ i) * X) := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    change (f.comp _).comp _ = _
    rw [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, pow_succ]

theorem locJet1_add (f g : LocPoly) : locJet1 (f + g) = locJet1 f + locJet1 g := by
  ext n
  simp only [coeff_locJet1_aux, coeff_add, map_add]

/-- The Leibniz rule for the first jet. -/
theorem locJet1_mul (f g : LocPoly) :
    locJet1 (f * g) = locJet1 f * locJet0 g + locJet0 f * locJet1 g := by
  ext n
  simp only [coeff_locJet1_aux, coeff_add, coeff_mul, map_sum, PowerSeries.coeff_one_mul,
    coeff_locJet0_aux, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The shift does not change the reduction. -/
theorem locJet0_shift (δ : LocDilation) (i : ℕ) (f : LocPoly) :
    locJet0 (δ.shiftHom^[i] f) = locJet0 f := by
  ext n
  rw [coeff_locJet0_aux, coeff_locJet0_aux, shiftHom_iterate_eq_comp_aux, comp_C_mul_X_coeff,
    map_mul, map_pow, map_pow, δ.constantCoeff_Q, one_pow, one_pow, mul_one]

/-- The first jet of an iterated shift: `σ^i(f)₁ = f₁ + i c z f₀'`. -/
theorem locJet1_shift (δ : LocDilation) (i : ℕ) (f : LocPoly) :
    locJet1 (δ.shiftHom^[i] f) = locJet1 f + C ((i : ℂ) * δ.c) * (X * derivative (locJet0 f)) := by
  ext n
  rw [coeff_add, coeff_C_mul, coeff_locJet1_aux, coeff_locJet1_aux, shiftHom_iterate_eq_comp_aux,
    comp_C_mul_X_coeff, PowerSeries.coeff_one_mul, ← pow_mul, PowerSeries.coeff_one_pow,
    map_pow, δ.constantCoeff_Q]
  rcases n with _ | n
  · simp
  · rw [coeff_X_mul, coeff_derivative, coeff_locJet0_aux, LocDilation.c]
    push_cast
    ring

/-- The jets of `h`, and `h` is fixed by the shift. -/
theorem locJet_locH (δ : LocDilation) :
    locJet0 locH = 0 ∧ locJet1 locH = 1 ∧ δ.shift locH = locH := by
  refine ⟨?_, ?_, ?_⟩
  · simp [locJet0, locH]
  · ext n
    rw [coeff_locJet1_aux, locH, coeff_C, coeff_one]
    split_ifs <;> simp
  · change (C PowerSeries.X).comp _ = _
    rw [C_comp, locH]

/-- The coefficients of the reduction: `(f₀)_n = (f_n)(0)`. -/
theorem coeff_locJet0 (f : LocPoly) (n : ℕ) :
    (locJet0 f).coeff n = PowerSeries.constantCoeff (f.coeff n) :=
  coeff_locJet0_aux f n

/-- The coefficients of the first jet: `(f₁)_n = [h¹] f_n`. -/
theorem coeff_locJet1 (f : LocPoly) (n : ℕ) :
    (locJet1 f).coeff n = PowerSeries.coeff 1 (f.coeff n) :=
  coeff_locJet1_aux f n

/-- The iterated shift is the substitution `z ↦ Q^i z`. -/
theorem shiftHom_iterate_eq_comp (δ : LocDilation) (i : ℕ) (f : LocPoly) :
    δ.shiftHom^[i] f = f.comp (C ((δ.Q : PowerSeries ℂ) ^ i) * X) :=
  shiftHom_iterate_eq_comp_aux δ i f

end AJConjecture
