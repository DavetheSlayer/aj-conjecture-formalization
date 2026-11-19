import Mathlib
import AJConjecture.ExtraFactorIrreducible
import AJHandoff.Geometry.GeoMilnorK2

/-!
# The symbol `{M, L}` vanishes in `K₂ᴹ(ℚ̄(E)) ⊗ ℚ` (G-K2)

For any field `F` with `2 ≠ 0` and units `M, L` with `E(M, L) = 0` and `M² ≠ 1`, one has
`2 {M, L} = 0` in `K₂ᴹ(F)`, hence `{M, L} ⊗ 1 = 0` in `K₂ᴹ(F) ⊗_ℤ ℚ`. Applied to the function
field `ℚ̄(E)` with its coordinate functions this is the contract's rational symbol identity.

Scope. Only the symbol identity is formalized. The optional existential corollary (an abstract
`A`-factor realization by some manifold with toric boundary, Guilloux–Marché Prop. 5.2) is not:
it is a statement about 3-manifolds outside the library, and it names no specific manifold or Bloch
class.

Route (geometry_v2 (4)). With `x = M²` and `r = (x + L)/(x(x - 1))` (a unit, as are `1 ± r`, by
`E(M, -x) = x(x - 1)²`, `E(M, x² - 2x) = 2x(x - 1)²`, `E(M, -x²) = 2x²(x - 1)²` and `2 ≠ 0`):
`L = (x r)²` and `x = f/r`, `f = (1 + r)/(1 - r)`. Then
`{M, L} = 2{M, x} + 2{M, r} = 4{M, M} + {x, r} = 4{M, -1} + {f, r} - {r, r}`, and
`{f, r} = {1 + r, r} - {1 - r, r} = -{-1, 1 + r}` by Steinberg at `-r` and `r`; every remaining
term is a multiple of some `{-1, ·}`, which is `2`-torsion.
-/

open Polynomial TensorProduct

noncomputable section

namespace AJConjecture

/-- The square root `f = (x + L)/(x - 1)` of `L` (`x = M²`) and the parameter `r = f/x` on `E`:
`f² = L`, and `r`, `1 - r`, `1 + r` are nonzero with `f(1 - r) = 1 + r`. -/
private theorem geo_extraFactor_param_field {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (M L : F) (hM0 : M ≠ 0) (hL0 : L ≠ 0)
    (hE : L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 = 0) (hM : M ^ 2 ≠ 1) :
    ((M ^ 2 + L) / (M ^ 2 - 1)) ^ 2 = L ∧ (M ^ 2 + L) / (M ^ 2 - 1) ≠ 0 ∧
      (M ^ 2 + L) / (M ^ 2 - 1) / M ^ 2 ≠ 0 ∧ 1 - (M ^ 2 + L) / (M ^ 2 - 1) / M ^ 2 ≠ 0 ∧
      1 + (M ^ 2 + L) / (M ^ 2 - 1) / M ^ 2 ≠ 0 ∧
      (M ^ 2 + L) / (M ^ 2 - 1) * (1 - (M ^ 2 + L) / (M ^ 2 - 1) / M ^ 2) =
        1 + (M ^ 2 + L) / (M ^ 2 - 1) / M ^ 2 := by
  have hx1 : M ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hM
  have hx0 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM0
  have hf : (M ^ 2 + L) / (M ^ 2 - 1) * (M ^ 2 - 1) = M ^ 2 + L := div_mul_cancel₀ _ hx1
  generalize (M ^ 2 + L) / (M ^ 2 - 1) = f at hf ⊢
  have hf2 : f ^ 2 = L := by
    have h : (f ^ 2 - L) * (M ^ 2 - 1) ^ 2 = 0 := by
      linear_combination (f * (M ^ 2 - 1) + M ^ 2 + L) * hf + hE
    rcases mul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hx1
  have hf0 : f ≠ 0 := by
    rintro h
    rw [h] at hf2
    exact hL0 (by rw [← hf2]; ring)
  have h4 : (4 : F) * (M ^ 2) ^ 3 ≠ 0 :=
    mul_ne_zero (by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)
      (pow_ne_zero 3 hx0)
  refine ⟨hf2, hf0, div_ne_zero hf0 hx0, ?_, ?_, ?_⟩
  · intro h
    have hfx : f = M ^ 2 := by field_simp at h; linear_combination -h
    apply h4
    rw [hfx] at hf2
    rw [← hf2] at hE
    linear_combination hE
  · intro h
    have hfx : f = -M ^ 2 := by field_simp at h; linear_combination h
    apply h4
    rw [hfx] at hf2
    rw [← hf2] at hE
    linear_combination hE
  · field_simp
    linear_combination -hf2 + hf

/-- `2 {M, L} = 0` in `K₂ᴹ(F)` for every point of `E` with `M² ≠ 1`, over any field with
`2 ≠ 0`. -/
theorem geo_two_nsmul_symbol_extraFactor {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (M L : Fˣ)
    (hE : (L : F) ^ 2 - ((M : F) ^ 4 - 4 * (M : F) ^ 2 + 1) * L + (M : F) ^ 4 = 0)
    (hM : (M : F) ^ 2 ≠ 1) :
    2 • geoSymbol M L = 0 := by
  obtain ⟨hf2, hf0, hR0, hQ0, hP0, hfQ⟩ :=
    geo_extraFactor_param_field h2 (M : F) L M.ne_zero L.ne_zero hE hM
  set f := ((M : F) ^ 2 + L) / ((M : F) ^ 2 - 1)
  set R := f / (M : F) ^ 2
  set fu := Units.mk0 f hf0
  set Ru := Units.mk0 R hR0
  set Pu := Units.mk0 (1 + R) hP0
  set Qu := Units.mk0 (1 - R) hQ0
  have hLf : L = fu * fu := Units.ext (by simp [fu, ← hf2, sq])
  have hfM : fu = M * M * Ru := Units.ext (by
    simp only [fu, Ru, R, Units.val_mul, Units.val_mk0]
    field_simp)
  have hPQ : fu * Qu = Pu := Units.ext (by simp [fu, Qu, Pu, hfQ])
  have hA : geoSymbol M L = geoSymbol M fu + geoSymbol M fu := by
    rw [hLf, geoSymbol_mul_right]
  have hB : geoSymbol M fu = geoSymbol M M + geoSymbol M M + geoSymbol M Ru := by
    rw [hfM, geoSymbol_mul_right, geoSymbol_mul_right]
  have hC : geoSymbol M (-1) + geoSymbol M M = 0 := by
    have h := geoSymbol_neg_self M
    rwa [show -M = -1 * M by simp, geoSymbol_mul_right] at h
  have hD1 := geoSymbol_antisymm M (-1)
  have hD2 := geoSymbol_two_nsmul_neg_one M
  have hE1 : geoSymbol (M * M) Ru = geoSymbol M Ru + geoSymbol M Ru := geoSymbol_mul_left _ _ _
  have hE2 : geoSymbol fu Ru = geoSymbol (M * M) Ru + geoSymbol Ru Ru := by
    rw [hfM, geoSymbol_mul_left]
  have hF1 : geoSymbol Ru (-1) + geoSymbol Ru Ru = 0 := by
    have h := geoSymbol_neg_self Ru
    rwa [show -Ru = -1 * Ru by simp, geoSymbol_mul_right] at h
  have hF2 := geoSymbol_antisymm Ru (-1)
  have hF3 := geoSymbol_two_nsmul_neg_one Ru
  have hG1 : geoSymbol fu Ru + geoSymbol Qu Ru = geoSymbol Pu Ru := by
    rw [← geoSymbol_mul_left, hPQ]
  have hG2 := geoSymbol_antisymm Qu Ru
  have hG3 : geoSymbol Ru Qu = 0 :=
    geoSymbol_eq_zero_of_add_eq_one _ _ (by simp [Ru, Qu])
  have hG4 : geoSymbol (-Ru) Pu = 0 :=
    geoSymbol_eq_zero_of_add_eq_one _ _ (by simp [Ru, Pu])
  have hG5 : geoSymbol (-Ru) Pu = geoSymbol (-1) Pu + geoSymbol Ru Pu := by
    rw [show -Ru = -1 * Ru by simp, geoSymbol_mul_left]
  have hG6 := geoSymbol_antisymm Pu Ru
  have hG7 := geoSymbol_two_nsmul_neg_one Pu
  linear_combination (norm := module) (2 : ℤ) • hA + (4 : ℤ) • hB - (2 : ℤ) • hE1 -
    (2 : ℤ) • hE2 + (8 : ℤ) • hC - (8 : ℤ) • hD1 + (4 : ℤ) • hD2 - (2 : ℤ) • hF1 +
    (2 : ℤ) • hF2 - hF3 + (2 : ℤ) • hG1 - (2 : ℤ) • hG2 + (2 : ℤ) • hG3 + (2 : ℤ) • hG6 +
    (2 : ℤ) • hG5 - (2 : ℤ) • hG4 + hG7

/-- `{M, L} ⊗ 1 = 0` in `K₂ᴹ(F) ⊗_ℤ ℚ`. -/
theorem geo_symbol_extraFactor_tmul_rat {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (M L : Fˣ)
    (hE : (L : F) ^ 2 - ((M : F) ^ 4 - 4 * (M : F) ^ 2 + 1) * L + (M : F) ^ 4 = 0)
    (hM : (M : F) ^ 2 ≠ 1) :
    geoSymbol M L ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
  have h := geo_two_nsmul_symbol_extraFactor h2 M L hE hM
  have h' : (2 : ℤ) • geoSymbol M L = 0 := by rw [two_zsmul, ← two_nsmul, h]
  rw [show (1 : ℚ) = (2 : ℤ) • (1 / 2 : ℚ) by norm_num, ← TensorProduct.smul_tmul, h',
    TensorProduct.zero_tmul]

/-- `E` over `ℚ̄`. -/
abbrev geoExtraFactorQbar : (AlgebraicClosure ℚ)[X][X] :=
  extraFactor.map (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure ℚ)))

/-- `E` over `ℚ̄`, written out. -/
private theorem geoExtraFactorQbar_eq :
    geoExtraFactorQbar = X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) := by
  simp [geoExtraFactorQbar, extraFactor]

/-- `E` has degree `2` in `L`. -/
private theorem geoExtraFactorQbar_natDegree : geoExtraFactorQbar.natDegree = 2 := by
  rw [geoExtraFactorQbar_eq]
  compute_degree!

/-- No monomial `c Mⁱ` has a complementary monomial summing to `M⁴ - 4M² + 1` over `ℚ̄`. -/
private theorem geo_monomial_add_ne_trace_Qbar (c : AlgebraicClosure ℚ) (hc : c ≠ 0) (i : ℕ)
    (hi : i ≤ 4) :
    (C c * (C c * X ^ i) + X ^ (4 - i) : (AlgebraicClosure ℚ)[X]) ≠
      C c * (X ^ 4 - 4 * X ^ 2 + 1) := by
  intro h
  have h2 := congrArg (fun p : (AlgebraicClosure ℚ)[X] ↦ p.coeff 2) h
  have h0 := congrArg (fun p : (AlgebraicClosure ℚ)[X] ↦ p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one, coeff_ofNat_mul] at h0 h2
  clear h
  interval_cases i <;> simp_all

/-- `E` has no root in `ℚ̄[M]`. -/
private theorem geo_extraFactorQbar_no_root (a : (AlgebraicClosure ℚ)[X]) :
    a ^ 2 - (X ^ 4 - 4 * X ^ 2 + 1) * a + X ^ 4 ≠ 0 := by
  intro h
  have hab : a * ((X ^ 4 - 4 * X ^ 2 + 1) - a) = X ^ 4 := by linear_combination -h
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X _).mp (Dvd.intro _ hab)
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  obtain rfl : a = C c * X ^ i := by rw [← hu, ← hcu, mul_comm]
  have hXi : (X ^ i : (AlgebraicClosure ℚ)[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hsplit : (X ^ 4 : (AlgebraicClosure ℚ)[X]) = X ^ i * X ^ (4 - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have hb : C c * ((X ^ 4 - 4 * X ^ 2 + 1) - C c * X ^ i) = X ^ (4 - i) := by
    apply mul_left_cancel₀ hXi
    rw [← hsplit]
    linear_combination hab
  apply geo_monomial_add_ne_trace_Qbar c hc0 i hi
  rw [← hb]
  ring

/-- `E` is prime in `ℚ̄[M][L]` (it is irreducible over `ℂ ⊇ ℚ̄`). -/
theorem geo_prime_extraFactorQbar : Prime geoExtraFactorQbar := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime, geoExtraFactorQbar_eq]
  have hmonic : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) :
      (AlgebraicClosure ℚ)[X][X]).Monic := by
    monicity!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by
    rw [← geoExtraFactorQbar_eq, geoExtraFactorQbar_natDegree]) (by
    rw [← geoExtraFactorQbar_eq, geoExtraFactorQbar_natDegree]; omega)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha ↦ geo_extraFactorQbar_no_root a ?_
  have hroot := (mem_roots hmonic.ne_zero).mp ha
  simpa [IsRoot.def] using hroot

/-- The coordinate ring `ℚ̄[M, L]/(E)`. -/
abbrev GeoCoordEbar : Type := AdjoinRoot geoExtraFactorQbar

instance : IsDomain GeoCoordEbar := AdjoinRoot.isDomain_of_prime geo_prime_extraFactorQbar

/-- The function field `ℚ̄(E)`. -/
abbrev GeoFunFieldEbar : Type := FractionRing GeoCoordEbar

/-- The coordinate function `M` on `E`. -/
def geoMerBar : GeoFunFieldEbar := algebraMap GeoCoordEbar _ (AdjoinRoot.of _ Polynomial.X)

/-- The coordinate function `L` on `E`. -/
def geoLongBar : GeoFunFieldEbar := algebraMap GeoCoordEbar _ (AdjoinRoot.root _)

/-- A nonzero polynomial in `M` alone is a nonzero function on `E`. -/
private theorem geo_algebraMap_of_ne_zero_Qbar (p : (AlgebraicClosure ℚ)[X]) (hp : p ≠ 0) :
    algebraMap GeoCoordEbar GeoFunFieldEbar (AdjoinRoot.of _ p) ≠ 0 := by
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), AdjoinRoot.of,
    RingHom.comp_apply, AdjoinRoot.mk_eq_zero]
  intro h
  have h' := Polynomial.natDegree_le_of_dvd h (C_ne_zero.mpr hp)
  rw [geoExtraFactorQbar_natDegree, natDegree_C] at h'
  omega

theorem geoMerBar_ne_zero : geoMerBar ≠ 0 :=
  geo_algebraMap_of_ne_zero_Qbar X X_ne_zero

theorem geoLongBar_ne_zero : geoLongBar ≠ 0 := by
  rw [geoLongBar, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), AdjoinRoot.root,
    AdjoinRoot.mk_eq_zero]
  intro h
  have h' := Polynomial.natDegree_le_of_dvd h X_ne_zero
  rw [geoExtraFactorQbar_natDegree, natDegree_X] at h'
  omega

/-- The coordinate functions satisfy `E(M, L) = 0`. -/
private theorem geo_extraFactor_merBar_longBar :
    geoLongBar ^ 2 - (geoMerBar ^ 4 - 4 * geoMerBar ^ 2 + 1) * geoLongBar + geoMerBar ^ 4 = 0 := by
  have h : eval₂ (AdjoinRoot.of geoExtraFactorQbar) (AdjoinRoot.root geoExtraFactorQbar)
      (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4)) = 0 := by
    rw [← geoExtraFactorQbar_eq]
    exact AdjoinRoot.eval₂_root _
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_X_pow] at h
  have h' := congrArg (algebraMap GeoCoordEbar GeoFunFieldEbar) h
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at h'
  rw [geoMerBar, geoLongBar]
  linear_combination h'

/-- G-K2: `{M, L} = 0` in `K₂ᴹ(ℚ̄(E)) ⊗ ℚ`. -/
theorem geo_K2_functionField :
    geoSymbol (Units.mk0 geoMerBar geoMerBar_ne_zero) (Units.mk0 geoLongBar geoLongBar_ne_zero)
      ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
  have h2 : (2 : GeoFunFieldEbar) ≠ 0 := by
    have h := geo_algebraMap_of_ne_zero_Qbar 2 two_ne_zero
    simpa only [map_ofNat] using h
  have hM : geoMerBar ^ 2 ≠ 1 := by
    have h := geo_algebraMap_of_ne_zero_Qbar (X ^ 2 - 1) (X_pow_sub_C_ne_zero two_pos 1)
    simp only [map_sub, map_pow, map_one] at h
    rw [geoMerBar]
    exact sub_ne_zero.mp h
  exact geo_symbol_extraFactor_tmul_rat h2 _ _ geo_extraFactor_merBar_longBar hM

end AJConjecture
