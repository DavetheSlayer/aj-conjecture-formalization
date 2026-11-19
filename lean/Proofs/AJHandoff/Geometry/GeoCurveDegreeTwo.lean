import Mathlib
import AJHandoff.Geometry.GeoCurveFunctionField

/-!
# `ℚ(E)` is a quadratic extension of the `r`-line (G-CURVE)

The parameter `r = (M² + L)/(M²(M² - 1))` is transcendental over `ℚ`, and
`[ℚ(E) : ℚ(r)] = 2`: the rational square quotient `(M, L) ↦ (M², L)` has degree two, so `E` is
not birational to the rational square curve.

Route. `M` is transcendental over `ℚ` (`AdjoinRoot.of` is injective since `E` has positive degree
in `L`), and `x = M² = (1 + r)/(r(1 - r))`, so `r` is transcendental. `ℚ(E) = ℚ(r)(M)` because
`L = ((1 + r)/(1 - r))²`; `M` is a root of `T² - x(r)`, irreducible over `ℚ(r)` since `x(r)` has a
simple zero at `r = -1` and so is not a square in `ℚ(r)` (compare `r + 1`-adic valuations, or
evaluate the would-be square root's numerator degree parity).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The parameter `r = (M² + L)/(M²(M² - 1))` in `ℚ(E)`. -/
def geoRfun : GeoFunFieldE :=
  (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 + algebraMap GeoCoordE GeoFunFieldE geoLong) /
    (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 *
      (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 - 1))

/-- `M` in `ℚ(E)`. -/
private def geoMK : GeoFunFieldE := algebraMap GeoCoordE GeoFunFieldE geoMer

/-- `L` in `ℚ(E)`. -/
private def geoLK : GeoFunFieldE := algebraMap GeoCoordE GeoFunFieldE geoLong

/-- The ring map `ℚ[M] → ℚ(E)`. -/
private def geoOfK : ℚ[X] →+* GeoFunFieldE :=
  (algebraMap GeoCoordE GeoFunFieldE).comp (AdjoinRoot.of geoExtraFactorℚ)

/-- The map `ℚ[M] → ℚ(E)` is injective. -/
private theorem geoOfK_injective : Function.Injective geoOfK := by
  have hdeg : geoExtraFactorℚ.degree = 2 := by
    simp only [geoExtraFactorℚ, extraFactor, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coe_mapRingHom, Polynomial.map_one,
      Polynomial.map_ofNat]
    compute_degree!
  exact (IsFractionRing.injective GeoCoordE GeoFunFieldE).comp
    (AdjoinRoot.of.injective_of_degree_ne_zero (by rw [hdeg]; decide))

/-- `geoOfK` is evaluation at `M`. -/
private theorem geoOfK_eq_aeval (p : ℚ[X]) : geoOfK p = aeval geoMK p := by
  conv_lhs => rw [← Polynomial.eval₂_C_X (p := p)]
  rw [Polynomial.hom_eval₂, aeval_def, RingHom.ext_rat (geoOfK.comp C) (algebraMap ℚ _)]
  rfl

/-- The relation `E(M, L) = 0` in `ℚ(E)`. -/
private theorem geo_funFieldE_rel :
    geoLK ^ 2 - (geoMK ^ 4 - 4 * geoMK ^ 2 + 1) * geoLK + geoMK ^ 4 = 0 := by
  have heq : geoExtraFactorℚ = X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) := by
    simp [geoExtraFactorℚ, extraFactor]
  have h : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) : ℚ[X][X]).eval₂
      (AdjoinRoot.of geoExtraFactorℚ) (AdjoinRoot.root geoExtraFactorℚ) = 0 := by
    rw [← heq]
    exact AdjoinRoot.eval₂_root _
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, eval₂_one, map_sub,
    map_add, map_pow, map_mul, map_one, map_ofNat] at h
  have hA : geoLong ^ 2 - (geoMer ^ 4 - 4 * geoMer ^ 2 + 1) * geoLong + geoMer ^ 4 = 0 := by
    simpa [geoMer, geoLong] using h
  have h' := congrArg (algebraMap GeoCoordE GeoFunFieldE) hA
  simp only [map_sub, map_add, map_pow, map_mul, map_one, map_ofNat, map_zero] at h'
  exact h'

/-- On the square curve over a field of characteristic zero, with `x ∉ {0, 1}`, the parameter
`r = (x + L)/(x(x - 1))` satisfies `r ≠ 0`, `r ≠ 1`, `x r (1 - r) = 1 + r` and
`L (1 - r)² = (1 + r)²`. -/
private theorem geo_param_of_curve_field {K : Type*} [Field K] [CharZero K] (x L : K)
    (hE : L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0) (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) :
    (x + L) / (x * (x - 1)) ≠ 0 ∧ 1 - (x + L) / (x * (x - 1)) ≠ 0 ∧
      x * ((x + L) / (x * (x - 1))) * (1 - (x + L) / (x * (x - 1))) =
        1 + (x + L) / (x * (x - 1)) ∧
      L * (1 - (x + L) / (x * (x - 1))) ^ 2 = (1 + (x + L) / (x * (x - 1))) ^ 2 := by
  have hb : x * (x - 1) ≠ 0 := mul_ne_zero hx0 hx1
  have ha : x + L ≠ 0 := by
    intro h
    obtain rfl : L = -x := by linear_combination h
    exact mul_ne_zero hx0 (pow_ne_zero 2 hx1) (by linear_combination hE)
  have hc : x ^ 2 - 2 * x - L ≠ 0 := by
    intro h
    obtain rfl : L = x ^ 2 - 2 * x := by linear_combination -h
    exact mul_ne_zero (mul_ne_zero two_ne_zero hx0) (pow_ne_zero 2 hx1)
      (by linear_combination hE)
  have h1r : 1 - (x + L) / (x * (x - 1)) = (x ^ 2 - 2 * x - L) / (x * (x - 1)) := by
    field_simp
    ring
  have h1r' : 1 + (x + L) / (x * (x - 1)) = (x ^ 2 + L) / (x * (x - 1)) := by
    field_simp
    ring
  refine ⟨div_ne_zero ha hb, by rw [h1r]; exact div_ne_zero hc hb, ?_, ?_⟩
  · rw [h1r, h1r', mul_assoc, div_mul_div_comm, mul_div_assoc',
      div_eq_div_iff (mul_ne_zero hb hb) hb]
    linear_combination (-x * (x * (x - 1))) * hE
  · rw [h1r, h1r', div_pow, div_pow, mul_div_assoc', div_left_inj₀ (pow_ne_zero 2 hb)]
    linear_combination (L - x ^ 2) * hE

/-- The basic facts about `r` in `ℚ(E)`: `r ≠ 0`, `r ≠ 1`, `M² r (1 - r) = 1 + r` and
`L (1 - r)² = (1 + r)²`. -/
private theorem geo_rfun_facts :
    geoRfun ≠ 0 ∧ 1 - geoRfun ≠ 0 ∧ geoMK ^ 2 * geoRfun * (1 - geoRfun) = 1 + geoRfun ∧
      geoLK * (1 - geoRfun) ^ 2 = (1 + geoRfun) ^ 2 := by
  have : CharZero GeoFunFieldE :=
    charZero_of_injective_algebraMap (algebraMap ℚ GeoFunFieldE).injective
  have hM : geoMK ≠ 0 := by
    intro h
    have : geoOfK X = geoOfK 0 := by rw [map_zero]; exact h
    exact X_ne_zero (geoOfK_injective this)
  have hM1 : geoMK ^ 2 - 1 ≠ 0 := by
    intro h
    have : geoOfK (X ^ 2 - 1) = geoOfK 0 := by
      rw [map_zero, map_sub, map_pow, map_one]
      exact h
    have h2 := congrArg (eval 2) (geoOfK_injective this)
    norm_num at h2
  have hE : geoLK ^ 2 - ((geoMK ^ 2) ^ 2 - 4 * geoMK ^ 2 + 1) * geoLK + (geoMK ^ 2) ^ 2 = 0 := by
    linear_combination geo_funFieldE_rel
  exact geo_param_of_curve_field _ _ hE (pow_ne_zero 2 hM) hM1

/-- `M` is transcendental over `ℚ`. -/
private theorem geo_transcendental_merK : Transcendental ℚ geoMK := by
  rw [transcendental_iff_injective]
  intro p q h
  apply geoOfK_injective
  rw [geoOfK_eq_aeval, geoOfK_eq_aeval]
  exact h

/-- `r` is transcendental over `ℚ`. -/
theorem geo_transcendental_rfun : Transcendental ℚ geoRfun := by
  obtain ⟨h0, h1, hx, -⟩ := geo_rfun_facts
  intro halg
  have hx' : geoMK ^ 2 = (1 + geoRfun) * (geoRfun * (1 - geoRfun))⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff (mul_ne_zero h0 h1), ← hx]
    ring
  apply geo_transcendental_merK
  refine IsAlgebraic.of_pow two_pos ?_
  rw [hx']
  exact (isAlgebraic_one.add halg).mul (halg.mul (isAlgebraic_one.sub halg)).inv

/-- `M` does not lie in `ℚ(r)`: `x(r) = (1 + r)/(r(1 - r))` is not a square in `ℚ(r)`, by the
parity of degrees. -/
private theorem geo_merK_notMem_adjoin_rfun :
    geoMK ∉ IntermediateField.adjoin ℚ {geoRfun} := by
  obtain ⟨h0, h1, hx, -⟩ := geo_rfun_facts
  intro hmem
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) geoMK).mp hmem
  have hq : aeval geoRfun q ≠ 0 := by
    intro h
    rw [h, div_zero] at hpq
    exact geo_transcendental_merK (hpq ▸ isAlgebraic_zero)
  have hrel : aeval geoRfun ((1 + X) * q ^ 2 - X * (1 - X) * p ^ 2) = 0 := by
    rw [eq_div_iff hq] at hpq
    simp only [map_sub, map_mul, map_add, map_one, map_pow, aeval_X]
    rw [← hpq]
    linear_combination (-(aeval geoRfun q) ^ 2) * hx
  have hpoly : (1 + X) * q ^ 2 = X * (1 - X) * p ^ 2 := by
    have := (transcendental_iff_injective.mp geo_transcendental_rfun) (hrel.trans (map_zero _).symm)
    exact sub_eq_zero.mp this
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  have hA : (1 + X : ℚ[X]).natDegree = 1 := by compute_degree!
  have hB : (X * (1 - X) : ℚ[X]).natDegree = 2 := by compute_degree!
  have hA0 : (1 + X : ℚ[X]) ≠ 0 := fun h ↦ by simp [h] at hA
  have hB0 : (X * (1 - X) : ℚ[X]) ≠ 0 := fun h ↦ by simp [h] at hB
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero] at hpoly
    exact mul_ne_zero hA0 (pow_ne_zero 2 hq0) hpoly
  have hdeg := congrArg natDegree hpoly
  rw [natDegree_mul hA0 (pow_ne_zero 2 hq0), natDegree_mul hB0 (pow_ne_zero 2 hp0), natDegree_pow,
    natDegree_pow, hA, hB] at hdeg
  omega

/-- `[ℚ(E) : ℚ(r)] = 2`. -/
theorem geo_finrank_functionField_adjoin_rfun :
    Module.finrank (IntermediateField.adjoin ℚ {geoRfun}) GeoFunFieldE = 2 := by
  set F := IntermediateField.adjoin ℚ {geoRfun}
  obtain ⟨h0, h1, hx, hL⟩ := geo_rfun_facts
  have hrF : geoRfun ∈ F := IntermediateField.mem_adjoin_simple_self ℚ geoRfun
  have hxF : (1 + geoRfun) / (geoRfun * (1 - geoRfun)) ∈ F :=
    div_mem (add_mem (one_mem _) hrF) (mul_mem hrF (sub_mem (one_mem _) hrF))
  have hLF : geoLK ∈ F := by
    have h : geoLK = ((1 + geoRfun) / (1 - geoRfun)) ^ 2 := by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 h1)]
      exact hL
    rw [h]
    exact pow_mem (div_mem (add_mem (one_mem _) hrF) (sub_mem (one_mem _) hrF)) 2
  let xF : F := ⟨_, hxF⟩
  have hMx : geoMK ^ 2 = algebraMap F GeoFunFieldE xF := by
    change geoMK ^ 2 = (1 + geoRfun) / (geoRfun * (1 - geoRfun))
    rw [eq_div_iff (mul_ne_zero h0 h1), ← hx]
    ring
  have heval : aeval geoMK (X ^ 2 - C xF) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hMx, sub_self]
  have hint : IsIntegral F geoMK := ⟨X ^ 2 - C xF, monic_X_pow_sub_C _ two_ne_zero, heval⟩
  have htop : IntermediateField.adjoin F {geoMK} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    set G := IntermediateField.adjoin F {geoMK}
    have hFG : ∀ y ∈ F, y ∈ G := fun y hy ↦ G.algebraMap_mem ⟨y, hy⟩
    have hMG : geoMK ∈ G := IntermediateField.mem_adjoin_simple_self F geoMK
    have hLG : geoLK ∈ G := hFG _ hLF
    have hpoly : ∀ p : ℚ[X], geoOfK p ∈ G := by
      intro p
      refine Polynomial.induction_on p (fun a ↦ ?_) (fun p q hp hq ↦ ?_) (fun n a h ↦ ?_)
      · rw [geoOfK_eq_aeval, aeval_C]
        exact hFG _ (F.algebraMap_mem a)
      · rw [map_add]
        exact add_mem hp hq
      · rw [pow_succ, ← mul_assoc, map_mul]
        exact mul_mem h hMG
    have hA : ∀ a : GeoCoordE, algebraMap GeoCoordE GeoFunFieldE a ∈ G := by
      intro a
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      refine Polynomial.induction_on p (fun a ↦ ?_) (fun p q hp hq ↦ ?_) (fun n a h ↦ ?_)
      · rw [AdjoinRoot.mk_C]
        exact hpoly a
      · rw [map_add, map_add]
        exact add_mem hp hq
      · rw [pow_succ, ← mul_assoc, map_mul, map_mul, AdjoinRoot.mk_X]
        exact mul_mem h hLG
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := GeoCoordE) z
    exact div_mem (hA a) (hA b)
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint]
  have hle : (minpoly F geoMK).natDegree ≤ 2 := by
    have hdvd := minpoly.dvd F geoMK heval
    exact (natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero two_pos _)).trans
      (natDegree_X_pow_sub_C (n := 2) (a := xF)).le
  have hne1 : (minpoly F geoMK).natDegree ≠ 1 := by
    rw [Ne, minpoly.natDegree_eq_one_iff]
    rintro ⟨y, hy⟩
    exact geo_merK_notMem_adjoin_rfun (hy ▸ y.2)
  have hpos := minpoly.natDegree_pos hint
  omega

end AJConjecture
