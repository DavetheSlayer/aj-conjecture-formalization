import Mathlib
import AJHandoff.LocalTheory.LocJointRing
import AJHandoff.LocalTheory.LocHJet

/-!
# I-GAUGE: rational basis changes (law (7) of the source)

Under a change of basis of the quotient with matrix `G ∈ GL_r(F)`, convention
`B' = G⁻¹ B σ(G)`, the determinant becomes `D' = D σ(g)/g`, `g = det G`. Write
`g = h^k g'` with `g'` an `h`-adic unit of reduction `g₀ ∈ ℂ(z)^×`. Then `D'₀ = D₀` and
`D'₁/D'₀ = D₁/D₀ + c z g₀'/g₀`, so the normalized index shifts by the integer `ord_{z₀} g₀`:
`ind(D') = ind(D) + ord_{z₀}(g₀)`. Hence the invariant under rational gauges is the class in
`ℂ/ℤ`; a jointly regular invertible gauge (`G ∈ GL_r(R₀)`) has `ord_{z₀} g₀ = 0` and preserves the
number; the opposite convention `B' = G B σ(G)⁻¹` shifts by `-ord_{z₀}(g₀)`. Singular gauges are
included: no regularity of `G` at the node is assumed in law (7).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The reduction of a shift. -/
private theorem locJet0_shift_gauge (δ : LocDilation) (f : LocPoly) :
    locJet0 (δ.shift f) = locJet0 f :=
  locJet0_shift δ 1 f

/-- The first jet of a shift. -/
private theorem locJet1_shift_gauge (δ : LocDilation) (f : LocPoly) :
    locJet1 (δ.shift f) = locJet1 f + C δ.c * (X * derivative (locJet0 f)) := by
  have := locJet1_shift δ 1 f
  simpa using this

/-- Multiplying by the coboundary `σ(a/b)/(a/b)` adds `ord (a₀) - ord (b₀)` to the index. -/
private theorem hasNormalizedIndex_mul_shift_div_gauge (δ : LocDilation) {z₀ : ℂ}
    {D : LocField} {D₀ D₁ : RatFunc ℂ} (hD : HasHJet D D₀ D₁) (hD₀ : D₀ ≠ 0) {ι : ℂ}
    (hι : HasNormalizedIndex δ.c z₀ D₀ D₁ ι) {a b : LocPoly} (ha : locJet0 a ≠ 0)
    (hb : locJet0 b ≠ 0) :
    ∃ D₁' : RatFunc ℂ, HasHJet (D * (algebraMap LocPoly LocField (δ.shift a) *
        algebraMap LocPoly LocField b / (algebraMap LocPoly LocField a *
          algebraMap LocPoly LocField (δ.shift b)))) D₀ D₁' ∧
      HasNormalizedIndex δ.c z₀ D₀ D₁'
        (ι + ((locJet0 a).rootMultiplicity z₀ - (locJet0 b).rootMultiplicity z₀)) := by
  obtain ⟨c, e, he, hce, rfl, rfl⟩ := hD
  have hinjF := IsFractionRing.injective LocPoly LocField
  have hneF : ∀ p : LocPoly, locJet0 p ≠ 0 → algebraMap LocPoly LocField p ≠ 0 :=
    fun p hp ↦ (map_ne_zero_iff _ hinjF).2 fun h ↦ hp (by rw [h, map_zero])
  have hσa := hneF (δ.shift a) (by rwa [locJet0_shift_gauge])
  have hσb := hneF (δ.shift b) (by rwa [locJet0_shift_gauge])
  have haF := hneF a ha
  have hbF := hneF b hb
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hne : ∀ p : ℂ[X], p ≠ 0 → algebraMap ℂ[X] (RatFunc ℂ) p ≠ 0 :=
    fun p hp ↦ (map_ne_zero_iff _ hinj).2 hp
  have hE := hne _ he
  have hA := hne _ ha
  have hB := hne _ hb
  have hC : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 c) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hD₀
    exact hD₀ rfl
  have hden : locJet0 (e * a * δ.shift b) ≠ 0 := by
    rw [map_mul, map_mul, locJet0_shift_gauge]
    exact mul_ne_zero (mul_ne_zero he ha) hb
  refine ⟨_, ⟨c * δ.shift a * b, e * a * δ.shift b, hden, ?_, ?_, rfl⟩, ?_⟩
  · simp only [map_mul]
    rw [← hce]
    field_simp
  · simp only [map_mul, locJet0_shift_gauge]
    field_simp
  · have h1 := hasSimpleResidue_logDeriv ha z₀
    have h2 : HasSimpleResidue (-(algebraMap ℂ[X] (RatFunc ℂ) (derivative (locJet0 b)) /
        algebraMap ℂ[X] (RatFunc ℂ) (locJet0 b))) z₀
        (-((locJet0 b).rootMultiplicity z₀ : ℂ)) := by
      have := isRegularAt_neg (hasSimpleResidue_logDeriv hb z₀)
      unfold HasSimpleResidue
      convert this using 1
      rw [map_neg]
      ring
    have key := hι.add (h1.add h2)
    unfold HasNormalizedIndex
    have hc' : (RatFunc.C δ.c : RatFunc ℂ) ≠ 0 := by simpa using δ.c_ne_zero
    have hX' : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    convert key using 1
    · simp only [locJet1_mul, map_mul, locJet0_shift_gauge, locJet1_shift_gauge, map_sub,
        map_add, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      field_simp
      ring

/-- An order `m` of `a₀/b₀` at `z₀` is `ord a₀ - ord b₀`. -/
private theorem eq_rootMultiplicity_sub_of_hasOrderAt_gauge {a b : ℂ[X]} (ha : a ≠ 0)
    (hb : b ≠ 0) {z₀ : ℂ} {m : ℤ}
    (hm : HasOrderAt (algebraMap ℂ[X] (RatFunc ℂ) a / algebraMap ℂ[X] (RatFunc ℂ) b) z₀ m) :
    m = (a.rootMultiplicity z₀ : ℤ) - b.rootMultiplicity z₀ := by
  obtain ⟨u, ⟨α, β, hα, hβ, huβ⟩, hu⟩ := hm
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hne : ∀ p : ℂ[X], p ≠ 0 → algebraMap ℂ[X] (RatFunc ℂ) p ≠ 0 :=
    fun p hp ↦ (map_ne_zero_iff _ hinj).2 hp
  have hα0 : α ≠ 0 := fun h ↦ hα (by rw [h, eval_zero])
  have hβ0 : β ≠ 0 := fun h ↦ hβ (by rw [h, eval_zero])
  have hB := hne b hb
  have hμ : (RatFunc.X - RatFunc.C z₀ : RatFunc ℂ) = algebraMap ℂ[X] (RatFunc ℂ) (X - C z₀) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hμ0 := hne _ (X_sub_C_ne_zero z₀)
  have hrα : α.rootMultiplicity z₀ = 0 := rootMultiplicity_eq_zero hα
  have hrβ : β.rootMultiplicity z₀ = 0 := rootMultiplicity_eq_zero hβ
  rcases m with n | n
  · have hpoly : a * β = (X - C z₀) ^ n * α * b := by
      apply hinj
      simp only [map_mul, map_pow, ← huβ]
      rw [hμ, Int.ofNat_eq_natCast, zpow_natCast] at hu
      rw [← div_mul_cancel₀ (algebraMap ℂ[X] (RatFunc ℂ) a) hB, hu]
      ring
    have h := congrArg (rootMultiplicity z₀) hpoly
    rw [rootMultiplicity_mul (mul_ne_zero ha hβ0), rootMultiplicity_mul, rootMultiplicity_mul,
      rootMultiplicity_X_sub_C_pow, hrα, hrβ] at h
    · simp only [Int.ofNat_eq_natCast]
      omega
    · exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero z₀)) hα0
    · rw [← hpoly]
      exact mul_ne_zero ha hβ0
  · have hpoly : a * β * (X - C z₀) ^ (n + 1) = α * b := by
      apply hinj
      simp only [map_mul, map_pow, ← huβ]
      rw [hμ, zpow_negSucc] at hu
      rw [← div_mul_cancel₀ (algebraMap ℂ[X] (RatFunc ℂ) a) hB, hu]
      field_simp
    have h := congrArg (rootMultiplicity z₀) hpoly
    rw [rootMultiplicity_mul, rootMultiplicity_mul (mul_ne_zero ha hβ0), rootMultiplicity_mul,
      rootMultiplicity_X_sub_C_pow, hrα, hrβ] at h
    · rw [Int.negSucc_eq]
      omega
    · exact mul_ne_zero hα0 hb
    · exact mul_ne_zero (mul_ne_zero ha hβ0) (pow_ne_zero _ (X_sub_C_ne_zero z₀))

/-- A presentation of the gauge: `σ(g)/g = σ(a/b)/(a/b)` with `g₀ = a₀/b₀`. -/
private theorem exists_presentation_shift_div_gauge (δ : LocDilation) {g : LocField} {k : ℤ}
    {g₀ g₁ : RatFunc ℂ} (hg : HasHJet (algebraMap LocPoly LocField locH ^ (-k) * g) g₀ g₁)
    (hg₀ : g₀ ≠ 0) :
    ∃ a b : LocPoly, locJet0 a ≠ 0 ∧ locJet0 b ≠ 0 ∧
      g₀ = algebraMap ℂ[X] (RatFunc ℂ) (locJet0 a) / algebraMap ℂ[X] (RatFunc ℂ) (locJet0 b) ∧
      g ≠ 0 ∧ δ.fieldShift g / g = algebraMap LocPoly LocField (δ.shift a) *
        algebraMap LocPoly LocField b / (algebraMap LocPoly LocField a *
          algebraMap LocPoly LocField (δ.shift b)) := by
  obtain ⟨a, b, hb, hab, rfl, -⟩ := hg
  have ha : locJet0 a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_div] at hg₀
    exact hg₀ rfl
  have hinjF := IsFractionRing.injective LocPoly LocField
  have hneF : ∀ p : LocPoly, locJet0 p ≠ 0 → algebraMap LocPoly LocField p ≠ 0 :=
    fun p hp ↦ (map_ne_zero_iff _ hinjF).2 fun h ↦ hp (by rw [h, map_zero])
  have hσa := hneF (δ.shift a) (by rwa [locJet0_shift_gauge])
  have hσb := hneF (δ.shift b) (by rwa [locJet0_shift_gauge])
  have haF := hneF a ha
  have hbF := hneF b hb
  have hH : algebraMap LocPoly LocField locH ≠ 0 :=
    (map_ne_zero_iff _ hinjF).2 (Polynomial.prime_C_iff.2 PowerSeries.prime_X).ne_zero
  have hg : g = algebraMap LocPoly LocField locH ^ k *
      (algebraMap LocPoly LocField a / algebraMap LocPoly LocField b) := by
    rw [← hab, zpow_neg]
    field_simp
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact mul_ne_zero (zpow_ne_zero _ hH) (div_ne_zero haF hbF)
  refine ⟨a, b, ha, hb, rfl, hg0, ?_⟩
  rw [hg, map_mul, map_zpow₀, map_div₀, δ.fieldShift_algebraMap, δ.fieldShift_algebraMap,
    δ.fieldShift_algebraMap, (locJet_locH δ).2.2]
  field_simp

/-- The determinant of a gauge-transformed matrix. -/
theorem det_gauge (δ : LocDilation) {r : ℕ} (B G : Matrix (Fin r) (Fin r) LocField)
    (hG : G.det ≠ 0) :
    (G⁻¹ * B * G.map δ.fieldShift).det = B.det * δ.fieldShift G.det / G.det := by
  have h : (G.map δ.fieldShift).det = δ.fieldShift G.det := (RingHom.map_det δ.fieldShiftHom G).symm
  rw [Matrix.det_mul, Matrix.det_mul, h, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  field_simp

set_option linter.unusedVariables false in
/-- Law (7): `ind(D σ(g)/g) = ind(D) + ord_{z₀}(g₀)`. -/
theorem hasNormalizedIndex_mul_coboundary (δ : LocDilation) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    {D g : LocField} {D₀ D₁ : RatFunc ℂ} (hD : HasHJet D D₀ D₁) (hD₀ : D₀ ≠ 0) {ι : ℂ}
    (hι : HasNormalizedIndex δ.c z₀ D₀ D₁ ι) {k : ℤ} {g₀ g₁ : RatFunc ℂ}
    (hg : HasHJet (algebraMap LocPoly LocField locH ^ (-k) * g) g₀ g₁) (hg₀ : g₀ ≠ 0) {m : ℤ}
    (hm : HasOrderAt g₀ z₀ m) :
    ∃ D₁' : RatFunc ℂ, HasHJet (D * δ.fieldShift g / g) D₀ D₁' ∧
      HasNormalizedIndex δ.c z₀ D₀ D₁' (ι + m) := by
  obtain ⟨a, b, ha, hb, rfl, -, hσg⟩ := exists_presentation_shift_div_gauge δ hg hg₀
  rw [eq_rootMultiplicity_sub_of_hasOrderAt_gauge ha hb hm, mul_div_assoc, hσg]
  push_cast
  exact hasNormalizedIndex_mul_shift_div_gauge δ hD hD₀ hι ha hb

set_option linter.unusedVariables false in
/-- The opposite convention `B' = G B σ(G)⁻¹`: `ind(D g/σ(g)) = ind(D) - ord_{z₀}(g₀)`. -/
theorem hasNormalizedIndex_mul_inv_coboundary (δ : LocDilation) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    {D g : LocField} {D₀ D₁ : RatFunc ℂ} (hD : HasHJet D D₀ D₁) (hD₀ : D₀ ≠ 0) {ι : ℂ}
    (hι : HasNormalizedIndex δ.c z₀ D₀ D₁ ι) {k : ℤ} {g₀ g₁ : RatFunc ℂ}
    (hg : HasHJet (algebraMap LocPoly LocField locH ^ (-k) * g) g₀ g₁) (hg₀ : g₀ ≠ 0) {m : ℤ}
    (hm : HasOrderAt g₀ z₀ m) :
    ∃ D₁' : RatFunc ℂ, HasHJet (D * g / δ.fieldShift g) D₀ D₁' ∧
      HasNormalizedIndex δ.c z₀ D₀ D₁' (ι - m) := by
  obtain ⟨a, b, ha, hb, rfl, hg0, hσg⟩ := exists_presentation_shift_div_gauge δ hg hg₀
  have hσg0 : δ.fieldShift g ≠ 0 := (map_ne_zero_iff _ δ.fieldShift.injective).2 hg0
  have hinv : D * g / δ.fieldShift g = D * (algebraMap LocPoly LocField (δ.shift b) *
      algebraMap LocPoly LocField a / (algebraMap LocPoly LocField b *
        algebraMap LocPoly LocField (δ.shift a))) := by
    rw [mul_div_assoc, ← inv_div, hσg, inv_div]
    ring
  rw [eq_rootMultiplicity_sub_of_hasOrderAt_gauge ha hb hm, hinv]
  obtain ⟨D₁', h1, h2⟩ := hasNormalizedIndex_mul_shift_div_gauge δ hD hD₀ hι hb ha
  refine ⟨D₁', h1, ?_⟩
  convert h2 using 1
  push_cast
  ring

set_option linter.unusedVariables false in
/-- A jointly regular invertible gauge preserves the normalized index. -/
theorem hasNormalizedIndex_gauge_of_isJointRegular (δ : LocDilation) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    {r : ℕ} {B G : Matrix (Fin r) (Fin r) LocField} (hG : IsJointRegular z₀ G)
    {D₀ D₁ : RatFunc ℂ} (hD : HasHJet B.det D₀ D₁) (hD₀ : D₀ ≠ 0) {ι : ℂ}
    (hι : HasNormalizedIndex δ.c z₀ D₀ D₁ ι) :
    ∃ D₁' : RatFunc ℂ, HasHJet (G⁻¹ * B * G.map δ.fieldShift).det D₀ D₁' ∧
      HasNormalizedIndex δ.c z₀ D₀ D₁' ι := by
  obtain ⟨G', hG'u, rfl⟩ := hG
  set j := algebraMap (LocJointRing z₀) LocField
  obtain ⟨⟨x, t⟩, hxt⟩ := IsLocalization.mk'_surjective (jointIdeal z₀).primeCompl G'.det
  dsimp only at hxt
  have hx : x ∈ (jointIdeal z₀).primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_mk'_iff (LocJointRing z₀), hxt]
    exact hG'u
  have hspec := IsLocalization.mk'_spec (LocJointRing z₀) x t
  rw [hxt] at hspec
  have hspec' := congrArg j hspec
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec'
  have hdet : (G'.map j).det = j G'.det := by exact (RingHom.map_det j G').symm
  have hx0 : locJet0 x ≠ 0 := fun h ↦ hx (by
    change jointEval z₀ x = 0
    exact (congrArg (eval z₀) h).trans (eval_zero))
  have ht0 : locJet0 (t : LocPoly) ≠ 0 := fun h ↦ t.2 (by
    change jointEval z₀ t = 0
    exact (congrArg (eval z₀) h).trans (eval_zero))
  have hinjF := IsFractionRing.injective LocPoly LocField
  have hneF : ∀ p : LocPoly, locJet0 p ≠ 0 → algebraMap LocPoly LocField p ≠ 0 :=
    fun p hp ↦ (map_ne_zero_iff _ hinjF).2 fun h ↦ hp (by rw [h, map_zero])
  have htF := hneF _ ht0
  have hxF := hneF _ hx0
  have hσt := hneF (δ.shift t) (by rwa [locJet0_shift_gauge])
  have hjdet : j G'.det = algebraMap LocPoly LocField x / algebraMap LocPoly LocField t :=
    eq_div_of_mul_eq htF hspec'
  rw [det_gauge δ B _ (by rw [hdet, hjdet]; exact div_ne_zero hxF htF), hdet, hjdet, map_div₀,
    δ.fieldShift_algebraMap, δ.fieldShift_algebraMap]
  obtain ⟨D₁', h1, h2⟩ := hasNormalizedIndex_mul_shift_div_gauge δ hD hD₀ hι hx0 ht0
  refine ⟨D₁', ?_, ?_⟩
  · convert h1 using 1
    field_simp
  · have hrx : (locJet0 x).rootMultiplicity z₀ = 0 := rootMultiplicity_eq_zero hx
    have hrt : (locJet0 (t : LocPoly)).rootMultiplicity z₀ = 0 := rootMultiplicity_eq_zero t.2
    rw [hrx, hrt] at h2
    simpa using h2

end AJConjecture
