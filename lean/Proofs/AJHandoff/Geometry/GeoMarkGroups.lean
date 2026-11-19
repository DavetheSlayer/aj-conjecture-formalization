import Mathlib

/-!
# The Tillmann and Schilder presentations of the Whitehead link group (MARK, group level)

Tillmann (thesis 2002, Ch. 5) presents the group of the right-handed Whitehead link `W⁺` with
meridians `a = μ₀` (axis cusp 0) and `b = μ₁` (outer cusp 1), relation
`babABAba = abABAbab` (capitals are inverses) and preferred longitudes `λ₀ = AbaBABab`,
`λ₁ = BabABAba`. Schilder (arXiv:2104.01251v1, pp. 19–20) uses the outer meridian `x`, the axis
meridian `y`, the relation `Ω = reverse(Ω)` with `Ω = yxYxyXyx`, and the longitudes
`λ_x = YxyXyxYX`, `λ_y = YXyxYxyX`. The word map `x ↦ b`, `y ↦ a⁻¹` is an isomorphism; it sends
`λ_x ↦ b λ₁ b⁻¹` and `λ_y ↦ a λ₀⁻¹ a⁻¹`, so the peripheral marking is
outer `(μ, λ) = (μ₁, λ₁)`, axis `(μ, λ) = (μ₀⁻¹, λ₀⁻¹)` (geometry_v2 §6, G4 §4).

In each group the meridian of a cusp commutes with its longitude.

Route. Every relation check is a free-group identity after reduction: the image of the Schilder
relator is `a⁻¹ R_T a`; `[a, λ₀]` and `[b, λ₁]` are cyclic conjugates of `R_T^{±1}` (replayed by
free reduction in the design run). In Lean: `PresentedGroup.toGroup` with the relator mapped into
the normal closure (`QuotientGroup.eq_one_iff`, `Subgroup.normalClosure`, conjugation), and
`PresentedGroup.ext` on generators for the composites.
-/

noncomputable section

namespace AJConjecture

/-- Tillmann's relator `babABAba (abABAbab)⁻¹`, `a = of 0`, `b = of 1`. -/
def geoTilRel : FreeGroup (Fin 2) :=
  let a := FreeGroup.of (0 : Fin 2)
  let b := FreeGroup.of (1 : Fin 2)
  (b * a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a) * (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b)⁻¹

/-- Tillmann's presentation of the group of the right-handed Whitehead link. -/
abbrev GeoTillmannGroup : Type := PresentedGroup ({geoTilRel} : Set (FreeGroup (Fin 2)))

/-- The meridian `a = μ₀` of the axis cusp. -/
def geoTilA : GeoTillmannGroup := PresentedGroup.of 0

/-- The meridian `b = μ₁` of the outer cusp. -/
def geoTilB : GeoTillmannGroup := PresentedGroup.of 1

/-- The preferred longitude `λ₀ = AbaBABab` of the axis cusp. -/
def geoTilLong0 : GeoTillmannGroup :=
  geoTilA⁻¹ * geoTilB * geoTilA * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA * geoTilB

/-- The preferred longitude `λ₁ = BabABAba` of the outer cusp. -/
def geoTilLong1 : GeoTillmannGroup :=
  geoTilB⁻¹ * geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA

/-- Schilder's relator `Ω reverse(Ω)⁻¹`, `Ω = yxYxyXyx`, `x = of 0`, `y = of 1`. -/
def geoSchRel : FreeGroup (Fin 2) :=
  let x := FreeGroup.of (0 : Fin 2)
  let y := FreeGroup.of (1 : Fin 2)
  (y * x * y⁻¹ * x * y * x⁻¹ * y * x) * (x * y * x⁻¹ * y * x * y⁻¹ * x * y)⁻¹

/-- Schilder's presentation. -/
abbrev GeoSchilderGroup : Type := PresentedGroup ({geoSchRel} : Set (FreeGroup (Fin 2)))

/-- The outer meridian `x`. -/
def geoSchX : GeoSchilderGroup := PresentedGroup.of 0

/-- The axis meridian `y`. -/
def geoSchY : GeoSchilderGroup := PresentedGroup.of 1

/-- The outer longitude `λ_x = YxyXyxYX`. -/
def geoSchLongX : GeoSchilderGroup :=
  geoSchY⁻¹ * geoSchX * geoSchY * geoSchX⁻¹ * geoSchY * geoSchX * geoSchY⁻¹ * geoSchX⁻¹

/-- The axis longitude `λ_y = YXyxYxyX`. -/
def geoSchLongY : GeoSchilderGroup :=
  geoSchY⁻¹ * geoSchX⁻¹ * geoSchY * geoSchX * geoSchY⁻¹ * geoSchX * geoSchY * geoSchX⁻¹

/-- A conjugate of a power of a trivial element is trivial. -/
private theorem geo_conj_zpow_eq_one {G : Type*} [Group G] {r : G} (g : G) (h : r = 1) (n : ℤ) :
    g * r ^ n * g⁻¹ = 1 := by
  rw [h, one_zpow, mul_one, mul_inv_cancel]

/-- Tillmann's relation `babABAba = abABAbab` in `GeoTillmannGroup`. -/
private theorem geo_tillmann_rel :
    geoTilB * geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA *
        (geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA * geoTilB)⁻¹ =
      1 := by
  have h := PresentedGroup.one_of_mem (rels := ({geoTilRel} : Set (FreeGroup (Fin 2))))
    (Set.mem_singleton geoTilRel)
  exact h

/-- Schilder's relation `Ω = reverse(Ω)` in `GeoSchilderGroup`. -/
private theorem geo_schilder_rel :
    geoSchY * geoSchX * geoSchY⁻¹ * geoSchX * geoSchY * geoSchX⁻¹ * geoSchY * geoSchX *
        (geoSchX * geoSchY * geoSchX⁻¹ * geoSchY * geoSchX * geoSchY⁻¹ * geoSchX * geoSchY)⁻¹ =
      1 := by
  have h := PresentedGroup.one_of_mem (rels := ({geoSchRel} : Set (FreeGroup (Fin 2))))
    (Set.mem_singleton geoSchRel)
  exact h

/-- The Schilder relator maps to `1` under `x ↦ b`, `y ↦ a⁻¹`. -/
theorem geo_schToTil_rel :
    FreeGroup.lift (![geoTilB, geoTilA⁻¹] : Fin 2 → GeoTillmannGroup) geoSchRel = 1 := by
  simp only [geoSchRel, map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  set a := geoTilA
  set b := geoTilB
  calc _ = a⁻¹ * (b * a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a *
        (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b)⁻¹) ^ (1 : ℤ) * a⁻¹⁻¹ := by group
    _ = 1 := geo_conj_zpow_eq_one _ geo_tillmann_rel _

/-- The Tillmann relator maps to `1` under `a ↦ y⁻¹`, `b ↦ x`. -/
theorem geo_tilToSch_rel :
    FreeGroup.lift (![geoSchY⁻¹, geoSchX] : Fin 2 → GeoSchilderGroup) geoTilRel = 1 := by
  simp only [geoTilRel, map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  set x := geoSchX
  set y := geoSchY
  calc _ = (x * y⁻¹ * x * y * x⁻¹ * y * x * y⁻¹ * x⁻¹ * y * x⁻¹ * y⁻¹ * x * y⁻¹ * x⁻¹) *
        (y * x * y⁻¹ * x * y * x⁻¹ * y * x * (x * y * x⁻¹ * y * x * y⁻¹ * x * y)⁻¹) ^ (1 : ℤ) *
        (x * y⁻¹ * x * y * x⁻¹ * y * x * y⁻¹ * x⁻¹ * y * x⁻¹ * y⁻¹ * x * y⁻¹ * x⁻¹)⁻¹ := by group
    _ = 1 := geo_conj_zpow_eq_one _ geo_schilder_rel _

/-- The word map `x ↦ b`, `y ↦ a⁻¹`. -/
def geoSchToTil : GeoSchilderGroup →* GeoTillmannGroup :=
  PresentedGroup.toGroup (by rintro r rfl; exact geo_schToTil_rel)

/-- The inverse word map `a ↦ y⁻¹`, `b ↦ x`. -/
def geoTilToSch : GeoTillmannGroup →* GeoSchilderGroup :=
  PresentedGroup.toGroup (by rintro r rfl; exact geo_tilToSch_rel)

/-- The two word maps are mutually inverse, and the longitudes go to the stated conjugates:
`λ_x ↦ b λ₁ b⁻¹`, `λ_y ↦ a λ₀⁻¹ a⁻¹`. -/
theorem geo_schilder_tillmann :
    geoTilToSch.comp geoSchToTil = MonoidHom.id _ ∧
      geoSchToTil.comp geoTilToSch = MonoidHom.id _ ∧
      geoSchToTil geoSchX = geoTilB ∧ geoSchToTil geoSchY = geoTilA⁻¹ ∧
      geoSchToTil geoSchLongX = geoTilB * geoTilLong1 * geoTilB⁻¹ ∧
      geoSchToTil geoSchLongY = geoTilA * geoTilLong0⁻¹ * geoTilA⁻¹ := by
  have hX : geoSchToTil geoSchX = geoTilB := PresentedGroup.toGroup.of _
  have hY : geoSchToTil geoSchY = geoTilA⁻¹ := PresentedGroup.toGroup.of _
  have hA : geoTilToSch geoTilA = geoSchY⁻¹ := PresentedGroup.toGroup.of _
  have hB : geoTilToSch geoTilB = geoSchX := PresentedGroup.toGroup.of _
  refine ⟨?_, ?_, hX, hY, ?_, ?_⟩
  · refine PresentedGroup.ext fun i ↦ ?_
    fin_cases i
    · change geoTilToSch (geoSchToTil geoSchX) = geoSchX
      rw [hX, hB]
    · change geoTilToSch (geoSchToTil geoSchY) = geoSchY
      rw [hY, map_inv, hA, inv_inv]
  · refine PresentedGroup.ext fun i ↦ ?_
    fin_cases i
    · change geoSchToTil (geoTilToSch geoTilA) = geoTilA
      rw [hA, map_inv, hY, inv_inv]
    · change geoSchToTil (geoTilToSch geoTilB) = geoTilB
      rw [hB, hX]
  · simp only [geoSchLongX, geoTilLong1, map_mul, map_inv, hX, hY]
    group
  · simp only [geoSchLongY, geoTilLong0, map_mul, map_inv, hX, hY]
    group

/-- Peripheral commutation in Tillmann's group: `[a, λ₀] = [b, λ₁] = 1`. -/
theorem geo_tillmann_peripheral :
    Commute geoTilA geoTilLong0 ∧ Commute geoTilB geoTilLong1 := by
  have hR := geo_tillmann_rel
  unfold geoTilLong0 geoTilLong1
  set a := geoTilA
  set b := geoTilB
  constructor
  · rw [Commute, SemiconjBy, ← mul_inv_eq_one, ← mul_inv_eq_one]
    calc _ = (b * a * b⁻¹ * a⁻¹ * b⁻¹) * (b * a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a *
          (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b)⁻¹) ^ (-1 : ℤ) *
          (b * a * b⁻¹ * a⁻¹ * b⁻¹)⁻¹ := by group
      _ = 1 := geo_conj_zpow_eq_one _ hR _
  · rw [Commute, SemiconjBy, ← mul_inv_eq_one, ← mul_inv_eq_one]
    calc _ = (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b⁻¹ * a⁻¹ * b⁻¹ * a * b * a * b⁻¹ * a⁻¹) *
          (b * a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a *
            (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b)⁻¹) ^ (1 : ℤ) *
          (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b⁻¹ * a⁻¹ * b⁻¹ * a * b * a * b⁻¹ * a⁻¹)⁻¹ := by
          group
      _ = 1 := geo_conj_zpow_eq_one _ hR _

/-- Tillmann's relation `babABAba = abABAbab`, as an identity in `GeoTillmannGroup`. -/
theorem geo_tillmann_relation :
    geoTilB * geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA *
        (geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA * geoTilB)⁻¹ =
      1 :=
  geo_tillmann_rel

end AJConjecture
