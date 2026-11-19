import Mathlib
import AJFamily.Classical.FamilyPeripheral
import AJHandoff.Geometry.GeoMarkGroups

/-!
# The library's Whitehead pattern and Tillmann's marked group (MARK, geometric part)

The knot group of each library knot `whiteheadTorusKnot k` carries the satellite structure
`IsSatelliteData` (`satellitePeripheral_whiteheadTorusKnot`): meridian `a`, second clasp arc
`a₁ = λ⁻¹ a λ`, companion meridian `c = a a₁⁻¹ a⁻¹ a₁`, companion longitude `λ`, and knot longitude
`l = a² λ a⁻¹ λ⁻¹ a a₁⁻¹ a⁻¹`. In the pattern (Whitehead link exterior) `λ` is the axis meridian
and `c` the axis longitude. `GeoPatternGroup` is the pattern group read off these words: generators
`p` (pattern meridian) and `m` (axis meridian), one relation `[c, m] = 1` with
`c = p a₁⁻¹ p⁻¹ a₁`, `a₁ = m⁻¹ p m`; pattern longitude `l = p² m p⁻¹ m⁻¹ p a₁⁻¹ p⁻¹`.

* `geo_pattern_to_knotGroup`: `p ↦ meridian`, `m ↦ λ` defines a homomorphism into the knot group
  of `whiteheadTorusKnot k` sending `l` to the library's preferred `longitude` and `c` to the
  companion meridian.
* `geo_pattern_tillmann`: `p ↦ b`, `m ↦ a⁻¹` is an isomorphism onto Tillmann's group with
  `l ↦ b² λ₁⁻¹ b⁻²` and `c ↦ a λ₀ a⁻¹`. So the library's own marking is
  outer `(μ, λ) = (μ₁, λ₁⁻¹)` up to conjugation: Schilder's outer pair with the longitude inverted,
  i.e. the mirror marking `(M, L) = (u, v⁻¹)` of G4, now derived from the braid rather than from a
  diagram comparison. (Free-group replay in the design run: the image of the pattern relator is a
  cyclic conjugate of `R_T⁻¹`, and of `R_T` back.)

What stays interpretation: that `GeoPatternGroup` with `(p, l)`, `(m, c)` is the fundamental group
of the pattern exterior with its two peripheral pairs, and that Tillmann's group is that of the
`W⁺` complement (the topology behind both presentations).

Route. Relation checks by free reduction (as in `GeoMarkGroups`). For the knot-group map:
`[c, λ] = 1` follows from the torus relation `(cd)^k c = d (cd)^k` (with `Δ = (cd)^k c`,
conjugation by `Δ` swaps `c` and `d`, so `Δ² = (cd)^{2k+1}` is central and
`λ = c^{-(4k+2)} Δ²` commutes with `c`); the longitude is the third conjunct of `IsSatelliteData`.
-/

noncomputable section

namespace AJConjecture

/-- The pattern relator `[c, m]`, `c = p a₁⁻¹ p⁻¹ a₁`, `a₁ = m⁻¹ p m`, `p = of 0`, `m = of 1`. -/
def geoPatRel : FreeGroup (Fin 2) :=
  let p := FreeGroup.of (0 : Fin 2)
  let m := FreeGroup.of (1 : Fin 2)
  let a₁ := m⁻¹ * p * m
  let c := p * a₁⁻¹ * p⁻¹ * a₁
  c * m * c⁻¹ * m⁻¹

/-- The group of the Whitehead pattern as read off the library's satellite structure. -/
abbrev GeoPatternGroup : Type := PresentedGroup ({geoPatRel} : Set (FreeGroup (Fin 2)))

/-- The pattern meridian `p`. -/
def geoPatMer : GeoPatternGroup := PresentedGroup.of 0

/-- The axis meridian `m` (the companion longitude in the satellite). -/
def geoPatAxisMer : GeoPatternGroup := PresentedGroup.of 1

/-- The second clasp arc `a₁ = m⁻¹ p m`. -/
def geoPatArc : GeoPatternGroup := geoPatAxisMer⁻¹ * geoPatMer * geoPatAxisMer

/-- The axis longitude `c = p a₁⁻¹ p⁻¹ a₁` (the companion meridian in the satellite). -/
def geoPatAxisLong : GeoPatternGroup := geoPatMer * geoPatArc⁻¹ * geoPatMer⁻¹ * geoPatArc

/-- The preferred longitude of the pattern `l = p² m p⁻¹ m⁻¹ p a₁⁻¹ p⁻¹`. -/
def geoPatLong : GeoPatternGroup :=
  geoPatMer ^ 2 * geoPatAxisMer * geoPatMer⁻¹ * geoPatAxisMer⁻¹ * geoPatMer * geoPatArc⁻¹ *
    geoPatMer⁻¹

/-- A conjugate of a power of a trivial element is trivial. -/
private theorem geo_pat_conj_zpow_eq_one {G : Type*} [Group G] {r : G} (g : G) (h : r = 1)
    (n : ℤ) : g * r ^ n * g⁻¹ = 1 := by
  rw [h, one_zpow, mul_one, mul_inv_cancel]

/-- The pattern relation `[c, m] = 1` in `GeoPatternGroup`. -/
private theorem geo_pattern_rel :
    geoPatAxisLong * geoPatAxisMer * geoPatAxisLong⁻¹ * geoPatAxisMer⁻¹ = 1 :=
  PresentedGroup.one_of_mem (rels := ({geoPatRel} : Set (FreeGroup (Fin 2))))
    (Set.mem_singleton geoPatRel)

/-- In a torus knot group `(cd)^k c = d (cd)^k`, the element `(cd)^(2k+1)` commutes with `c`. -/
private theorem geo_torus_pow_commute {G : Type*} [Group G] (k : ℕ) {c d : G}
    (h : (c * d) ^ k * c = d * (c * d) ^ k) : Commute c ((c * d) ^ (2 * k + 1)) := by
  obtain ⟨D, hD⟩ : ∃ D : G, D = (c * d) ^ k * c := ⟨_, rfl⟩
  have h1 : D * c = d * D := by
    calc D * c = d * (c * d) ^ k * c := by rw [hD, h]
      _ = d * D := by rw [hD, mul_assoc]
  have h2 : D * d = c * D := by
    calc D * d = (c * d) ^ (k + 1) := by rw [hD, pow_succ, mul_assoc]
      _ = c * D := by rw [pow_succ', hD, h, mul_assoc]
  have h3 : D * D = (c * d) ^ (2 * k + 1) := by
    calc D * D = (c * d) ^ k * (c * d) * (c * d) ^ k := by
          nth_rewrite 2 [hD]
          rw [h, hD]
          group
      _ = (c * d) ^ (2 * k + 1) := by rw [← pow_succ, ← pow_add]; ring_nf
  rw [← h3, Commute, SemiconjBy]
  calc c * (D * D) = D * d * D := by rw [h2, mul_assoc]
    _ = D * D * c := by rw [mul_assoc, ← h1, mul_assoc]

/-- The companion meridian commutes with the companion longitude. -/
private theorem geo_compMer_commute_compLong {G : Type*} [Group G] (k : ℕ) {c d : G}
    (h : (c * d) ^ k * c = d * (c * d) ^ k) : Commute c (compLong k c d) := by
  unfold compLong
  exact ((Commute.refl c).zpow_right _).mul_right (geo_torus_pow_commute k h)

/-- The pattern sits in the knot group of every library knot with its marking. -/
theorem geo_pattern_to_knotGroup (k : ℕ) (hk : 1 ≤ k) :
    ∃ f : GeoPatternGroup →* KnotGroup (whiteheadTorusKnot k hk),
      f geoPatMer = meridian (whiteheadTorusKnot k hk) ∧
        f geoPatLong = longitude (whiteheadTorusKnot k hk) ∧
        ∃ a₁ d : KnotGroup (whiteheadTorusKnot k hk),
          IsSatelliteData k (meridian (whiteheadTorusKnot k hk)) a₁ d
              (longitude (whiteheadTorusKnot k hk)) ∧
            f geoPatAxisMer =
              compLong k (compMer (meridian (whiteheadTorusKnot k hk)) a₁) d ∧
            f geoPatAxisLong = compMer (meridian (whiteheadTorusKnot k hk)) a₁ := by
  obtain ⟨a₁, d, hS⟩ := satellitePeripheral_whiteheadTorusKnot k hk
  have hc := geo_compMer_commute_compLong k hS.1
  have h2 := hS.2.1
  have h3 := hS.2.2
  set a := meridian (whiteheadTorusKnot k hk)
  set l := compLong k (compMer a a₁) d with hl
  have hrel : FreeGroup.lift (![a, l] : Fin 2 → KnotGroup (whiteheadTorusKnot k hk))
      geoPatRel = 1 := by
    simp only [geoPatRel, map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← h2]
    change compMer a a₁ * l * (compMer a a₁)⁻¹ * l⁻¹ = 1
    rw [hc.eq]
    group
  have hrel' : ∀ r ∈ ({geoPatRel} : Set (FreeGroup (Fin 2))),
      FreeGroup.lift (![a, l] : Fin 2 → KnotGroup (whiteheadTorusKnot k hk)) r = 1 := by
    rintro r rfl
    exact hrel
  have hm : PresentedGroup.toGroup hrel' geoPatMer = a := PresentedGroup.toGroup.of _
  have hx : PresentedGroup.toGroup hrel' geoPatAxisMer = l := PresentedGroup.toGroup.of _
  have harc : PresentedGroup.toGroup hrel' geoPatArc = a₁ := by
    simp only [geoPatArc, map_mul, map_inv, hm, hx]
    exact h2.symm
  refine ⟨PresentedGroup.toGroup hrel', hm, ?_, a₁, d, hS, hx, ?_⟩
  · simp only [geoPatLong, map_mul, map_inv, map_pow, hm, hx, harc]
    exact h3.symm
  · simp only [geoPatAxisLong, map_mul, map_inv, hm, harc]
    rfl

/-- The pattern relator maps to `1` under `p ↦ b`, `m ↦ a⁻¹`. -/
theorem geo_patToTil_rel :
    FreeGroup.lift (![geoTilB, geoTilA⁻¹] : Fin 2 → GeoTillmannGroup) geoPatRel = 1 := by
  simp only [geoPatRel, map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hR := geo_tillmann_relation
  set a := geoTilA
  set b := geoTilB
  calc _ = (b * a * b⁻¹ * a⁻¹ * b⁻¹) * (b * a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a *
        (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b)⁻¹) ^ (-1 : ℤ) *
        (b * a * b⁻¹ * a⁻¹ * b⁻¹)⁻¹ := by group
    _ = 1 := geo_pat_conj_zpow_eq_one _ hR _

/-- The Tillmann relator maps to `1` under `a ↦ m⁻¹`, `b ↦ p`. -/
theorem geo_tilToPat_rel :
    FreeGroup.lift (![geoPatAxisMer⁻¹, geoPatMer] : Fin 2 → GeoPatternGroup) geoTilRel = 1 := by
  simp only [geoTilRel, map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hR := geo_pattern_rel
  unfold geoPatAxisLong geoPatArc at hR
  set p := geoPatMer
  set m := geoPatAxisMer
  calc _ = (p * m⁻¹ * p * m * p⁻¹) *
        ((p * (m⁻¹ * p * m)⁻¹ * p⁻¹ * (m⁻¹ * p * m)) * m *
          (p * (m⁻¹ * p * m)⁻¹ * p⁻¹ * (m⁻¹ * p * m))⁻¹ * m⁻¹) ^ (-1 : ℤ) *
        (p * m⁻¹ * p * m * p⁻¹)⁻¹ := by group
    _ = 1 := geo_pat_conj_zpow_eq_one _ hR _

/-- The marking map `p ↦ b`, `m ↦ a⁻¹`. -/
def geoPatToTil : GeoPatternGroup →* GeoTillmannGroup :=
  PresentedGroup.toGroup (by rintro r rfl; exact geo_patToTil_rel)

/-- Its inverse `a ↦ m⁻¹`, `b ↦ p`. -/
def geoTilToPat : GeoTillmannGroup →* GeoPatternGroup :=
  PresentedGroup.toGroup (by rintro r rfl; exact geo_tilToPat_rel)

/-- The library's pattern is Tillmann's group with the mirror marking: outer pair
`(p, l) ↦ (b, b² λ₁⁻¹ b⁻²)`, axis pair `(m, c) ↦ (a⁻¹, a λ₀ a⁻¹)`. -/
theorem geo_pattern_tillmann :
    geoTilToPat.comp geoPatToTil = MonoidHom.id _ ∧
      geoPatToTil.comp geoTilToPat = MonoidHom.id _ ∧
      geoPatToTil geoPatMer = geoTilB ∧ geoPatToTil geoPatAxisMer = geoTilA⁻¹ ∧
      geoPatToTil geoPatLong = geoTilB ^ 2 * geoTilLong1⁻¹ * (geoTilB ^ 2)⁻¹ ∧
      geoPatToTil geoPatAxisLong = geoTilA * geoTilLong0 * geoTilA⁻¹ := by
  have hP : geoPatToTil geoPatMer = geoTilB := PresentedGroup.toGroup.of _
  have hM : geoPatToTil geoPatAxisMer = geoTilA⁻¹ := PresentedGroup.toGroup.of _
  have hA : geoTilToPat geoTilA = geoPatAxisMer⁻¹ := PresentedGroup.toGroup.of _
  have hB : geoTilToPat geoTilB = geoPatMer := PresentedGroup.toGroup.of _
  refine ⟨?_, ?_, hP, hM, ?_, ?_⟩
  · refine PresentedGroup.ext fun i ↦ ?_
    fin_cases i
    · change geoTilToPat (geoPatToTil geoPatMer) = geoPatMer
      rw [hP, hB]
    · change geoTilToPat (geoPatToTil geoPatAxisMer) = geoPatAxisMer
      rw [hM, map_inv, hA, inv_inv]
  · refine PresentedGroup.ext fun i ↦ ?_
    fin_cases i
    · change geoPatToTil (geoTilToPat geoTilA) = geoTilA
      rw [hA, map_inv, hM, inv_inv]
    · change geoPatToTil (geoTilToPat geoTilB) = geoTilB
      rw [hB, hP]
  · simp only [geoPatLong, geoPatArc, geoTilLong1, map_mul, map_inv, map_pow, hP, hM]
    group
  · simp only [geoPatAxisLong, geoPatArc, geoTilLong0, map_mul, map_inv, hP, hM]
    group

end AJConjecture
