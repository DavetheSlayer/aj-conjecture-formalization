import Mathlib
import AJHandoff.TorusKnot.PairKSatellite
import AJHandoff.TorusKnot.PairKTorusDichotomy

/-!
# Twisted Whitehead satellites: the peripheral structure (Unit C1, definitions)

Source: revision 5, Section 2 (`marking.tex`, eq. (twistgluing)): the `ℓ`-twisted negative-clasp
double `W_(-,ℓ)(C)` is glued by `μ_C ↦ λ_A`, `λ_C ↦ μ_A λ_A^(-ℓ)`, so the axis meridian is the
image of `λ_C μ_C^ℓ`; Section 8.2 (`conclusion.tex`, eq. (mirror-marked)) for the positive clasp.

* `IsWhPattern μ t c l`: the relations of the marked Whitehead pattern between the outer
  meridian `μ`, the axis meridian `t`, the axis longitude `c = compMer μ (t⁻¹ μ t)` and the
  outer longitude `l = μ² t μ⁻¹ t⁻¹ μ (t⁻¹ μ t)⁻¹ μ⁻¹` (the words of the library's
  `IsWhSatellite`, where `t` is the image of the companion longitude).
* `IsTwWhSatellite C K ℓ`: the knot group of `K` carries the pattern relations with
  `t = φ (λ_C μ_C^ℓ)`, `c = φ μ_C` for a homomorphism `φ` from the group of the companion `C`.
  For `ℓ = 0` this is `IsWhSatellite C K` (`isTwWhSatellite_zero_iff`).
* `IsTwWhSatelliteP C K ℓ`: the positive clasp: the same relations for `t⁻¹` and the inverse
  longitude. (The mirror image inverts the longitudes of the knot and of the companion and
  keeps the meridians; in this form no mirror companion appears.)
* `CompanionDichotomyZ C n`: `CompanionDichotomy` with a signed exponent: every `SL₂(ℂ)`
  representation of the group of `C` sends the longitude to `1` or to a central element times
  the `(-n)`-th power of the meridian. For `T(r, s)` it holds with `n = r s`.

The sign of `ℓ` was fixed by computer for the closed braids of package TwK (`SCR/C/py`):
Alexander polynomial `ℓ t + (1 - 2ℓ) + ℓ t⁻¹` (so `ℓ = -1` over the unknot would be the
figure-eight knot, as on the quantum side; `w1_twk_basic.py`), and the relations themselves on
numerical representations of the braid groups with the library's meridian and longitude, for
both clasp signs (`w2_twk_all.py`).
-/

namespace AJConjecture

/-- The relations of the marked negative-clasp Whitehead pattern: outer meridian `μ`, axis
meridian `t`, axis longitude `c`, outer longitude `l`. -/
def IsWhPattern {G : Type*} [Group G] (μ t c l : G) : Prop :=
  c = compMer μ (t⁻¹ * μ * t) ∧
    l = μ ^ 2 * t * μ⁻¹ * t⁻¹ * μ * (t⁻¹ * μ * t)⁻¹ * μ⁻¹

/-- The peripheral structure of the `ℓ`-twisted negative-clasp Whitehead double of `C` in the
knot group of `K`. -/
def IsTwWhSatellite (C K : BraidKnot) (ℓ : ℤ) : Prop :=
  ∃ φ : KnotGroup C →* KnotGroup K,
    IsWhPattern (meridian K) (φ (longitude C * meridian C ^ ℓ)) (φ (meridian C)) (longitude K)

/-- The peripheral structure of the `ℓ`-twisted positive-clasp Whitehead double of `C` in the
knot group of `K`. -/
def IsTwWhSatelliteP (C K : BraidKnot) (ℓ : ℤ) : Prop :=
  ∃ φ : KnotGroup C →* KnotGroup K,
    IsWhPattern (meridian K) (φ (longitude C * meridian C ^ ℓ))⁻¹ (φ (meridian C))
      (longitude K)⁻¹

/-- Every `SL₂(ℂ)` representation of the companion group sends the longitude to `1` or to a
central element times the `(-n)`-th power of the meridian (`n` a signed integer). -/
def CompanionDichotomyZ (C : BraidKnot) (n : ℤ) : Prop :=
  ∀ ρ : KnotGroup C →* Matrix.SpecialLinearGroup (Fin 2) ℂ,
    ρ (longitude C) = 1 ∨
      ∃ z : Matrix.SpecialLinearGroup (Fin 2) ℂ, (∀ x, z * x = x * z) ∧
        ρ (longitude C) = z * ρ (meridian C) ^ (-n)

/-- The pattern relations are preserved by homomorphisms. -/
theorem IsWhPattern.map {G H : Type*} [Group G] [Group H] (f : G →* H) {μ t c l : G}
    (h : IsWhPattern μ t c l) : IsWhPattern (f μ) (f t) (f c) (f l) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [h1]; simp only [compMer, map_mul, map_inv]
  · rw [h2]; simp only [map_mul, map_inv, map_pow]

/-- The untwisted structure is the library's `IsWhSatellite`. -/
theorem isTwWhSatellite_zero_iff (C K : BraidKnot) :
    IsTwWhSatellite C K 0 ↔ IsWhSatellite C K := by
  constructor
  · rintro ⟨φ, h1, h2⟩
    rw [zpow_zero, mul_one] at h1 h2
    exact ⟨φ, _, h1, rfl, h2⟩
  · rintro ⟨φ, μ₁, h1, h2, h3⟩
    subst h2
    refine ⟨φ, ?_, ?_⟩ <;> rw [zpow_zero, mul_one]
    · exact h1
    · exact h3

/-- The dichotomy with a natural exponent is the signed one. -/
theorem CompanionDichotomy.toZ {C : BraidKnot} {m : ℕ} (h : CompanionDichotomy C m) :
    CompanionDichotomyZ C (m : ℤ) := h

/-- The right-handed torus knot `T(r, s)` has the dichotomy with exponent `r s`. -/
theorem companionDichotomyZ_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    CompanionDichotomyZ (torusPairKnot r s h) ((r * s : ℕ) : ℤ) :=
  (companionDichotomy_torusPairKnot h).toZ

end AJConjecture
