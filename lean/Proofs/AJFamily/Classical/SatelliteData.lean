import Mathlib
import AJConjecture.KnotGroup
import AJFamily.Classical.FamilyPolynomials

/-!
# The satellite structure of `Wh(T(2, 2k+1))`

The companion meridian `c = a a₁⁻¹ a⁻¹ a₁`, the zero-framed companion longitude
`λ = c^(-2(2k+1)) (cd)^(2k+1)`, and the relations `IsSatelliteData` tying the meridian `a`, the
second clasp arc `a₁ = λ⁻¹ a λ`, a second companion generator `d` with `(cd)^k c = d (cd)^k`, and
the longitude. `SatellitePeripheral K k` says that the knot group of `K` satisfies them with its
own meridian and longitude.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The companion meridian `c = a a₁⁻¹ a⁻¹ a₁`. -/
def compMer {G : Type*} [Group G] (a a₁ : G) : G := a * a₁⁻¹ * a⁻¹ * a₁

/-- The zero-framed longitude `λ = c^(-2(2k+1)) (c d)^(2k+1)` of the companion `T(2, 2k+1)`. -/
def compLong {G : Type*} [Group G] (k : ℕ) (c d : G) : G :=
  c ^ (-(famDegree k : ℤ)) * (c * d) ^ (2 * k + 1)

/-- The relations of the satellite structure of `Wh(T(2, 2k+1))` between the meridian `a`, the
second clasp arc `a₁`, the second companion generator `d` and the longitude `l`. -/
def IsSatelliteData {G : Type*} [Group G] (k : ℕ) (a a₁ d l : G) : Prop :=
  (compMer a a₁ * d) ^ k * compMer a a₁ = d * (compMer a a₁ * d) ^ k ∧
    a₁ = (compLong k (compMer a a₁) d)⁻¹ * a * compLong k (compMer a a₁) d ∧
    l = a ^ 2 * compLong k (compMer a a₁) d * a⁻¹ * (compLong k (compMer a a₁) d)⁻¹ * a *
      a₁⁻¹ * a⁻¹

/-- The knot group of `K` carries the satellite structure of `Wh(T(2, 2k+1))` with its meridian
and preferred longitude. -/
def SatellitePeripheral (K : BraidKnot) (k : ℕ) : Prop :=
  ∃ a₁ d : KnotGroup K, IsSatelliteData k (meridian K) a₁ d (longitude K)

theorem IsSatelliteData.map {G H : Type*} [Group G] [Group H] (f : G →* H) {k : ℕ}
    {a a₁ d l : G} (h : IsSatelliteData k a a₁ d l) :
    IsSatelliteData k (f a) (f a₁) (f d) (f l) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hc : f (compMer a a₁) = compMer (f a) (f a₁) := by
    simp only [compMer, map_mul, map_inv]
  have hl : f (compLong k (compMer a a₁) d) = compLong k (compMer (f a) (f a₁)) (f d) := by
    simp only [compLong, map_mul, map_zpow, map_pow, hc]
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg f h1
    simpa only [map_mul, map_pow, hc] using this
  · have := congrArg f h2
    simpa only [map_mul, map_inv, hl] using this
  · have := congrArg f h3
    simpa only [map_mul, map_inv, map_pow, hl] using this

end AJConjecture
