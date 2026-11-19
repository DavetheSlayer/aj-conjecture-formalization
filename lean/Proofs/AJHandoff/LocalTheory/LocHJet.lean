import Mathlib
import AJHandoff.LocalTheory.LocJets
import AJHandoff.LocalTheory.LocResidue

/-!
# `h`-adic expansions in `F` and the normalized index

An element `D ∈ F = ℂ((h))(z)` with `v_h(D) ≥ 0` has an expansion `D = D₀ + h D₁ + O(h²)`,
`D₀, D₁ ∈ ℂ(z)`: write `D = a/b` with `a, b ∈ ℂ[[h]][z]` and `b₀ ≠ 0`, and take
`D₀ = a₀/b₀`, `D₁ = (a₁ b₀ - a₀ b₁)/b₀²`. `v_h(D) = 0` means `D₀ ≠ 0`. Reduction is the reduction
after removing the `h`-valuation, never the substitution of an orbit value for `z`.

The normalized index of `D` at `z₀` is the residue of the one-form `(D₁/D₀) dz/(c z)`, where
`c z d/dz` is the first-order part of the shift.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `D ∈ F` has `h`-expansion `D = D₀ + h D₁ + O(h²)`. -/
def HasHJet (D : LocField) (D₀ D₁ : RatFunc ℂ) : Prop :=
  ∃ a b : LocPoly, locJet0 b ≠ 0 ∧
    D * algebraMap LocPoly LocField b = algebraMap LocPoly LocField a ∧
    D₀ = algebraMap ℂ[X] (RatFunc ℂ) (locJet0 a) / algebraMap ℂ[X] (RatFunc ℂ) (locJet0 b) ∧
    D₁ = algebraMap ℂ[X] (RatFunc ℂ) (locJet1 a * locJet0 b - locJet0 a * locJet1 b) /
      algebraMap ℂ[X] (RatFunc ℂ) (locJet0 b) ^ 2

/-- The expansion does not depend on the presentation. -/
theorem HasHJet.unique {D : LocField} {D₀ D₁ D₀' D₁' : RatFunc ℂ} (h : HasHJet D D₀ D₁)
    (h' : HasHJet D D₀' D₁') : D₀ = D₀' ∧ D₁ = D₁' := by
  obtain ⟨a, b, hb, hab, rfl, rfl⟩ := h
  obtain ⟨a', b', hb', hab', rfl, rfl⟩ := h'
  have hpoly : a * b' = a' * b := by
    apply IsFractionRing.injective LocPoly LocField
    rw [map_mul, map_mul, ← hab, ← hab']
    ring
  have E0 := congrArg locJet0 hpoly
  have E1 := congrArg locJet1 hpoly
  rw [map_mul, map_mul] at E0
  rw [locJet1_mul, locJet1_mul] at E1
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hb0 : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 b) ≠ 0 := (map_ne_zero_iff _ hinj).2 hb
  have hb0' : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 b') ≠ 0 := (map_ne_zero_iff _ hinj).2 hb'
  refine ⟨?_, ?_⟩
  · rw [div_eq_div_iff hb0 hb0', ← map_mul (algebraMap ℂ[X] (RatFunc ℂ)),
      ← map_mul (algebraMap ℂ[X] (RatFunc ℂ)), E0]
  · have key : (locJet1 a * locJet0 b - locJet0 a * locJet1 b) * locJet0 b' ^ 2 =
        (locJet1 a' * locJet0 b' - locJet0 a' * locJet1 b') * locJet0 b ^ 2 := by
      linear_combination (locJet0 b * locJet0 b') * E1 -
        (locJet1 b * locJet0 b' + locJet1 b' * locJet0 b) * E0
    rw [div_eq_div_iff (pow_ne_zero 2 hb0) (pow_ne_zero 2 hb0'),
      ← map_pow (algebraMap ℂ[X] (RatFunc ℂ)), ← map_pow (algebraMap ℂ[X] (RatFunc ℂ)),
      ← map_mul (algebraMap ℂ[X] (RatFunc ℂ)), ← map_mul (algebraMap ℂ[X] (RatFunc ℂ)), key]

/-- The normalized index: `Res_{z₀} (D₁/D₀) dz/(c z) = ι`, with at most a simple pole. -/
def HasNormalizedIndex (c z₀ : ℂ) (D₀ D₁ : RatFunc ℂ) (ι : ℂ) : Prop :=
  HasSimpleResidue (D₁ / D₀ / (RatFunc.C c * RatFunc.X)) z₀ ι

end AJConjecture
