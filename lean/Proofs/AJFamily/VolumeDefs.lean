import Mathlib
import AJConjecture.APolynomial
import AJConjecture.WitnessPolynomials

/-!
# Mahler measure, the Bloch–Wigner dilogarithm and the Whitehead link triangulation

Definitions for the analytic and geometric statements that accompany the family of
counterexamples.

* `catalanConstant` is Catalan's constant `G = ∑_{n ≥ 0} (-1)ⁿ / (2n+1)²`.
* `logMahlerMeasure₂ P` is the logarithmic Mahler measure of a polynomial `P(M, L)`: the
  integral of `log |P(e^{iθ}, e^{iφ})|` over `[0, 2π]²` divided by `(2π)²` (normalised Haar
  measure of the torus). A statement about it also asserts that the integrand is integrable.
* `blochWigner z` is the Bloch–Wigner dilogarithm `D(z) = Im Li₂(z) + arg(1 - z) log |z|` for
  `|z| ≤ 1`, with `Li₂(z) = ∑_{n ≥ 1} zⁿ / n²`, and `D(z) = -D(1/z)` for `|z| > 1`. The
  hyperbolic volume of an ideal tetrahedron of shape `z` with `Im z > 0` is `D(z)`.
* `WhiteheadGluing`, `whiteheadPeripheral` and `WhiteheadComplete` are the gluing equations, the
  holonomy coordinates and the completeness conditions of the four-tetrahedron ideal
  triangulation of the complement of the right-handed Whitehead link, with shapes
  `(w, a, b, c)` as in Tillmann's thesis (2002), formulas (5.2), (5.3), (5.18)–(5.22): gluing
  equations `wabc = 1`, `wa(1 - b)(1 - c) = (1 - w)(1 - a)bc`, and holonomy coordinates
  `(meridian₀², longitude₀, meridian₁², longitude₁) = (a' c'' / b, ab, w' c'' / b, wb)` with
  `z' = 1/(1 - z)`, `z'' = (z - 1)/z`. A cusp is complete when the holonomy derivatives (the
  squared eigenvalues) of its meridian and longitude are `1`. The volume of the complete
  hyperbolic structure is the sum of the Bloch–Wigner values of the shapes of the positively
  oriented complete solution (Thurston).

The meridian and longitude coordinates of `AJConjecture.evalPoint` are `(M, L)`: the inner
variable of `ℂ[X][X]` is `M`, the outer one `L`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The extra factor `E = L² - (M⁴ - 4M² + 1) L + M⁴` with complex coefficients. -/
abbrev extraFactorℂ : ℂ[X][X] :=
  extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- Catalan's constant `G = ∑_{n ≥ 0} (-1)ⁿ / (2n+1)²`. -/
def catalanConstant : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2

/-- The point `(e^{iθ}, e^{iφ})` of the unit torus. -/
def torusPoint (θ : ℝ × ℝ) : ℂ × ℂ :=
  (Complex.exp (θ.1 * Complex.I), Complex.exp (θ.2 * Complex.I))

/-- The square `[0, 2π] × [0, 2π]` of angles. -/
def torusBox : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The integrand of the Mahler measure: `log |P(e^{iθ}, e^{iφ})|`. -/
def torusLogAbs (P : ℂ[X][X]) (θ : ℝ × ℝ) : ℝ :=
  Real.log ‖evalPoint P (torusPoint θ)‖

/-- The logarithmic Mahler measure of `P(M, L)`:
`m(P) = (2π)⁻² ∫_{[0,2π]²} log |P(e^{iθ}, e^{iφ})| dθ dφ`. -/
def logMahlerMeasure₂ (P : ℂ[X][X]) : ℝ :=
  ((2 * Real.pi) ^ 2)⁻¹ * ∫ θ in torusBox, torusLogAbs P θ

/-- The dilogarithm series `Li₂(z) = ∑_{n ≥ 1} zⁿ / n²`, convergent for `|z| ≤ 1`. -/
def dilogSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1) ^ 2

/-- The Bloch–Wigner dilogarithm: `D(z) = Im Li₂(z) + arg(1 - z) log |z|` for `|z| ≤ 1`, and
`D(z) = -D(1/z)` for `|z| > 1`. -/
def blochWigner (z : ℂ) : ℝ :=
  if ‖z‖ ≤ 1 then (dilogSeries z).im + Complex.arg (1 - z) * Real.log ‖z‖
  else -((dilogSeries z⁻¹).im + Complex.arg (1 - z⁻¹) * Real.log ‖z⁻¹‖)

/-- The shape parameter `z' = 1 / (1 - z)` of the same ideal tetrahedron at another edge. -/
def shapePrime (z : ℂ) : ℂ :=
  1 / (1 - z)

/-- The shape parameter `z'' = (z - 1) / z` of the same ideal tetrahedron at the third edge. -/
def shapeDoublePrime (z : ℂ) : ℂ :=
  (z - 1) / z

/-- The gluing equations of Tillmann's four-tetrahedron ideal triangulation of the complement
of the right-handed Whitehead link, for nondegenerate shapes `z = (w, a, b, c)`:
`wabc = 1` and `wa(1 - b)(1 - c) = (1 - w)(1 - a)bc`. -/
def WhiteheadGluing (z : Fin 4 → ℂ) : Prop :=
  (∀ j, z j ≠ 0 ∧ z j ≠ 1) ∧ z 0 * z 1 * z 2 * z 3 = 1 ∧
    z 0 * z 1 * (1 - z 2) * (1 - z 3) = (1 - z 0) * (1 - z 1) * z 2 * z 3

/-- The holonomy coordinates `(meridian₀², longitude₀, meridian₁², longitude₁)
= (a' c'' / b, ab, w' c'' / b, wb)` of the triangulation, for `z = (w, a, b, c)`. -/
def whiteheadPeripheral (z : Fin 4 → ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (shapePrime (z 1) * shapeDoublePrime (z 3) / z 2, z 1 * z 2,
    shapePrime (z 0) * shapeDoublePrime (z 3) / z 2, z 0 * z 2)

/-- Both cusps are complete: the holonomy derivatives of both meridians and both longitudes,
the squares of their eigenvalues, are `1`. -/
def WhiteheadComplete (z : Fin 4 → ℂ) : Prop :=
  (whiteheadPeripheral z).1 = 1 ∧ (whiteheadPeripheral z).2.1 ^ 2 = 1 ∧
    (whiteheadPeripheral z).2.2.1 = 1 ∧ (whiteheadPeripheral z).2.2.2 ^ 2 = 1

end AJConjecture
