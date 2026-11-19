import Mathlib

/-!
# The normal form of a rational solution of a Riccati equation of order three (TwF, F4, generic)

Source: revision 5, Section 5.6 (`operators.tex`), eq. (riccati-normal):
`r_0 = c(q) x^μ ∏_k (x - q^k)^{n_k} σ(g)/g`, obtained from "For such a good prime `𝔭`, let
`e_𝔭` be the minimum valuation of the coordinates of `v`. The matrix equation gives
`ord_𝔭 r_0 = e_𝔭 - ord_𝔭 σ(v)` … Consequently `r_0/(h/σ(h))` is supported on the remaining
primes."

The Lean statement avoids valuations, and it is **proved** in this file. Let `k` be a field, `τ`
an injective ring endomorphism of `k[X]` (here `x ↦ q x`), and let `ρ = n/e` (`e ≠ 0`) solve
`p₀ + p₁ ρ + p₂ ρ τ(ρ) + p₃ ρ τ(ρ) τ²(ρ) = 0`, in cleared form
`p₀ e τe τ²e + p₁ n τe τ²e + p₂ n τn τ²e + p₃ n τn τ²n = 0`.
Then there are `g ≠ 0` and `A, B ∈ k[X]` with
`p₃ · n τ(g) = A · τ²(e) g` and `p₀ · τ²(e) g = B · n τ(g)`:
with `w = n τ(g)/(τ²(e) g)` (so `ρ = w · h/τ(h)`, `h = g/(e τe)`), `p₃ w = A` and `p₀/w = B` are
polynomials; in particular `A B = p₀ p₃`, so `w` is supported on the zeros of `p₀ p₃`.

Proof (principal ideal domain, no primes). Let `Y₀ = e τe`, `Y₁ = n τe`, `Y₂ = n τn` (the
coordinates `1, ρ, ρ τρ` times `e τe`), `g = gcd(Y₀, Y₁, Y₂)`, `Y_i = g m_i`,
`c₀ m₀ + c₁ m₁ + c₂ m₂ = 1` (Bézout). With `u = n τ(g)`, `v = τ²(e) g`:
`u τ(m₀) = v m₁`, `u τ(m₁) = v m₂` (from `n τ(Y₀) = Y₁ τ²e`, `n τ(Y₁) = Y₂ τ²e`) and the equation
reads `v (p₀ m₀ + p₁ m₁ + p₂ m₂) + p₃ u τ(m₂) = 0`. Multiplying `p₃ u` by
`1 = τc₀ τm₀ + τc₁ τm₁ + τc₂ τm₂` gives
`p₃ u = v (p₃ τc₀ m₁ + p₃ τc₁ m₂ - τc₂ (p₀ m₀ + p₁ m₁ + p₂ m₂))`, and multiplying `p₀ v` by
`1 = c₀ m₀ + c₁ m₁ + c₂ m₂` gives
`p₀ v = u (c₁ p₀ τm₀ + c₂ p₀ τm₁ - c₀ (p₁ τm₀ + p₂ τm₁ + p₃ τm₂))`. Each step is a
`linear_combination`. (`gcd` of three elements: `EuclideanDomain.gcd` twice,
`EuclideanDomain.gcd_eq_gcd_ab`.) This is the Gosper–Petkovšek observation that the "numerator"
of a hypergeometric solution divides the trailing coefficient and the "denominator" the leading
one, in a form that needs no coprimality normalisation.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The normal form of a rational solution `n/e` of a Riccati equation of order three over
`k[X]`. -/
theorem twf_riccati_normalForm {k : Type*} [Field k] (τ : k[X] →+* k[X])
    (hτ : Function.Injective τ) (p₀ p₁ p₂ p₃ : k[X]) {n e : k[X]} (he : e ≠ 0)
    (hric : p₀ * (e * τ e * τ (τ e)) + p₁ * (n * τ e * τ (τ e)) + p₂ * (n * τ n * τ (τ e)) +
      p₃ * (n * τ n * τ (τ n)) = 0) :
    ∃ A B g : k[X], g ≠ 0 ∧ p₃ * (n * τ g) = A * (τ (τ e) * g) ∧
      p₀ * (τ (τ e) * g) = B * (n * τ g) := by
  classical
  have hτe : τ e ≠ 0 := (map_ne_zero_iff τ hτ).mpr he
  set Y₀ := e * τ e with hY₀
  set Y₁ := n * τ e with hY₁
  set Y₂ := n * τ n with hY₂
  set g₁ := EuclideanDomain.gcd Y₀ Y₁ with hg₁
  set g := EuclideanDomain.gcd g₁ Y₂ with hgdef
  have hY₀0 : Y₀ ≠ 0 := mul_ne_zero he hτe
  have hg₁0 : g₁ ≠ 0 := fun h0 ↦ hY₀0 (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
  have hg0 : g ≠ 0 := fun h0 ↦ hg₁0 (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
  obtain ⟨m₀, h0⟩ : g ∣ Y₀ :=
    (EuclideanDomain.gcd_dvd_left g₁ Y₂).trans (EuclideanDomain.gcd_dvd_left Y₀ Y₁)
  obtain ⟨m₁, h1⟩ : g ∣ Y₁ :=
    (EuclideanDomain.gcd_dvd_left g₁ Y₂).trans (EuclideanDomain.gcd_dvd_right Y₀ Y₁)
  obtain ⟨m₂, h2⟩ : g ∣ Y₂ := EuclideanDomain.gcd_dvd_right g₁ Y₂
  have hb1 := EuclideanDomain.gcd_eq_gcd_ab Y₀ Y₁
  have hb2 := EuclideanDomain.gcd_eq_gcd_ab g₁ Y₂
  set a := EuclideanDomain.gcdA Y₀ Y₁
  set b := EuclideanDomain.gcdB Y₀ Y₁
  set a' := EuclideanDomain.gcdA g₁ Y₂
  set b' := EuclideanDomain.gcdB g₁ Y₂
  have hbez : a' * a * m₀ + a' * b * m₁ + b' * m₂ = 1 := by
    have h : g * (a' * a * m₀ + a' * b * m₁ + b' * m₂) = g * 1 := by
      rw [mul_one]
      calc g * (a' * a * m₀ + a' * b * m₁ + b' * m₂)
          = (g * m₀ * a + g * m₁ * b) * a' + g * m₂ * b' := by ring
        _ = (Y₀ * a + Y₁ * b) * a' + Y₂ * b' := by rw [← h0, ← h1, ← h2]
        _ = g₁ * a' + Y₂ * b' := by rw [← hb1]
        _ = g := hb2.symm
    exact mul_left_cancel₀ hg0 h
  have hbezτ : τ (a' * a) * τ m₀ + τ (a' * b) * τ m₁ + τ b' * τ m₂ = 1 := by
    have := congrArg τ hbez
    simpa only [map_add, map_mul, map_one] using this
  have hR2 : n * τ g * τ m₀ = τ (τ e) * g * m₁ := by
    have : n * τ Y₀ = Y₁ * τ (τ e) := by rw [hY₀, hY₁, map_mul]; ring
    rw [h0, h1, map_mul] at this
    linear_combination this
  have hR3 : n * τ g * τ m₁ = τ (τ e) * g * m₂ := by
    have : n * τ Y₁ = Y₂ * τ (τ e) := by rw [hY₁, hY₂, map_mul]; ring
    rw [h1, h2, map_mul] at this
    linear_combination this
  have hR1 : τ (τ e) * g * (p₀ * m₀ + p₁ * m₁ + p₂ * m₂) + p₃ * (n * τ g * τ m₂) = 0 := by
    have : p₀ * (Y₀ * τ (τ e)) + p₁ * (Y₁ * τ (τ e)) + p₂ * (Y₂ * τ (τ e)) +
        p₃ * (n * τ Y₂) = 0 := by
      rw [hY₀, hY₁, hY₂, map_mul]
      linear_combination hric
    rw [h0, h1, h2, map_mul] at this
    linear_combination this
  refine ⟨p₃ * τ (a' * a) * m₁ + p₃ * τ (a' * b) * m₂ -
      τ b' * (p₀ * m₀ + p₁ * m₁ + p₂ * m₂),
    a' * b * p₀ * τ m₀ + b' * p₀ * τ m₁ - a' * a * (p₁ * τ m₀ + p₂ * τ m₁ + p₃ * τ m₂), g, hg0,
    ?_, ?_⟩
  · linear_combination (-(p₃ * (n * τ g))) * hbezτ + p₃ * τ (a' * a) * hR2 +
      p₃ * τ (a' * b) * hR3 + τ b' * hR1
  · linear_combination (-(p₀ * (τ (τ e) * g))) * hbez + a' * a * hR1 +
      (a' * a * p₁ - a' * b * p₀) * hR2 + (a' * a * p₂ - b' * p₀) * hR3

end AJConjecture
