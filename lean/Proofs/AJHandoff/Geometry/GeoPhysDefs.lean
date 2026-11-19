import Mathlib

/-!
# Zheng's diagonal at `q_N = e^{2πi/N}` and the cited analytic estimates (G-PHYS, definitions)

Fix `a = 2k + 1 ≥ 3` (the companion `T(2, a) = T(a, 2)`, Zheng's `(p, q) = (a, 2)`, `pq = 2a`) and
zero twist. With `s = q_N^{1/2} = e^{πi/N}` (`geoHalfRoot`), Zheng (math/0508138v4) writes the
reduced coloured Jones polynomial of the Whitehead double at `q_N`, after L'Hôpital's rule on the
vanishing quantum dimension, as (5.3)

  `J_N(q_N) = (s⁻¹/N) ∑_{n<N} ∑_{i ≤ N-1-n} a_n^{-1} S_{n,i} (b_{n,i} Ĥ_n + q∂_q Ĥ_n)`

(`geoZhengDiagonal`), with the phase `a_n = exp(πi n(n+1-N)/(2N))` (3.2), the norm factor
`S_{n,i} = ∏_{j=1}^{n} 4 sin²((i+j)π/N)/(2 sin(jπ/N))` (3.3), the hatted companion input
`Ĥ_n = (q^{1/2} - q^{-1/2}) u_n = s^{-4an(n+1)} ∑_{k=-n}^{n} s^{2ak(2k+1)}(s^{4k+1} - s^{-4k-1})`
and `q∂_q = (s/2) d/ds`.

**Correction to the source.** `b_{n,i}` is the logarithmic `q`-derivative of the summand of
Zheng's clasp coefficient (2.7),
`b_{n,i} = -N(i + n) + ∑_{j=1}^{n} [(N-i-j)/(1 - q^{-N+i+j}) + (i+j)/(1 - q^{-i-j})`
`- j/(1 - q^{-j})]`
(`geoZhengB`; the constant from the prefactor drops out because the numerator vanishes at `q_N`).
Zheng's printed (5.4) has the opposite sign on the three summed terms. With the printed sign (5.3)
disagrees with the library's reduced formula at `q_N`; with the sign above it agrees (checked
numerically for `a ∈ {3, 5}`, `2 ≤ N ≤ 6`, against `torusReducedFormula`). The sign change alters
`|b_{n,i}|` itself, so `ZhengEq516` and `ZhengEq519` below are the estimates of Zheng's (5.16) and
(5.19) for the corrected `b`, not verbatim his: his proofs concern the printed `b` and have to be
re-checked for the corrected one (numerically `|b Ĥ|/N²` stays near `0.42` for `a = 3` up to
`N = 1203`). The other named propositions are verbatim.

The analytic inputs are stated as named propositions, exactly at the scope used:
* `ZhengLemma32` — Lemma 3.2 (localization of `S_{n,i}` near `(N/2, N/4)`);
* `ZhengLemma33 β δ` — Lemma 3.3 with `α = 0` and the explicit constant (3.34) (`geoGaussConst`);
* `ZhengEq516 a` — (5.16), the global bound `O(N⁴)` of the bracket;
* `ZhengEq519 a`, `ZhengEq520 a` — (5.19), (5.20) on `|n - N/2| + |i - N/4| < N/(4pq) = N/(8a)`;
* `ZhengProp41 a` — Proposition 4.1, `A⁺_{a,2}(N, 1) ≠ 0` for every `N`.
They need Riemann-sum and Stirling asymptotics of `∑ log|2 sin|` with uniform errors, a
contour-integral formula for torus-knot coloured Jones polynomials with residue shifts (Lemmas
5.1–5.2), and Galois-trace arguments in cyclotomic fields: far beyond the present library, so they
stay hypotheses (G-PHYS is `SOURCE_ONLY_OPEN` in the handoff).
-/

open Real

noncomputable section

namespace AJConjecture

/-- `s = q_N^{1/2} = e^{πi/N}`. -/
def geoHalfRoot (N : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / N)

/-- `q_N = e^{2πi/N}`. -/
def geoRootQ (N : ℕ) : ℂ := geoHalfRoot N ^ 2

/-- The angle of Zheng's phase: `a_n = exp(i · π n(n+1-N)/(2N))` (3.2). -/
def geoPhaseArg (N n : ℕ) : ℝ := Real.pi * ((n : ℝ) * ((n : ℝ) + 1 - N)) / (2 * N)

/-- `a_n^β = exp(iβ · π n(n+1-N)/(2N))`. -/
def geoPhasePow (N n : ℕ) (β : ℝ) : ℂ := Complex.exp ((β * geoPhaseArg N n : ℝ) * Complex.I)

/-- Zheng's norm factor `S_{n,i} = ∏_{j=1}^{n} 4 sin²((i+j)π/N) / (2 sin(jπ/N))` (3.3). -/
def geoNormFactor (N n i : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 n,
    4 * Real.sin (((i : ℝ) + j) * Real.pi / N) ^ 2 / (2 * Real.sin ((j : ℝ) * Real.pi / N))

/-- `S₀ = S_{[N/2],[N/4]}`. -/
def geoNormFactor0 (N : ℕ) : ℝ := geoNormFactor N (N / 2) (N / 4)

/-- The hatted odd-colour input of `T(a, 2)` as a function of `s = q^{1/2}`:
`Ĥ_n(s) = s^{-4an(n+1)} ∑_{k=-n}^{n} s^{2ak(2k+1)} (s^{4k+1} - s^{-(4k+1)})`
(`= (q^{1/2} - q^{-1/2}) u_n(q)`, Zheng's `Ĵ_{T(a,2), 2n+1}`). -/
def geoHatInput (a n : ℕ) (s : ℂ) : ℂ :=
  s ^ (-(4 * (a : ℤ) * n * (n + 1))) *
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      s ^ (2 * (a : ℤ) * k * (2 * k + 1)) * (s ^ (4 * k + 1) - s ^ (-(4 * k + 1)))

/-- `q ∂_q Ĥ_n` at `q = q_N`, i.e. `(s/2) dĤ_n/ds` at `s = e^{πi/N}`. -/
def geoHatInputDeriv (a n N : ℕ) : ℂ :=
  geoHalfRoot N / 2 * deriv (geoHatInput a n) (geoHalfRoot N)

/-- The logarithmic derivative `b_{n,i}` of the clasp summand at `q_N`, zero twist (corrected sign;
see the module docstring). -/
def geoZhengB (N n i : ℕ) : ℂ :=
  -(N : ℂ) * ((i : ℂ) + n) +
    ∑ j ∈ Finset.Icc 1 n,
      (((N : ℂ) - i - j) / (1 - geoRootQ N ^ (-(N : ℤ) + i + j)) +
        ((i : ℂ) + j) / (1 - geoRootQ N ^ (-((i : ℤ) + j))) -
        (j : ℂ) / (1 - geoRootQ N ^ (-(j : ℤ))))

/-- Zheng's diagonal (5.3) at zero twist. -/
def geoZhengDiagonal (a N : ℕ) : ℂ :=
  (geoHalfRoot N)⁻¹ / N *
    ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
      geoPhasePow N n (-1) * geoNormFactor N n i *
        (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N)

/-- The window `|n - N/2| + |i - N/4| < ρ`. -/
def GeoInWindow (N : ℕ) (ρ : ℝ) (n i : ℕ) : Prop :=
  |(n : ℝ) - N / 2| + |(i : ℝ) - N / 4| < ρ

open Classical in
/-- The diagonal (5.3) restricted to the window `D_N = {|n - N/2| + |i - N/4| < N^δ}`. -/
def geoZhengDiagonalIn (a N : ℕ) (δ : ℝ) : ℂ :=
  (geoHalfRoot N)⁻¹ / N *
    ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
      if GeoInWindow N ((N : ℝ) ^ δ) n i then
        geoPhasePow N n (-1) * geoNormFactor N n i *
          (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N)
      else 0

open Classical in
/-- The weighted sum `∑_{D_N} a_n^β S_{n,i}` of Lemma 3.3 (`α = 0`). -/
def geoWindowSum (N : ℕ) (δ β : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
    if GeoInWindow N ((N : ℝ) ^ δ) n i then geoPhasePow N n β * geoNormFactor N n i else 0

/-- Zheng's constant (3.34) at `α = 0`:
`C_β = e^{βπi/4} ∫_{ℝ²} exp(-π(x² + 2xy + 2y²) + βπi x²/2) dx dy`. -/
def geoGaussConst (β : ℝ) : ℂ :=
  Complex.exp (β * Real.pi * Complex.I / 4) *
    ∫ p : ℝ × ℝ, Complex.exp (-(Real.pi : ℂ) * (p.1 ^ 2 + 2 * p.1 * p.2 + 2 * p.2 ^ 2) +
      β * Real.pi * Complex.I * p.1 ^ 2 / 2)

/-- `A⁺_{a,2}(N, k) = ∑_{j=1}^{2a-1} e^{-N j² πi/(4a)} j^{2k} sin(jπ/a) sin(jπ/2)` (4.2). -/
def geoZhengA (a : ℕ) (N : ℤ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 (2 * a - 1),
    Complex.exp (-(N : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) * (j : ℂ) ^ (2 * k) *
      Real.sin (j * Real.pi / a) * Real.sin (j * Real.pi / 2)

/-- The amplitude of (5.20):
`C_{a,N} = -2 N^{5/2}/(4a)^{3/2} exp(-(a/2 + 2/a) πi/(2N) + πi/4) A⁺_{a,2}(N, 1)`. -/
def geoZhengC (a N : ℕ) : ℂ :=
  -2 * (((N : ℝ) ^ (5 / 2 : ℝ) / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
    Complex.exp (-((a : ℂ) / 2 + 2 / a) * Real.pi * Complex.I / (2 * N) +
      Real.pi * Complex.I / 4) * geoZhengA a N 1

/-- Zheng, Lemma 3.2. -/
def ZhengLemma32 : Prop :=
  ∀ δ : ℝ, 1 / 2 < δ → δ < 1 → ∃ ε > 0, ∃ C > 0, ∀ N n i : ℕ, 1 ≤ N → n + i < N →
    (N : ℝ) ^ δ ≤ |(n : ℝ) - N / 2| + |(i : ℝ) - N / 4| →
      geoNormFactor N n i < C * Real.exp (-ε * (N : ℝ) ^ (2 * δ - 1)) * geoNormFactor0 N

/-- Zheng, Lemma 3.3 with `α = 0` and the constant (3.34). -/
def ZhengLemma33 (β δ : ℝ) : Prop :=
  ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    ‖geoWindowSum N δ β -
        geoGaussConst β * N * Complex.exp (-(β : ℂ) * N * Real.pi * Complex.I / 8) *
          geoNormFactor0 N‖ ≤
      K * (N : ℝ) ^ (3 * δ - 2) * (N * geoNormFactor0 N)

/-- Zheng (5.16): the bracket is `O(N⁴)` uniformly on `0 ≤ n, i, n + i < N`. -/
def ZhengEq516 (a : ℕ) : Prop :=
  ∃ K : ℝ, ∀ N n i : ℕ, 1 ≤ N → n + i < N →
    ‖geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N‖ ≤
      K * (N : ℝ) ^ 4

/-- Zheng (5.19): `b_{n,i} Ĥ_n = O(N²)` on `|n - N/2| + |i - N/4| < N/(8a)`. -/
def ZhengEq519 (a : ℕ) : Prop :=
  ∃ K : ℝ, ∀ N n i : ℕ, 1 ≤ N → n + i < N → GeoInWindow N (N / (8 * a)) n i →
    ‖geoZhengB N n i * geoHatInput a n (geoHalfRoot N)‖ ≤ K * (N : ℝ) ^ 2

/-- Zheng (5.20): `q∂_q Ĥ_n = C_{a,N} a_n^{-8a} + O(N²)` on the same region. -/
def ZhengEq520 (a : ℕ) : Prop :=
  ∃ K : ℝ, ∀ N n i : ℕ, 1 ≤ N → n + i < N → GeoInWindow N (N / (8 * a)) n i →
    ‖geoHatInputDeriv a n N - geoZhengC a N * geoPhasePow N n (-(8 * a : ℝ))‖ ≤
      K * (N : ℝ) ^ 2

/-- Zheng, Proposition 4.1 for `(p, q) = (a, 2)`. -/
def ZhengProp41 (a : ℕ) : Prop := ∀ N : ℤ, geoZhengA a N 1 ≠ 0

/-- All cited estimates for the companion `T(a, 2)` (with (5.16), (5.19) for the corrected `b`). -/
def ZhengEstimates (a : ℕ) : Prop :=
  ZhengLemma32 ∧
    (∀ δ : ℝ, 1 / 2 < δ → δ < 2 / 3 →
      ZhengLemma33 (-(8 * a + 1 : ℝ)) δ ∧ ZhengLemma33 0 δ) ∧
    ZhengEq516 a ∧ ZhengEq519 a ∧ ZhengEq520 a ∧ ZhengProp41 a

end AJConjecture
