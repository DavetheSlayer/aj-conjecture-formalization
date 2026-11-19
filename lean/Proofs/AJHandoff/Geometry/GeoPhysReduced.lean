import Mathlib
import AJFamily.Skein.TorusSequenceIdentity
import AJHandoff.Geometry.GeoKernelFormula
import AJHandoff.Geometry.GeoPhysDefs
import AJHandoff.Geometry.GeoPhysReducedCleared
import AJHandoff.Geometry.GeoPhysReducedValue

/-!
# Zheng's diagonal is the value of the actual reduced invariant (G-PHYS, identification; optional)

For the library knot `whiteheadTorusKnot k` (`a = 2k + 1`), `J(N) = [N] F_N` with
`F_N = torusReducedFormula a N`. If the reduced invariant is a Laurent polynomial `P` in `t`
(integrality of the reduced coloured Jones polynomial: standard, e.g. via Habiro's cyclotomic
expansion, but not in the library — stated as the hypothesis `GeoReducedIntegral`), then its value
at `t_N = e^{πi/(2N)}` (`t² = q_N^{1/2}`) is Zheng's diagonal (5.3) with the corrected `b_{n,i}`.
So `geoZhengDiagonal` is the actual generically reduced invariant at the root, not a separate
model. Checked numerically for `a ∈ {3, 5}`, `2 ≤ N ≤ 6` (limit of `F_N(t)` as `t → t_N`).

Route. Coefficient extraction (`geo_torusWhiteheadFormula_eq_extract`) writes
`[N] F_N = ∑_n ξ_{N,n} u_n` with every `ξ_{N,n}` (Zheng (2.7)) regular at `t_N`. Since
`[N](t_N) = 0` and `P` is regular, `P(t_N) · [N]'(t_N) = (∑ ξ u)'(t_N)` (differentiate
`P · [N] = ∑ ξ u` as functions regular near `t_N`); in the variable `q` with `q^{1/2} = t²`,
`[N] = (q^{N/2} - q^{-N/2})/(q^{1/2} - q^{-1/2})`, the numerator has `q∂_q`-derivative `-N` at
`q_N` (Zheng's `-N` in (5.3)), and the product rule on `ξ_{N,n} Ĥ_n` gives the summands
`a_n^{-1} S_{n,i} (b_{n,i} Ĥ_n + q∂_q Ĥ_n)` after evaluating `ξ`'s summand at the root
(`(1 - q^{-i-j})(1 - q^{i+j}) = 4 sin²((i+j)π/N)`, `∏ 1/(1 - q^j) = a_n^{-1}/∏ 2 sin(jπ/N)`,
`q^{N² - (N+1)/2} = -q^{-1/2}`).
-/

noncomputable section

namespace AJConjecture

/-- Integrality of the reduced invariant of `T(2, a)`'s Whitehead double at colour `N`. -/
def GeoReducedIntegral (a N : ℕ) : Prop :=
  ∃ P : LaurentPolynomial ℤ, laurentToField P = torusReducedFormula a N

/-- A Laurent polynomial evaluated on `ℂˣ` is a holomorphic function of `t ≠ 0`. -/
private theorem geo_exists_eval₂_differentiable (P : LaurentPolynomial ℤ) :
    ∃ F : ℂ → ℂ, (∀ (t : ℂ) (ht : t ≠ 0),
      LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) P = F t) ∧
      ∀ t : ℂ, t ≠ 0 → DifferentiableAt ℂ F t := by
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨F, hF, hdF⟩ := hp
    obtain ⟨G, hG, hdG⟩ := hq
    exact ⟨F + G, fun t ht ↦ by rw [map_add, hF t ht, hG t ht, Pi.add_apply],
      fun t ht ↦ (hdF t ht).add (hdG t ht)⟩
  | C_mul_T n c =>
    refine ⟨fun t ↦ (c : ℂ) * t ^ n, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val, Units.val_mk0, eq_intCast]
    · exact (differentiableAt_zpow.mpr (Or.inl ht)).const_mul _

/-- `Ĥ_n` is holomorphic at every `s ≠ 0`. -/
private theorem geo_differentiableAt_hatInput (a n : ℕ) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (geoHatInput a n) s := by
  unfold geoHatInput
  fun_prop (disch := exact Or.inl hs)

/-- The value `c_{n,i}(t_N) = -s⁻¹ a_n^{-1} S_{n,i}` of Zheng's clasp summand. -/
private def geoClaspValue (N n i : ℕ) : ℂ :=
  -(geoHalfRoot N)⁻¹ * geoPhasePow N n (-1) * geoNormFactor N n i

/-- The derivative at `t_N` of the summand `c_{n,i}(t) Ĥ_n(t²)`. -/
private def geoReducedDerivTerm (a N n i : ℕ) : ℂ :=
  4 / geoQuarterRoot N * (((N : ℂ) ^ 2 - N / 2 - 1 / 2) + geoZhengB N n i) *
      geoClaspValue N n i * geoHatInput a n (geoHalfRoot N) +
    geoClaspValue N n i * (deriv (geoHatInput a n) (geoHalfRoot N) * (2 * geoQuarterRoot N))

/-- The numerator `t^{2N} - t^{-2N}` of `[N]` vanishes at `t_N`, with derivative `-4N/t_N`. -/
private theorem geo_quantumNumerator_quarterRoot {N : ℕ} (hN : 1 ≤ N) :
    geoQuarterRoot N ^ (2 * (N : ℤ)) - geoQuarterRoot N ^ (-(2 * (N : ℤ))) = 0 ∧
      HasDerivAt (fun t ↦ t ^ (2 * (N : ℤ)) - t ^ (-(2 * (N : ℤ))))
        (-(4 / geoQuarterRoot N * N)) (geoQuarterRoot N) := by
  have ht0 := geoQuarterRoot_ne_zero N
  have hpow : geoQuarterRoot N ^ (2 * (N : ℤ)) = -1 ∧
      geoQuarterRoot N ^ (-(2 * (N : ℤ))) = -1 := by
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have harg : (((2 * (N : ℤ) : ℤ)) : ℂ) * (Real.pi * Complex.I / (2 * N)) =
        Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [geoQuarterRoot_zpow, harg, Complex.exp_pi_mul_I, geoQuarterRoot_zpow,
      Int.cast_neg, neg_mul, harg, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  refine ⟨by rw [hpow.1, hpow.2, sub_self], ?_⟩
  have := (geo_hasDerivAt_zpow_logDeriv ht0 (2 * (N : ℤ))).sub
    (geo_hasDerivAt_zpow_logDeriv ht0 (-(2 * (N : ℤ))))
  rw [hpow.1, hpow.2] at this
  convert this using 1
  push_cast
  ring

/-- Near `t_N`, `(t^{2N} - t^{-2N}) P(t)` is the double sum of the summands `c_{n,i}(t) Ĥ_n(t²)`. -/
private theorem geo_reduced_eventually_eq (a N : ℕ) (hN : 1 ≤ N) (P : LaurentPolynomial ℤ)
    (hP : laurentToField P = torusReducedFormula a N) (F : ℂ → ℂ)
    (hF : ∀ (t : ℂ) (ht : t ≠ 0),
      LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) P = F t) :
    ∀ᶠ t in nhds (geoQuarterRoot N), (t ^ (2 * (N : ℤ)) - t ^ (-(2 * (N : ℤ)))) * F t =
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        geoClaspSummand N n i t * geoHatInput a n (t ^ 2) := by
  have h1 : ∀ᶠ t in nhds (geoQuarterRoot N), t ≠ 0 :=
    isOpen_ne.mem_nhds (geoQuarterRoot_ne_zero N)
  have h2 : ∀ᶠ t in nhds (geoQuarterRoot N), ∀ r ∈ Finset.Icc 1 (N - 1),
      1 - t ^ (4 * r) ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro r hr
    have hr0 : 1 - geoQuarterRoot N ^ (4 * r) ≠ 0 := by
      rw [pow_mul]
      exact sub_ne_zero.mpr (geoQuarterRoot_pow_four_pow_ne_one hN hr).symm
    exact (continuous_const.sub (continuous_pow _)).continuousAt.eventually_ne hr0
  filter_upwards [h1, h2] with t ht hU
  rw [← hF t ht]
  exact geo_reduced_eval_identity a N P hP ht hU

/-- The derivative at `t_N` of the double sum of the summands `c_{n,i}(t) Ĥ_n(t²)`. -/
private theorem geo_hasDerivAt_reduced_sum (a N : ℕ) (hN : 1 ≤ N) :
    HasDerivAt (fun t ↦ ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        geoClaspSummand N n i t * geoHatInput a n (t ^ 2))
      (∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n), geoReducedDerivTerm a N n i)
      (geoQuarterRoot N) := by
  have ht0 := geoQuarterRoot_ne_zero N
  have hs : geoQuarterRoot N ^ 2 = geoHalfRoot N := geoQuarterRoot_sq hN
  have hHd : ∀ n : ℕ, HasDerivAt (fun t ↦ geoHatInput a n (t ^ 2))
      (deriv (geoHatInput a n) (geoHalfRoot N) * (2 * geoQuarterRoot N)) (geoQuarterRoot N) := by
    intro n
    have h1 : HasDerivAt (fun t : ℂ ↦ t ^ 2) (2 * geoQuarterRoot N) (geoQuarterRoot N) := by
      simpa using hasDerivAt_pow 2 (geoQuarterRoot N)
    have h3 := (geo_differentiableAt_hatInput a n
      (pow_ne_zero 2 ht0)).hasDerivAt.comp (geoQuarterRoot N) h1
    rw [hs] at h3
    exact h3
  refine HasDerivAt.fun_sum fun n _ ↦ HasDerivAt.fun_sum fun i hi ↦ ?_
  have hni : n + i < N := by
    have := Finset.mem_range.mp hi
    omega
  have h1 := geo_hasDerivAt_claspSummand hni ht0
    (fun k hk ↦ geoQuarterRoot_pow_four_pow_ne_one hN hk)
  rw [geo_logDeriv_claspSummand_quarterRoot hN hni] at h1
  convert h1.mul (hHd n) using 1
  simp only [geoReducedDerivTerm, geoClaspValue, geo_claspSummand_quarterRoot hN hni, hs]

/-- Splitting the derivative: the constant `N² - N/2 - 1/2` multiplies the vanishing value of
the double sum, the rest is `-(4N/t_N)` times Zheng's diagonal. -/
private theorem geo_reduced_deriv_sum_split (a N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n), geoReducedDerivTerm a N n i =
      4 / geoQuarterRoot N * ((N : ℂ) ^ 2 - N / 2 - 1 / 2) *
          (∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
            geoClaspValue N n i * geoHatInput a n (geoHalfRoot N)) +
        -(4 / geoQuarterRoot N * N) * geoZhengDiagonal a N := by
  have ht0 := geoQuarterRoot_ne_zero N
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [geoZhengDiagonal, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [geoReducedDerivTerm, geoClaspValue, geoHatInputDeriv, ← geoQuarterRoot_sq hN]
  field_simp
  ring

/-- The value of the reduced invariant at `t_N = e^{πi/(2N)}` is Zheng's diagonal. -/
theorem geo_reduced_value_eq_zhengDiagonal (a N : ℕ) (hN : 1 ≤ N) (P : LaurentPolynomial ℤ)
    (hP : laurentToField P = torusReducedFormula a N) :
    LaurentPolynomial.eval₂ (Int.castRingHom ℂ)
        (Units.mk0 (Complex.exp (Real.pi * Complex.I / (2 * N))) (Complex.exp_ne_zero _)) P =
      geoZhengDiagonal a N := by
  obtain ⟨F, hF, hdF⟩ := geo_exists_eval₂_differentiable P
  rw [hF]
  change F (geoQuarterRoot N) = _
  have ht0 := geoQuarterRoot_ne_zero N
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hev := geo_reduced_eventually_eq a N hN P hP F hF
  obtain ⟨hg0, hgd⟩ := geo_quantumNumerator_quarterRoot hN
  have huniq := ((hgd.mul (hdF _ ht0).hasDerivAt).congr_of_eventuallyEq
    (hev.mono fun t ht ↦ ht.symm)).unique (geo_hasDerivAt_reduced_sum a N hN)
  have hf0 : ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
      geoClaspValue N n i * geoHatInput a n (geoHalfRoot N) = 0 := by
    have h0 := hev.self_of_nhds
    rw [hg0, zero_mul] at h0
    refine Eq.trans ?_ h0.symm
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
    have hni : n + i < N := by
      have := Finset.mem_range.mp hi
      omega
    rw [geoClaspValue, geo_claspSummand_quarterRoot hN hni, geoQuarterRoot_sq hN]
  rw [geo_reduced_deriv_sum_split a N hN, hf0, mul_zero, zero_add, hg0, zero_mul,
    add_zero] at huniq
  have h4 : -(4 / geoQuarterRoot N * (N : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (div_ne_zero (by norm_num) ht0) hN0)
  exact mul_left_cancel₀ h4 huniq

end AJConjecture
