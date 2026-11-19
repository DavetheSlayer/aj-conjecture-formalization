import Mathlib
import AJHandoff.LocalTheory.LocQuotientIndex
import AJHandoff.LocalTheory.LocGaugeIndex
import AJHandoff.LocalTheory.LocRamification
import AJHandoff.LocalTheory.LocToyOperator

/-!
# I-CTRL: the failed weak-regularity formulation (the moving-pole half-residue)

With `c = 1`, `Q = exp(h)`, the rank-one module with matrix
`D = (z - 1 + (Q - 1)/4) / (z - 1 - (Q - 1)/4)` has `v_h(D) = 0`, specialization `D₀ = 1` (a unit
with unit endpoints at `z₀ = 1`), and first logarithmic coefficient `D₁/D₀ = 1/(2(z - 1))`: its
normalized index at `z₀ = 1` is `1/2`. It is a quotient of itself. So the version of Lemma 1 that
assumes only `h`-adic regularity and a unit specialization at `z₀` (`WeakLatticeLemma`) is false.
`D` does not satisfy (JL): numerator and denominator lie in `(h, z - 1)` and are not associates,
and no rational gauge `D σ(g)/g` is a unit of `R₀`, since the gauge law preserves the nonzero
class `1/2 mod ℤ` while Lemma 1 would make it integral. Under a degree-two meridian ramification
the half-index becomes `1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The moving pole `(Q - 1)/4 = h/4 + O(h²)`. -/
def weakPole : PowerSeries ℂ := PowerSeries.C (1 / 4 : ℂ) * ((toyDilation.Q : PowerSeries ℂ) - 1)

/-- The weak-regularity counterexample `(z - 1 + (Q - 1)/4) / (z - 1 - (Q - 1)/4)`. -/
def weakD : LocField :=
  algebraMap LocPoly LocField (X - 1 + C weakPole) /
    algebraMap LocPoly LocField (X - 1 - C weakPole)

/-- The weak formulation of Lemma 1: `h`-adic regularity and a unit specialization at `z₀`
suffice for an integral normalized index. -/
def WeakLatticeLemma : Prop :=
  ∀ (δ : LocDilation) (z₀ : ℂ), z₀ ≠ 0 → ∀ (D : LocField) (D₀ D₁ : RatFunc ℂ),
    HasHJet D D₀ D₁ → IsUnitAt z₀ D₀ → ∃ n : ℤ, HasNormalizedIndex δ.c z₀ D₀ D₁ n

/-- The constant and linear coefficients of the moving pole. -/
private theorem coeff_weakPole : PowerSeries.constantCoeff weakPole = 0 ∧
    PowerSeries.coeff 1 weakPole = 1 / 4 := by
  have hQ0 : PowerSeries.constantCoeff (toyDilation.Q : PowerSeries ℂ) = 1 :=
    toyDilation.constantCoeff_Q
  have hQ1 : PowerSeries.coeff 1 (toyDilation.Q : PowerSeries ℂ) = 1 :=
    LocDilation.exp_c 1 one_ne_zero
  refine ⟨?_, ?_⟩
  · simp [weakPole, hQ0]
  · rw [weakPole, PowerSeries.coeff_C_mul, map_sub, hQ1, PowerSeries.coeff_one]
    norm_num

/-- The reduction of `z - 1 + s p`, `s = ± 1`. -/
private theorem locJet0_X_sub_one_add_weak (s : ℂ) :
    locJet0 (X - 1 + C (PowerSeries.C s * weakPole)) = X - 1 := by
  simp [locJet0, coeff_weakPole.1]

/-- The first jet of `z - 1 + s p`, `s = ± 1`. -/
private theorem locJet1_X_sub_one_add_weak (s : ℂ) :
    locJet1 (X - 1 + C (PowerSeries.C s * weakPole)) = C (s / 4) := by
  ext n
  rw [coeff_locJet1, coeff_C]
  rcases n with _ | _ | n
  · simp [PowerSeries.coeff_C_mul, coeff_weakPole.2, div_eq_mul_inv]
  · simp [coeff_X, coeff_one]
  · simp [coeff_X, coeff_one]

/-- `z - 1 ≠ 0` in `ℂ(z)`. -/
private theorem ratFunc_X_sub_one_ne_zero_weak : (RatFunc.X - 1 : RatFunc ℂ) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← map_one (algebraMap ℂ[X] (RatFunc ℂ)), ← map_sub]
  exact (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 (X_sub_C_ne_zero 1)

/-- The jets of `weakD` and its half-integral index. -/
theorem weakD_hasHJet_index :
    HasHJet weakD 1 (1 / (2 * (RatFunc.X - 1))) ∧ IsUnitAt 1 1 ∧
      HasNormalizedIndex toyDilation.c 1 1 (1 / (2 * (RatFunc.X - 1))) (1 / 2) := by
  have hX1 := ratFunc_X_sub_one_ne_zero_weak
  have ha : (X - 1 + C weakPole : LocPoly) = X - 1 + C (PowerSeries.C 1 * weakPole) := by
    rw [map_one, one_mul]
  have hb : (X - 1 - C weakPole : LocPoly) = X - 1 + C (PowerSeries.C (-1) * weakPole) := by
    rw [map_neg, map_one, neg_one_mul, map_neg, sub_eq_add_neg]
  have hb0 : locJet0 (X - 1 - C weakPole) ≠ 0 := by
    rw [hb, locJet0_X_sub_one_add_weak]
    exact X_sub_C_ne_zero 1
  have hbF : algebraMap LocPoly LocField (X - 1 - C weakPole) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective LocPoly LocField)).2
      fun h ↦ hb0 (by rw [h, map_zero])
  refine ⟨⟨_, _, hb0, div_mul_cancel₀ _ hbF, ?_, ?_⟩, ⟨1, 1, by simp, by simp, by simp⟩, ?_⟩
  · rw [ha, hb, locJet0_X_sub_one_add_weak, locJet0_X_sub_one_add_weak, div_self]
    rw [map_sub, map_one, RatFunc.algebraMap_X]
    exact hX1
  · rw [ha, hb, locJet0_X_sub_one_add_weak, locJet0_X_sub_one_add_weak,
      locJet1_X_sub_one_add_weak, locJet1_X_sub_one_add_weak]
    simp only [map_sub, map_mul, map_one, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    field_simp
    simp only [map_div₀, map_neg, map_one, map_ofNat]
    ring
  · have hc : toyDilation.c = 1 := LocDilation.exp_c 1 one_ne_zero
    have hres : HasSimpleResidue (1 / (2 * (RatFunc.X - 1))) 1 (1 / 2) := by
      unfold HasSimpleResidue
      have h0 : (1 / (2 * (RatFunc.X - 1)) - RatFunc.C (1 / 2 : ℂ) / (RatFunc.X - RatFunc.C 1) :
          RatFunc ℂ) = 0 := by
        rw [map_one, map_div₀, map_one, map_ofNat]
        field_simp
        ring
      rw [h0]
      exact ⟨0, 1, by simp, by simp⟩
    have := hres.div_C_mul_X one_ne_zero one_ne_zero
    unfold HasNormalizedIndex
    rw [hc, div_one]
    convert this using 1
    norm_num

/-- The weak formulation is false. -/
theorem not_weakLatticeLemma : ¬ WeakLatticeLemma := by
  intro h
  obtain ⟨hjet, hunit, hind⟩ := weakD_hasHJet_index
  obtain ⟨n, hn⟩ := h toyDilation 1 one_ne_zero weakD _ _ hjet hunit
  have h2 : ((2 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
    push_cast
    rw [HasSimpleResidue.unique hn hind]
    norm_num
  have := Int.cast_injective h2
  omega

/-- A nonzero element of `ℂ[[h]][z]` is `h^k γ` with `γ` of nonzero reduction. -/
private theorem exists_locH_pow_mul_weak {a : LocPoly} (ha : a ≠ 0) :
    ∃ (k : ℕ) (γ : LocPoly), locJet0 γ ≠ 0 ∧ a = locH ^ k * γ := by
  have hprime : Prime locH := Polynomial.prime_C_iff.2 PowerSeries.prime_X
  obtain ⟨k, γ, hndvd, rfl⟩ := WfDvdMonoid.max_power_factor ha hprime.irreducible
  refine ⟨k, γ, fun h0 ↦ hndvd ?_, rfl⟩
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i ↦ PowerSeries.X_dvd_iff.2 ?_
  rw [← coeff_locJet0, h0, coeff_zero]

/-- A nonzero element of `F` is `h^k` times an `h`-adic unit, whose reduction is a quotient of
nonzero polynomials. -/
private theorem exists_hasHJet_locH_zpow_mul_weak {g : LocField} (hg : g ≠ 0) :
    ∃ (k : ℤ) (g₀ g₁ : RatFunc ℂ),
      HasHJet (algebraMap LocPoly LocField locH ^ (-k) * g) g₀ g₁ ∧ g₀ ≠ 0 ∧
        ∃ a b : ℂ[X], a ≠ 0 ∧ b ≠ 0 ∧
          g₀ = algebraMap ℂ[X] (RatFunc ℂ) a / algebraMap ℂ[X] (RatFunc ℂ) b := by
  have hinjF := IsFractionRing.injective LocPoly LocField
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := LocPoly) g
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hg
    exact hg rfl
  obtain ⟨k₁, γ₁, hγ₁, rfl⟩ := exists_locH_pow_mul_weak hx0
  obtain ⟨k₂, γ₂, hγ₂, rfl⟩ := exists_locH_pow_mul_weak hy0
  have hH : algebraMap LocPoly LocField locH ≠ 0 :=
    (map_ne_zero_iff _ hinjF).2 (Polynomial.prime_C_iff.2 PowerSeries.prime_X).ne_zero
  have hG₂ : algebraMap LocPoly LocField γ₂ ≠ 0 :=
    (map_ne_zero_iff _ hinjF).2 fun h ↦ hγ₂ (by rw [h, map_zero])
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  refine ⟨(k₁ : ℤ) - k₂, _, _, ⟨γ₁, γ₂, hγ₂, ?_, rfl, rfl⟩, ?_, _, _, hγ₁, hγ₂, rfl⟩
  · simp only [map_mul, map_pow]
    rw [zpow_neg, zpow_sub₀ hH, zpow_natCast, zpow_natCast]
    field_simp
  · exact div_ne_zero ((map_ne_zero_iff _ hinj).2 hγ₁) ((map_ne_zero_iff _ hinj).2 hγ₂)

/-- A quotient of nonzero polynomials has an order at every point. -/
private theorem exists_hasOrderAt_div_weak {a b : ℂ[X]} (ha : a ≠ 0) (hb : b ≠ 0) (z₀ : ℂ) :
    ∃ m : ℤ, HasOrderAt (algebraMap ℂ[X] (RatFunc ℂ) a / algebraMap ℂ[X] (RatFunc ℂ) b) z₀ m := by
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  obtain ⟨p, hap, hp⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha z₀
  obtain ⟨q, hbq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb z₀
  have hp0 : p.eval z₀ ≠ 0 := fun h ↦ hp (dvd_iff_isRoot.2 h)
  have hq0 : q.eval z₀ ≠ 0 := fun h ↦ hq (dvd_iff_isRoot.2 h)
  have hQ : algebraMap ℂ[X] (RatFunc ℂ) q ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 fun h ↦ hq0 (by rw [h, eval_zero])
  have hμ : algebraMap ℂ[X] (RatFunc ℂ) (X - C z₀) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (X_sub_C_ne_zero z₀)
  refine ⟨(a.rootMultiplicity z₀ : ℤ) - b.rootMultiplicity z₀,
    algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q,
    ⟨p, q, hp0, hq0, div_mul_cancel₀ _ hQ⟩, ?_⟩
  have hX : (RatFunc.X - RatFunc.C z₀ : RatFunc ℂ) = algebraMap ℂ[X] (RatFunc ℂ) (X - C z₀) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [hX, zpow_sub₀ hμ, zpow_natCast, zpow_natCast]
  conv_lhs => rw [hap, hbq]
  simp only [map_mul, map_pow]
  field_simp

/-- No rational gauge makes `weakD` jointly regular at `z₀ = 1`. -/
theorem weakD_not_isJointRegular {g : LocField} (hg : g ≠ 0) :
    ¬ IsJointRegular 1
      (!![weakD * toyDilation.fieldShift g / g] : Matrix (Fin 1) (Fin 1) LocField) := by
  intro hA
  obtain ⟨hjet, -, hind⟩ := weakD_hasHJet_index
  obtain ⟨k, g₀, g₁, hgj, hg₀, a, b, ha, hb, rfl⟩ := exists_hasHJet_locH_zpow_mul_weak hg
  obtain ⟨m, hm⟩ := exists_hasOrderAt_div_weak ha hb 1
  obtain ⟨D₁', hj', hi'⟩ := hasNormalizedIndex_mul_coboundary toyDilation one_ne_zero hjet
    one_ne_zero hind hgj hg₀ hm
  have hQ : Function.Surjective (1 : Matrix (Fin 1) (Fin 1) LocField).mulVecLin := by
    rw [Matrix.mulVecLin_one]
    exact Function.surjective_id
  have hBQ : (!![weakD * toyDilation.fieldShift g / g] : Matrix (Fin 1) (Fin 1) LocField) *
      (1 : Matrix (Fin 1) (Fin 1) LocField).map toyDilation.fieldShift =
      1 * !![weakD * toyDilation.fieldShift g / g] := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one, one_mul]
  obtain ⟨D₀'', D₁'', hj'', -, n, hn⟩ :=
    exists_hasNormalizedIndex_int_of_quotient toyDilation one_ne_zero hA hQ hBQ
  rw [Matrix.det_fin_one_of] at hj''
  obtain ⟨rfl, rfl⟩ := hj''.unique hj'
  have h2 : ((2 * n : ℤ) : ℂ) = ((1 + 2 * m : ℤ) : ℂ) := by
    push_cast
    rw [HasSimpleResidue.unique hn hi']
    ring
  have := Int.cast_injective h2
  omega

/-- A degree-two ramification at `z₀ = 1` doubles the half-index to `1`. -/
theorem weakD_ramify :
    HasSimpleResidue
      (ratRamify 1 2 two_pos (1 / (2 * (RatFunc.X - 1)) / (RatFunc.C 1 * RatFunc.X)) *
        ((2 : ℕ) : RatFunc ℂ) * RatFunc.X ^ (2 - 1)) 0 1 := by
  have hind := weakD_hasHJet_index.2.2
  have hc : toyDilation.c = 1 := LocDilation.exp_c 1 one_ne_zero
  unfold HasNormalizedIndex at hind
  rw [hc, div_one] at hind
  convert hasSimpleResidue_ramify hind two_pos using 1
  norm_num

end AJConjecture
