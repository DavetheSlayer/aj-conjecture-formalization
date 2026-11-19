import Mathlib
import AJHandoff.LocalTheory.LocHJet

/-!
# I-GAUGE: unramified meridian coordinates `x = a z^k`

The substitution `x = a z^k` (`a ≠ 0`, `k ≥ 1`) carries the shift `σ(z) = Q z` to
`σ(x) = Q^k x`, whose first-order constant is `k c`, and the vector field `c z d/dz` to
`k c x d/dx`: the one-form `(D₁/D₀) dx/(k c x)` pulls back to `(D₁/D₀)(a z^k) dz/(c z)`. At a point
`z₀ ≠ 0` the map is unramified, so the residue, hence the normalized index, is unchanged. This
covers the knot conventions `x = M²` at `M ≠ 0` (the source's passage from `C(x)` to `C(M)`).
A determinant `D = A/B` in the variable `x` (`A, B ∈ ℂ[[h]][x]`, `B₀ ≠ 0`) pulls back to
`A(a z^k)/B(a z^k)`.

The coordinate inversion `z ↦ z⁻¹` (also unramified at `z₀ ≠ 0`, with `c ↦ -c`) is not
formalized: no statement of the package uses it.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The dilation `σ(x) = Q^k x`, `k ≥ 1`, with first-order constant `k c`. -/
def locDilationPow (δ : LocDilation) (k : ℕ) (hk : 0 < k) : LocDilation where
  Q := δ.Q ^ k
  constantCoeff_Q := by rw [Units.val_pow_eq_pow_val, map_pow, δ.constantCoeff_Q, one_pow]
  coeff_one_Q_ne_zero := by
    rw [Units.val_pow_eq_pow_val, PowerSeries.coeff_one_pow, δ.constantCoeff_Q, one_pow, mul_one]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') δ.c_ne_zero

theorem locDilationPow_c (δ : LocDilation) (k : ℕ) (hk : 0 < k) :
    (locDilationPow δ k hk).c = k * δ.c := by
  rw [LocDilation.c, locDilationPow, Units.val_pow_eq_pow_val, PowerSeries.coeff_one_pow,
    δ.constantCoeff_Q, one_pow, mul_one, LocDilation.c]

/-- The substitution `x ↦ a z^k` on `ℂ[[h]][x]`. -/
def locPowerSubst (a : ℂ) (k : ℕ) : LocPoly →+* LocPoly :=
  Polynomial.compRingHom (C (PowerSeries.C a) * X ^ k)

/-- The substitution `x ↦ a z^k`, `a ≠ 0`, `k ≥ 1`, maps nonzero polynomials to nonzero
polynomials. -/
private theorem nonZeroDivisors_le_comap_compRingHom_powerSubst {a : ℂ} {k : ℕ} (ha : a ≠ 0)
    (hk : 0 < k) :
    nonZeroDivisors ℂ[X] ≤
      (nonZeroDivisors ℂ[X]).comap (Polynomial.compRingHom (C a * X ^ k : ℂ[X])) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  rcases comp_eq_zero_iff.1 h with h | ⟨-, h⟩
  · exact nonZeroDivisors.ne_zero hp h
  · have := congrArg natDegree h
    rw [natDegree_C, natDegree_C_mul_X_pow k a ha] at this
    omega

/-- The substitution `x ↦ a z^k` on `ℂ(x)`. -/
def ratPowerSubst (a : ℂ) (k : ℕ) (ha : a ≠ 0) (hk : 0 < k) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.compRingHom (C a * X ^ k : ℂ[X]))
    (nonZeroDivisors_le_comap_compRingHom_powerSubst ha hk)

/-- The substitution intertwines the shifts: `φ ∘ σ_{Q^k} = σ_Q ∘ φ`. -/
theorem locPowerSubst_shift (δ : LocDilation) (a : ℂ) (k : ℕ) (hk : 0 < k) (f : LocPoly) :
    locPowerSubst a k ((locDilationPow δ k hk).shift f) = δ.shift (locPowerSubst a k f) := by
  have h1 : (locDilationPow δ k hk).shift f = f.comp (C ((δ.Q : PowerSeries ℂ) ^ k) * X) := by
    rw [← Units.val_pow_eq_pow_val]
    rfl
  have h2 : ∀ g : LocPoly, δ.shift g = g.comp (C (δ.Q : PowerSeries ℂ) * X) := fun g ↦ rfl
  have h3 : ∀ g : LocPoly, locPowerSubst a k g = g.comp (C (PowerSeries.C a) * X ^ k) :=
    fun g ↦ rfl
  rw [h1, h2, h3, h3, comp_assoc, comp_assoc, mul_comp, C_comp, X_comp, mul_comp, C_comp,
    X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul,
    mul_comm (PowerSeries.C a)]

/-- The substitution commutes with the reduction. -/
private theorem locJet0_locPowerSubst (a : ℂ) (k : ℕ) (f : LocPoly) :
    locJet0 (locPowerSubst a k f) = (locJet0 f).comp (C a * X ^ k) := by
  change (f.comp (C (PowerSeries.C a) * X ^ k)).map PowerSeries.constantCoeff = _
  rw [Polynomial.map_comp, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
    PowerSeries.constantCoeff_C]
  rfl

/-- The substitution commutes with the first jet. -/
private theorem locJet1_locPowerSubst (a : ℂ) (k : ℕ) (f : LocPoly) :
    locJet1 (locPowerSubst a k f) = (locJet1 f).comp (C a * X ^ k) := by
  change locJet1 (f.comp (C (PowerSeries.C a) * X ^ k)) = _
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, locJet1_add, hp, hq, locJet1_add, add_comp]
  | monomial n c =>
    have hm : ∀ (m : ℕ) (x : PowerSeries ℂ), locJet1 (monomial m x) =
        monomial m (PowerSeries.coeff 1 x) := by
      intro m x
      ext j
      rw [coeff_locJet1]
      rcases eq_or_ne m j with rfl | hmj
      · rw [coeff_monomial_same, coeff_monomial_same]
      · rw [coeff_monomial_of_ne _ hmj.symm, coeff_monomial_of_ne _ hmj.symm, map_zero]
    rw [monomial_comp, hm, monomial_comp, mul_pow, mul_pow, ← C_pow, ← C_pow, ← pow_mul,
      ← pow_mul, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, C_mul_X_pow_eq_monomial,
      C_mul_X_pow_eq_monomial, hm, ← map_pow, PowerSeries.coeff_mul_C]

/-- The substitution on polynomials. -/
private theorem ratPowerSubst_algebraMap {a : ℂ} {k : ℕ} (ha : a ≠ 0) (hk : 0 < k) (p : ℂ[X]) :
    ratPowerSubst a k ha hk (algebraMap ℂ[X] (RatFunc ℂ) p) =
      algebraMap ℂ[X] (RatFunc ℂ) (p.comp (C a * X ^ k)) := by
  have h := RatFunc.map_apply_div (Polynomial.compRingHom (C a * X ^ k : ℂ[X]))
    (nonZeroDivisors_le_comap_compRingHom_powerSubst ha hk) p 1
  simp only [map_one, div_one] at h
  exact h

/-- The substitution fixes constants. -/
private theorem ratPowerSubst_C {a : ℂ} {k : ℕ} (ha : a ≠ 0) (hk : 0 < k) (c : ℂ) :
    ratPowerSubst a k ha hk (RatFunc.C c) = RatFunc.C c := by
  rw [← RatFunc.algebraMap_C, ratPowerSubst_algebraMap, C_comp]

/-- The substitution maps `x` to `a z^k`. -/
private theorem ratPowerSubst_X {a : ℂ} {k : ℕ} (ha : a ≠ 0) (hk : 0 < k) :
    ratPowerSubst a k ha hk RatFunc.X = RatFunc.C a * RatFunc.X ^ k := by
  rw [← RatFunc.algebraMap_X, ratPowerSubst_algebraMap, X_comp, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]

/-- An unramified pullback `x = a z^k` at `z₀ ≠ 0` keeps simple residues: the residue of
`f(x) dx` at `a z₀^k` is the residue of `f(a z^k) k a z^(k-1) dz` at `z₀`. -/
private theorem hasSimpleResidue_ratPowerSubst {a : ℂ} (ha : a ≠ 0) {k : ℕ} (hk : 0 < k)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {F : RatFunc ℂ} {ι : ℂ} (hF : HasSimpleResidue F (a * z₀ ^ k) ι) :
    HasSimpleResidue (ratPowerSubst a k ha hk F *
      (RatFunc.C ((k : ℂ) * a) * RatFunc.X ^ (k - 1))) z₀ ι := by
  obtain ⟨p, b, hb, hpb⟩ := hF
  have hψ := congrArg (ratPowerSubst a k ha hk) hpb
  rw [map_mul, map_sub, map_div₀, map_sub, ratPowerSubst_X, ratPowerSubst_C, ratPowerSubst_C,
    ratPowerSubst_algebraMap, ratPowerSubst_algebraMap] at hψ
  obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (X : ℂ[X]) (C z₀) k
  have hS' := congrArg derivative hS
  simp only [derivative_sub, derivative_X_pow, derivative_mul, derivative_X, derivative_C,
    sub_zero, one_mul, ← C_pow] at hS'
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hSz : S.eval z₀ = (n + 1 : ℂ) * z₀ ^ n := by
    have := congrArg (eval z₀) hS'
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_sub, sub_self, zero_mul,
      add_zero, Nat.add_sub_cancel] at this
    rw [← this]
    push_cast
    ring
  refine ⟨C ι * derivative S * b.comp (C a * X ^ (n + 1)) +
    p.comp (C a * X ^ (n + 1)) * C (((n + 1 : ℕ) : ℂ) * a) * X ^ n * S,
    S * b.comp (C a * X ^ (n + 1)), ?_, ?_⟩
  · rw [eval_mul, eval_comp, hSz]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) (pow_ne_zero _ hz₀))
      hb
  · have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    have hne : ∀ q : ℂ[X], q.eval z₀ ≠ 0 → algebraMap ℂ[X] (RatFunc ℂ) q ≠ 0 :=
      fun q hq ↦ (map_ne_zero_iff _ hinj).2 fun h ↦ hq (by rw [h, eval_zero])
    have hB := hne (b.comp (C a * X ^ (n + 1))) (by simpa [eval_comp] using hb)
    have hSne := hne S (by
      rw [hSz]
      exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) (pow_ne_zero _ hz₀))
    have hXz : (RatFunc.X - RatFunc.C z₀ : RatFunc ℂ) ≠ 0 := by
      rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
      exact (map_ne_zero_iff _ hinj).2 (X_sub_C_ne_zero z₀)
    have ha' : (RatFunc.C a : RatFunc ℂ) ≠ 0 := by simpa using ha
    have hSR := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hS
    have hS'R := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hS'
    simp only [map_sub, map_mul, map_pow, map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      Nat.add_sub_cancel, map_natCast] at hSR hS'R
    have hden : RatFunc.C a * RatFunc.X ^ (n + 1) - RatFunc.C (a * z₀ ^ (n + 1)) =
        RatFunc.C a * ((RatFunc.X - RatFunc.C z₀) * algebraMap ℂ[X] (RatFunc ℂ) S) := by
      rw [← hSR, map_mul, map_pow]
      ring
    rw [hden] at hψ
    have hY : ratPowerSubst a (n + 1) ha hk F =
        algebraMap ℂ[X] (RatFunc ℂ) (p.comp (C a * X ^ (n + 1))) /
          algebraMap ℂ[X] (RatFunc ℂ) (b.comp (C a * X ^ (n + 1))) + RatFunc.C ι /
          (RatFunc.C a * ((RatFunc.X - RatFunc.C z₀) * algebraMap ℂ[X] (RatFunc ℂ) S)) := by
      rw [← hψ, mul_div_cancel_right₀ _ hB, sub_add_cancel]
    rw [hY, Nat.add_sub_cancel]
    simp only [map_add, map_mul, map_pow, map_natCast, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    field_simp
    linear_combination (algebraMap ℂ[X] (RatFunc ℂ) (b.comp (C a * X ^ (n + 1))) * RatFunc.C ι) *
      hS'R

/-- The pullback of a determinant along `x = a z^k` has the pulled-back jets and, at
`z₀ ≠ 0`, the same normalized index. -/
theorem hasNormalizedIndex_powerSubst (δ : LocDilation) {a : ℂ} (ha : a ≠ 0) {k : ℕ}
    (hk : 0 < k) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {A B : LocPoly} (hB : locJet0 B ≠ 0)
    {D₀ D₁ : RatFunc ℂ}
    (hD : HasHJet (algebraMap LocPoly LocField A / algebraMap LocPoly LocField B) D₀ D₁) {ι : ℂ}
    (hι : HasNormalizedIndex (locDilationPow δ k hk).c (a * z₀ ^ k) D₀ D₁ ι) :
    HasHJet (algebraMap LocPoly LocField (locPowerSubst a k A) /
        algebraMap LocPoly LocField (locPowerSubst a k B))
      (ratPowerSubst a k ha hk D₀) (ratPowerSubst a k ha hk D₁) ∧
    HasNormalizedIndex δ.c z₀ (ratPowerSubst a k ha hk D₀) (ratPowerSubst a k ha hk D₁) ι := by
  have hinjF := IsFractionRing.injective LocPoly LocField
  have hcomp : ∀ p : ℂ[X], p ≠ 0 → p.comp (C a * X ^ k) ≠ 0 := fun p hp ↦
    nonZeroDivisors.ne_zero (nonZeroDivisors_le_comap_compRingHom_powerSubst ha hk
      (mem_nonZeroDivisors_of_ne_zero hp))
  have hBF : algebraMap LocPoly LocField B ≠ 0 :=
    (map_ne_zero_iff _ hinjF).2 fun h ↦ hB (by rw [h, map_zero])
  have hφB : locJet0 (locPowerSubst a k B) ≠ 0 := by
    rw [locJet0_locPowerSubst]
    exact hcomp _ hB
  have hφBF : algebraMap LocPoly LocField (locPowerSubst a k B) ≠ 0 :=
    (map_ne_zero_iff _ hinjF).2 fun h ↦ hφB (by rw [h, map_zero])
  have h' : HasHJet (algebraMap LocPoly LocField A / algebraMap LocPoly LocField B) _ _ :=
    ⟨A, B, hB, div_mul_cancel₀ _ hBF, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hD.unique h'
  refine ⟨⟨locPowerSubst a k A, locPowerSubst a k B, hφB, div_mul_cancel₀ _ hφBF, ?_, ?_⟩, ?_⟩
  · rw [map_div₀, ratPowerSubst_algebraMap, ratPowerSubst_algebraMap, locJet0_locPowerSubst,
      locJet0_locPowerSubst]
  · rw [map_div₀, map_pow, ratPowerSubst_algebraMap, ratPowerSubst_algebraMap,
      locJet0_locPowerSubst, locJet0_locPowerSubst, locJet1_locPowerSubst, locJet1_locPowerSubst,
      sub_comp, mul_comp, mul_comp]
  · unfold HasNormalizedIndex at hι ⊢
    rw [locDilationPow_c] at hι
    have key := hasSimpleResidue_ratPowerSubst ha hk hz₀ hι
    convert key using 1
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hc' : (RatFunc.C δ.c : RatFunc ℂ) ≠ 0 := by simpa using δ.c_ne_zero
    have ha' : (RatFunc.C a : RatFunc ℂ) ≠ 0 := by simpa using ha
    have hX' : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    have hk' : (RatFunc.C ((n + 1 : ℕ) : ℂ) : RatFunc ℂ) ≠ 0 := by
      rw [map_natCast]
      exact_mod_cast Nat.succ_ne_zero n
    simp only [map_div₀, map_mul, ratPowerSubst_C, ratPowerSubst_X, Nat.add_sub_cancel]
    field_simp
    ring

end AJConjecture
