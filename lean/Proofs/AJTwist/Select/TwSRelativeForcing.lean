import Mathlib
import AJConjecture.QAlgOrePseudoDivision
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgOreMulDegree
import AJTwist.Select.TwSGrowthClass

/-!
# The relative forcing lemma (Lemma 6.1)

Source: Lemma 6.1 (`lem:relative`) of the revision-5 manuscript: for a left `𝔻`-submodule `𝒰` of
tails with `P F ∈ 𝒰`, `P ≠ 0` and `F ∉ 𝒰`, the annihilator of the class `F + 𝒰` has a non-unit
generator `R` that right-divides `P` and every tail annihilator of `F`; if `P` is irreducible,
`R` is associated to `P`.

Here `𝒰` is the saturation `TwsSat U` of a growth class `U`, operators are `RecOp`, and "`A`
right-divides `B` over `ℚ(t, M)`" is the pseudo-factorization `C β * B = oreMul coeffShift S A`
with `β ≠ 0` (`AJHandoff.LocalTheory.LocPseudoField`). The library's
`exists_C_mul_eq_oreMul_of_tail_annihilator_of_irreducible` is the case of the class of
eventually rational sequences.

* `tws_exists_selected_divisor`: the selected right divisor `R`.
* `tws_exists_C_mul_eq_oreMul_of_relative`: if `P` has no right pseudo-factor of intermediate
  order, every tail annihilator of `F` is a left pseudo-multiple of `P`.
* `tws_exists_selected_divisor_of_no_linear`: if `P` has no right pseudo-factor of order one, the
  selected divisor has order at least two (the case `a = 0`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A constant operator acts by the value of its coefficient at the colour. -/
private theorem opApplyField_C_twsRelative (c : Coeff) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (C c) f n = evalAtField n c * f n := by
  rw [← monomial_zero_left, opApplyField_monomial, Nat.cast_zero, add_zero]

/-- A nonzero operator of minimal degree among those mapping `F` into the saturated class is a
right pseudo-factor of every operator with that property. -/
private theorem exists_C_mul_eq_oreMul_of_minimalDegree_twsRelative
    {U : (ℤ → RatFunc ℚ) → Prop} (hU : TwsGrowthClass U) {F : ℤ → RatFunc ℚ} {R : RecOp}
    (hR0 : R ≠ 0) (hR : TwsSat U fun n ↦ opApplyField R F n)
    (hmin : ∀ Q' : RecOp, Q' ≠ 0 → (TwsSat U fun n ↦ opApplyField Q' F n) →
      R.natDegree ≤ Q'.natDegree)
    {Q : RecOp} (hQ : TwsSat U fun n ↦ opApplyField Q F n) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T R := by
  obtain ⟨γ, hγ, S, Rem, hdiv, hdeg⟩ := exists_C_mul_eq_oreMul_add coeffShift_injective Q hR0
  have hRem : Rem = C γ * Q - oreMul coeffShift S R := by
    rw [hdiv]
    ring
  have hmem : TwsSat U fun n ↦ opApplyField Rem F n := by
    refine hU.sat.congr_tail (n₀ := 0)
      (hU.sat.sub (hU.sat.opApplyField hQ (C γ)) (hU.sat.opApplyField hR S)) fun n _ ↦ ?_
    rw [hRem, opApplyField_sub_left, opApplyField_oreMul, opApplyField_C_mul_left,
      opApplyField_C_twsRelative]
  have hzero : Rem = 0 := by
    by_contra h0
    have hlt := natDegree_lt_natDegree h0 hdeg
    have hle := hmin Rem h0 hmem
    omega
  refine ⟨γ, hγ, S, ?_⟩
  rw [hdiv, hzero, add_zero]

/-- If `F` is not in the saturated class, no nonzero operator of degree `0` maps it into the
saturated class. -/
private theorem natDegree_ne_zero_of_sat_twsRelative {U : (ℤ → RatFunc ℚ) → Prop}
    (hU : TwsGrowthClass U) {F : ℤ → RatFunc ℚ} (hF : ¬ TwsSat U F) {Q : RecOp} (hQ0 : Q ≠ 0)
    (hQ : TwsSat U fun n ↦ opApplyField Q F n) : Q.natDegree ≠ 0 := by
  intro hdeg
  obtain ⟨c, rfl⟩ : ∃ c, Q = C c := ⟨Q.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩
  have hc : c ≠ 0 := fun h0 ↦ hQ0 (by rw [h0, C_0])
  exact hF (TwsSat.of_coeff_mul hU hc (hU.sat.congr_tail (n₀ := 0) hQ fun n _ ↦
    opApplyField_C_twsRelative c F n))

/-- Among the nonzero operators mapping `F` into the saturated class there is one of least
degree. -/
private theorem exists_minimalDegree_twsRelative {U : (ℤ → RatFunc ℚ) → Prop} {P : RecOp}
    {F : ℤ → RatFunc ℚ} (hP : P ≠ 0) (hPF : TwsSat U fun n ↦ opApplyField P F n) :
    ∃ R : RecOp, R ≠ 0 ∧ (TwsSat U fun n ↦ opApplyField R F n) ∧
      ∀ Q' : RecOp, Q' ≠ 0 → (TwsSat U fun n ↦ opApplyField Q' F n) →
        R.natDegree ≤ Q'.natDegree := by
  classical
  have hex : ∃ d : ℕ, ∃ Q : RecOp, Q ≠ 0 ∧
      (TwsSat U fun n ↦ opApplyField Q F n) ∧ Q.natDegree = d :=
    ⟨_, P, hP, hPF, rfl⟩
  obtain ⟨R, hR0, hR, hRd⟩ := Nat.find_spec hex
  refine ⟨R, hR0, hR, fun Q' h0 hm ↦ ?_⟩
  rw [hRd]
  exact Nat.find_min' hex ⟨Q', h0, hm, rfl⟩

/-- **Lemma 6.1.** If `P F` lies in the saturated class and `F` does not, there is an operator `R`
of positive order, with `R F` in the class, that is a right pseudo-factor of `P` and of every
operator `Q` with `Q F` in the class. -/
theorem tws_exists_selected_divisor {U : (ℤ → RatFunc ℚ) → Prop} (hU : TwsGrowthClass U)
    {P : RecOp} {F : ℤ → RatFunc ℚ} (hP : P ≠ 0)
    (hPF : TwsSat U fun n ↦ opApplyField P F n) (hF : ¬ TwsSat U F) :
    ∃ R : RecOp, 0 < R.natDegree ∧ TwsSat U (fun n ↦ opApplyField R F n) ∧
      (∃ β : Coeff, β ≠ 0 ∧ ∃ S : RecOp, C β * P = oreMul coeffShift S R) ∧
      ∀ Q : RecOp, TwsSat U (fun n ↦ opApplyField Q F n) →
        ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T R := by
  obtain ⟨R, hR0, hR, hmin⟩ := exists_minimalDegree_twsRelative hP hPF
  exact ⟨R, Nat.pos_of_ne_zero (natDegree_ne_zero_of_sat_twsRelative hU hF hR0 hR), hR,
    exists_C_mul_eq_oreMul_of_minimalDegree_twsRelative hU hR0 hR hmin hPF,
    fun _ hQ ↦ exists_C_mul_eq_oreMul_of_minimalDegree_twsRelative hU hR0 hR hmin hQ⟩

/-- **Lemma 6.1, irreducible case.** If moreover the right pseudo-factors of `P` have order `0` or
`deg P`, every operator annihilating a tail of `F` is a left pseudo-multiple of `P`. -/
theorem tws_exists_C_mul_eq_oreMul_of_relative {U : (ℤ → RatFunc ℚ) → Prop}
    (hU : TwsGrowthClass U) {P : RecOp} {F : ℤ → RatFunc ℚ} (hP : P ≠ 0)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hPF : TwsSat U fun n ↦ opApplyField P F n) (hF : ¬ TwsSat U F)
    {Q : RecOp} {n₁ : ℤ} (hQ : ∀ n : ℤ, n₁ ≤ n → opApplyField Q F n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T P := by
  obtain ⟨R, hR0, hR, hmin⟩ := exists_minimalDegree_twsRelative hP hPF
  obtain ⟨β, hβ, S, hfac⟩ :=
    exists_C_mul_eq_oreMul_of_minimalDegree_twsRelative hU hR0 hR hmin hPF
  rcases hirr hβ hfac with h0 | hdeg
  · exact absurd h0 (natDegree_ne_zero_of_sat_twsRelative hU hF hR0 hR)
  · exact exists_C_mul_eq_oreMul_of_minimalDegree_twsRelative hU hP hPF
      (fun Q' h0 hm ↦ hdeg ▸ hmin Q' h0 hm) (hU.sat.zero_tail hQ)

/-- **Lemma 6.1, the case of no first-order right divisor** (`a = 0`). If `P` has no right
pseudo-factor of order one, there is a right pseudo-factor `R` of `P` of order at least two such
that every operator annihilating a tail of `F` is a left pseudo-multiple of `R`. -/
theorem tws_exists_selected_divisor_of_no_linear {U : (ℤ → RatFunc ℚ) → Prop}
    (hU : TwsGrowthClass U) {P : RecOp} {F : ℤ → RatFunc ℚ} (hP : P ≠ 0)
    (hlin : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree ≠ 1)
    (hPF : TwsSat U fun n ↦ opApplyField P F n) (hF : ¬ TwsSat U F) :
    ∃ R : RecOp, 2 ≤ R.natDegree ∧
      (∃ β : Coeff, β ≠ 0 ∧ ∃ S : RecOp, C β * P = oreMul coeffShift S R) ∧
      ∀ {Q : RecOp} {n₁ : ℤ}, (∀ n : ℤ, n₁ ≤ n → opApplyField Q F n = 0) →
        ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T R := by
  obtain ⟨R, hpos, -, ⟨β, hβ, S, hfac⟩, hall⟩ := tws_exists_selected_divisor hU hP hPF hF
  have hne : R.natDegree ≠ 1 := hlin hβ hfac
  exact ⟨R, by omega, ⟨β, hβ, S, hfac⟩, fun hQ ↦ hall _ (hU.sat.zero_tail hQ)⟩

end AJConjecture
