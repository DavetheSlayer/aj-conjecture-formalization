import Mathlib
import AJConjecture.QAlgGaugeOpApply
import AJConjecture.QAlgGaugeOpSpecialize
import AJConjecture.QAlgSpecializeDvdOfOreMul
import AJHandoff.LocalTheory.LocTheoremSRecOp

/-!
# I-SEQ, §§4–5: every factor of the special symbol survives in every primitive saturated row

Let `P` be an irreducible recurrence operator of positive order with nonzero special symbol
`P(-1, M, L)`, `F` a sequence that is not eventually rational with `P F` eventually rational, and
`J(n) = [n] F(n)` on positive colours (the unreduced quantum-dimension gauge). If `Q` is primitive
and some nonzero coefficient multiple `c Q` annihilates a tail of `J`, then `P(-1, M, L)` divides
`Q(-1, M, L)` in `ℚ(M)[L, L⁻¹]`.

Proof: the gauge `gaugeOp Q` annihilates a tail of `F` (`opApplyField_gaugeOp`; the coefficient
`c` is cancelled only on a tail, after its exceptional colours), Theorem S
(`exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational`) gives `β gaugeOp Q = T ⋆ P`, the
multiplicativity of the Gauss valuation at `t + 1` gives `P₀ ∣ (gaugeOp Q)₀`
(`toComparison_specialize_dvd_of_oreMul`), and `(gaugeOp Q)₀ = (M² - 1) Q₀` with `Q₀ ≠ 0` for
primitive `Q`. This generalizes the family's `extraFactor_dvd_specialize_of_annihilates_...`
from `E` to the whole special symbol of `P`, for any `P` and `F`, with zero forcing allowed.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The action at `n` depends only on the values of the sequence at the colours `m ≥ n`. -/
private theorem opApplyField_congr_of_ge (Q : RecOp) {g h : ℤ → RatFunc ℚ} {n : ℤ}
    (hgh : ∀ m : ℤ, n ≤ m → g m = h m) : opApplyField Q g n = opApplyField Q h n := by
  unfold opApplyField
  rw [Polynomial.sum_def, Polynomial.sum_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hgh (n + i) (le_add_of_nonneg_right (Int.natCast_nonneg i))]

/-- If a nonzero multiple `c Q` annihilates a tail of `J = [n] F`, the gauge of `Q` annihilates a
tail of `F`. -/
private theorem exists_tail_annihilator_gaugeOp_of_quantumInt_mul {F J : ℤ → RatFunc ℚ}
    (hJ : ∀ n : ℤ, 1 ≤ n → J n = quantumInt n * F n) {Q : RecOp}
    (hann : ∃ c : Coeff, c ≠ 0 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → opApplyField (C c * Q) J n = 0) :
    ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField (gaugeOp Q) F n = 0 := by
  obtain ⟨c, hc, n₀, hn₀⟩ := hann
  obtain ⟨n₂, hn₂⟩ := exists_forall_ge_evalAtField_ne_zero hc
  refine ⟨max (max n₀ n₂) 1, fun n hn ↦ ?_⟩
  have h := hn₀ n ((le_max_left _ _).trans ((le_max_left _ _).trans hn))
  rw [opApplyField_C_mul_left] at h
  have hQJ := (mul_eq_zero.mp h).resolve_left
    (hn₂ n ((le_max_right _ _).trans ((le_max_left _ _).trans hn)))
  rw [opApplyField_congr_of_ge Q fun m hm ↦ hJ m ((le_max_right _ _).trans (hn.trans hm))] at hQJ
  rw [opApplyField_gaugeOp, hQJ, mul_zero]

theorem toComparison_specialize_dvd_of_tail_annihilator_gauge {P : RecOp} (hP : 0 < P.natDegree)
    (hP0 : specialize P ≠ 0)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    {F : ℤ → RatFunc ℚ} (hnr : ¬ EventuallyRational F)
    (hrat : EventuallyRational fun n ↦ opApplyField P F n) {J : ℤ → RatFunc ℚ}
    (hJ : ∀ n : ℤ, 1 ≤ n → J n = quantumInt n * F n) {Q : RecOp} (hQ : Q.IsPrimitive)
    (hann : ∃ c : Coeff, c ≠ 0 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → opApplyField (C c * Q) J n = 0) :
    toComparison (specialize P) ∣ toComparison (specialize Q) := by
  obtain ⟨n₁, hn₁⟩ := exists_tail_annihilator_gaugeOp_of_quantumInt_mul hJ hann
  obtain ⟨β, hβ, T, hT⟩ :=
    exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational hP hirr hnr hrat hn₁
  have hX : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval 0) h0
    norm_num at h1
  have hspec : specialize (gaugeOp Q) ≠ 0 := by
    rw [specialize_gaugeOp]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hX) (specialize_ne_zero_of_isPrimitive hQ)
  have h := toComparison_specialize_dvd_of_oreMul hβ hT hspec hP0
  rw [specialize_gaugeOp, map_mul] at h
  exact (isUnit_toComparison_coeff_of_ne_zero hX).dvd_mul_left.mp h

end AJConjecture
