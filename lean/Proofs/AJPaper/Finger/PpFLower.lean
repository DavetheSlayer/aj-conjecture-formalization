import Mathlib
import AJTwist.Main.TwMTheorem
import AJPaper.Finger.PpFExists

/-!
# The factor of Theorem 1.1 divides every extra support (Unit PpF, node `PpF_Lower`)

Source: Section 9 of the paper, proof of Corollary 9.2: "Theorem 1.1 supplies `E` as a divisor
of every `Δ_{W_{-,ℓ}(C)}` in the testing family."

* `ppf_mem_testSet_iff`: the tested satellites are the knots `twFamilyKnot r s h σ η ℓ` of the
  library (`eq_twFamilyKnot_of_word`).
* `ppf_factor_dvd_of_clauses`: for a knot satisfying `TwFamilyClauses K G P` with `G` prime in
  `R`, `G` divides `Δ_K`: `G ∣ f_K` (clause 3 for the recurrence polynomial), `G ∤ A_K`
  (clause 5 and primality), then `isExtraSupport_prime_dvd`.
* `ppf_twFamilyFactor_dvd`: for every tested satellite of `W_ε`, the factor `E` (negative
  clasp), respectively `E^∨`, divides `Δ`.
* `ppf_exists_isExtraSupportOf`: every tested satellite has an extra support: the testing
  family lies in the domain of Definition 9.1.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The tested satellites are the knots of the four families. -/
theorem ppf_mem_testSet_iff (σ : Bool) (K : BraidKnot) :
    K ∈ ppfTestSet σ ↔
      ∃ (r s : ℕ) (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ), K = twFamilyKnot r s h σ η ℓ := by
  constructor
  · rintro ⟨r, s, h, η, ℓ, hs, hw⟩
    exact ⟨r, s, h, η, ℓ, eq_twFamilyKnot_of_word h σ η ℓ hs hw⟩
  · rintro ⟨r, s, h, η, ℓ, rfl⟩
    exact ⟨r, s, h, η, ℓ, strands_twFamilyKnot r s h σ η ℓ, word_twFamilyKnot r s h σ η ℓ⟩

/-- A prime obstruction factor of Theorem 1.1 divides the extra support. -/
theorem ppf_factor_dvd_of_clauses {K : BraidKnot} {G P : ℤ[X][X]}
    (hG : Prime (toComparison G)) (hK : TwFamilyClauses K G P) {Δ : ComparisonRing}
    (hΔ : IsExtraSupportOf K Δ) : toComparison G ∣ Δ := by
  obtain ⟨α, A, hα, hA, h⟩ := hΔ
  refine isExtraSupport_prime_dvd hG (hK.2.2.1 α hα.1 hα.2.2.2 hα.2.1).2 (fun hd ↦ ?_) h
  exact hG.not_isUnit ((hK.2.2.2.2.1 A hA).2.isUnit_of_dvd' dvd_rfl hd)

/-- For every tested satellite of the Whitehead pattern of clasp sign `σ`, the factor of
Theorem 1.1 divides the extra support. -/
theorem ppf_twFamilyFactor_dvd {σ : Bool} {K : BraidKnot} (hK : K ∈ ppfTestSet σ)
    {Δ : ComparisonRing} (hΔ : IsExtraSupportOf K Δ) : toComparison (twFamilyFactor σ) ∣ Δ := by
  obtain ⟨r, s, h, η, ℓ, rfl⟩ := (ppf_mem_testSet_iff σ K).mp hK
  have hc := twFamilyClauses_twFamilyKnot h σ η ℓ
  cases σ
  · exact ppf_factor_dvd_of_clauses prime_toComparison_extraFactorMirror hc hΔ
  · exact ppf_factor_dvd_of_clauses prime_toComparison_extraFactor hc hΔ

/-- Every tested satellite has an extra support. -/
theorem ppf_exists_isExtraSupportOf {σ : Bool} {K : BraidKnot} (hK : K ∈ ppfTestSet σ) :
    ∃ Δ : ComparisonRing, IsExtraSupportOf K Δ := by
  obtain ⟨r, s, h, η, ℓ, rfl⟩ := (ppf_mem_testSet_iff σ K).mp hK
  have hc := twFamilyClauses_twFamilyKnot h σ η ℓ
  exact exists_isExtraSupportOf hc.2.1 hc.2.2.2.1

end AJConjecture
