import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.QAlgPseudoFactorNormalize
import AJConjecture.QAlgSpecializeOreMul
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgTwistFactorPrime
import AJConjecture.QAlgToComparisonUnit

/-!
# Three linked prime blocks force irreducibility (TwF, generic assembly)

Source: revision 5, Section 4 (`residues.tex`), Theorem "Crossing criterion", last paragraph:
"Take the residual blocks as vertices and join two when a crossing satisfies these hypotheses and
has nonintegral index. Each right factor selects a union of graph components. In particular a
connected graph forces irreducibility"; Section 5.1: "The monic Gauss argument … forces any proper
factorization to partition the residual blocks, preserving shift degrees and both endpoints".

`natDegree_eq_zero_or_of_linked_blocks`: let the symbol of `P` be `G₁ G₂ G₃` up to nonzero
polynomials in `M`, of full degree, with `G₁, G₂, G₃` pairwise non-associated primes of the
comparison ring with nonzero constant coefficients. If no right pseudo-factor of `P` separates
`G₁` from `G₂`, nor `G₂` from `G₃`, then every right pseudo-factor of `P` has degree `0` or the
order of `P`.

Route: the proof of `natDegree_eq_zero_or_of_oreMul_eq_famTransferOp`
(`AJFamily/Quantum/FamTransferOpIrreducible.lean`), with `(L - 1, E, B_m)` replaced by
`(G₁, G₂, G₃)`: `exists_normalized_pseudoFactor`, `specialize_oreMul`, `natDegree_oreMul`,
the degree bound for divisibility in the comparison ring (`dvd_of_toLaurent_dvd`), primality.
Where that proof separates the blocks by their degrees, use `h12`, `h13`, `h23`.

Two small general facts used by the assemblies of this package are stated here:
`natDegree_le_of_toComparison_dvd` (the private `natDegree_le_of_toComparison_dvd_famIrred` of that
file) and `eval_one_eq_zero_of_toComparison_X_sub_one_dvd` (`dvd_of_toLaurent_dvd` for `L - 1`,
then evaluation at `L = 1` and injectivity of `ℤ[M] → ℚ(M)`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Divisibility in the comparison ring by the image of a polynomial with nonzero constant
coefficient bounds the degree in `L`. -/
theorem natDegree_le_of_toComparison_dvd {d g : ℤ[X][X]} (hd : d.coeff 0 ≠ 0) (hg : g ≠ 0)
    (h : toComparison d ∣ toComparison g) : d.natDegree ≤ g.natDegree := by
  have hdvd : d.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) ∣ g.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) := by
    refine dvd_of_toLaurent_dvd ?_ h
    rw [coeff_map]
    exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr hd
  have hle := natDegree_le_of_dvd hdvd
    ((Polynomial.map_ne_zero_iff intPolyToRatFunc_injective).mpr hg)
  rwa [natDegree_map_eq_of_injective intPolyToRatFunc_injective,
    natDegree_map_eq_of_injective intPolyToRatFunc_injective] at hle

/-- If `L - 1` divides the image of `g` in the comparison ring, then `g(M, 1) = 0`. -/
theorem eval_one_eq_zero_of_toComparison_X_sub_one_dvd {g : ℤ[X][X]}
    (h : toComparison (X - 1) ∣ toComparison g) : g.eval 1 = 0 := by
  have hdvd : (X - 1 : ℤ[X][X]).map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) ∣ g.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) := by
    refine dvd_of_toLaurent_dvd ?_ h
    simp
  obtain ⟨r, hr⟩ := hdvd
  have hev := congrArg (Polynomial.eval 1) hr
  rw [eval_one_map, eval_mul, eval_one_map] at hev
  simp only [eval_sub, eval_X, eval_one, sub_self, map_zero, zero_mul] at hev
  exact (map_eq_zero_iff _ intPolyToRatFunc_injective).mp hev

/-- A nonzero polynomial whose image in the comparison ring is divisible by three pairwise
non-associated primes with nonzero constant coefficients has at least the degree of their
product. -/
private theorem natDegree_mul_mul_le_of_dvd_twfBlockCount {G₁ G₂ G₃ g : ℤ[X][X]}
    (hp₁ : Prime (toComparison G₁)) (hp₂ : Prime (toComparison G₂))
    (hp₃ : Prime (toComparison G₃))
    (hc₁ : G₁.coeff 0 ≠ 0) (hc₂ : G₂.coeff 0 ≠ 0) (hc₃ : G₃.coeff 0 ≠ 0)
    (h12 : ¬ toComparison G₁ ∣ toComparison G₂) (h13 : ¬ toComparison G₁ ∣ toComparison G₃)
    (h23 : ¬ toComparison G₂ ∣ toComparison G₃) (hg : g ≠ 0)
    (h1 : toComparison G₁ ∣ toComparison g) (h2 : toComparison G₂ ∣ toComparison g)
    (h3 : toComparison G₃ ∣ toComparison g) : (G₁ * G₂ * G₃).natDegree ≤ g.natDegree := by
  obtain ⟨q₁, hq₁⟩ := h1
  have h2' : toComparison G₂ ∣ q₁ := by
    rw [hq₁] at h2
    exact (hp₂.dvd_or_dvd h2).resolve_left
      fun hdvd ↦ h12 ((hp₂.dvd_prime_iff_associated hp₁).mp hdvd).dvd'
  obtain ⟨q₂, rfl⟩ := h2'
  have h3' : toComparison G₃ ∣ q₂ := by
    rw [hq₁] at h3
    rcases hp₃.dvd_or_dvd h3 with hdvd | hdvd
    · exact absurd ((hp₃.dvd_prime_iff_associated hp₁).mp hdvd).dvd' h13
    · exact (hp₃.dvd_or_dvd hdvd).resolve_left
        fun hdvd' ↦ h23 ((hp₃.dvd_prime_iff_associated hp₂).mp hdvd').dvd'
  obtain ⟨q₃, rfl⟩ := h3'
  have hall : toComparison (G₁ * G₂ * G₃) ∣ toComparison g := by
    rw [hq₁, map_mul, map_mul]
    exact ⟨q₃, by ring⟩
  have hc : (G₁ * G₂ * G₃).coeff 0 ≠ 0 := by
    rw [mul_coeff_zero, mul_coeff_zero]
    exact mul_ne_zero (mul_ne_zero hc₁ hc₂) hc₃
  exact natDegree_le_of_toComparison_dvd hc hg hall

/-- Three pairwise non-associated prime blocks linked in a path: every right pseudo-factor has
degree `0` or the order of the operator. -/
theorem natDegree_eq_zero_or_of_linked_blocks {P : RecOp} {G₁ G₂ G₃ : ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (hsym : C κ₁ * specialize P = C κ₂ * (G₁ * G₂ * G₃))
    (hdeg : (specialize P).natDegree = P.natDegree)
    (hp₁ : Prime (toComparison G₁)) (hp₂ : Prime (toComparison G₂))
    (hp₃ : Prime (toComparison G₃))
    (hc₁ : G₁.coeff 0 ≠ 0) (hc₂ : G₂.coeff 0 ≠ 0) (hc₃ : G₃.coeff 0 ≠ 0)
    (h12 : ¬ toComparison G₁ ∣ toComparison G₂) (h13 : ¬ toComparison G₁ ∣ toComparison G₃)
    (h23 : ¬ toComparison G₂ ∣ toComparison G₃)
    (hlink12 : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      (toComparison G₁ ∣ toComparison (specialize R) ↔
        toComparison G₂ ∣ toComparison (specialize R)))
    (hlink23 : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      (toComparison G₂ ∣ toComparison (specialize R) ↔
        toComparison G₃ ∣ toComparison (specialize R)))
    {β : Coeff} (hβ : β ≠ 0) {S R : RecOp} (h : C β * P = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = P.natDegree := by
  have hG : G₁ * G₂ * G₃ ≠ 0 := fun h0 ↦ by
    have hc := congrArg (fun p : ℤ[X][X] ↦ p.coeff 0) h0
    simp only [mul_coeff_zero, coeff_zero, mul_eq_zero] at hc
    tauto
  have hP : specialize P ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hsym
    exact mul_ne_zero (C_ne_zero.mpr hκ₂) hG hsym.symm
  have hdegG : (G₁ * G₂ * G₃).natDegree = P.natDegree := by
    rw [← hdeg, ← natDegree_C_mul hκ₂ (p := G₁ * G₂ * G₃), ← hsym, natDegree_C_mul hκ₁]
  obtain ⟨β', S', R', hβ', hS', hR', -, hRdeg, h', -⟩ := exists_normalized_pseudoFactor hP hβ h
  have hβ'0 : β' ≠ 0 := fun h0 ↦ hβ' (by rw [h0, Polynomial.map_zero])
  have hS'0 : S' ≠ 0 := fun h0 ↦ hS' (by rw [h0, map_zero])
  have hR'0 : R' ≠ 0 := fun h0 ↦ hR' (by rw [h0, map_zero])
  have hsp : C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize P =
      specialize S' * specialize R' := by
    have hC : specialize (C β') = C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) :=
      Polynomial.map_C _
    rw [← specialize_oreMul, ← h', map_mul, hC]
  have hdegOre : S'.natDegree + R'.natDegree = P.natDegree := by
    rw [← natDegree_oreMul coeffShift_injective hS'0 hR'0, ← h', natDegree_C_mul hβ'0]
  have hdeg₀ : (specialize S').natDegree + (specialize R').natDegree = P.natDegree := by
    rw [← natDegree_mul hS' hR', ← hsp, natDegree_C_mul hβ', hdeg]
  have hSle : (specialize S').natDegree ≤ S'.natDegree := natDegree_map_le
  have hRle : (specialize R').natDegree ≤ R'.natDegree := natDegree_map_le
  have hprod : ∀ {p : ℤ[X][X]}, p ∣ G₁ * G₂ * G₃ →
      toComparison p ∣ toComparison (specialize S') * toComparison (specialize R') := by
    intro p hp
    have hu : toComparison (C κ₁) * toComparison (specialize P) =
        toComparison (C κ₂) * toComparison (G₁ * G₂ * G₃) := by
      rw [← map_mul, ← map_mul, hsym]
    have hdvdP : toComparison p ∣ toComparison (specialize P) := by
      rw [← (isUnit_toComparison_coeff_of_ne_zero hκ₁).dvd_mul_left, hu]
      exact (map_dvd toComparison hp).mul_left _
    rw [← map_mul, ← hsp, map_mul]
    exact hdvdP.mul_left _
  have hl12 := hlink12 hβ'0 h'
  have hl23 := hlink23 hβ'0 h'
  by_cases h3 : toComparison G₃ ∣ toComparison (specialize R')
  · right
    have hle := natDegree_mul_mul_le_of_dvd_twfBlockCount hp₁ hp₂ hp₃ hc₁ hc₂ hc₃ h12 h13 h23 hR'
      (hl12.mpr (hl23.mpr h3)) (hl23.mpr h3) h3
    omega
  · left
    have hS1 := (hp₁.dvd_or_dvd (hprod ⟨G₂ * G₃, by ring⟩)).resolve_right
      fun hdvd ↦ h3 (hl23.mp (hl12.mp hdvd))
    have hS2 := (hp₂.dvd_or_dvd (hprod ⟨G₁ * G₃, by ring⟩)).resolve_right
      fun hdvd ↦ h3 (hl23.mp hdvd)
    have hS3 := (hp₃.dvd_or_dvd (hprod ⟨G₁ * G₂, by ring⟩)).resolve_right h3
    have hle := natDegree_mul_mul_le_of_dvd_twfBlockCount hp₁ hp₂ hp₃ hc₁ hc₂ hc₃ h12 h13 h23 hS'
      hS1 hS2 hS3
    omega

end AJConjecture
