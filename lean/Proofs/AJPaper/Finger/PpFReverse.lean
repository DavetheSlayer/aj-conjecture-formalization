import Mathlib
import AJConjecture.APolynomial
import AJConjecture.ZeroSetDvd

/-!
# Reversal in `L` of irreducible curves (Unit PpF, node `PpF_Reverse`)

Source: Section 8.2 of the paper: "the same meridian inversion on the full boundary eigenvalue
set gives `A_{S^*}(M, L) ≐ A_S(M⁻¹, L)`"; in the library the mirror image inverts the longitude
(`eigenvalueSet_inv`), which is the same up to the simultaneous inversion.

Let `S, S' ⊆ ℂ²` with `L ≠ 0` on `S` and `(M, L⁻¹) ∈ S'` for every `(M, L) ∈ S`. For an
irreducible `h ∈ ℂ[M][L]` not divisible by `L` (`h.coeff 0 ≠ 0`):

* `ppf_reverse_reverse`: `h.reverse.reverse = h` (`Polynomial.coeff_reverse`,
  `Polynomial.reverse_natDegree`, `natTrailingDegree = 0`);
* `ppf_irreducible_reverse`: `h.reverse` is irreducible (`Polynomial.reverse_mul_of_domain`: a
  factorization of `h.reverse` reverses to a factorization of `h`, and a factor of `h.reverse`
  has nonzero constant coefficient, so it is a unit if its reverse is);
* `ppf_zeroSet_reverse_subset`: if the zero set of `h` lies in the Zariski closure of `S`, then
  the zero set of `h.reverse` lies in the Zariski closure of `S'`. Route: if `F` vanishes on
  `S'`, then `F.reverse` vanishes on `S` (`Polynomial.eval₂_reverse_eq_zero_iff`), hence on the
  zero set of `h`, so `h ∣ F.reverse` (`dvd_of_forall_evalPoint_eq_zero`); then `L · F` vanishes
  on the zero set of `h.reverse` (at points with `L ≠ 0` by `eval₂_reverse_eq_zero_iff` again),
  so `h.reverse ∣ L · F`, and `h.reverse ∤ L`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Reversing twice a polynomial with nonzero constant coefficient gives it back. -/
theorem ppf_reverse_reverse {h : ℂ[X][X]} (h0 : h.coeff 0 ≠ 0) : h.reverse.reverse = h := by
  have hdeg : h.reverse.natDegree = h.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h0), Nat.sub_zero]
  rw [reverse, hdeg, reverse, reflect_reflect]

/-- The reverse of a unit is a unit. -/
private theorem isUnit_reverse_ppfReverse {u : ℂ[X][X]} (hu : IsUnit u) : IsUnit u.reverse := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 := congrArg reverse hv
  rw [reverse_mul_of_domain, ← C_1, reverse_C] at h1
  exact IsUnit.of_mul_eq_one _ h1

/-- The value of a product at a point. -/
private theorem evalPoint_mul_ppfReverse (P Q : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (P * Q) p = evalPoint P p * evalPoint Q p := by
  rw [evalPoint, evalPoint, evalPoint, eval₂_mul]

/-- The reverse of `F` vanishes at `(M, L)` exactly when `F` vanishes at `(M, L⁻¹)`, for
`L ≠ 0`. -/
private theorem evalPoint_reverse_eq_zero_iff_ppfReverse (F : ℂ[X][X]) (M L : ℂ) (hL : L ≠ 0) :
    evalPoint F.reverse (M, L) = 0 ↔ evalPoint F (M, L⁻¹) = 0 := by
  have : Invertible L⁻¹ := invertibleOfNonzero (inv_ne_zero hL)
  have hinv : ⅟(L⁻¹) = L := by rw [invOf_eq_inv, inv_inv]
  have h := eval₂_reverse_eq_zero_iff (Polynomial.evalRingHom M) L⁻¹ F
  rwa [hinv] at h

/-- The reverse of an irreducible polynomial with nonzero constant coefficient is
irreducible. -/
theorem ppf_irreducible_reverse {h : ℂ[X][X]} (hh : Irreducible h) (h0 : h.coeff 0 ≠ 0) :
    Irreducible h.reverse := by
  refine ⟨fun hu ↦ hh.not_isUnit ?_, fun a b hab ↦ ?_⟩
  · have h1 := isUnit_reverse_ppfReverse hu
    rwa [ppf_reverse_reverse h0] at h1
  · have hlc : h.reverse.coeff 0 ≠ 0 := by
      rw [coeff_zero_reverse]
      exact leadingCoeff_ne_zero.mpr hh.ne_zero
    rw [hab, mul_coeff_zero] at hlc
    have hrev : h = a.reverse * b.reverse := by
      rw [← reverse_mul_of_domain, ← hab, ppf_reverse_reverse h0]
    rcases hh.isUnit_or_isUnit hrev with hu | hu
    · left
      have h1 := isUnit_reverse_ppfReverse hu
      rwa [ppf_reverse_reverse (left_ne_zero_of_mul hlc)] at h1
    · right
      have h1 := isUnit_reverse_ppfReverse hu
      rwa [ppf_reverse_reverse (right_ne_zero_of_mul hlc)] at h1

/-- The zero set of the reverse of an irreducible curve of the closure of `S` lies in the
closure of the image of `S` under `(M, L) ↦ (M, L⁻¹)`. -/
theorem ppf_zeroSet_reverse_subset {S S' : Set (ℂ × ℂ)}
    (hSS' : ∀ p ∈ S, p.2 ≠ 0 ∧ (p.1, p.2⁻¹) ∈ S') {h : ℂ[X][X]} (hh : Irreducible h)
    (h0 : h.coeff 0 ≠ 0) (hz : ∀ p : ℂ × ℂ, evalPoint h p = 0 → p ∈ zariskiClosure S) :
    ∀ p : ℂ × ℂ, evalPoint h.reverse p = 0 → p ∈ zariskiClosure S' := by
  intro p hp F hF
  have hirr : Irreducible h.reverse := ppf_irreducible_reverse hh h0
  have hFS : ∀ s ∈ S, evalPoint F.reverse s = 0 := fun s hs ↦
    (evalPoint_reverse_eq_zero_iff_ppfReverse F s.1 s.2 (hSS' s hs).1).mpr (hF _ (hSS' s hs).2)
  have hXF : ∀ q : ℂ × ℂ, evalPoint h.reverse q = 0 → evalPoint (X * F) q = 0 := by
    intro q hq
    rw [evalPoint_mul_ppfReverse]
    by_cases hq2 : q.2 = 0
    · rw [evalPoint, eval₂_X, hq2, zero_mul]
    · have h1 : evalPoint h (q.1, q.2⁻¹) = 0 :=
        (evalPoint_reverse_eq_zero_iff_ppfReverse h q.1 q.2 hq2).mp hq
      have h2 : evalPoint F.reverse (q.1, q.2⁻¹) = 0 := hz _ h1 _ hFS
      have h3 := (evalPoint_reverse_eq_zero_iff_ppfReverse F q.1 q.2⁻¹ (inv_ne_zero hq2)).mp h2
      rw [inv_inv] at h3
      rw [h3, mul_zero]
  have hdvd : h.reverse ∣ X * F := dvd_of_forall_evalPoint_eq_zero hirr hXF
  have hnX : ¬ h.reverse ∣ X := by
    intro hX
    have hXh : (X : ℂ[X][X]) ∣ h.reverse := hirr.dvd_symm Polynomial.irreducible_X hX
    have hc := X_dvd_iff.mp hXh
    rw [coeff_zero_reverse] at hc
    exact leadingCoeff_ne_zero.mpr hh.ne_zero hc
  obtain ⟨g, hg⟩ := (hirr.prime.dvd_or_dvd hdvd).resolve_left hnX
  rw [hg, evalPoint_mul_ppfReverse, hp, zero_mul]

end AJConjecture
