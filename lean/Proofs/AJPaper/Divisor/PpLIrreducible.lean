import Mathlib
import AJTwist.Factor.TwFMain
import AJPaper.Divisor.PpLNoQuadratic

/-!
# `P_a` is irreducible for every integer `a` (Unit PpL, node `PpL_Irreducible`)

Source: Section 5 of the paper (`operators.tex`), first paragraph: "We prove irreducibility
over `ℚ(t, M)` for `a ≠ 0` and exclude first-order right divisors at `a = 0`." The second half
is completed here: `P_0` has no right factor of order two either (`ppl_no_quadratic`), so the
operator of order three is irreducible. This is stronger than what the paper states: Sections
5.6 and 6.7 leave the degree of the divisor selected at `a = 0` open ("the degree of `R_0` is
two or three").

* `ppl_irreducible_zero`: every right pseudo-factor of `P_0 = twTransferOp 0` has degree `0` or
  `3` (`twf_no_linear`, `ppl_no_quadratic`).
* `ppl_irreducible`: for every integer `a`, every right pseudo-factor of `P_a` has degree `0`
  or the order of `P_a` (`twf_irreducible` for `a ≠ 0`).

This is the hypothesis `hirr` of the selection package (`tws_tail_annihilator_of_selects`,
`tws_exists_C_mul_eq_oreMul_of_relative`), now without the condition `a ≠ 0`.

This file is proved from `ppl_no_quadratic`; it has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **`P_0` is irreducible over `ℚ(t, M)`**: in every pseudo-factorisation `β · P_0 = S ⋆ R`
the right factor has degree `0` or the order `3` of `P_0`. -/
theorem ppl_irreducible_zero {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp 0 = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = (twTransferOp 0).natDegree := by
  have hP0 := twTransferOp_ne_zero 0
  have hne : oreMul coeffShift S R ≠ 0 := h ▸ mul_ne_zero (C_ne_zero.mpr hβ) hP0
  have hS0 : S ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_left _ _)
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_right _ _)
  have hd := congrArg natDegree h
  rw [natDegree_C_mul hβ, natDegree_twTransferOp, twWindow_zero,
    natDegree_oreMul coeffShift_injective hS0 hR0] at hd
  rw [natDegree_twTransferOp, twWindow_zero]
  have h1 := twf_no_linear hβ h
  have h2 := ppl_no_quadratic hβ h
  omega

/-- **`P_a` is irreducible over `ℚ(t, M)` for every integer `a`**: in every
pseudo-factorisation `β · P_a = S ⋆ R` the right factor has degree `0` or the order of `P_a`. -/
theorem ppl_irreducible (a : ℤ) {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp a = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = (twTransferOp a).natDegree := by
  by_cases ha : a = 0
  · subst ha
    exact ppl_irreducible_zero hβ h
  · exact twf_irreducible a ha hβ h

end AJConjecture
