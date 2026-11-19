import Mathlib
import AJTwist.Quantum.TwQSymbolFacts
import AJTwist.Factor.TwFPosIrreducible
import AJTwist.Factor.TwFNegIrreducible
import AJTwist.Factor.TwFOneIrreducible
import AJTwist.Factor.TwFZeroNoLinear

/-!
# Rational factors of the satellite operators `P_a` (package TwF, final statements)

Source: revision 5, Section 5 (`operators.tex`), first paragraph: "We prove irreducibility over
`ℚ(t, M)` for `a ≠ 0` and exclude first-order right divisors at `a = 0`."

In the library's language (pseudo-factorisations `β P = S ⋆ R` over `ℤ[t][M]`, which are the
factorisations over `ℚ(t, M)`: `oreIrreducible_map_iff` in
`AJHandoff/LocalTheory/LocPseudoField.lean`), for `P_a = twTransferOp a`:

* `twf_irreducible`: for `a ≠ 0`, every right pseudo-factor has degree `0` or the order of `P_a`
  (`a ≥ 2`: the library's theorem; `a = 1`: the simple crossing `E/B_1` and the two rank-one
  tests at `K = 3`; `a < 0`: the two simple crossings `(L - 1)/C_b`, `E/C_b`);
* `twf_no_linear`: for `a = 0`, no right pseudo-factor has degree one.

These are exactly the hypotheses `hirr` and `hlin` of the selection package
(`AJTwist/Select/TwSRelativeForcing.lean`: `tws_exists_C_mul_eq_oreMul_of_relative`,
`tws_exists_selected_divisor_of_no_linear`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- For `a ≠ 0` the operator `P_a` is irreducible over `ℚ(t, M)`: in every pseudo-factorisation
`β · P_a = S ⋆ R` the right factor has degree `0` or the order of `P_a`. -/
theorem twf_irreducible (a : ℤ) (ha : a ≠ 0) {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp a = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = (twTransferOp a).natDegree := by
  rcases lt_trichotomy a 0 with hneg | h0 | hpos
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = -(b : ℤ) := ⟨(-a).toNat, by omega⟩
    have hb : 1 ≤ b := by omega
    rw [natDegree_twTransferOp, twWindow_neg_natCast b hb]
    exact natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_neg b hb hβ h
  · exact absurd h0 ha
  · rcases eq_or_lt_of_le (show (1 : ℤ) ≤ a by omega) with h1 | h2
    · subst h1
      exact natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_one hβ h
    · exact natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_of_two_le a (by omega) hβ h

/-- For `a = 0` the operator `P_0` has no right pseudo-factor of degree one. -/
theorem twf_no_linear {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp 0 = oreMul coeffShift S R) : R.natDegree ≠ 1 :=
  natDegree_ne_one_of_oreMul_eq_twTransferOp_zero hβ h

end AJConjecture
