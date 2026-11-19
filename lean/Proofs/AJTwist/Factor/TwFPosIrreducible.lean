import Mathlib
import AJFamily.Quantum.FamTransferOpIrreducible
import AJTwist.Quantum.TwQTransferOp

/-!
# `P_a` has no proper right factor for `a ≥ 2` (TwF, unit F1)

Source: revision 5, Section 5.3 (`operators.tex`, "Positive effective index"): for `a ≥ 2` the two
simple crossings `(L - 1)/B_a` and `E/B_a`, both with indices `(-1/2, -1/2)`, connect the three
blocks, so `P_a` is irreducible over `ℚ(t, M)`.

For `a = m ≥ 1` the operator `twTransferOp a` is the library's `famTransferOp m`
(`twTransferOp_natCast`), and for `m ≥ 2` the statement is the library's
`natDegree_eq_zero_or_of_oreMul_eq_famTransferOp`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- For `a ≥ 2`, in every pseudo-factorisation `β · P_a = S ⋆ R` the right factor has degree `0`
or the order of `P_a`. -/
theorem natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_of_two_le (a : ℤ) (ha : 2 ≤ a)
    {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp a = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = (twTransferOp a).natDegree := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ a)
  have hm : 2 ≤ m := by exact_mod_cast ha
  rw [twTransferOp_natCast m (by omega)] at h ⊢
  rw [natDegree_famTransferOp m (by omega)]
  exact natDegree_eq_zero_or_of_oreMul_eq_famTransferOp m hm hβ h

end AJConjecture
