import Mathlib
import AJConjecture.QAlgDualJet

/-!
# Numerals and `q` in the dual numbers

`1 - dualQ = 4ε` squares to zero, and the components of a numeral of `ℂ[ε]` are the numeral and
`0` (`simp` lemmas for componentwise computations in the dual numbers; Mathlib has them for
natural-number casts only).
-/

namespace AJConjecture

/-- `(1 - q)² = 0` for `q = 1 - 4ε`. -/
theorem one_sub_dualQ_sq : (1 - dualQ) ^ 2 = 0 := by
  rw [dualQ, sub_sub_cancel, mul_pow, sq DualNumber.eps, DualNumber.eps_mul_eps, mul_zero]

/-- The first component of a numeral of the dual numbers. -/
theorem fst_ofNat_dual (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : DualNumber ℂ).fst = ofNat(n) := rfl

/-- The second component of a numeral of the dual numbers. -/
theorem snd_ofNat_dual (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : DualNumber ℂ).snd = 0 := rfl

end AJConjecture
