import Mathlib
import AJTwist.Quantum.TwQInput
import AJTwist.Quantum.TwQBarBasic

/-!
# The input of the mirror companion and the bar involution (Unit Q1)

Source: revision 5, Section 3, after eq. (commoninput): "For `η = -1` the companion input is
obtained by inverting `q` in the torus formula. Quantum dimensions are invariant under that
inversion."

* `twInput_false`: `v_n = q^(ℓ n(n+1)) \bar{u_n}` with `u = pairQOddColor r s`.
* `twInput_false_eq_bar`: the input of the mirror companion with twist `ℓ` is the bar of the
  input of the right-handed companion with twist `-ℓ` (the mirror of the whole satellite reverses
  the twist, Section 8.2).
-/

noncomputable section

namespace AJConjecture

/-- For the mirror companion the input is `q^(ℓ n(n+1))` times the bar of the odd colours of
`T(r, s)`. -/
theorem twInput_false (r s : ℕ) (ℓ : ℤ) (n : ℕ) :
    twInput false r s ℓ n = qParam ^ (ℓ * n * ((n : ℤ) + 1)) * twQBar (pairQOddColor r s n) := by
  rw [twInput, pairQOddColor, map_mul, twQBar_qParam_zpow, ← mul_assoc,
    ← zpow_add₀ qParam_ne_zero, twIndex, map_sum]
  congr 1
  · congr 1
    push_cast
    ring
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, twQBar_qParam_zpow, twQBar_quantumInt]
    simp only [Bool.false_eq_true, ite_false, neg_mul, one_mul]

/-- The input of the mirror companion with twist `ℓ` is the bar of the input of the right-handed
companion with twist `-ℓ`. -/
theorem twInput_false_eq_bar (r s : ℕ) (ℓ : ℤ) (n : ℕ) :
    twInput false r s ℓ n = twQBar (twInput true r s (-ℓ) n) := by
  rw [twInput_false, twInput_true, map_mul, twQBar_qParam_zpow]
  congr 2
  ring

end AJConjecture
