import Mathlib
import AJFamily.Classical.FamilyPolynomials
import AJHandoff.TorusKnot.PairKBmIdentity
import AJTwist.Quantum.TwQTwistPolyNeg

/-!
# The classical bound polynomials of the four families

Source: revision 5, Section 7.2 (`classical.tex`, eq. (classicalcontainment)). For a signed
filling index `k` the paper puts `𝒫_k = B_k` for `k > 0`, `𝒫_0 = 1` and `𝒫_k = C_(-k)` for
`k < 0`; every generic boundary eigenvalue pair of the negative-clasp satellite
`W_(-,ℓ)(T_η)` lies on `(L - 1) 𝒫_(-ℓ) 𝒫_a = 0`, `a = η r s - ℓ`.

* `twP k` is `𝒫_k` in `ℤ[M][L]` (`x = M²`): the library's `twistPoly k = B_k` for `k ≥ 0`
  (`twistPoly 0 = 1`) and `twistPolyNeg (-k) = C_(-k)` of `AJTwist.Quantum.TwQTwistPolyNeg`
  for `k < 0`.
* `twBound k₁ k₂ = (L - 1) 𝒫_(k₁) 𝒫_(k₂)`. The bound of the paper is `twBound (-ℓ) a`; at
  `ℓ = 0`, `η = +1` it is the library's `famBound (r s)` (`twBound_zero_natCast`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The filling polynomial `𝒫_k`: `B_k` for `k ≥ 1`, `1` for `k = 0`, `C_(-k)` for `k < 0`. -/
def twP (k : ℤ) : ℤ[X][X] :=
  if 0 ≤ k then twistPoly k.toNat else twistPolyNeg (-k).toNat

/-- The classical bound `(L - 1) 𝒫_(k₁) 𝒫_(k₂)` for the two filling indices `k₁`, `k₂`. -/
def twBound (k₁ k₂ : ℤ) : ℤ[X][X] :=
  (X - 1) * twP k₁ * twP k₂

theorem twP_zero : twP 0 = 1 := by
  simp [twP, twistPoly]

theorem twP_natCast (m : ℕ) : twP (m : ℤ) = twistPoly m := by
  simp [twP]

theorem twP_neg_natCast (b : ℕ) (hb : 1 ≤ b) : twP (-(b : ℤ)) = twistPolyNeg b := by
  have h : ¬ (0 : ℤ) ≤ -(b : ℤ) := by omega
  rw [twP, ite_eq_right h, neg_neg, Int.toNat_natCast]

/-- At `ℓ = 0` over the right-handed companion the bound is the library's `(L - 1) B_m`. -/
theorem twBound_zero_natCast (m : ℕ) (hm : 1 ≤ m) : twBound 0 (m : ℤ) = famBound m := by
  rw [twBound, twP_zero, twP_natCast, mul_one, famBound, famB_eq_twistPoly m hm]

end AJConjecture
