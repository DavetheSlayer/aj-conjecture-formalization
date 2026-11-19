import Mathlib
import AJConjecture.FieldActionBridge

/-!
# The bar involution `t ↦ t⁻¹` of `ℚ(t)`

Source: *Whitehead doubles and the failure of the square-free AJ conjecture*, revision 5,
Section 3 (`transfer.tex`), eq. (commoninput): the input of the mirror companion `T(r, -s)` is
obtained from that of `T(r, s)` by inverting `q`. In the library's variable `t` (`q = t⁴`) this
is the field automorphism `twQBar` of `ℚ(t)` with `t ↦ t⁻¹`.

`twQBar` is the lift to `ℚ(t)` of the substitution `t ↦ t⁻¹` on `ℚ[t]`; it inverts the powers
of `t` and is an involution. Its values on `q`, on the quantum integers and on Laurent polynomials
are in `AJTwist.Quantum.TwQBarBasic`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- Evaluation at `X⁻¹` does not kill nonzero polynomials, over any field. -/
private theorem eval₂_inv_X_nonZeroDivisors_le_twQBarFile (K : Type*) [Field K] :
    nonZeroDivisors K[X] ≤ Submonoid.comap
      (Polynomial.eval₂RingHom (RatFunc.C : K →+* RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
      (nonZeroDivisors (RatFunc K)) := by
  intro p hp
  have htr : Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := fun h ↦
    RatFunc.transcendental_X (K := K) (by simpa using h.inv)
  have hinj := transcendental_iff_injective.mp htr
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h0
  refine nonZeroDivisors.ne_zero hp (hinj ?_)
  rw [map_zero, Polynomial.aeval_def, RatFunc.algebraMap_eq_C]
  exact h0

/-- The substitution `t ↦ t⁻¹` on polynomials sends nonzero polynomials to nonzero elements of
`ℚ(t)` (`t⁻¹` is transcendental). -/
theorem twQBar_nonZeroDivisors_le :
    nonZeroDivisors ℚ[X] ≤ (nonZeroDivisors (RatFunc ℚ)).comap
      (Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X : RatFunc ℚ)⁻¹) := by
  have hC : algebraMap ℚ (RatFunc ℚ) = (RatFunc.C : ℚ →+* RatFunc ℚ) := Subsingleton.elim _ _
  rw [hC]
  exact eval₂_inv_X_nonZeroDivisors_le_twQBarFile ℚ

/-- The bar involution of `ℚ(t)`: the field automorphism with `t ↦ t⁻¹`. -/
def twQBar : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom
    (Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X : RatFunc ℚ)⁻¹)
    twQBar_nonZeroDivisors_le

/-- The bar involution on the image of a polynomial is the substitution `t ↦ t⁻¹`. -/
private theorem twQBar_algebraMap_twQBarFile (p : ℚ[X]) :
    twQBar (algebraMap ℚ[X] (RatFunc ℚ) p) =
      Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X : RatFunc ℚ)⁻¹ p := by
  rw [twQBar, RatFunc.liftRingHom_algebraMap]
  rfl

theorem twQBar_X : twQBar RatFunc.X = (RatFunc.X : RatFunc ℚ)⁻¹ := by
  have h := twQBar_algebraMap_twQBarFile Polynomial.X
  rwa [RatFunc.algebraMap_X, Polynomial.eval₂_X] at h

theorem twQBar_X_zpow (k : ℤ) :
    twQBar ((RatFunc.X : RatFunc ℚ) ^ k) = (RatFunc.X : RatFunc ℚ) ^ (-k) := by
  rw [map_zpow₀, twQBar_X, inv_zpow, zpow_neg]

/-- The bar involution is an involution. -/
theorem twQBar_twQBar (f : RatFunc ℚ) : twQBar (twQBar f) = f := by
  have hcomp : (twQBar.comp twQBar).comp (algebraMap ℚ[X] (RatFunc ℚ)) =
      algebraMap ℚ[X] (RatFunc ℚ) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · have hC : algebraMap ℚ (RatFunc ℚ) a = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C a) := by
        rw [RatFunc.algebraMap_C]
        exact DFunLike.congr_fun (Subsingleton.elim _ _) a
      simp only [RingHom.comp_apply, twQBar_algebraMap_twQBarFile, Polynomial.eval₂_C]
      rw [hC, twQBar_algebraMap_twQBarFile, Polynomial.eval₂_C]
      exact hC
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, twQBar_X, map_inv₀, inv_inv]
  induction f using RatFunc.induction_on with
  | f p q hq =>
    have hp := DFunLike.congr_fun hcomp p
    have hq' := DFunLike.congr_fun hcomp q
    simp only [RingHom.comp_apply] at hp hq'
    rw [map_div₀, map_div₀, hp, hq']

end AJConjecture
