import Mathlib
import AJHandoff.TorusQuantum.PairQTOrder
import AJTwist.Select.TwSInput

/-!
# The inversion `t ↦ t⁻¹`

Source: Sections 6.2 and 6.4 of `selection.tex` (revision 5): `ν_∞(f) = ν(f(t⁻¹))`, and the
inverted inputs of the normalized inversion `(𝓑 F)_N = q^(N(N-1)) F_N(t⁻¹)`.

* `twsInv`: the automorphism `t ↦ t⁻¹` of `ℚ(t)`; it is an involution and exchanges the order at
  `t = 0` with minus the degree.
* the inverted inputs: `twsInv (twsInput false r s ℓ n) = q^(a n(n+1)) V_n(q)` and
  `twsInv (twsPeriodInput ℓ c n) = twsPeriodInput (-ℓ) (-c) n`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Evaluation at `X⁻¹` does not kill nonzero polynomials. -/
theorem twsInv_aux (K : Type*) [Field K] :
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

/-- The automorphism `t ↦ t⁻¹` of `ℚ(t)`. -/
def twsInv : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom _ (twsInv_aux ℚ)

/-- `twsInv` sends `t` to `t⁻¹`. -/
theorem twsInv_X : twsInv RatFunc.X = (RatFunc.X : RatFunc ℚ)⁻¹ := by
  simp [twsInv, RatFunc.liftRingHom_apply]

/-- `twsInv` on the image of a polynomial is the substitution `t ↦ t⁻¹`. -/
theorem twsInv_algebraMap_twsInvertFile (p : ℚ[X]) :
    twsInv (algebraMap ℚ[X] (RatFunc ℚ) p) =
      Polynomial.eval₂ (RatFunc.C : ℚ →+* RatFunc ℚ) (RatFunc.X : RatFunc ℚ)⁻¹ p := by
  rw [twsInv, RatFunc.liftRingHom_algebraMap]
  rfl

/-- `twsInv` inverts the integer powers of `t`. -/
theorem twsInv_X_zpow_twsInvertFile (k : ℤ) :
    twsInv ((RatFunc.X : RatFunc ℚ) ^ k) = (RatFunc.X : RatFunc ℚ) ^ (-k) := by
  rw [map_zpow₀, twsInv_X, inv_zpow, zpow_neg]

/-- `twsInv` inverts the integer powers of `q = t⁴`. -/
theorem twsInv_qParam_zpow_twsInvertFile (k : ℤ) :
    twsInv (qParam ^ k) = qParam ^ (-k) := by
  rw [qParam_zpow_eq_ratFuncX_zpow, qParam_zpow_eq_ratFuncX_zpow, twsInv_X_zpow_twsInvertFile,
    mul_neg]

/-- `twsInv` fixes the quantum integers. -/
theorem twsInv_quantumInt_twsInvertFile (m : ℤ) :
    twsInv (quantumInt m) = quantumInt m := by
  rw [quantumInt, map_div₀, map_sub, map_sub, twsInv_X_zpow_twsInvertFile,
    twsInv_X_zpow_twsInvertFile, twsInv_X_zpow_twsInvertFile, twsInv_X_zpow_twsInvertFile,
    neg_neg, neg_neg, ← neg_sub, ← neg_sub (RatFunc.X ^ (2 : ℤ)), neg_div_neg_eq]

/-- `twsInv` is an involution. -/
theorem twsInv_twsInv (f : RatFunc ℚ) : twsInv (twsInv f) = f := by
  have hcomp : (twsInv.comp twsInv).comp (algebraMap ℚ[X] (RatFunc ℚ)) =
      algebraMap ℚ[X] (RatFunc ℚ) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · have hC : twsInv (RatFunc.C a) = RatFunc.C a := by
        rw [← RatFunc.algebraMap_C, twsInv_algebraMap_twsInvertFile, Polynomial.eval₂_C,
          RatFunc.algebraMap_C]
      rw [RingHom.comp_apply, RingHom.comp_apply, RatFunc.algebraMap_C, hC, hC]
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, twsInv_X, map_inv₀, inv_inv]
  induction f using RatFunc.induction_on with
  | f p q hq =>
    have hp := DFunLike.congr_fun hcomp p
    have hq' := DFunLike.congr_fun hcomp q
    simp only [RingHom.comp_apply] at hp hq'
    rw [map_div₀, map_div₀, hp, hq']

/-- A nonzero constant is nonzero of order `0` at `t = 0`. -/
private theorem pairQTOrder_C_twsInvertFile {c : ℚ} (hc : c ≠ 0) :
    (RatFunc.C c : RatFunc ℚ) ≠ 0 ∧ pairQTOrder (RatFunc.C c) = 0 := by
  refine ⟨(_root_.map_ne_zero _).mpr hc, ?_⟩
  rw [pairQTOrder, RatFunc.num_C, RatFunc.denom_C, Polynomial.natTrailingDegree_C,
    Polynomial.natTrailingDegree_one, sub_self]

/-- The inversion of a nonzero polynomial is nonzero of order minus its degree. -/
private theorem pairQTOrder_twsInv_algebraMap_twsInvertFile {p : ℚ[X]} (hp : p ≠ 0) :
    twsInv (algebraMap ℚ[X] (RatFunc ℚ) p) ≠ 0 ∧
      pairQTOrder (twsInv (algebraMap ℚ[X] (RatFunc ℚ) p)) = -(p.natDegree : ℤ) := by
  rw [twsInv_algebraMap_twsInvertFile, Polynomial.eval₂_eq_sum_range]
  have hterm : ∀ i : ℕ, p.coeff i ≠ 0 →
      RatFunc.C (p.coeff i) * (RatFunc.X : RatFunc ℚ)⁻¹ ^ i ≠ 0 ∧
        pairQTOrder (RatFunc.C (p.coeff i) * (RatFunc.X : RatFunc ℚ)⁻¹ ^ i) = -(i : ℤ) := by
    intro i hi
    have h := pairQTOrder_mul_eq (pairQTOrder_C_twsInvertFile hi)
      (pairQTOrder_X_zpow_eq (-(i : ℤ)))
    rwa [zero_add, zpow_neg, zpow_natCast, ← inv_pow] at h
  refine pairQTOrder_sum_eq_of_lt (a := p.natDegree) (Finset.self_mem_range_succ _)
    (hterm _ (Polynomial.leadingCoeff_ne_zero.mpr hp)) fun i hi hne ↦ ?_
  by_cases hc : p.coeff i = 0
  · exact Or.inl (by rw [hc, map_zero, zero_mul])
  · refine Or.inr ?_
    rw [(hterm i hc).2]
    have := Finset.mem_range.mp hi
    omega

/-- The order at `t = 0` of the inverted function is minus the degree. -/
theorem tws_tOrder_twsInv {f : RatFunc ℚ} (hf : f ≠ 0) :
    twsInv f ≠ 0 ∧ pairQTOrder (twsInv f) = -f.intDegree := by
  have h := pairQTOrder_div_eq
    (pairQTOrder_twsInv_algebraMap_twsInvertFile (RatFunc.num_ne_zero hf))
    (pairQTOrder_twsInv_algebraMap_twsInvertFile (RatFunc.denom_ne_zero f))
  rw [← map_div₀, RatFunc.num_div_denom] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [RatFunc.intDegree]
  ring

/-- The inverted input of the mirror companion is `q^(a n(n+1)) V_n(q)`. -/
theorem twsInv_twsInput_false (r s : ℕ) (ℓ : ℤ) (n : ℕ) :
    twsInv (twsInput false r s ℓ n) =
      qParam ^ (twIndex false r s ℓ * n * ((n : ℤ) + 1)) * twsTorusSum true r s n := by
  simp only [twsInput, twsTorusSum, map_mul, map_sum, twsInv_qParam_zpow_twsInvertFile,
    twsInv_quantumInt_twsInvertFile, neg_neg, Bool.false_eq_true, ↓reduceIte, neg_one_mul,
    one_mul]

/-- The inverted period input is the period input of the opposite twist and exponent. -/
theorem twsInv_twsPeriodInput (ℓ c : ℤ) (n : ℕ) :
    twsInv (twsPeriodInput ℓ c n) = twsPeriodInput (-ℓ) (-c) n := by
  simp only [twsPeriodInput, map_mul, map_sub, twsInv_qParam_zpow_twsInvertFile, neg_mul,
    neg_neg]

end AJConjecture
