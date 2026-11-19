import Mathlib
import AJTwist.Main.TwMBarAction

/-!
# The specialization of the mirror operator (Unit M2)

Source: revision 5, Section 8.2 (`conclusion.tex`): "Under `t⁻¹ + 1 = (t + 1)/t` the primitive
parameter order is preserved. Thus `f_{S^*}(M, L) ≐ f_S(M⁻¹, L)`."

At `t = -1` the inversion of `t` is invisible (`(-1)⁻¹ = -1`), so the specialization of
`Θ(P) = t^A M^B P(t⁻¹, M⁻¹, L)` is `(-1)^A M^B P(-1, M⁻¹, L)`:

* `twmMReflect B F = M^B F(M⁻¹, L)` for `F ∈ ℤ[M][L]`: every coefficient of `F` reflected in
  `M` (`Polynomial.reflect B`);
* `specialize_twHBarOp`: `specialize (twHBarOp A B P) = (-1)^A · twmMReflect B (specialize P)`
  for bounds `A`, `B` of the degrees of the coefficients of `P`;
* `specialize_twmBarOp`: the same for `Θ(P) = twmBarOp P`.

Checked in exact arithmetic on random operators (`SCR/M/py/m01_mirror.py`, item (2)) and on an
explicit second-order annihilator (item (5)). This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `M^B F(M⁻¹, L)`: the coefficients of `F ∈ ℤ[M][L]` reflected in `M` at the degree `B`. -/
def twmMReflect (B : ℕ) (F : ℤ[X][X]) : ℤ[X][X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1), monomial i (Polynomial.reflect B (F.coeff i))

/-- The coefficients of `twmMReflect B F` are the reflected coefficients of `F`. -/
theorem coeff_twmMReflect (B : ℕ) (F : ℤ[X][X]) (i : ℕ) :
    (twmMReflect B F).coeff i = Polynomial.reflect B (F.coeff i) := by
  simp only [twmMReflect, finsetSum_coeff, coeff_monomial, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), reflect_zero]

/-- At `t = -1` a reflected polynomial of `ℤ[t]` has the value `(-1)^A` times the value of the
polynomial (`Polynomial.eval₂_reflect_mul_pow` at `x = -1`, its own inverse). -/
theorem eval_neg_one_reflect (A : ℕ) (p : ℤ[X]) (hp : p.natDegree ≤ A) :
    (Polynomial.reflect A p).eval (-1) = (-1) ^ A * p.eval (-1) := by
  have : Invertible (-1 : ℤ) := ⟨-1, by norm_num, by norm_num⟩
  have h := eval₂_reflect_mul_pow (RingHom.id ℤ) (-1 : ℤ) A p hp
  have hinv : ⅟(-1 : ℤ) = -1 := invOf_eq_right_inv (by norm_num)
  rw [hinv, eval₂_id, eval₂_id] at h
  rw [← h, mul_comm, mul_assoc, ← pow_add, Even.neg_one_pow ⟨A, rfl⟩, mul_one]

/-- The specialization at `t = -1` of a reflected coefficient: `(-1)^A` times the reflection in
`M` of the specialized coefficient. -/
theorem map_eval_neg_one_twHBarCoeff (A B : ℕ) (c : Coeff)
    (hA : ∀ b : ℕ, (c.coeff b).natDegree ≤ A) (hB : c.natDegree ≤ B) :
    (twHBarCoeff A B c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      C ((-1 : ℤ) ^ A) * Polynomial.reflect B (c.map (Polynomial.evalRingHom (-1 : ℤ))) := by
  ext k
  rw [twHBarCoeff, Polynomial.map_sum, finsetSum_coeff, coeff_C_mul, coeff_reflect, coeff_map]
  simp only [Polynomial.map_monomial, coeff_monomial, Finsupp.single_apply, coe_evalRingHom]
  by_cases hk : k ≤ B
  · rw [revAt_le hk, Finset.sum_eq_single (B - k)]
    · rw [ite_eq_left (Nat.sub_sub_self hk), eval_neg_one_reflect A _ (hA _)]
    · intro b hb hne
      have hb' : b ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      exact ite_eq_right (by omega)
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · have hk' : B < k := by omega
    rw [revAt_eq_self_of_lt hk', coeff_eq_zero_of_natDegree_lt (by omega), eval_zero, mul_zero]
    refine Finset.sum_eq_zero fun b hb ↦ ite_eq_right ?_
    omega

/-- **The specialization of the mirror operator**: for bounds `A`, `B` of the degrees of the
coefficients of `P` in `t` and `M`,
`(twHBarOp A B P)(-1, M, L) = (-1)^A M^B P(-1, M⁻¹, L)`. -/
theorem specialize_twHBarOp (A B : ℕ) (P : RecOp)
    (hA : ∀ i b : ℕ, ((P.coeff i).coeff b).natDegree ≤ A)
    (hB : ∀ i : ℕ, (P.coeff i).natDegree ≤ B) :
    specialize (twHBarOp A B P) = C (C ((-1 : ℤ) ^ A)) * twmMReflect B (specialize P) := by
  ext i : 2
  rw [coeff_C_mul, coeff_twmMReflect, specialize, coe_mapRingHom, coeff_map, coeff_map,
    coeff_twHBarOp, coe_mapRingHom, map_eval_neg_one_twHBarCoeff A B _ (hA i) (hB i)]

/-- The specialization of `Θ(P)`: `f_{Θ(P)}(M, L) = ± M^B f_P(M⁻¹, L)`. -/
theorem specialize_twmBarOp (P : RecOp) :
    specialize (twmBarOp P) =
      C (C ((-1 : ℤ) ^ twmTDeg P)) * twmMReflect (twmMDeg P) (specialize P) :=
  specialize_twHBarOp _ _ P (natDegree_coeff_coeff_le_twmTDeg P) (natDegree_coeff_le_twmMDeg P)

/-- The coefficients of the specialization of `P` have degree in `M` at most `twmMDeg P`. -/
theorem natDegree_coeff_specialize_le_twmMDeg (P : RecOp) (i : ℕ) :
    ((specialize P).coeff i).natDegree ≤ twmMDeg P := by
  rw [specialize, coe_mapRingHom, coeff_map, coe_mapRingHom]
  exact natDegree_map_le.trans (natDegree_coeff_le_twmMDeg P i)

end AJConjecture
