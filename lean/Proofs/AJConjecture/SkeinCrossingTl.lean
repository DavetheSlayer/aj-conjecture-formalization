import Mathlib
import AJConjecture.SkeinCapSlideThin
import AJConjecture.SkeinTlRelations

/-!
# A generator slides across a single strand

`e_i σ_{i+1} σ_i = σ_{i+1} σ_i e_{i+1}` and `e_{i+1} σ_i σ_{i+1} = σ_i σ_{i+1} e_i`, for crossings
of either sign: with `σ^{±1} = t^{±1} + t^{∓1} e` both sides of the first identity are
`e_i e_{i+1}`, because `t² + t⁻² + δ = 0` and `e_i e_{i+1} e_i = e_i`. The hypothesis `i + 2 < n` is
necessary (if `e_{i+1} = 0` the right-hand side vanishes and the left-hand side does not).
-/

namespace AJConjecture

/-- The slide of a generator across a strand in an abstract algebra: if `E`, `F` satisfy the
Temperley–Lieb relations with loop value `δ`, and `a b = 1`, `a² + b² + δ = 0`, then
`E (a + b F) (a + b E) = (a + b F) (a + b E) F`. -/
private theorem tl_slide_of_relations_crossingTl {K R : Type*} [Field K] [Ring R] [Algebra K R]
    (E F : R) (a b δ : K) (hab : a * b = 1) (hδ : a * a + b * b + δ = 0)
    (hEE : E * E = δ • E) (hFF : F * F = δ • F) (hEFE : E * F * E = E) (hFEF : F * E * F = F) :
    E * ((a • (1 : R) + b • F) * (a • (1 : R) + b • E)) =
      (a • (1 : R) + b • F) * (a • (1 : R) + b • E) * F := by
  have hc : a * a + a * b * δ + b * b = 0 := by rw [hab]; linear_combination hδ
  have hL : E * ((a • (1 : R) + b • F) * (a • (1 : R) + b • E)) =
      (a * a + a * b * δ + b * b) • E + (a * b) • (E * F) := by
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, ← mul_assoc,
      hEE, hEFE]
    module
  have hR : (a • (1 : R) + b • F) * (a • (1 : R) + b • E) * F =
      (a * a + a * b * δ + b * b) • F + (a * b) • (E * F) := by
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hFF, hFEF]
    module
  rw [hL, hR, hc, zero_smul, zero_smul]

/-- A generator slides to the right across the strand on its right. -/
theorem tlGenF_mul_crossingF_mul_crossingF (n i : ℕ) (s : Bool) (h : i + 2 < n) :
    tlGenF n i * (crossingF n (i + 1, s) * crossingF n (i, s)) =
      crossingF n (i + 1, s) * crossingF n (i, s) * tlGenF n (i + 1) := by
  cases s
  · rw [crossingF_neg, crossingF_neg]
    exact tl_slide_of_relations_crossingTl _ _ _ _ _
      ((mul_comm _ _).trans ratFuncX_mul_inv)
      ratFuncX_inv_sq_add_loop
      (tlGenF_mul_self n i) (tlGenF_mul_self n (i + 1)) (tlGenF_mul_succ_mul n i h)
      (tlGenF_succ_mul_mul n i)
  · rw [crossingF_pos, crossingF_pos]
    exact tl_slide_of_relations_crossingTl _ _ _ _ _ ratFuncX_mul_inv
      ratFuncX_sq_add_loop
      (tlGenF_mul_self n i) (tlGenF_mul_self n (i + 1)) (tlGenF_mul_succ_mul n i h)
      (tlGenF_succ_mul_mul n i)

/-- A generator slides to the left across the strand on its left. -/
theorem tlGenF_succ_mul_crossingF_mul_crossingF (n i : ℕ) (s : Bool) (h : i + 2 < n) :
    tlGenF n (i + 1) * (crossingF n (i, s) * crossingF n (i + 1, s)) =
      crossingF n (i, s) * crossingF n (i + 1, s) * tlGenF n i := by
  cases s
  · rw [crossingF_neg, crossingF_neg]
    exact tl_slide_of_relations_crossingTl _ _ _ _ _
      ((mul_comm _ _).trans ratFuncX_mul_inv)
      ratFuncX_inv_sq_add_loop
      (tlGenF_mul_self n (i + 1)) (tlGenF_mul_self n i) (tlGenF_succ_mul_mul n i)
      (tlGenF_mul_succ_mul n i h)
  · rw [crossingF_pos, crossingF_pos]
    exact tl_slide_of_relations_crossingTl _ _ _ _ _ ratFuncX_mul_inv
      ratFuncX_sq_add_loop
      (tlGenF_mul_self n (i + 1)) (tlGenF_mul_self n i) (tlGenF_succ_mul_mul n i)
      (tlGenF_mul_succ_mul n i h)

end AJConjecture
