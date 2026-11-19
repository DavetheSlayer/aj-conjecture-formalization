import Mathlib

/-!
# Irreducibility of `X⁴ - aX² + 1`

A square-class criterion for the irreducibility of `X⁴ - aX² + 1` over a field, by comparing
coefficients of a factorisation.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- A monic quadratic is determined by its two lower coefficients. -/
private lemma monic_quadratic_eq {F : Type*} [Field F] {f : F[X]} (hf : f.Monic)
    (hd : f.natDegree = 2) : f = X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
  ext n
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · have : f.coeff 2 = 1 := by rw [← hd]; exact hf
    simp [this]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [coeff_X_pow]

/-- Coefficient comparison for a product of two monic quadratics equal to `X⁴ - aX² + 1`. -/
private lemma quadratic_product_coeffs {F : Type*} [Field F] {a b c b' d : F}
    (h : (X ^ 2 + C b' * X + C d) * (X ^ 2 + C b * X + C c) = (X ^ 4 - C a * X ^ 2 + 1 : F[X])) :
    b + b' = 0 ∧ c + d + b * b' = -a ∧ b * d + b' * c = 0 ∧ c * d = 1 := by
  have e : (X ^ 2 + C b' * X + C d) * (X ^ 2 + C b * X + C c) = X ^ 4 + C (b + b') * X ^ 3 +
      C (c + d + b * b') * X ^ 2 + C (b * d + b' * c) * X + C (c * d) := by
    simp only [map_add, map_mul]; ring
  rw [e] at h
  have h3 := congrArg (fun q : F[X] ↦ q.coeff 3) h
  have h2 := congrArg (fun q : F[X] ↦ q.coeff 2) h
  have h1 := congrArg (fun q : F[X] ↦ q.coeff 1) h
  have h0 := congrArg (fun q : F[X] ↦ q.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C, coeff_X, coeff_one,
    coeff_C_mul] at h3 h2 h1 h0
  norm_num at h3 h2 h1 h0
  exact ⟨h3, by linear_combination h2, h1, h0⟩

set_option linter.unusedVariables false in
/-- `X⁴ - aX² + 1` is irreducible when none of `a + 2`, `a - 2`, `(a + 2)(a - 2)` is a square. -/
theorem irreducible_X_pow_four_sub_C_mul_add_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {a : F}
    (ha : ¬ IsSquare (a + 2)) (hb : ¬ IsSquare (a - 2)) (hc : ¬ IsSquare ((a + 2) * (a - 2))) :
    Irreducible (X ^ 4 - C a * X ^ 2 + 1 : F[X]) := by
  have hm : (X ^ 4 - C a * X ^ 2 + 1 : F[X]).Monic := by monicity!
  have hdeg : (X ^ 4 - C a * X ^ 2 + 1 : F[X]).natDegree = 4 := by compute_degree!
  rw [hm.irreducible_iff_natDegree']
  refine ⟨fun h ↦ by simpa [hdeg] using congrArg natDegree h, fun f g hf hg hfg hg2 ↦ ?_⟩
  rw [hdeg, Finset.mem_Ioc] at hg2
  have hfd : f.natDegree + g.natDegree = 4 := by rw [← hf.natDegree_mul hg, hfg, hdeg]
  obtain hg1 | hg2' : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  · obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one (degree_eq_iff_natDegree_eq_of_pos
      (by norm_num) |>.mpr hg1)
    have hp := congrArg (eval r) hfg
    simp only [eval_mul, hr.eq_zero, mul_zero, eval_add, eval_sub, eval_pow, eval_X, eval_mul,
      eval_C, eval_one] at hp
    exact hc ⟨2 * r ^ 2 - a, by linear_combination 4 * hp⟩
  · rw [monic_quadratic_eq hf (by omega), monic_quadratic_eq hg hg2'] at hfg
    obtain ⟨e3, e2, e1, e0⟩ := quadratic_product_coeffs hfg
    set b := g.coeff 1
    set c := g.coeff 0
    set d := f.coeff 0
    have hb' : f.coeff 1 = -b := by linear_combination e3
    rw [hb'] at e2 e1
    have : b * (d - c) = 0 := by linear_combination e1
    rcases mul_eq_zero.mp this with hb0 | hdc
    · rw [hb0] at e2
      exact hc ⟨2 * c + a, by linear_combination 4 * e0 - 4 * c * e2⟩
    · have hdc' : d = c := by linear_combination hdc
      rw [hdc'] at e0 e2
      have : (c - 1) * (c + 1) = 0 := by linear_combination e0
      rcases mul_eq_zero.mp this with h1 | h1
      · exact ha ⟨b, by linear_combination e2 - 2 * h1⟩
      · exact hb ⟨b, by linear_combination e2 - 2 * h1⟩

end AJConjecture
