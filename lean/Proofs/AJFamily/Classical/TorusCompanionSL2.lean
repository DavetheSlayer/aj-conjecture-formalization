import Mathlib
import AJConjecture.BraidRelSL2

/-!
# SL₂ representations of the torus knot relation

If `Δ c = d Δ` and `Δ d = c Δ` in `SL₂(ℂ)`, then `c = d` or `Δ² = -1`. Applied to
`Δ = (cd)^k c`, a pair `c, d` satisfying `(cd)^k c = d (cd)^k` has `c = d` or
`(cd)^(2k+1) = -1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem eq_or_sq_eq_neg_one_of_swap (Δ c d : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h1 : Δ * c = d * Δ) (h2 : Δ * d = c * Δ) :
    c = d ∨ ((Δ ^ 2 : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  have h3 : Δ ^ 2 * c = c * Δ ^ 2 := by
    calc Δ ^ 2 * c = Δ * (Δ * c) := by rw [pow_two, mul_assoc]
      _ = Δ * (d * Δ) := by rw [h1]
      _ = Δ * d * Δ := by rw [mul_assoc]
      _ = c * Δ * Δ := by rw [h2]
      _ = c * Δ ^ 2 := by rw [pow_two, mul_assoc]
  have hCH : (Δ : Matrix (Fin 2) (Fin 2) ℂ) * Δ =
      (Δ : Matrix (Fin 2) (Fin 2) ℂ).trace • (Δ : Matrix (Fin 2) (Fin 2) ℂ) - 1 :=
    braidRel_sq_eq_trace_smul_sub_one _ Δ.det_coe
  by_cases ht : (Δ : Matrix (Fin 2) (Fin 2) ℂ).trace = 0
  · right
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, hCH, ht, zero_smul, zero_sub]
  · left
    have h3' : (Δ : Matrix (Fin 2) (Fin 2) ℂ) * Δ * c = c * ((Δ : Matrix (Fin 2) (Fin 2) ℂ) * Δ) := by
      have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) ℂ ↦
        (x : Matrix (Fin 2) (Fin 2) ℂ)) h3
      simpa [pow_two] using this
    rw [hCH, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h3'
    have h5 : (Δ : Matrix (Fin 2) (Fin 2) ℂ).trace •
        ((Δ : Matrix (Fin 2) (Fin 2) ℂ) * c - c * (Δ : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
      rw [smul_sub]
      exact sub_eq_zero.mpr (sub_left_inj.mp h3')
    have h4 : (Δ : Matrix (Fin 2) (Fin 2) ℂ) * c = c * (Δ : Matrix (Fin 2) (Fin 2) ℂ) := by
      rcases smul_eq_zero.mp h5 with h0 | h0
      · exact absurd h0 ht
      · exact sub_eq_zero.mp h0
    have h6 : Δ * c = c * Δ := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact h4
    exact mul_right_cancel (h6.symm.trans h1)

theorem torus_rel_eq_or_center_eq_neg_one (k : ℕ) (c d : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h : (c * d) ^ k * c = d * (c * d) ^ k) :
    c = d ∨ (((c * d) ^ (2 * k + 1) : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = (c * d) ^ k * c := ⟨_, rfl⟩
  have h1 : Δ * c = d * Δ := by
    calc Δ * c = (c * d) ^ k * c * c := by rw [hΔ]
      _ = d * (c * d) ^ k * c := by rw [h]
      _ = d * Δ := by rw [hΔ, mul_assoc]
  have h2 : Δ * d = c * Δ := by
    calc Δ * d = (c * d) ^ k * (c * d) := by rw [hΔ, mul_assoc]
      _ = (c * d) * (c * d) ^ k := by rw [← pow_succ, pow_succ']
      _ = c * (d * (c * d) ^ k) := by rw [mul_assoc]
      _ = c * ((c * d) ^ k * c) := by rw [h]
      _ = c * Δ := by rw [hΔ]
  have hsq : Δ ^ 2 = (c * d) ^ (2 * k + 1) := by
    calc Δ ^ 2 = (c * d) ^ k * c * ((c * d) ^ k * c) := by rw [pow_two, hΔ]
      _ = (c * d) ^ k * c * (d * (c * d) ^ k) := by rw [h]
      _ = (c * d) ^ k * (c * d) * (c * d) ^ k := by group
      _ = (c * d) ^ (2 * k + 1) := by rw [← pow_succ, ← pow_add]; ring_nf
  rcases eq_or_sq_eq_neg_one_of_swap Δ c d h1 h2 with hcd | hneg
  · exact Or.inl hcd
  · exact Or.inr (by rw [← hsq]; exact hneg)

end AJConjecture
