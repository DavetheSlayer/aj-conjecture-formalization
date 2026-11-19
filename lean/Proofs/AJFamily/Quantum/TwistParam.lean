import Mathlib
import AJFamily.Quantum.TwistPolyEval

/-!
# Inverting the twist parametrisation

From `T_m(Z, e) = 0` the Cassini identity gives `K = Z - ((U_(m-1)(Z) - U_m(Z)) U_(m-1)(Z))⁻¹`, the
twist parameter `twistParamK m` at `Z`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

theorem famParam_inverse {F : Type*} [Field F] {m : ℕ} (hm : 1 ≤ m) {K J : F}
    (hT : famTK m K J = 0) :
    chebU (famZK K J) (m - 1) ≠ 0 ∧ chebU (famZK K J) (m - 1) - chebU (famZK K J) m ≠ 0 ∧
      K = famZK K J - ((chebU (famZK K J) (m - 1) - chebU (famZK K J) m) *
        chebU (famZK K J) (m - 1))⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hc := chebU_succ_sq_add (famZK K J) n
  unfold famTK at hT
  rw [Nat.add_sub_cancel] at hT ⊢
  set Z := famZK K J with hZ
  set B := chebU Z n
  set C := chebU Z (n + 1)
  have hC : C = (K - J) * B := by linear_combination hT
  have hZ' : Z = 1 + K - K * J + J ^ 2 := hZ
  have hcas : B ^ 2 * ((Z - K) * (1 + J - K)) = 1 := by
    rw [hC] at hc
    linear_combination hc + B ^ 2 * hZ'
  have hB : B ≠ 0 := by
    rintro h
    rw [h] at hcas
    simp at hcas
  have he : 1 + J - K ≠ 0 := by
    rintro h
    rw [h] at hcas
    simp at hcas
  have hA : B - C = B * (1 + J - K) := by rw [hC]; ring
  refine ⟨hB, by rw [hA]; exact mul_ne_zero hB he, ?_⟩
  rw [hA]
  field_simp
  linear_combination -hcas

end AJConjecture
