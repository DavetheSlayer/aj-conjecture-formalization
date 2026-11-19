import Mathlib
import AJFamily.Quantum.EbNodeCollision
import AJFamily.Quantum.AbNodeFacts
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.TwistPolyEval

/-!
# Abelian node: collision freeness

`abNode_collisionFree`: the hypothesis `NodeCollisionFree` for `G = L - 1`, `D = B_m`, `T = E` at
the abelian node.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `∂_L E(m, l) = 2l - (x² - 4x + 1)`, `x = m²`. -/
private theorem evalIntPoint_derivative_extraFactor_abNodeCollision (m l : ℂ) :
    evalIntPoint (derivative extraFactor) m l = 2 * l - ((m ^ 2) ^ 2 - 4 * m ^ 2 + 1) := by
  rw [evalIntPoint_eq_evalEval, extraFactor]
  simp [derivative_pow, evalEval_C]
  ring

/-- `(L - 1)(m, l) = l - 1`. -/
private theorem evalIntPoint_X_sub_one_abNodeCollision (m l : ℂ) :
    evalIntPoint (X - 1) m l = l - 1 := by
  rw [evalIntPoint_eq_evalEval]
  simp

/-- At the abelian node, `B_m` does not vanish at a zero of the `E`-fibre. -/
private theorem twistPoly_ne_zero_of_extraFactor_abNode (m : ℕ) (hm : 2 ≤ m) {m₀ l : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) (h0 : m₀ ≠ 0)
    (h1 : m₀ ^ 2 ≠ 1)
    (hT : l ^ 2 - ((m₀ ^ 2) ^ 2 - 4 * m₀ ^ 2 + 1) * l + (m₀ ^ 2) ^ 2 = 0) :
    evalIntPoint (twistPoly m) m₀ l ≠ 0 := by
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hx1 : m₀ ^ 2 - 1 ≠ 0 := sub_ne_zero.2 h1
  have hL : l + m₀ ^ 2 ≠ 0 := by
    intro h
    have hl : l = -m₀ ^ 2 := by linear_combination h
    rw [hl] at hT
    have : m₀ ^ 2 * (m₀ ^ 2 - 1) ^ 2 = 0 := by linear_combination hT
    exact mul_ne_zero hx0 (pow_ne_zero 2 hx1) this
  rw [evalIntPoint_eq_evalEval, evalEval_twistPoly h0 hL (by omega)]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hx0)) ?_
  set K := famKQ (m₀ ^ 2) with hKdef
  set J := (m₀ ^ 2 * l + 1) / (l + m₀ ^ 2) with hJdef
  have hZ : famZK K J = -2 := by
    simp only [famZK, hKdef, hJdef, famKQ]
    field_simp
    linear_combination (m₀ ^ 2 + 1) ^ 2 * hT
  have hZ' : J ^ 2 - K * J + K + 3 = 0 := by
    simp only [famZK] at hZ
    linear_combination hZ
  have hK : (m : ℂ) * K = 2 * m + 1 := by
    simp only [hKdef, famKQ]
    field_simp
    linear_combination hab
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  rw [famTK, hZ, Nat.add_sub_cancel, (chebU_neg_two n).1, (chebU_neg_two n).2]
  intro h
  have hJ : ((n + 1 : ℕ) : ℂ) * (J - K) = (n + 1 : ℕ) + 1 := by
    push_cast
    rcases neg_one_pow_eq_or ℂ n with hs | hs
    · rw [pow_succ, hs] at h
      linear_combination h
    · rw [pow_succ, hs] at h
      linear_combination -h
  set c : ℂ := ((n + 1 : ℕ) : ℂ) with hc
  have hJ' : c * J = 3 * c + 2 := by linear_combination hJ + hK
  have hpos : (8 * c ^ 2 + 6 * c + 2 : ℂ) = 0 := by
    linear_combination c ^ 2 * hZ' - (c * J + 3 * c + 2 - (2 * c + 1)) * hJ' + (c * J - c) * hK
  have hnat : ((8 * (n + 1) ^ 2 + 6 * (n + 1) + 2 : ℕ) : ℂ) = 0 := by
    rw [← hpos, hc]
    push_cast
    ring
  exact absurd (Nat.cast_eq_zero.1 hnat) (by omega)

/-- The collision hypothesis at the abelian node `L = 1` of `L - 1` and `B_m`, with `T = E`. -/
theorem abNode_collisionFree (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) :
    NodeCollisionFree (X - 1) (twistPoly m) extraFactor m₀ 1 := by
  obtain ⟨h0, h1, -⟩ := abNode_facts m hm hab
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  refine ⟨fun l hG _ ↦ ?_, fun l hT ↦ ?_⟩
  · rw [evalIntPoint_X_sub_one_abNodeCollision] at hG
    linear_combination hG
  rw [evalIntPoint_extraFactor] at hT
  refine ⟨?_, twistPoly_ne_zero_of_extraFactor_abNode m hm hab h0 h1 hT, ?_⟩
  · rw [evalIntPoint_X_sub_one_abNodeCollision]
    intro h
    have hl : l = 1 := by linear_combination h
    rw [hl] at hT
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hx0 (by linear_combination hT)
  · rw [evalIntPoint_derivative_extraFactor_abNodeCollision]
    intro h
    have hsq : (l - m₀ ^ 2) * (l + m₀ ^ 2) = 0 := by
      linear_combination -hT + l * h
    rcases mul_eq_zero.1 hsq with h' | h'
    · have hq : (m₀ ^ 2) ^ 2 - 6 * m₀ ^ 2 + 1 = 0 := by linear_combination 2 * h' - h
      have : (4 * (m : ℂ) - 1) * m₀ ^ 2 = 0 := by linear_combination hab - (m : ℂ) * hq
      rcases mul_eq_zero.1 this with h4 | h4
      · have : ((4 * m : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; linear_combination h4
        have := Nat.cast_injective this
        omega
      · exact hx0 h4
    · have : (m₀ ^ 2 - 1) ^ 2 = 0 := by linear_combination 2 * h' - h
      exact h1 (by linear_combination pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this)

end AJConjecture
