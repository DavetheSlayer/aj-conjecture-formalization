import Mathlib
import AJFamily.Quantum.AbNodeCertificateIdentity
import AJFamily.Quantum.EbNodeFacts
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.TwistPolyEval

/-!
# E/B node: collision freeness

`ebNode_collisionFree`: the hypothesis `NodeCollisionFree` for `G = E`, `D = B_m`, `T = L - 1` at
the E/B node.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Chebyshev values at `-2`: `U_n(-2) = (-1)ⁿ (n + 1)`, together with the next value. -/
theorem chebU_neg_two (n : ℕ) :
    chebU (-2 : ℂ) n = (-1) ^ n * ((n : ℂ) + 1) ∧
      chebU (-2 : ℂ) (n + 1) = (-1) ^ (n + 1) * ((n : ℂ) + 2) := by
  induction n with
  | zero =>
    simp only [chebU, pow_zero, Nat.cast_zero, zero_add, pow_one]
    norm_num
  | succ n ih =>
    refine ⟨ih.2.trans (by push_cast; ring), ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, chebU, ih.2, ih.1]
    push_cast
    ring

/-- Chebyshev values at `2`: `U_n(2) = n + 1`, together with the next value. -/
private theorem chebU_two_ebNode (n : ℕ) :
    chebU (2 : ℂ) n = (n : ℂ) + 1 ∧ chebU (2 : ℂ) (n + 1) = (n : ℂ) + 2 := by
  induction n with
  | zero =>
    simp only [chebU, Nat.cast_zero, zero_add]
    norm_num
  | succ n ih =>
    refine ⟨ih.2.trans (by push_cast; ring), ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, chebU, ih.2, ih.1]
    push_cast
    ring

/-- `evalIntPoint` as `evalEval` of the complexified polynomial. -/
theorem evalIntPoint_eq_evalEval (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l = (p.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).evalEval m l := by
  rw [evalIntPoint, evalPoint, eval₂_evalRingHom]

/-- `E(m, l) = l² - (x² - 4x + 1) l + x²`, `x = m²`. -/
theorem evalIntPoint_extraFactor (m l : ℂ) :
    evalIntPoint extraFactor m l = l ^ 2 - ((m ^ 2) ^ 2 - 4 * m ^ 2 + 1) * l + (m ^ 2) ^ 2 := by
  rw [evalIntPoint_eq_evalEval, extraFactor]
  simp [evalEval_C]
  ring

/-- `(L - 1)(m, l) = l - 1`. -/
private theorem evalIntPoint_X_sub_one_ebNodeCollision (m l : ℂ) :
    evalIntPoint (X - 1) m l = l - 1 := by
  rw [evalIntPoint_eq_evalEval]
  simp

/-- At the E/B node, a common zero of the `E`- and `B_m`-fibres is `L₀`. -/
private theorem eq_ebNodeL_of_extraFactor_twistPoly (m : ℕ) (hm : 2 ≤ m) {m₀ l : ℂ}
    (heb : (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0) (h0 : m₀ ≠ 0) (h1 : m₀ ^ 2 ≠ 1) (hxJ : m₀ ^ 2 ≠ ebNodeJ m)
    (hT : l ^ 2 - ((m₀ ^ 2) ^ 2 - 4 * m₀ ^ 2 + 1) * l + (m₀ ^ 2) ^ 2 = 0)
    (hB : evalIntPoint (twistPoly m) m₀ l = 0) :
    l = ebNodeL m m₀ := by
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hx1 : m₀ ^ 2 - 1 ≠ 0 := sub_ne_zero.2 h1
  have hn0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hs0 : 2 * (m : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : 2 * m + 1 ≠ 0)
  have hL : l + m₀ ^ 2 ≠ 0 := by
    intro h
    have hl : l = -m₀ ^ 2 := by linear_combination h
    rw [hl] at hT
    have : m₀ ^ 2 * (m₀ ^ 2 - 1) ^ 2 = 0 := by linear_combination hT
    exact mul_ne_zero hx0 (pow_ne_zero 2 hx1) this
  rw [evalIntPoint_eq_evalEval, evalEval_twistPoly h0 hL (by omega)] at hB
  have hB' := (mul_eq_zero.1 hB).resolve_left
    (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hx0))
  set K := famKQ (m₀ ^ 2) with hKdef
  set J := (m₀ ^ 2 * l + 1) / (l + m₀ ^ 2) with hJdef
  have hJl : J * (l + m₀ ^ 2) = m₀ ^ 2 * l + 1 := by
    rw [hJdef]
    field_simp
  have hZ : famZK K J = -2 := by
    simp only [famZK, hKdef, hJdef, famKQ]
    field_simp
    linear_combination (m₀ ^ 2 + 1) ^ 2 * hT
  have hK : (m : ℂ) * (2 * m + 1) * K = -(4 * m ^ 2 + 2 * m + 1) := by
    simp only [hKdef, famKQ]
    field_simp
    linear_combination heb
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  rw [famTK, hZ, Nat.add_sub_cancel, (chebU_neg_two n).1,
    (chebU_neg_two n).2] at hB'
  have hJ : ((n + 1 : ℕ) : ℂ) * (J - K) = (n + 1 : ℕ) + 1 := by
    push_cast
    rcases neg_one_pow_eq_or ℂ n with hs | hs
    · rw [pow_succ, hs] at hB'
      linear_combination hB'
    · rw [pow_succ, hs] at hB'
      linear_combination -hB'
  set c : ℂ := ((n + 1 : ℕ) : ℂ) with hc
  have hJ0 : (2 * c + 1) * J = -(2 * c - 1) := by
    have : c * ((2 * c + 1) * J + (2 * c - 1)) = 0 := by
      linear_combination (2 * c + 1) * hJ + hK
    linear_combination (mul_eq_zero.1 this).resolve_left hn0
  have hJe : J = ebNodeJ (n + 1) := by
    rw [ebNodeJ, eq_div_iff hs0]
    linear_combination hJ0
  have hd : ebNodeJ (n + 1) - m₀ ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hxJ)
  rw [ebNodeL, famNodeL, eq_div_iff hd, ← hJe]
  linear_combination hJl

/-- At the E/B node, `B_m(m₀, 1) ≠ 0`. -/
private theorem twistPoly_one_ne_zero_ebNode (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (heb : (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0) (h0 : m₀ ≠ 0) (h2 : m₀ ^ 2 ≠ -1) :
    evalIntPoint (twistPoly m) m₀ 1 ≠ 0 := by
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hL : (1 : ℂ) + m₀ ^ 2 ≠ 0 := by
    intro h
    exact h2 (by linear_combination h)
  rw [evalIntPoint_eq_evalEval, evalEval_twistPoly h0 hL (by omega)]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hx0)) ?_
  have hJ : (m₀ ^ 2 * 1 + 1) / (1 + m₀ ^ 2) = 1 := by
    rw [div_eq_one_iff_eq hL]
    ring
  set K := famKQ (m₀ ^ 2) with hKdef
  have hK : (m : ℂ) * (2 * m + 1) * K = -(4 * m ^ 2 + 2 * m + 1) := by
    simp only [hKdef, famKQ]
    field_simp
    linear_combination heb
  have hZ : famZK K 1 = 2 := by
    simp only [famZK]
    ring
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  rw [hJ, famTK, hZ, Nat.add_sub_cancel, (chebU_two_ebNode n).1, (chebU_two_ebNode n).2]
  intro h
  push_cast at hK
  have hnat : ((8 * (n + 1) ^ 2 + 6 * (n + 1) + 2 : ℕ) : ℂ) = 0 := by
    push_cast
    linear_combination (2 * ((n : ℂ) + 1) + 1) * h + hK
  exact absurd (Nat.cast_eq_zero.1 hnat) (by omega)

/-- The collision hypothesis at the E/B node `L₀ = ebNodeL m m₀` of `E` and `B_m`,
with `T = L - 1`. -/
theorem ebNode_collisionFree (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (heb : (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0) :
    NodeCollisionFree extraFactor (twistPoly m) (X - 1) m₀ (ebNodeL m m₀) := by
  obtain ⟨h0, h1, h2, hxJ, -⟩ := ebNode_facts m hm heb
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  refine ⟨fun l hG hD ↦ ?_, fun l hT ↦ ?_⟩
  · rw [evalIntPoint_extraFactor] at hG
    exact eq_ebNodeL_of_extraFactor_twistPoly m hm heb h0 h1 hxJ hG hD
  rw [evalIntPoint_X_sub_one_ebNodeCollision] at hT
  have hl : l = 1 := by linear_combination hT
  subst hl
  refine ⟨?_, twistPoly_one_ne_zero_ebNode m hm heb h0 h2, ?_⟩
  · rw [evalIntPoint_extraFactor]
    intro h
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hx0 (by linear_combination h)
  · rw [evalIntPoint_derivative_X_sub_one]
    exact one_ne_zero

end AJConjecture
