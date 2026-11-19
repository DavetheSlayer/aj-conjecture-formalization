import Mathlib
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.TwistPolyNodeValues
import AJTwist.Factor.TwFBlocksPullback
import AJTwist.Factor.TwFNegSymbolValues
import AJTwist.Factor.TwFNegEval
import AJTwist.Factor.TwFNegEbNode

/-!
# The crossing `E/C_b`: transversality (TwF, unit F2)

Source: revision 5, Section 5.2, eq. (enode) and "At `Z = -2` the varying block fixes
`e = (2a + 1)/a`, and then `(J - 1) e = -4` fixes `J` uniquely. The two values of the meridian
trace `K` are distinct and neither is `± 2`"; Section 5.4: `s_H - s_G =
-6b h_b (8b² - 4b + 1)/((10b² - 5b + 1)(4b - 1))`, "All relevant derivatives are nonzero for
`b ≥ 1`".

At `(m₀, l₀)`, `l₀ = twNegNodeL b m₀`, `x₀ = m₀²` a root of
`b(2b - 1) x² + (4b² - 2b + 1) x + b(2b - 1)`:
* `twNeg_ebNode_facts`: the twelve facts of the library's `ebNode_facts` with `B_m → C_b`
  (`E = C_b = 0`, `L - 1 ≠ 0`, `∂_L E ≠ 0`, `∂_L C_b ≠ 0`, nonzero Jacobian, and the
  nondegeneracy of the point);
The fibre condition is in `AJTwist/Factor/TwFNegEbCollision.lean`.

Route. `(x + 1)² E` and `C_b` are the pullbacks of `ζ + 2x` and `T̂_(-b)`
(`twfPullback_symbolZeta_add`, `twfPullback_symbolTwistNeg`), which vanish at `(x₀, J₀)`
(`twNeg_ebNode_zeta`); there `w = -x₀` and, by `symbolTwistNeg_node_values` and
`dblRootDeriv_mul_of_crit`,
`6 b ∂_J T̂_(-b) = x₀ (10b² - 5b + 1) (-x₀)^(b-1)·(unit)` and the Jacobian
`∂_J ζ ∂_x T̂_(-b) - (∂_x ζ + 2) ∂_J T̂_(-b) = -(-x₀)^(b-2) x₀² (2b(2b - 1)(x₀ + 1) + 1)/b`
(computed symbolically in `b`, scratch `node_closed_neg.py`), nonzero on the node quadratic;
then `evalIntPoint_derivative_twfPullback`, `twfPullback_jacobian`.
Checked for `b ≤ 6` modulo a prime (scratch `check_node_facts.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The nondegeneracy of the `E/C_b` node in the coordinates `(x, J)`: `x₀ ≠ ± 1`, `x₀ ≠ J₀`,
`x₀ J₀ ≠ 1`. -/
private theorem twNeg_ebNode_ne_twfNegEbFacts (b : ℕ) (hb : 1 ≤ b) {x : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * x ^ 2 + (4 * b ^ 2 - 2 * b + 1) * x + b * (2 * b - 1) = 0) :
    x ≠ 1 ∧ x ≠ -1 ∧ x ≠ twNegNodeJ b ∧ x * twNegNodeJ b ≠ 1 := by
  have h2b : 2 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((2 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  have hJ : (2 * (b : ℂ) - 1) * twNegNodeJ b = -(2 * b + 1) := by
    rw [twNegNodeJ]
    field_simp
  generalize twNegNodeJ b = J at hJ ⊢
  have hP : (b : ℂ) * (2 * b - 1) * J ^ 2 + (4 * b ^ 2 - 2 * b + 1) * J + b * (2 * b - 1) = 1 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 h2b) ?_
    linear_combination ((b : ℂ) * (2 * b - 1) * ((2 * b - 1) * J - (2 * b + 1)) +
      (4 * (b : ℂ) ^ 2 - 2 * b + 1) * (2 * b - 1)) * hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    have h8 : ((8 * b ^ 2 + 1 : ℕ) : ℂ) = ((4 * b : ℕ) : ℂ) := by
      push_cast
      linear_combination heb
    have h8' : 8 * b ^ 2 + 1 = 4 * b := Nat.cast_injective h8
    nlinarith
  · rintro rfl
    exact one_ne_zero (α := ℂ) (by linear_combination -heb)
  · rintro rfl
    exact one_ne_zero (α := ℂ) (by linear_combination heb - hP)
  · intro h
    refine one_ne_zero (α := ℂ) ?_
    linear_combination J ^ 2 * heb - hP -
      ((b : ℂ) * (2 * b - 1) * (x * J + 1) + (4 * (b : ℂ) ^ 2 - 2 * b + 1) * J) * h

/-- Three natural numbers that do not vanish: `4b - 1`, `10b² - 5b + 1`, `8b² - 4b + 1`. -/
private theorem natCast_ne_zero_twfNegEbFacts (b : ℕ) (hb : 1 ≤ b) :
    4 * (b : ℂ) - 1 ≠ 0 ∧ 10 * (b : ℂ) ^ 2 - 5 * b + 1 ≠ 0 ∧ 8 * (b : ℂ) ^ 2 - 4 * b + 1 ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : ((4 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  · have h' : ((10 * b ^ 2 + 1 : ℕ) : ℂ) = ((5 * b : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    nlinarith
  · have h' : ((8 * b ^ 2 + 1 : ℕ) : ℂ) = ((4 * b : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    nlinarith

/-- At the `E/C_b` node, in the coordinates `(x, J)`: `∂_J ζ ≠ 0`, `∂_J T̂_(-b) ≠ 0`, and the
Jacobian of `(ζ + 2x, T̂_(-b))` is nonzero. -/
private theorem symbolTwistNeg_ebNode_twfNegEbFacts (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) :
    2 * m₀ ^ 2 * twNegNodeJ b - ((m₀ ^ 2) ^ 2 + 1) ≠ 0 ∧
      evalIntPoint (derivative (symbolTwistNeg b)) (m₀ ^ 2) (twNegNodeJ b) ≠ 0 ∧
      (2 * m₀ ^ 2 * twNegNodeJ b - ((m₀ ^ 2) ^ 2 + 1)) *
          evalIntPoint (coeffDerivative (symbolTwistNeg b)) (m₀ ^ 2) (twNegNodeJ b) -
        (twNegNodeJ b ^ 2 - 2 * m₀ ^ 2 * twNegNodeJ b + 2 * m₀ ^ 2 + 1 + 2) *
          evalIntPoint (derivative (symbolTwistNeg b)) (m₀ ^ 2) (twNegNodeJ b) ≠ 0 := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  obtain ⟨h4b, h10b, h8b⟩ := natCast_ne_zero_twfNegEbFacts b hb
  have h2b : 2 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((2 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  obtain ⟨hζ, -⟩ := twNeg_ebNode_zeta b hb heb
  have hJ : (2 * (b : ℂ) - 1) * twNegNodeJ b = -(2 * b + 1) := by
    rw [twNegNodeJ]
    field_simp
  generalize twNegNodeJ b = J at hζ hJ ⊢
  generalize m₀ ^ 2 = x at heb hζ ⊢
  obtain ⟨w, rfl⟩ : ∃ w, x = -w := ⟨-x, (neg_neg x).symm⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hb0 h2b (by linear_combination heb)
  rw [neg_neg] at hζ
  obtain ⟨-, hTJ, hTx⟩ := symbolTwistNeg_node_values hζ (by ring) hw0 b
  have hcrit : w + b * ((-w) ^ 2 + 1 - -w * J - w) = 0 := by
    refine mul_left_cancel₀ h2b ?_
    linear_combination heb + b * w * hJ
  have hDJ := dblRootDeriv_mul_of_crit (z₁ := - -w) (α := 2 * -w * J - ((-w) ^ 2 + 1)) (β := 0)
    hb hw0 hcrit
  have hDx := dblRootDeriv_mul_of_crit (z₁ := 2 * -w - J)
    (α := J ^ 2 - 2 * -w * J + 2 * -w + 1) (β := 2 * -w) hb hw0 hcrit
  rw [← hTJ] at hDJ
  rw [← hTx] at hDx
  generalize evalIntPoint (derivative (symbolTwistNeg b)) (-w) J = TJ at hDJ ⊢
  generalize evalIntPoint (coeffDerivative (symbolTwistNeg b)) (-w) J = Tx at hDx ⊢
  have hP : w ^ (b - 1) ≠ 0 := pow_ne_zero _ hw0
  generalize w ^ (b - 1) = P at hDJ hDx hP
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · refine mul_ne_zero h4b hw0 ?_
    linear_combination (b : ℂ) * (2 * b - 1) * h + heb + 2 * b * w * hJ
  · rw [h, mul_zero] at hDJ
    have h0 := (mul_eq_zero.1 hDJ.symm).resolve_left hP
    refine mul_ne_zero h10b (pow_ne_zero 2 hw0) ?_
    linear_combination (b : ℂ) * h0 + ((b : ℂ) - 1) * w * heb + 2 * b * ((b : ℂ) - 1) * w ^ 2 * hJ
  · have hbr : P * ((2 * -w * J - ((-w) ^ 2 + 1)) * (6 * b * w * (2 * -w - J) +
          ((b : ℂ) - 1) * (2 * b - 1) * (J ^ 2 - 2 * -w * J + 2 * -w + 1) * w -
          2 * ((b : ℂ) - 1) * (b + 1) * (2 * -w)) -
        (J ^ 2 - 2 * -w * J + 2 * -w + 1 + 2) * (6 * b * w * - -w +
          ((b : ℂ) - 1) * (2 * b - 1) * (2 * -w * J - ((-w) ^ 2 + 1)) * w -
          2 * ((b : ℂ) - 1) * (b + 1) * 0)) = 0 := by
      linear_combination 6 * w * h - (2 * -w * J - ((-w) ^ 2 + 1)) * hDx +
        (J ^ 2 - 2 * -w * J + 2 * -w + 1 + 2) * hDJ
    have h0 := (mul_eq_zero.1 hbr).resolve_left hP
    have hu : 2 * (b : ℂ) * (2 * b - 1) * (1 - w) + 1 = 0 := by
      have h6 : 6 * (2 * (b : ℂ) - 1) ^ 2 * w ^ 2 *
          (2 * (b : ℂ) * (2 * b - 1) * (1 - w) + 1) = 0 := by
        linear_combination -(b : ℂ) * (2 * b - 1) ^ 2 * h0 +
          6 * b * w * (2 * J * b ^ 2 * w - J * b * w + 6 * b ^ 2 * w ^ 2 - 6 * b ^ 2 * w +
            2 * b ^ 2 - 3 * b * w ^ 2 + 5 * b * w - b - 2 * w) * hJ +
          6 * w * (4 * b ^ 2 * w - 4 * b ^ 2 - 2 * b * w + 2 * b - 1) * heb
      exact (mul_eq_zero.1 h6).resolve_left
        (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h2b)) (pow_ne_zero 2 hw0))
    refine h8b ?_
    linear_combination -4 * (b : ℂ) * (2 * b - 1) * heb +
      (2 * (b : ℂ) * (2 * b - 1) * (1 - w) + 1) * hu

/-- The inner derivative of `1` vanishes. -/
private theorem innerDerivative_one_twfNegEbFacts : innerDerivative (1 : ℤ[X][X]) = 0 := by
  rw [← C_1, innerDerivative_C, derivative_one, C_0]

/-- The inner derivative of the outer variable vanishes. -/
private theorem innerDerivative_X_twfNegEbFacts : innerDerivative (X : ℤ[X][X]) = 0 := by
  rw [innerDerivative, sum_X_index] <;> simp

/-- The value and the first derivatives of `ζ + 2x` at a point. -/
private theorem evalIntPoint_symbolZeta_add_twfNegEbFacts (x₀ J₀ : ℂ) :
    evalIntPoint (symbolZeta + C (2 * X)) x₀ J₀ = evalIntPoint symbolZeta x₀ J₀ + 2 * x₀ ∧
      evalIntPoint (derivative (symbolZeta + C (2 * X))) x₀ J₀ = 2 * x₀ * J₀ - (x₀ ^ 2 + 1) ∧
      evalIntPoint (coeffDerivative (symbolZeta + C (2 * X))) x₀ J₀ =
        J₀ ^ 2 - 2 * x₀ * J₀ + 2 * x₀ + 1 + 2 := by
  have hdB : derivative (symbolZeta + C (2 * X) : ℤ[X][X]) = C (2 * X) * X - C (X ^ 2 + 1) := by
    simp only [symbolZeta, sq (X : ℤ[X][X]), derivative_add, derivative_sub, derivative_mul,
      derivative_C, derivative_X]
    simp only [C_mul, C_add, C_pow, C_1, C_ofNat]
    ring
  have hiB : innerDerivative (symbolZeta + C (2 * X) : ℤ[X][X]) =
      X ^ 2 - C (2 * X) * X + C (2 * X + 1) + 2 := by
    simp only [symbolZeta, sq (X : ℤ[X][X]), innerDerivative_sub, innerDerivative_add,
      innerDerivative_mul, innerDerivative_C, innerDerivative_X_twfNegEbFacts,
      sq (X : ℤ[X]), derivative_add, derivative_mul, derivative_X, derivative_one,
      derivative_ofNat]
    simp only [C_mul, C_add, C_1, C_0, C_ofNat]
    ring
  have hX : evalIntHomTwistNode x₀ J₀ X = J₀ := by
    simp [evalIntHomTwistNode]
  have hCX : evalIntHomTwistNode x₀ J₀ (C X) = x₀ := by
    simp [evalIntHomTwistNode]
  simp only [coeffDerivative_eq_innerDerivative, evalIntPoint_eq]
  rw [hdB, hiB]
  simp only [map_add, map_sub, map_mul, map_one, map_pow, map_ofNat, hX, hCX]
  exact ⟨trivial, trivial, by ring⟩

/-- Value and first derivatives of a multiple `C c * p` at a point. -/
private theorem evalIntPoint_C_mul_twfNegEbFacts (c : ℤ[X]) (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint (C c * p) m l = evalIntPoint (C c) m l * evalIntPoint p m l ∧
      evalIntPoint (derivative (C c * p)) m l =
        evalIntPoint (C c) m l * evalIntPoint (derivative p) m l ∧
      evalIntPoint (coeffDerivative (C c * p)) m l =
        evalIntPoint (C (derivative c)) m l * evalIntPoint p m l +
          evalIntPoint (C c) m l * evalIntPoint (coeffDerivative p) m l := by
  simp only [coeffDerivative_eq_innerDerivative, evalIntPoint_eq, derivative_C_mul,
    innerDerivative_mul, innerDerivative_C, map_mul, map_add]
  exact ⟨trivial, trivial, trivial⟩

/-- The values and derivatives at the `E/C_b` node used by the index criterion. -/
theorem twNeg_ebNode_facts (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) :
    m₀ ≠ 0 ∧ m₀ ^ 2 ≠ 1 ∧ m₀ ^ 2 ≠ -1 ∧ m₀ ^ 2 ≠ twNegNodeJ b ∧ m₀ ^ 2 * twNegNodeJ b ≠ 1 ∧
      twNegNodeL b m₀ ≠ 0 ∧ evalIntPoint (X - 1) m₀ (twNegNodeL b m₀) ≠ 0 ∧
      evalIntPoint extraFactor m₀ (twNegNodeL b m₀) = 0 ∧
      evalIntPoint (twistPolyNeg b) m₀ (twNegNodeL b m₀) = 0 ∧
      evalIntPoint (derivative extraFactor) m₀ (twNegNodeL b m₀) ≠ 0 ∧
      evalIntPoint (derivative (twistPolyNeg b)) m₀ (twNegNodeL b m₀) ≠ 0 ∧
      evalIntPoint (derivative extraFactor) m₀ (twNegNodeL b m₀) *
          evalIntPoint (coeffDerivative (twistPolyNeg b)) m₀ (twNegNodeL b m₀) -
        evalIntPoint (coeffDerivative extraFactor) m₀ (twNegNodeL b m₀) *
          evalIntPoint (derivative (twistPolyNeg b)) m₀ (twNegNodeL b m₀) ≠ 0 := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have h2b : 2 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((2 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  obtain ⟨h1, h2, hJ, hJ'⟩ := twNeg_ebNode_ne_twfNegEbFacts b hb heb
  obtain ⟨hζ, hT0⟩ := twNeg_ebNode_zeta b hb heb
  obtain ⟨hζJ, hTJ, hJac⟩ := symbolTwistNeg_ebNode_twfNegEbFacts b hb heb
  obtain ⟨hf, hfJ, hfx⟩ := evalIntPoint_symbolZeta_add_twfNegEbFacts (m₀ ^ 2) (twNegNodeJ b)
  have hf0 : evalIntPoint (symbolZeta + C (2 * X)) (m₀ ^ 2) (twNegNodeJ b) = 0 := by
    rw [hf, hζ]
    ring
  have hx0 : m₀ ^ 2 ≠ 0 := by
    intro h
    rw [h] at heb
    exact mul_ne_zero hb0 h2b (by linear_combination heb)
  have hm0 : m₀ ≠ 0 := fun h ↦ hx0 (by rw [h]; ring)
  have hJ1 : twNegNodeJ b ≠ 1 := by
    intro h
    have hJrel : (2 * (b : ℂ) - 1) * twNegNodeJ b = -(2 * b + 1) := by
      rw [twNegNodeJ]
      field_simp
    rw [h] at hJrel
    exact hb0 (by linear_combination (1 / 4 : ℂ) * hJrel)
  have hs : m₀ ^ 2 + 1 ≠ 0 := fun h ↦ h2 (by linear_combination h)
  have hx2 : (m₀ ^ 2) ^ 2 - 1 ≠ 0 := by
    intro h
    have h' : (m₀ ^ 2 - 1) * (m₀ ^ 2 + 1) = 0 := by linear_combination h
    exact mul_ne_zero (sub_ne_zero.2 h1) hs h'
  have hlrel : twNegNodeL b m₀ * (twNegNodeJ b - m₀ ^ 2) = 1 - m₀ ^ 2 * twNegNodeJ b := by
    rw [twNegNodeL, famNodeL]
    exact div_mul_cancel₀ _ (sub_ne_zero.2 (Ne.symm hJ))
  generalize twNegNodeL b m₀ = l at hlrel ⊢
  generalize twNegNodeJ b = J at *
  have hJl : J * (l + m₀ ^ 2) = m₀ ^ 2 * l + 1 := by linear_combination hlrel
  have hlx : l + m₀ ^ 2 ≠ 0 := by
    intro h
    exact hx2 (by linear_combination hlrel - (J - m₀ ^ 2) * h)
  have hdeg := natDegree_symbolTwistNeg_le b hb
  have hE := evalIntPoint_twfPullback 2 _ natDegree_symbolZeta_add_le hJl
  have hEL := evalIntPoint_derivative_twfPullback 2 _ natDegree_symbolZeta_add_le hJl hf0
  have hC := evalIntPoint_twfPullback (2 * b - 1) _ hdeg hJl
  have hCL := evalIntPoint_derivative_twfPullback (2 * b - 1) _ hdeg hJl hT0
  have hjac := twfPullback_jacobian 2 (2 * b - 1) _ _ natDegree_symbolZeta_add_le hdeg hJl hf0 hT0
  obtain ⟨hcE, hcEL, hcEM⟩ := evalIntPoint_C_mul_twfNegEbFacts ((X ^ 2 + 1) ^ 2) extraFactor m₀ l
  have hc : evalIntPoint (C ((X ^ 2 + 1) ^ 2) : ℤ[X][X]) m₀ l = (m₀ ^ 2 + 1) ^ 2 := by
    rw [evalIntPoint_eq]
    simp only [evalIntHomTwistNode, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
      coe_eval₂RingHom, eval₂_C, coe_evalRingHom, eval_pow, eval_X, eval_add, eval_one]
  rw [twfPullback_symbolZeta_add] at hE hEL hjac
  rw [twfPullback_symbolTwistNeg] at hC hCL hjac
  rw [hcE, hc, hf0, mul_zero] at hE
  have hE0 : evalIntPoint extraFactor m₀ l = 0 :=
    (mul_eq_zero.1 hE).resolve_left (pow_ne_zero 2 hs)
  rw [hcEL, hc, hfJ] at hEL
  rw [hcEL, hcEM, hc, hE0, mul_zero, zero_add, hfJ, hfx] at hjac
  refine ⟨hm0, h1, h2, hJ, hJ', ?_, ?_, hE0, ?_, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro rfl
    exact hJ' (by linear_combination hlrel)
  · rw [evalIntPoint_eq]
    simp only [evalIntHomTwistNode, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one, coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_one]
    intro h
    have h' : (J - 1) * (m₀ ^ 2 + 1) = 0 := by linear_combination hlrel - (J - m₀ ^ 2) * h
    exact mul_ne_zero (sub_ne_zero.2 hJ1) hs h'
  · rw [hC, hT0, mul_zero]
  · rw [h, mul_zero, mul_zero] at hEL
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hlx) hx2) hζJ hEL.symm
  · rw [h, mul_zero] at hCL
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hlx) hx2) hTJ hCL.symm
  · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hm0)
      (pow_ne_zero (2 + (2 * b - 1)) hlx)) hx2) hJac ?_
    linear_combination (l + m₀ ^ 2) ^ 2 * (m₀ ^ 2 + 1) ^ 2 * h - hjac

end AJConjecture
