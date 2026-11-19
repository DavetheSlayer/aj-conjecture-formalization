import Mathlib
import AJConjecture.WhiteheadFormula
import AJConjecture.QAlgOpApplyFieldBasic

/-!
# I-CTRL: the explicitly selected two-sided toy sequence

With `q = t²` transcendental, `f₀ = f₁ = 1` and
`f_(n+2) - 2 f_(n+1) + q^n (2 - q^n) f_n = 0` (equation (9) of the source) for every integer `n`.
Every coefficient `q^n (2 - q^n)` is nonzero in `ℚ(t)`, so the recursion runs in both directions
and defines a two-sided sequence; it is not eventually zero (two consecutive zeros would propagate
back to `f₀ = f₁ = 0`). In the library's conventions (`M` acts by `t^(2n) = q^n`) the operator is
`L² - 2 L + M(2 - M)` (`toyRecOp`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The toy recurrence operator `L² - 2 L + M(2 - M)` over `ℤ[t][M]`. -/
def toyRecOp : RecOp := X ^ 2 - C 2 * X + C ((X : Coeff) * (2 - X))

/-- The forward values `f_0, f_1, f_2, …`. -/
def toySeqFwd : ℕ → RatFunc ℚ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * toySeqFwd (n + 1) -
      RatFunc.X ^ (2 * n) * (2 - RatFunc.X ^ (2 * n)) * toySeqFwd n

/-- The backward values: `toySeqBwd k = f_(1-k)`, so `f_1, f_0, f_(-1), …`. -/
def toySeqBwd : ℕ → RatFunc ℚ
  | 0 => 1
  | 1 => 1
  | k + 2 => (2 * toySeqBwd (k + 1) - toySeqBwd k) /
      (RatFunc.X ^ (2 * (-(k : ℤ) - 1)) * (2 - RatFunc.X ^ (2 * (-(k : ℤ) - 1))))

/-- The two-sided toy sequence. -/
def toySeq (n : ℤ) : RatFunc ℚ :=
  if 0 ≤ n then toySeqFwd n.toNat else toySeqBwd (1 - n).toNat

/-- The integer degree of `X ^ j` in `ℚ(t)` is `j`. -/
private theorem intDegree_X_zpow_toy (j : ℤ) :
    RatFunc.intDegree (RatFunc.X ^ j : RatFunc ℚ) = j := by
  induction j using Int.induction_on with
  | zero => simp
  | succ j ih =>
    rw [zpow_add_one₀ RatFunc.X_ne_zero, RatFunc.intDegree_mul (zpow_ne_zero _ RatFunc.X_ne_zero)
      RatFunc.X_ne_zero, ih, RatFunc.intDegree_X]
  | pred j ih =>
    rw [zpow_sub_one₀ RatFunc.X_ne_zero, RatFunc.intDegree_mul (zpow_ne_zero _ RatFunc.X_ne_zero)
      (inv_ne_zero RatFunc.X_ne_zero), ih, RatFunc.intDegree_inv, RatFunc.intDegree_X]
    ring

/-- The toy coefficient `q^j (2 - q^j)` is nonzero for `j ≠ 0`. -/
private theorem toyCoeff_ne_zero {j : ℤ} (hj : j ≠ 0) :
    (RatFunc.X ^ (2 * j) * (2 - RatFunc.X ^ (2 * j)) : RatFunc ℚ) ≠ 0 := by
  refine mul_ne_zero (zpow_ne_zero _ RatFunc.X_ne_zero) (sub_ne_zero.mpr fun h ↦ ?_)
  have h2 := congrArg RatFunc.intDegree h
  rw [intDegree_X_zpow_toy, ← map_ofNat RatFunc.C 2, RatFunc.intDegree_C] at h2
  omega

/-- The action of the toy operator. -/
private theorem opApplyField_toyRecOp_eq (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField toyRecOp f n = f (n + 2) - 2 * f (n + 1) +
      RatFunc.X ^ (2 * n) * (2 - RatFunc.X ^ (2 * n)) * f n := by
  have h : toyRecOp = monomial 2 1 - monomial 1 2 + monomial 0 ((X : Coeff) * (2 - X)) := by
    simp only [toyRecOp, ← C_mul_X_pow_eq_monomial, map_one, one_mul, pow_one, pow_zero, mul_one]
  rw [h, opApplyField_add_left, opApplyField_sub_left, opApplyField_monomial,
    opApplyField_monomial, opApplyField_monomial]
  simp [evalAtField]

/-- Nonnegative colours use the forward values. -/
private theorem toySeq_natCast (m : ℕ) : toySeq m = toySeqFwd m := by
  simp [toySeq]

/-- Colours `≤ 1` use the backward values. -/
private theorem toySeq_one_sub (k : ℕ) : toySeq (1 - k) = toySeqBwd k := by
  rcases k with _ | _ | k
  · simp [toySeq, toySeqFwd, toySeqBwd]
  · simp [toySeq, toySeqFwd, toySeqBwd]
  · have h : ¬ (0 : ℤ) ≤ 1 - ((k + 2 : ℕ) : ℤ) := by omega
    simp only [toySeq, h, ↓reduceIte]
    congr 1
    omega

theorem toySeq_zero_one : toySeq 0 = 1 ∧ toySeq 1 = 1 := by
  simp [toySeq, toySeqFwd]

/-- The toy operator annihilates the sequence at every integer colour. -/
theorem opApplyField_toyRecOp_toySeq (n : ℤ) : opApplyField toyRecOp toySeq n = 0 := by
  rw [opApplyField_toyRecOp_eq]
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · have h2 : (m : ℤ) + 2 = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
    have h1 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, h1, toySeq_natCast, toySeq_natCast, toySeq_natCast, toySeqFwd]
    have hz : (RatFunc.X : RatFunc ℚ) ^ (2 * (m : ℤ)) = RatFunc.X ^ (2 * m) := by
      rw [← zpow_natCast]
      push_cast
      rfl
    rw [hz]
    ring
  · rcases m with _ | k
    · simp [toySeq, toySeqFwd]
    · have e2 : -((k + 1 : ℕ) : ℤ) + 2 = 1 - (k : ℕ) := by push_cast; ring
      have e1 : -((k + 1 : ℕ) : ℤ) + 1 = 1 - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      have e0 : -((k + 1 : ℕ) : ℤ) = 1 - ((k + 2 : ℕ) : ℤ) := by push_cast; ring
      have ec : -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 := by push_cast; ring
      rw [e2, e1, toySeq_one_sub, toySeq_one_sub, e0, toySeq_one_sub, toySeqBwd, ← e0, ec,
        mul_div_cancel₀ _ (toyCoeff_ne_zero (by omega))]
      ring

theorem toySeq_not_eventually_zero : ¬ ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → toySeq n = 0 := by
  rintro ⟨n₀, hn₀⟩
  have key : ∀ m : ℕ, ∀ n : ℤ, n₀ - m ≤ n → 1 ≤ n → toySeq n = 0 := by
    intro m
    induction m with
    | zero => exact fun n hn _ ↦ hn₀ n (by simpa using hn)
    | succ m ih =>
      intro n hn h1
      by_cases hlt : n₀ - m ≤ n
      · exact ih n hlt h1
      · have hrec := opApplyField_toyRecOp_toySeq n
        rw [opApplyField_toyRecOp_eq, ih (n + 2) (by omega) (by omega),
          ih (n + 1) (by omega) (by omega)] at hrec
        have hmul :
            (RatFunc.X ^ (2 * n) * (2 - RatFunc.X ^ (2 * n)) : RatFunc ℚ) * toySeq n = 0 := by
          linear_combination hrec
        exact (mul_eq_zero.mp hmul).resolve_left (toyCoeff_ne_zero (by omega))
  have h1 := key n₀.toNat 1 (by omega) le_rfl
  rw [toySeq_zero_one.2] at h1
  exact one_ne_zero h1

/-- The action of the toy operator: `f(n+2) - 2 f(n+1) + q^n (2 - q^n) f(n)`. -/
theorem opApplyField_toyRecOp_apply (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField toyRecOp f n = f (n + 2) - 2 * f (n + 1) +
      RatFunc.X ^ (2 * n) * (2 - RatFunc.X ^ (2 * n)) * f n :=
  opApplyField_toyRecOp_eq f n

/-- The integer degree of `t ^ j` in `ℚ(t)` is `j`. -/
theorem intDegree_ratFunc_X_zpow (j : ℤ) :
    RatFunc.intDegree (RatFunc.X ^ j : RatFunc ℚ) = j :=
  intDegree_X_zpow_toy j

end AJConjecture
