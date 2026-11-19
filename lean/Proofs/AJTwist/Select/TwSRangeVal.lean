import Mathlib
import AJTwist.Select.TwSSelects
import AJTwist.Select.TwSValTransferZero
import AJTwist.Select.TwSValTransferInf
import AJTwist.Select.TwSValActual

/-!
# Selection by colour growth: `η = +1, a ≥ 1` and `η = -1, a < 0`

Source: Sections 6.1 and 6.2 of `selection.tex` (revision 5), the first two rows of Table 1.

* Right-handed companion, `a = r s - ℓ ≥ 1`: the class is `ord_t ≥ -max(2, -4ℓ) N² - O(N)`
  (`ν ≥ -h N² - O(N)` for `ℓ = -h < 0`, `ν ≥ -N²/2 - O(N)` for `ℓ ≥ 0`), and
  `ord_t F_N = -4 (N-1)(a N - 1)` with `4a > max(2, -4ℓ)`.
* Mirror companion, `a = -r s - ℓ < 0`, `b = -a`: the class is
  `deg_t ≤ max(4, 4ℓ+2) N² + O(N)`, and `deg_t F_N = (4b+2) N (N-1)` with
  `4b + 2 > max(4, 4ℓ+2)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A class of sequences is contained in its saturation. -/
private theorem twsSat_of_mem_twsRangeVal {U : (ℤ → RatFunc ℚ) → Prop} {g : ℤ → RatFunc ℚ}
    (h : U g) : TwsSat U g := by
  refine ⟨1, one_ne_zero, ?_⟩
  have heq : (fun n ↦ evalAtField n 1 * g n) = g := funext fun n ↦ by rw [map_one, one_mul]
  rwa [heq]

/-- Selection for the right-handed companion at `a ≥ 1` (Section 6.1). -/
theorem tws_selects_pos_ge_one (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ)
    (ha : 1 ≤ twIndex true r s ℓ) : TwsSelects ℓ (twsInput true r s ℓ) := by
  have hrs : (0 : ℤ) < ((r * s : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hidx : twIndex true r s ℓ = ((r * s : ℕ) : ℤ) - ℓ := by
    simp only [twIndex, ↓reduceIte]
  refine ⟨TwsValClass pairQTOrder (max 2 (-(4 * ℓ))),
    TwsValClass.growthClass twsOrd_tOrder _,
    fun c ↦ twsSat_of_mem_twsRangeVal (tws_valClass_tOrder_period ℓ c),
    tws_not_sat_valClass twsOrd_tOrder (p' := 4 * twIndex true r s ℓ)
      (max_lt (by omega) (by omega)) ⟨4 * (twIndex true r s ℓ + 1), 1, fun n hn ↦ ?_⟩⟩
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
  have h := tws_tOrder_reducedFormula_of_input ha (tws_tOrder_input_true r s hr hs ℓ)
    (N := N) (by omega)
  rw [pairQReducedFormulaEven, Int.natAbs_natCast]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  nlinarith

/-- Selection for the mirror companion at `a < 0` (Section 6.2). -/
theorem tws_selects_neg_lt_zero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ)
    (ha : twIndex false r s ℓ < 0) : TwsSelects ℓ (twsInput false r s ℓ) := by
  have hrs : (0 : ℤ) < ((r * s : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hidx : twIndex false r s ℓ = -((r * s : ℕ) : ℤ) - ℓ := by
    simp only [twIndex, Bool.false_eq_true, ↓reduceIte]
  have hu : ∀ n : ℕ, twsInput false r s ℓ n ≠ 0 ∧ (twsInput false r s ℓ n).intDegree =
      4 * (-twIndex false r s ℓ) * n * ((n : ℤ) + 1) := fun n ↦ by
    have h := tws_intDegree_input_false r s hr hs ℓ n
    exact ⟨h.1, h.2.trans (by ring)⟩
  refine ⟨TwsValClass (fun f : RatFunc ℚ ↦ -f.intDegree) (max 4 (4 * ℓ + 2)),
    TwsValClass.growthClass twsOrd_negIntDegree _,
    fun c ↦ twsSat_of_mem_twsRangeVal (tws_valClass_inf_period ℓ c),
    tws_not_sat_valClass twsOrd_negIntDegree (p' := 4 * (-twIndex false r s ℓ) + 2)
      (max_lt (by omega) (by omega)) ⟨4 * (-twIndex false r s ℓ) + 2, 1, fun n hn ↦ ?_⟩⟩
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
  have h := tws_intDegree_reducedFormula_of_input (b := -twIndex false r s ℓ) (by omega) hu
    (N := N) (by omega)
  rw [pairQReducedFormulaEven, Int.natAbs_natCast]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  nlinarith

end AJConjecture
