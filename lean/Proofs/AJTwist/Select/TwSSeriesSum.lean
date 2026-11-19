import Mathlib
import AJTwist.Select.TwSCtrlDefs

/-!
# Convergent sums in `ℚ((t))`

Source: Lemma 6.2 (`lem:coefficient-cutoff`) of `selection.tex` (revision 5): "the sums defining
`A_{θ,d}(w)` converge in `ℚ((q))`". A family `s : ℕ → ℚ((t))` whose orders tend to infinity
(`TwsSummable`) has a sum `twsSum s`, computed coefficient by coefficient.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The orders of the terms of the family tend to infinity. -/
def TwsSummable (s : ℕ → LaurentSeries ℚ) : Prop :=
  ∀ g : ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → s n = 0 ∨ g < (s n).order

open Classical in
/-- The sum of a family of Laurent series, coefficient by coefficient (the junk value `0` if the
support of the coefficientwise sum is not bounded below; for a `TwsSummable` family it is the
sum). -/
def twsSum (s : ℕ → LaurentSeries ℚ) : LaurentSeries ℚ :=
  if h : BddBelow (Function.support fun g : ℤ ↦ ∑ᶠ n, (s n).coeff g) then
    HahnSeries.ofSuppBddBelow _ h
  else 0

/-- For a summable family, the coefficients of degree at most `g` vanish from some index on. -/
private theorem coeff_eq_zero_tail_seriesSum {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s)
    (g : ℤ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ g' : ℤ, g' ≤ g → (s n).coeff g' = 0 := by
  obtain ⟨n₀, h⟩ := hs g
  refine ⟨n₀, fun n hn g' hg' ↦ ?_⟩
  rcases h n hn with h0 | hlt
  · rw [h0, HahnSeries.coeff_zero]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_le_of_lt hg' hlt)

/-- Finitely many series have a common lower bound for their supports. -/
private theorem coeff_eq_zero_head_seriesSum (s : ℕ → LaurentSeries ℚ) (N : ℕ) :
    ∃ b : ℤ, ∀ n : ℕ, n < N → ∀ g : ℤ, g < b → (s n).coeff g = 0 := by
  induction N with
  | zero => exact ⟨0, fun n hn ↦ absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨min b (s N).order, fun n hn g hg ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | rfl
    · exact hb n hlt g (lt_of_lt_of_le hg (min_le_left _ _))
    · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hg (min_le_right _ _))

/-- The supports of a summable family have a common lower bound. -/
private theorem coeff_eq_zero_of_lt_seriesSum {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s) :
    ∃ b : ℤ, ∀ (n : ℕ) (g : ℤ), g < b → (s n).coeff g = 0 := by
  obtain ⟨n₀, h₀⟩ := coeff_eq_zero_tail_seriesSum hs 0
  obtain ⟨b, hb⟩ := coeff_eq_zero_head_seriesSum s n₀
  refine ⟨min b 0, fun n g hg ↦ ?_⟩
  rcases lt_or_ge n n₀ with hn | hn
  · exact hb n hn g (lt_of_lt_of_le hg (min_le_left _ _))
  · exact h₀ n hn g (le_of_lt (lt_of_lt_of_le hg (min_le_right _ _)))

/-- The coefficientwise sum of a summable family has support bounded below. -/
private theorem bddBelow_support_seriesSum {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s) :
    BddBelow (Function.support fun g : ℤ ↦ ∑ᶠ n, (s n).coeff g) := by
  obtain ⟨b, hb⟩ := coeff_eq_zero_of_lt_seriesSum hs
  refine ⟨b, fun g hg ↦ ?_⟩
  by_contra hlt
  exact hg (finsum_eq_zero_of_forall_eq_zero fun n ↦ hb n g (not_le.mp hlt))

/-- The coefficients of the sum of a summable family. -/
theorem twsSum_coeff {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s) (g : ℤ) :
    (twsSum s).coeff g = ∑ᶠ n, (s n).coeff g := by
  rw [twsSum, dite_eq_left (bddBelow_support_seriesSum hs), HahnSeries.coeff_ofSuppBddBelow]

/-- A coefficient of the sum of a summable family is a finite sum. -/
private theorem twsSum_coeff_eq_sum_seriesSum {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s)
    {g : ℤ} {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → (s n).coeff g = 0) :
    (twsSum s).coeff g = ∑ n ∈ Finset.range N, (s n).coeff g := by
  rw [twsSum_coeff hs]
  refine finsum_eq_sum_of_support_subset _ fun n hn ↦ ?_
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hle
  exact hn (hN n (not_lt.mp hle))

/-- A tail of a summable family is summable. -/
private theorem twsSummable_shift_seriesSum {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s)
    (N : ℕ) : TwsSummable fun n ↦ s (n + N) := fun g ↦ by
  obtain ⟨n₀, h⟩ := hs g
  exact ⟨n₀, fun n hn ↦ h (n + N) (le_trans hn (Nat.le_add_right n N))⟩

/-- Splitting off the first `N` terms. -/
theorem twsSum_eq_sum_add {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s) (N : ℕ) :
    twsSum s = ∑ n ∈ Finset.range N, s n + twsSum fun n ↦ s (n + N) := by
  refine HahnSeries.ext (funext fun g ↦ ?_)
  obtain ⟨n₀, h₀⟩ := coeff_eq_zero_tail_seriesSum hs g
  rw [HahnSeries.coeff_add, HahnSeries.coeff_sum,
    twsSum_coeff_eq_sum_seriesSum hs (N := N + n₀) fun n hn ↦
      h₀ n (le_trans (Nat.le_add_left n₀ N) hn) g le_rfl,
    twsSum_coeff_eq_sum_seriesSum (twsSummable_shift_seriesSum hs N) (N := n₀) fun n hn ↦
      h₀ (n + N) (le_trans hn (Nat.le_add_right n N)) g le_rfl,
    Finset.sum_range_add]
  simp only [add_comm N]

/-- A lower bound for the order of a sum. -/
theorem le_orderTop_twsSum {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s) {d : ℤ}
    (h : ∀ n : ℕ, (d : WithTop ℤ) ≤ (s n).orderTop) : (d : WithTop ℤ) ≤ (twsSum s).orderTop := by
  refine HahnSeries.le_orderTop_iff_forall.mpr fun j hj ↦ ?_
  rw [twsSum_coeff hs]
  exact finsum_eq_zero_of_forall_eq_zero fun n ↦
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le hj (h n))

/-- A sum with a unique term of least order has that order. -/
theorem order_twsSum_eq {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s) {n₀ : ℕ}
    (h0 : s n₀ ≠ 0) (hmin : ∀ n : ℕ, n ≠ n₀ → s n = 0 ∨ (s n₀).order < (s n).order) :
    twsSum s ≠ 0 ∧ (twsSum s).order = (s n₀).order := by
  have hother : ∀ n : ℕ, n ≠ n₀ → ∀ g : ℤ, g ≤ (s n₀).order → (s n).coeff g = 0 := by
    intro n hn g hg
    rcases hmin n hn with hz | hlt
    · rw [hz, HahnSeries.coeff_zero]
    · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_le_of_lt hg hlt)
  have hc : (twsSum s).coeff (s n₀).order ≠ 0 := by
    rw [twsSum_coeff hs, finsum_eq_single _ n₀ fun n hn ↦ hother n hn _ le_rfl]
    exact fun h ↦ h0 (HahnSeries.coeff_order_eq_zero.mp h)
  have hne : twsSum s ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hc
  refine ⟨hne, le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc)
    ((HahnSeries.le_order_iff_forall hne).mpr fun j hj ↦ ?_)⟩
  rw [twsSum_coeff hs]
  refine finsum_eq_zero_of_forall_eq_zero fun n ↦ ?_
  by_cases hn : n = n₀
  · rw [hn]
    exact HahnSeries.coeff_eq_zero_of_lt_order hj
  · exact hother n hn j hj.le

end AJConjecture
