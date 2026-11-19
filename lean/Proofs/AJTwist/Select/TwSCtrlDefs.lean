import Mathlib
import AJHandoff.TorusQuantum.PairQTOrder
import AJTwist.Select.TwSGrowthClass

/-!
# Controlled expansions on a tail

Source: Section 6.4 of `selection.tex` (revision 5), "Controlled expansions on a tail": an
expansion `∑_{j ≥ j₀} c_j(t) M^j` of a sequence is *controlled* if, for every cutoff `J`,
subtracting its terms `j < J` evaluated at `M = t^(2N)` from the sequence leaves a remainder of
`t`-order at least `2 J N - O_J(1)`. Equality on a tail then implies equality of the coefficients.

The coefficients `c_j` are Laurent series in `t` (the coefficients produced by the finite-cutoff
lemma are infinite sums in `ℚ((q))`, `q = t⁴`), so sequences `ℤ → ℚ(t)` are compared inside
`ℚ((t))` through `twsSeries`.

* `twsSeries`: the expansion `ℚ(t) → ℚ((t))` at `t = 0`; `twsT k = t^k`.
* `TwsCtrl c g`: `c` is a controlled expansion of the sequence `g : ℤ → ℚ((t))`.
* `TwsCtrlAll`: the sequences `ℤ → ℚ(t)` with a controlled expansion.
* `TwsCtrlB D`: those whose coefficients satisfy `D · ord_t c_j ≥ -(j² + C |j| + C)` for some `C`
  (the quadratic coefficient bounds `-d_M² / [2 (2γ+1)]` and `-d_M² / [4 (γ+1)]` of Sections 6.5
  and 6.6, with `D = 2 (2γ+1)` and `D = 4 (γ+1)`).
* `TwsCtrl.unique`: the coefficients are determined by the sequence.
* `tws_order_twsSeries`: the order of the expansion is the order `pairQTOrder` at `t = 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

open scoped RatFunc in
/-- The expansion of a rational function at `t = 0`, in `ℚ((t))`: Mathlib's
`algebraMap (RatFunc ℚ) ℚ⸨X⸩` (the coercion `RatFunc.coeToLaurentSeries`; the algebra structure is
the scoped instance `RatFunc.liftAlgebra`). -/
def twsSeries : RatFunc ℚ →+* LaurentSeries ℚ :=
  algebraMap (RatFunc ℚ) (LaurentSeries ℚ)

/-- The monomial `t^k` of `ℚ((t))`. -/
def twsT (k : ℤ) : LaurentSeries ℚ :=
  HahnSeries.single k (1 : ℚ)

/-- `c` is a controlled expansion of the sequence `g`: the coefficients vanish below some degree
`j₀`, and for every cutoff `J` the remainder `g(n) - ∑_{j₀ ≤ j < J} c_j t^(2 n j)` has order at
least `2 J n - C` on a tail, with `C` depending on `J`. -/
def TwsCtrl (c : ℤ → LaurentSeries ℚ) (g : ℤ → LaurentSeries ℚ) : Prop :=
  ∃ j₀ : ℤ, (∀ j : ℤ, j < j₀ → c j = 0) ∧ ∀ J : ℤ, ∃ C n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
    ((2 * J * n - C : ℤ) : WithTop ℤ) ≤
      (g n - ∑ j ∈ Finset.Ico j₀ J, c j * twsT (2 * n * j)).orderTop

/-- The sequences `ℤ → ℚ(t)` that have a controlled expansion. -/
def TwsCtrlAll (g : ℤ → RatFunc ℚ) : Prop :=
  ∃ c : ℤ → LaurentSeries ℚ, TwsCtrl c fun n ↦ twsSeries (g n)

/-- The sequences `ℤ → ℚ(t)` that have a controlled expansion whose coefficients satisfy
`D · ord_t c_j ≥ -(j² + C |j| + C)` for some `C`. -/
def TwsCtrlB (D : ℕ) (g : ℤ → RatFunc ℚ) : Prop :=
  ∃ c : ℤ → LaurentSeries ℚ, (TwsCtrl c fun n ↦ twsSeries (g n)) ∧
    ∃ C : ℤ, ∀ j : ℤ, c j = 0 ∨ -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (c j).order

open scoped RatFunc in
/-- The coefficients of the expansion of a polynomial. -/
private theorem coeff_twsSeries_algebraMap_ctrlDefs (p : ℚ[X]) (i : ℤ) :
    (twsSeries (algebraMap ℚ[X] (RatFunc ℚ) p)).coeff i =
      if i < 0 then 0 else p.coeff i.natAbs := by
  have h : twsSeries (algebraMap ℚ[X] (RatFunc ℚ) p) = ((p : PowerSeries ℚ) : LaurentSeries ℚ) :=
    (RatFunc.coe_coe p).symm
  rw [h, PowerSeries.coeff_coe, Polynomial.coeff_coe]

/-- The expansion of a nonzero rational function is nonzero. -/
private theorem twsSeries_ne_zero_ctrlDefs {f : RatFunc ℚ} (hf : f ≠ 0) : twsSeries f ≠ 0 :=
  (map_ne_zero twsSeries).mpr hf

/-- The order of the expansion of a nonzero polynomial is its order at `t = 0`. -/
private theorem order_twsSeries_algebraMap_ctrlDefs {p : ℚ[X]} (hp : p ≠ 0) :
    (twsSeries (algebraMap ℚ[X] (RatFunc ℚ) p)).order = (p.natTrailingDegree : ℤ) := by
  have h0 : twsSeries (algebraMap ℚ[X] (RatFunc ℚ) p) ≠ 0 :=
    twsSeries_ne_zero_ctrlDefs ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hp)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_)
    ((HahnSeries.le_order_iff_forall h0).mpr fun j hj ↦ ?_)
  · rw [coeff_twsSeries_algebraMap_ctrlDefs]
    split_ifs with h
    · lia
    · rw [Int.natAbs_natCast]
      exact Polynomial.trailingCoeff_ne_zero.mpr hp
  · rw [coeff_twsSeries_algebraMap_ctrlDefs]
    split_ifs with h
    · rfl
    · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by lia)

/-- The order of the expansion at `t = 0` of a nonzero rational function is its order at
`t = 0`. -/
theorem tws_order_twsSeries {f : RatFunc ℚ} (hf : f ≠ 0) :
    (twsSeries f).order = pairQTOrder f := by
  have hn := RatFunc.num_ne_zero hf
  have hd := RatFunc.denom_ne_zero f
  have hd' := (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hd
  have h : twsSeries f * twsSeries (algebraMap ℚ[X] (RatFunc ℚ) f.denom) =
      twsSeries (algebraMap ℚ[X] (RatFunc ℚ) f.num) := by
    rw [← map_mul, (eq_div_iff hd').mp (RatFunc.num_div_denom f).symm]
  have h2 := congrArg HahnSeries.order h
  rw [HahnSeries.order_mul (twsSeries_ne_zero_ctrlDefs hf) (twsSeries_ne_zero_ctrlDefs hd'),
    order_twsSeries_algebraMap_ctrlDefs hd, order_twsSeries_algebraMap_ctrlDefs hn] at h2
  unfold pairQTOrder
  lia

open scoped RatFunc in
/-- The expansion of `t^k`. -/
theorem twsSeries_X_zpow (k : ℤ) : twsSeries ((RatFunc.X : RatFunc ℚ) ^ k) = twsT k := by
  rw [map_zpow₀, twsT, RatFunc.single_zpow]
  congr 1
  exact RatFunc.coe_X

/-- The order of a product with a monomial. -/
private theorem orderTop_mul_twsT_ctrlDefs (x : LaurentSeries ℚ) (k : ℤ) :
    (x * twsT k).orderTop = x.orderTop + (k : WithTop ℤ) := by
  rw [HahnSeries.orderTop_mul, twsT, HahnSeries.orderTop_single one_ne_zero]

/-- The lower end of a truncated sum may be moved down. -/
private theorem sum_Ico_eq_of_le_ctrlDefs {c : ℤ → LaurentSeries ℚ} {j₀ j₁ : ℤ}
    (h₀ : ∀ j : ℤ, j < j₀ → c j = 0) (hle : j₁ ≤ j₀) (J : ℤ) (x : ℤ → LaurentSeries ℚ) :
    ∑ j ∈ Finset.Ico j₀ J, c j * x j = ∑ j ∈ Finset.Ico j₁ J, c j * x j := by
  refine Finset.sum_subset (Finset.Ico_subset_Ico_left hle) fun j hj hj' ↦ ?_
  rw [Finset.mem_Ico] at hj hj'
  rw [h₀ j (by lia), zero_mul]

/-- The truncated sums do not depend on the degree below which the coefficients vanish. -/
private theorem sum_Ico_rebase_ctrlDefs {c : ℤ → LaurentSeries ℚ} {j₀ j₁ : ℤ}
    (h₀ : ∀ j : ℤ, j < j₀ → c j = 0) (h₁ : ∀ j : ℤ, j < j₁ → c j = 0) (J : ℤ)
    (x : ℤ → LaurentSeries ℚ) :
    ∑ j ∈ Finset.Ico j₀ J, c j * x j = ∑ j ∈ Finset.Ico j₁ J, c j * x j := by
  rw [sum_Ico_eq_of_le_ctrlDefs h₀ (min_le_left j₀ j₁),
    sum_Ico_eq_of_le_ctrlDefs h₁ (min_le_right j₀ j₁)]

/-- The remainder estimates of a controlled expansion, with the truncated sums starting at any
degree below which the coefficients vanish. -/
private theorem twsCtrl_bound_of_vanish_ctrlDefs {c : ℤ → LaurentSeries ℚ}
    {g : ℤ → LaurentSeries ℚ} (h : TwsCtrl c g) {j₁ : ℤ} (h₁ : ∀ j : ℤ, j < j₁ → c j = 0)
    (J : ℤ) :
    ∃ C n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ((2 * J * n - C : ℤ) : WithTop ℤ) ≤
      (g n - ∑ j ∈ Finset.Ico j₁ J, c j * twsT (2 * n * j)).orderTop := by
  obtain ⟨j₀, h₀, hJ⟩ := h
  obtain ⟨C, n₀, hC⟩ := hJ J
  refine ⟨C, n₀, fun n hn ↦ ?_⟩
  rw [sum_Ico_rebase_ctrlDefs h₁ h₀]
  exact hC n hn

/-- A sequence has at most one controlled expansion. -/
theorem TwsCtrl.unique {c c' : ℤ → LaurentSeries ℚ} {g : ℤ → LaurentSeries ℚ}
    (h : TwsCtrl c g) (h' : TwsCtrl c' g) : c = c' := by
  by_contra hne
  obtain ⟨j₀, h₀, -⟩ := id h
  obtain ⟨j₀', h₀', -⟩ := id h'
  have hbdd : ∀ z : ℤ, c z ≠ c' z → min j₀ j₀' ≤ z := by
    intro z hz
    by_contra hlt
    rw [not_le, lt_min_iff] at hlt
    exact hz (by rw [h₀ z hlt.1, h₀' z hlt.2])
  obtain ⟨j₁, hj₁, hmin⟩ := Int.exists_least_of_bdd ⟨_, hbdd⟩ (Function.ne_iff.mp hne)
  have hmj := hbdd j₁ hj₁
  have hlow : ∀ j : ℤ, j < j₁ → c j = c' j := fun j hj ↦ by
    by_contra hcj
    exact absurd (hmin j hcj) (not_le.mpr hj)
  set m := min j₀ j₀' with hm
  have hmc : ∀ j : ℤ, j < m → c j = 0 := fun j hj ↦ h₀ j (lt_of_lt_of_le hj (min_le_left _ _))
  have hmc' : ∀ j : ℤ, j < m → c' j = 0 := fun j hj ↦ h₀' j (lt_of_lt_of_le hj (min_le_right _ _))
  obtain ⟨C, n₀, hC⟩ := twsCtrl_bound_of_vanish_ctrlDefs h hmc (j₁ + 1)
  obtain ⟨C', n₀', hC'⟩ := twsCtrl_bound_of_vanish_ctrlDefs h' hmc' (j₁ + 1)
  have hd0 : c j₁ - c' j₁ ≠ 0 := sub_ne_zero.mpr hj₁
  set n := max (max n₀ n₀') (|(c j₁ - c' j₁).order| + |C| + |C'| + 1) with hn
  have key : (c j₁ - c' j₁) * twsT (2 * n * j₁) =
      (g n - ∑ j ∈ Finset.Ico m (j₁ + 1), c' j * twsT (2 * n * j)) -
        (g n - ∑ j ∈ Finset.Ico m (j₁ + 1), c j * twsT (2 * n * j)) := by
    rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
    symm
    rw [Finset.sum_eq_single j₁]
    · rw [sub_mul]
    · intro j hj hjne
      rw [Finset.mem_Ico] at hj
      rw [hlow j (by lia), sub_self]
    · intro hj
      rw [Finset.mem_Ico] at hj
      exact absurd hj (by lia)
  have h1 := hC n (le_trans (le_max_left _ _) (le_max_left _ _))
  have h2 := hC' n (le_trans (le_max_right _ _) (le_max_left _ _))
  have h3 := le_trans (min_le_min h2 h1) HahnSeries.min_orderTop_le_orderTop_sub
  rw [← key, orderTop_mul_twsT_ctrlDefs, ← HahnSeries.order_eq_orderTop_of_ne_zero hd0,
    ← WithTop.coe_min, ← WithTop.coe_add, WithTop.coe_le_coe] at h3
  have h4 : |(c j₁ - c' j₁).order| + |C| + |C'| + 1 ≤ n := le_max_right _ _
  have h5 := le_abs_self (c j₁ - c' j₁).order
  have h6 := le_abs_self C
  have h7 := le_abs_self C'
  have h9 := abs_nonneg (c j₁ - c' j₁).order
  have h10 := abs_nonneg C
  have h11 := abs_nonneg C'
  rcases min_le_iff.mp h3 with h8 | h8 <;> linarith

end AJConjecture
