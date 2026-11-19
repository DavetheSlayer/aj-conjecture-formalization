import Mathlib
import AJTwist.Select.TwSCtrlMul
import AJTwist.Select.TwSCtrlClass

/-!
# Separation by a varying leading coefficient

Source: Section 6.5 of `selection.tex` (revision 5), the case `a = 0` of the right-handed
companion: "A nonflat controlled expansion has a fixed leading coefficient on a tail, by its
first nonzero `M`-coefficient. A flat expansion has larger eventual slope than `4N - 4` in
`t`-order. Thus neither can represent the displayed actual sequence."

If `F(n)` has order `A n + B` at `t = 0` and leading coefficient `n` on a tail, then no nonzero
coefficient multiple of `F` has a controlled expansion: the leading coefficient of
`κ(t, t^(2n)) F(n)` is `κ₀ n` for a fixed nonzero integer `κ₀` (the coefficient of the dominant
monomial of `κ`), which is not eventually constant, and its order is affine in `n`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A sequence with a nonzero controlled expansion has, on a tail, affine order and constant
leading coefficient: those of its first nonzero term. -/
theorem twsCtrl_lead_of_ne_zero_ctrlLead {c : ℤ → LaurentSeries ℚ}
    {g : ℤ → LaurentSeries ℚ} (h : TwsCtrl c g) (hc : ∃ j : ℤ, c j ≠ 0) :
    ∃ (a b : ℤ) (l : ℚ) (n₁ : ℤ), ∀ n : ℤ, n₁ ≤ n →
      g n ≠ 0 ∧ (g n).order = a * n + b ∧ (g n).leadingCoeff = l := by
  obtain ⟨j₀, h₀, hJ⟩ := h
  have hbdd : ∀ z : ℤ, c z ≠ 0 → j₀ ≤ z := fun z hz ↦ by
    by_contra hlt
    exact hz (h₀ z (not_le.mp hlt))
  obtain ⟨j₁, hj₁, hmin⟩ := Int.exists_least_of_bdd ⟨_, hbdd⟩ hc
  have hmj := hbdd j₁ hj₁
  obtain ⟨C, n₀, hC⟩ := hJ (j₁ + 1)
  refine ⟨2 * j₁, (c j₁).order, (c j₁).leadingCoeff, max n₀ (|(c j₁).order + C| + 1),
    fun n hn ↦ ?_⟩
  have hsum : ∑ j ∈ Finset.Ico j₀ (j₁ + 1), c j * twsT (2 * n * j) =
      c j₁ * twsT (2 * n * j₁) := by
    rw [Finset.sum_eq_single j₁]
    · intro j hj hjne
      rw [Finset.mem_Ico] at hj
      have hcj : c j = 0 := by
        by_contra hcj
        exact absurd (hmin j hcj) (by lia)
      rw [hcj, zero_mul]
    · intro hj
      rw [Finset.mem_Ico] at hj
      exact absurd hj (by lia)
  have h1 := hC n (le_trans (le_max_left _ _) hn)
  rw [hsum] at h1
  set x := c j₁ * twsT (2 * n * j₁) with hx
  have hxo : x.orderTop = (((c j₁).order + 2 * n * j₁ : ℤ) : WithTop ℤ) := by
    rw [hx, HahnSeries.orderTop_mul, twsT, HahnSeries.orderTop_single one_ne_zero,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hj₁, WithTop.coe_add]
  have hxl : x.leadingCoeff = (c j₁).leadingCoeff := by
    rw [hx, HahnSeries.leadingCoeff_mul, twsT, HahnSeries.leadingCoeff_of_single, mul_one]
  have hlt : x.orderTop < (g n - x).orderTop := by
    refine lt_of_lt_of_le ?_ h1
    rw [hxo, WithTop.coe_lt_coe]
    have h2 : |(c j₁).order + C| + 1 ≤ n := le_trans (le_max_right _ _) hn
    have h3 := le_abs_self ((c j₁).order + C)
    have h4 := abs_nonneg ((c j₁).order + C)
    linarith
  have ho := HahnSeries.orderTop_add_eq_left hlt
  have hl := HahnSeries.leadingCoeff_add_eq_left hlt
  rw [add_sub_cancel] at ho hl
  have hg0 : g n ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [ho, hxo]; exact WithTop.coe_ne_top)
  refine ⟨hg0, ?_, hl.trans hxl⟩
  rw [hxo, ← HahnSeries.order_eq_orderTop_of_ne_zero hg0, WithTop.coe_inj] at ho
  rw [ho]
  ring

/-- A sequence whose controlled expansion vanishes has eventual slope larger than any bound. -/
theorem twsCtrl_flat_ctrlLead {c : ℤ → LaurentSeries ℚ} {g : ℤ → LaurentSeries ℚ}
    (h : TwsCtrl c g) (hc : ∀ j : ℤ, c j = 0) (J : ℤ) :
    ∃ C n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ((2 * J * n - C : ℤ) : WithTop ℤ) ≤ (g n).orderTop := by
  obtain ⟨j₀, -, hJ⟩ := h
  obtain ⟨C, n₀, hC⟩ := hJ J
  refine ⟨C, n₀, fun n hn ↦ ?_⟩
  have h1 := hC n hn
  simp only [hc, zero_mul, Finset.sum_const_zero, sub_zero] at h1
  exact h1

/-- The constant sequence `1` has the expansion `1`. -/
private theorem twsCtrl_one_ctrlLead :
    TwsCtrl (fun k ↦ if k = 0 then 1 else 0) (fun _ : ℤ ↦ (1 : LaurentSeries ℚ)) := by
  refine ⟨0, fun j hj ↦ ite_eq_right (ne_of_lt hj), fun J ↦ ⟨0, 0, fun n hn ↦ ?_⟩⟩
  beta_reduce
  rcases le_or_gt J 0 with hJ | hJ
  · rw [Finset.Ico_eq_empty (by lia), Finset.sum_empty, sub_zero, sub_zero, HahnSeries.orderTop_one,
      ← WithTop.coe_zero, WithTop.coe_le_coe]
    have := mul_nonneg (neg_nonneg.mpr hJ) hn
    linarith
  · rw [Finset.sum_eq_single 0]
    · have hT : twsT (2 * n * 0) = 1 := by rw [mul_zero]; rfl
      rw [ite_eq_left rfl, hT, mul_one, sub_self, HahnSeries.orderTop_zero]
      exact le_top
    · intro j _ hj
      rw [ite_eq_right hj, zero_mul]
    · intro h0
      rw [Finset.mem_Ico] at h0
      exact absurd h0 (by lia)

/-- The expansion in `ℚ((t))` of a nonzero element of `ℤ[t]` is nonzero. -/
private theorem twsSeries_eval₂_ne_zero_ctrlLead {p : ℤ[X]} (hp : p ≠ 0) :
    twsSeries (Polynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X p) ≠ 0 := by
  have h : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [RatFunc.algebraMap_X]
  have h' := RingHom.congr_fun h p
  rw [Polynomial.coe_eval₂RingHom, RingHom.comp_apply, Polynomial.coe_mapRingHom] at h'
  rw [h']
  exact (map_ne_zero twsSeries).mpr ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr
    ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp))

/-- A nonzero coefficient, evaluated at `M = t^(2n)`, has affine order and constant leading
coefficient on a tail. -/
private theorem twsSeries_evalAtField_lead_ctrlLead {κ : Coeff} (hκ : κ ≠ 0) :
    ∃ (a b : ℤ) (l : ℚ) (n₁ : ℤ), ∀ n : ℤ, n₁ ≤ n → twsSeries (evalAtField n κ) ≠ 0 ∧
      (twsSeries (evalAtField n κ)).order = a * n + b ∧
      (twsSeries (evalAtField n κ)).leadingCoeff = l := by
  have h := twsCtrl_lead_of_ne_zero_ctrlLead (twsCtrl_coeff_mul twsCtrl_one_ctrlLead κ)
    ⟨κ.natDegree, by
      rw [twsConv, Finset.sum_eq_single κ.natDegree]
      · rw [sub_self, ite_eq_left rfl, mul_one]
        exact twsSeries_eval₂_ne_zero_ctrlLead (Polynomial.leadingCoeff_ne_zero.mpr hκ)
      · intro j _ hj
        rw [ite_eq_right (by lia), mul_zero]
      · intro h0
        exact absurd (Finset.self_mem_range_succ _) h0⟩
  simp only [mul_one] at h
  exact h

/-- A sequence of affine order with leading coefficient `n` is not in the saturation of the
class of sequences with a controlled expansion. -/
theorem tws_not_sat_ctrlAll_of_leadingCoeff {F : ℤ → RatFunc ℚ}
    (hF : ∃ A B n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → F n ≠ 0 ∧ pairQTOrder (F n) = A * n + B ∧
      (twsSeries (F n)).leadingCoeff = (n : ℚ)) :
    ¬ TwsSat TwsCtrlAll F := by
  rintro ⟨κ, hκ, c, hc⟩
  beta_reduce at hc
  obtain ⟨A, B, n₀, hF⟩ := hF
  obtain ⟨a, b, l, n₁, hE⟩ := twsSeries_evalAtField_lead_ctrlLead hκ
  have hprod : ∀ n : ℤ, max n₀ n₁ ≤ n → twsSeries (evalAtField n κ * F n) ≠ 0 ∧
      (twsSeries (evalAtField n κ * F n)).order = (a + A) * n + (b + B) ∧
      (twsSeries (evalAtField n κ * F n)).leadingCoeff = l * n ∧ l ≠ 0 := by
    intro n hn
    obtain ⟨hF0, hFo, hFl⟩ := hF n (le_trans (le_max_left _ _) hn)
    obtain ⟨hE0, hEo, hEl⟩ := hE n (le_trans (le_max_right _ _) hn)
    have hF0' : twsSeries (F n) ≠ 0 := (map_ne_zero twsSeries).mpr hF0
    rw [map_mul, HahnSeries.order_mul hE0 hF0', HahnSeries.leadingCoeff_mul, hEo, hEl, hFl,
      tws_order_twsSeries hF0, hFo]
    exact ⟨mul_ne_zero hE0 hF0', by ring, rfl, hEl ▸ HahnSeries.leadingCoeff_ne_zero.mpr hE0⟩
  by_cases hc0 : ∃ j : ℤ, c j ≠ 0
  · obtain ⟨a', b', l', n₂, hL⟩ := twsCtrl_lead_of_ne_zero_ctrlLead hc hc0
    set n := max (max n₀ n₁) n₂ with hn
    obtain ⟨-, -, h1, hl0⟩ := hprod n (le_max_left _ _)
    have hn1 : n ≤ n + 1 := by lia
    obtain ⟨-, -, h2, -⟩ := hprod (n + 1) (le_trans (le_max_left _ _) hn1)
    have h3 := (hL n (le_max_right _ _)).2.2
    have h4 := (hL (n + 1) (le_trans (le_max_right _ _) hn1)).2.2
    rw [h3] at h1
    rw [h4, h1] at h2
    push_cast at h2
    exact hl0 (by linarith)
  · have hc0' : ∀ j : ℤ, c j = 0 := fun j ↦ by_contra fun hj ↦ hc0 ⟨j, hj⟩
    obtain ⟨C, n₂, hL⟩ := twsCtrl_flat_ctrlLead hc hc0' (|a + A| + 1)
    set n := max (max (max n₀ n₁) n₂) (|C + (b + B)| + 1) with hn
    obtain ⟨h0, h1, -, -⟩ := hprod n (le_trans (le_max_left _ _) (le_max_left _ _))
    have h2 := hL n (le_trans (le_max_right _ _) (le_max_left _ _))
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0, WithTop.coe_le_coe, h1] at h2
    have h3 : |C + (b + B)| + 1 ≤ n := le_max_right _ _
    have h4 := le_abs_self (C + (b + B))
    have h5 := abs_nonneg (C + (b + B))
    have h6 := le_abs_self (a + A)
    have h7 := abs_nonneg (a + A)
    have h8 : 0 ≤ (2 * |a + A| - (a + A)) * n := mul_nonneg (by linarith) (by linarith)
    linarith

end AJConjecture
