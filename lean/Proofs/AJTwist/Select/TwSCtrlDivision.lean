import Mathlib
import AJTwist.Select.TwSCtrlMul
import AJTwist.Select.TwSCtrlClass

/-!
# Separation by the growth of controlled coefficients

Source: Sections 6.4-6.6 of `selection.tex` (revision 5): "Bounds after rational
multiplication" (the triangular convolution recursion for the inverse of a coefficient) and
"Uniqueness of controlled coefficients now excludes `F` from `𝒰_ℓ`".

* `tws_bound_of_twsConv`: if the convolution `κ * f` of a nonzero coefficient with a family `f`
  (vanishing below some degree) satisfies `D · ord (κ * f)_k ≥ -(k² + O(k))`, so does `f`: divide
  by the lowest `M`-coefficient of `κ` and induct on `k`; each step loses the constant
  `ord κ_min`, hence a linear total.
* `tws_not_sat_ctrlB`: a sequence with a controlled expansion whose coefficients violate every
  bound `D · ord f_j ≥ -(j² + C |j| + C)` is not in the saturation of `TwsCtrlB D`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value at `t` of an element of `ℤ[t]` is the image of a polynomial over `ℚ`. -/
private theorem eval₂_eq_algebraMap_ctrlDivision (p : ℤ[X]) :
    Polynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X p =
      algebraMap ℚ[X] (RatFunc ℚ) (p.map (Int.castRingHom ℚ)) := by
  have h : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [RatFunc.algebraMap_X]
  have h' := RingHom.congr_fun h p
  rwa [Polynomial.coe_eval₂RingHom, RingHom.comp_apply, Polynomial.coe_mapRingHom] at h'

/-- The expansion of a nonzero `M`-coefficient of `κ` is nonzero. -/
private theorem twsCoeffT_ne_zero_ctrlDivision {κ : Coeff} {j : ℕ} (h : κ.coeff j ≠ 0) :
    twsCoeffT κ j ≠ 0 := by
  rw [twsCoeffT, eval₂_eq_algebraMap_ctrlDivision]
  exact (map_ne_zero twsSeries).mpr ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr
    ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr h))

open scoped RatFunc in
/-- The expansion of an `M`-coefficient of `κ` is a power series. -/
private theorem order_twsCoeffT_nonneg_ctrlDivision (κ : Coeff) (j : ℕ) :
    0 ≤ (twsCoeffT κ j).order := by
  by_cases h0 : twsCoeffT κ j = 0
  · rw [h0, HahnSeries.order_zero]
  refine (HahnSeries.le_order_iff_forall h0).mpr fun i hi ↦ ?_
  have h : twsCoeffT κ j =
      ((((κ.coeff j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) : LaurentSeries ℚ) := by
    rw [twsCoeffT, eval₂_eq_algebraMap_ctrlDivision]
    exact (RatFunc.coe_coe _).symm
  rw [h, PowerSeries.coeff_coe, ite_eq_left hi]

/-- A lower bound for the orders of two series is one for their sum. -/
private theorem order_add_bound_ctrlDivision {x y : LaurentSeries ℚ} {b : ℤ} (D : ℕ)
    (hx : x = 0 ∨ b ≤ (D : ℤ) * x.order) (hy : y = 0 ∨ b ≤ (D : ℤ) * y.order) :
    x + y = 0 ∨ b ≤ (D : ℤ) * (x + y).order := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  refine Or.inr ?_
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd (add_zero _) hxy
    · rwa [zero_add]
  rcases hy with rfl | hy
  · rwa [add_zero]
  have hm := HahnSeries.min_order_le_order_add (x := x) (y := y) hxy
  have hD : (0 : ℤ) ≤ D := Nat.cast_nonneg D
  rcases min_le_iff.mp hm with h | h
  · exact le_trans hx (mul_le_mul_of_nonneg_left h hD)
  · exact le_trans hy (mul_le_mul_of_nonneg_left h hD)

/-- A lower bound for the orders of finitely many series is one for their sum. -/
private theorem order_sum_bound_ctrlDivision {ι : Type*} (S : Finset ι)
    {x : ι → LaurentSeries ℚ} {b : ℤ} (D : ℕ)
    (h : ∀ i ∈ S, x i = 0 ∨ b ≤ (D : ℤ) * (x i).order) :
    ∑ i ∈ S, x i = 0 ∨ b ≤ (D : ℤ) * (∑ i ∈ S, x i).order := by
  classical
  induction S using Finset.induction_on with
  | empty => exact Or.inl Finset.sum_empty
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact order_add_bound_ctrlDivision D (h a (Finset.mem_insert_self a S))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Multiplication by a series of nonnegative order preserves a lower bound for the order. -/
private theorem order_mul_bound_ctrlDivision {a x : LaurentSeries ℚ} {b : ℤ} (D : ℕ)
    (ha : 0 ≤ a.order) (hx : x = 0 ∨ b ≤ (D : ℤ) * x.order) :
    a * x = 0 ∨ b ≤ (D : ℤ) * (a * x).order := by
  by_cases h0 : a * x = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h0
  have hx0 : x ≠ 0 := right_ne_zero_of_mul h0
  rw [HahnSeries.order_mul ha0 hx0]
  have hD : (0 : ℤ) ≤ D := Nat.cast_nonneg D
  have h1 := hx.resolve_left hx0
  have h2 := mul_nonneg hD ha
  linarith

/-- One step of the division: a bound for the convolution at degree `k + m` (`m` the lowest
`M`-degree of `κ`) and for the coefficients below `k` gives one for the coefficient at `k`, with
the loss `D · ord κ_m`. -/
private theorem bound_step_ctrlDivision {D : ℕ} {κ : Coeff} (hκ : κ ≠ 0)
    {f : ℤ → LaurentSeries ℚ} {k b : ℤ}
    (hg : twsConv κ f (k + κ.natTrailingDegree) = 0 ∨
      b ≤ (D : ℤ) * (twsConv κ f (k + κ.natTrailingDegree)).order)
    (hlow : ∀ i : ℤ, i < k → f i = 0 ∨ b ≤ (D : ℤ) * (f i).order) :
    f k = 0 ∨
      b - (D : ℤ) * (twsCoeffT κ κ.natTrailingDegree).order ≤ (D : ℤ) * (f k).order := by
  set m : ℕ := κ.natTrailingDegree with hm
  have hmem : m ∈ Finset.range (κ.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree κ))
  have key : twsCoeffT κ m * f k = twsConv κ f (k + m) +
      ∑ j ∈ (Finset.range (κ.natDegree + 1)).erase m, -(twsCoeffT κ j * f (k + m - j)) := by
    rw [twsConv, ← Finset.add_sum_erase _ _ hmem, Finset.sum_neg_distrib, add_sub_cancel_right]
    ring
  have hrhs := order_add_bound_ctrlDivision D hg
    (order_sum_bound_ctrlDivision ((Finset.range (κ.natDegree + 1)).erase m) D
      (x := fun j ↦ -(twsCoeffT κ j * f (k + m - j))) (b := b) fun j hj ↦ by
        rw [Finset.mem_erase] at hj
        rw [neg_eq_zero, HahnSeries.order_neg]
        rcases lt_or_gt_of_ne hj.1 with hlt | hgt
        · left
          rw [twsCoeffT, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt,
            Polynomial.eval₂_zero, map_zero, zero_mul]
        · exact order_mul_bound_ctrlDivision D (order_twsCoeffT_nonneg_ctrlDivision κ j)
            (hlow _ (by lia)))
  rw [← key] at hrhs
  by_cases h0 : f k = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hc : twsCoeffT κ m ≠ 0 :=
    twsCoeffT_ne_zero_ctrlDivision (Polynomial.trailingCoeff_ne_zero.mpr hκ)
  have h1 := hrhs.resolve_left (mul_ne_zero hc h0)
  rw [HahnSeries.order_mul hc h0] at h1
  linarith

/-- The induction of the division lemma, in the variable `p = k - j₀`: with
`E = 2 |s| + |C| + s² + |C| |s| + D e`, `s = j₀ + m`, the coefficients of degree `< j₀ + p`
satisfy `D · ord ≥ -(p² + E p + E)`. -/
private theorem bound_induction_ctrlDivision {D : ℕ} {κ : Coeff} (hκ : κ ≠ 0)
    {f : ℤ → LaurentSeries ℚ} {j₀ C : ℤ} (hj₀ : ∀ j : ℤ, j < j₀ → f j = 0)
    (hC : ∀ k : ℤ, twsConv κ f k = 0 ∨
      -(k ^ 2 + C * |k| + C) ≤ (D : ℤ) * (twsConv κ f k).order) {E : ℤ}
    (hE : E = 2 * |j₀ + κ.natTrailingDegree| + |C| + (j₀ + κ.natTrailingDegree) ^ 2 +
      |C| * |j₀ + κ.natTrailingDegree| + D * (twsCoeffT κ κ.natTrailingDegree).order)
    (p : ℕ) (k : ℤ) (hk : k < j₀ + p) :
    f k = 0 ∨ -((p : ℤ) ^ 2 + E * p + E) ≤ (D : ℤ) * (f k).order := by
  set m : ℕ := κ.natTrailingDegree with hm
  set e : ℤ := (twsCoeffT κ m).order with he
  have he0 : 0 ≤ e := order_twsCoeffT_nonneg_ctrlDivision κ m
  have hD : (0 : ℤ) ≤ D := Nat.cast_nonneg D
  have hDe : 0 ≤ (D : ℤ) * e := mul_nonneg hD he0
  set s : ℤ := j₀ + m with hs
  have hs0 := abs_nonneg s
  have hC0 := abs_nonneg C
  have hCs : 0 ≤ |C| * |s| := mul_nonneg hC0 hs0
  have hs2 := sq_nonneg s
  induction p generalizing k with
  | zero => exact Or.inl (hj₀ k (by simpa using hk))
  | succ p ih =>
    have hp : (0 : ℤ) ≤ p := Nat.cast_nonneg p
    have hEp : (2 * |s| + |C|) * p ≤ E * p := mul_le_mul_of_nonneg_right (by linarith) hp
    have hmono : -((p : ℤ) ^ 2 + E * p + E) ≥
        -(((p + 1 : ℕ) : ℤ) ^ 2 + E * ((p + 1 : ℕ) : ℤ) + E) + D * e := by
      push_cast
      nlinarith
    rcases lt_or_ge k (j₀ + p) with hlt | hge
    · refine (ih k hlt).imp_right fun h ↦ le_trans ?_ h
      linarith
    · have hk' : k = j₀ + p := by
        push_cast at hk
        lia
      have hkm : k + m = p + s := by rw [hk', hs]; ring
      have hstep := bound_step_ctrlDivision (D := D) hκ (f := f) (k := k)
        (b := -(((p + 1 : ℕ) : ℤ) ^ 2 + E * ((p + 1 : ℕ) : ℤ) + E) + D * e)
        ((hC (k + m)).imp_right fun h ↦ le_trans ?_ h)
        (fun i hi ↦ (ih i (by lia)).imp_right fun h ↦ le_trans hmono h)
      · refine hstep.imp_right fun h ↦ le_trans ?_ h
        linarith
      · rw [hkm]
        push_cast
        have h1 : C * |(p : ℤ) + s| ≤ |C| * (p + |s|) := by
          refine mul_le_mul (le_abs_self C) ?_ (abs_nonneg _) hC0
          exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hp])
        have h2 : (p : ℤ) * s ≤ p * |s| := mul_le_mul_of_nonneg_left (le_abs_self s) hp
        have h3 := le_abs_self C
        nlinarith

/-- Division by a nonzero coefficient preserves the quadratic bound on coefficient orders. -/
theorem tws_bound_of_twsConv {D : ℕ} {κ : Coeff} (hκ : κ ≠ 0) {f : ℤ → LaurentSeries ℚ}
    (hf : ∃ j₀ : ℤ, ∀ j : ℤ, j < j₀ → f j = 0)
    (hg : ∃ C : ℤ, ∀ k : ℤ, twsConv κ f k = 0 ∨
      -(k ^ 2 + C * |k| + C) ≤ (D : ℤ) * (twsConv κ f k).order) :
    ∃ C : ℤ, ∀ k : ℤ, f k = 0 ∨ -(k ^ 2 + C * |k| + C) ≤ (D : ℤ) * (f k).order := by
  obtain ⟨j₀, hj₀⟩ := hf
  obtain ⟨C, hC⟩ := hg
  have hD : (0 : ℤ) ≤ D := Nat.cast_nonneg D
  have hE0 : 0 ≤ 2 * |j₀ + κ.natTrailingDegree| + |C| + (j₀ + κ.natTrailingDegree) ^ 2 +
      |C| * |j₀ + κ.natTrailingDegree| + D * (twsCoeffT κ κ.natTrailingDegree).order := by
    have h1 := mul_nonneg hD (order_twsCoeffT_nonneg_ctrlDivision κ κ.natTrailingDegree)
    positivity
  obtain ⟨E, hE⟩ : ∃ E : ℤ, E = 2 * |j₀ + κ.natTrailingDegree| + |C| +
      (j₀ + κ.natTrailingDegree) ^ 2 + |C| * |j₀ + κ.natTrailingDegree| +
      D * (twsCoeffT κ κ.natTrailingDegree).order := ⟨_, rfl⟩
  rw [← hE] at hE0
  refine ⟨2 * |1 - j₀| + E + (1 - j₀) ^ 2 + E * |1 - j₀| + E, fun k ↦ ?_⟩
  rcases lt_or_ge k j₀ with hlt | hge
  · exact Or.inl (hj₀ k hlt)
  have hp : ((k - j₀ + 1).toNat : ℤ) = k - j₀ + 1 := Int.toNat_of_nonneg (by lia)
  refine (bound_induction_ctrlDivision hκ hj₀ hC hE (k - j₀ + 1).toNat k (by lia)).imp_right
    fun h ↦ le_trans ?_ h
  rw [hp]
  have h1 := abs_nonneg (1 - j₀)
  have h2 := abs_nonneg k
  have h3 : k * (1 - j₀) ≤ |k| * |1 - j₀| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h4 : k - j₀ + 1 ≤ |k| + |1 - j₀| := by
    have := le_abs_self k
    have := le_abs_self (1 - j₀)
    linarith
  have h5 := mul_le_mul_of_nonneg_left h4 hE0
  have h6 : 0 ≤ (1 - j₀) ^ 2 * |k| := mul_nonneg (sq_nonneg _) h2
  have h7 : 0 ≤ E * |1 - j₀| * |k| := mul_nonneg (mul_nonneg hE0 h1) h2
  have h8 : 0 ≤ E * |k| := mul_nonneg hE0 h2
  nlinarith

/-- A sequence with a controlled expansion whose coefficients violate every bound of the class
`TwsCtrlB D` is not in the saturation of that class. -/
theorem tws_not_sat_ctrlB {D : ℕ} {F : ℤ → RatFunc ℚ} {f : ℤ → LaurentSeries ℚ}
    (hf : TwsCtrl f fun n ↦ twsSeries (F n))
    (hbad : ∀ C : ℤ, ∃ j : ℤ, f j ≠ 0 ∧ (D : ℤ) * (f j).order < -(j ^ 2 + C * |j| + C)) :
    ¬ TwsSat (TwsCtrlB D) F := by
  rintro ⟨κ, hκ, c, hc, hbound⟩
  have hconv := twsCtrl_coeff_mul hf κ
  have e : (fun n ↦ twsSeries (evalAtField n κ * F n)) =
      fun n ↦ twsSeries (evalAtField n κ) * twsSeries (F n) := funext fun n ↦ map_mul _ _ _
  rw [e] at hc
  obtain rfl := hc.unique hconv
  obtain ⟨j₀, hj₀, -⟩ := hf
  obtain ⟨C, hC⟩ := tws_bound_of_twsConv hκ ⟨j₀, hj₀⟩ hbound
  obtain ⟨j, hj, hlt⟩ := hbad C
  exact absurd ((hC j).resolve_left hj) (not_le.mpr hlt)

end AJConjecture
