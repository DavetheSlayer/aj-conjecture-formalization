import Mathlib
import AJConjecture.QAlgEvalAtFieldDegree
import AJHandoff.TorusQuantum.PairQTOrder
import AJTwist.Select.TwSGrowthClass

/-!
# Valuation growth classes

Source: Sections 6.1 and 6.2 of `selection.tex` (revision 5): the bounds
`ν(w_N) ≥ -c N² - O_w(N)` for the colour valuation `ν = ord_{t=0} / 4` and for
`ν_∞(f) = ν(f(t⁻¹))`.

* `TwsOrd v σ`: `v` is an order function on `ℚ(t)` with `v(t^k) = σ k` (the order at `t = 0`,
  `pairQTOrder`, with `σ = 1`; minus the degree, `ν_∞` in units of `t`, with `σ = -1`), whose
  values on evaluated nonzero coefficients are eventually bounded above by an affine function of
  the colour.
* `TwsValClass v p`: the sequences with `v(g(n)) ≥ -(p n² + C n + C)` on a tail, for some `C`
  depending on the sequence. It is a growth class (`TwsValClass.growthClass`).
* `tws_not_sat_valClass`: a sequence with `v(F(n)) ≤ -p' n² + B n + B` on a tail, `p' > p`, is not
  in the saturation of `TwsValClass v p`. This is the strict separation of quadratic
  coefficients of Sections 6.1 and 6.2.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- An order function on `ℚ(t)` normalised by `v(t^k) = σ k`, additive on products of nonzero
elements, with the ultrametric inequality, and at most affine in the colour on the values of a
nonzero coefficient. -/
structure TwsOrd (v : RatFunc ℚ → ℤ) (σ : ℤ) : Prop where
  /-- The value on powers of `t`. -/
  map_X_zpow : ∀ k : ℤ, v ((RatFunc.X : RatFunc ℚ) ^ k) = σ * k
  /-- Additivity on products. -/
  map_mul : ∀ {f g : RatFunc ℚ}, f ≠ 0 → g ≠ 0 → v (f * g) = v f + v g
  /-- The ultrametric inequality. -/
  map_sub : ∀ {f g : RatFunc ℚ}, f ≠ 0 → g ≠ 0 → f - g ≠ 0 → min (v f) (v g) ≤ v (f - g)
  /-- The values of a nonzero coefficient have order at most affine in the colour. -/
  eval_le : ∀ {κ : Coeff}, κ ≠ 0 → ∃ C n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → v (evalAtField n κ) ≤ C * n + C

/-- The sequences whose order is bounded below on a tail by `-(p n² + C n + C)` for some `C`. -/
def TwsValClass (v : RatFunc ℚ → ℤ) (p : ℤ) (g : ℤ → RatFunc ℚ) : Prop :=
  ∃ C n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → g n = 0 ∨ -(p * n ^ 2 + C * n + C) ≤ v (g n)

/-- At a natural colour, the value of a coefficient is the image of a polynomial in `t`. -/
private theorem evalAtField_natCast_eq_algebraMap_twsVal (m : ℕ) (c : Coeff) :
    evalAtField (m : ℤ) c = algebraMap ℚ[X] (RatFunc ℚ)
      ((c.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).eval (X ^ (2 * m))) := by
  have hφ : (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) =
      Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [RatFunc.algebraMap_X]
  rw [eval_map, Polynomial.hom_eval₂, hφ, map_pow, RatFunc.algebraMap_X]
  simp only [evalAtField, coe_eval₂RingHom]
  congr 1

/-- The order at `t = 0` of a polynomial is at most its degree. -/
private theorem pairQTOrder_algebraMap_le_intDegree_twsVal (Q : ℚ[X]) :
    pairQTOrder (algebraMap ℚ[X] (RatFunc ℚ) Q) ≤
      (algebraMap ℚ[X] (RatFunc ℚ) Q).intDegree := by
  rw [pairQTOrder, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natTrailingDegree_one,
    RatFunc.intDegree_polynomial]
  have h := natTrailingDegree_le_natDegree (p := Q)
  omega

/-- The ultrametric inequality for the order at `t = 0`. -/
private theorem pairQTOrder_sub_ge_twsVal {f g : RatFunc ℚ} (hfg : f - g ≠ 0) :
    min (pairQTOrder f) (pairQTOrder g) ≤ pairQTOrder (f - g) := by
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  have h := pairQTOrder_sum_eq_of_lt (s := Finset.univ)
    (f := fun b : Bool ↦ if b then f - g else g) (a := true) (Finset.mem_univ _) ⟨hfg, rfl⟩
    fun i _ hi ↦ Or.inr (by
      cases i
      · exact hlt.2
      · exact absurd rfl hi)
  have hsum : ∑ b : Bool, (if b then f - g else g) = f := by
    rw [Fintype.sum_bool]
    simp
  rw [hsum] at h
  exact absurd h.2 hlt.1.ne'

/-- An integer power of `t` has degree its exponent. -/
private theorem intDegree_ratFuncX_zpow_twsVal (n : ℤ) :
    ((RatFunc.X : RatFunc ℚ) ^ n).intDegree = n := by
  have hnat : ∀ m : ℕ, ((RatFunc.X : RatFunc ℚ) ^ m).intDegree = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m RatFunc.X_ne_zero) RatFunc.X_ne_zero, ih,
        RatFunc.intDegree_X]
      push_cast
      rfl
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, hnat]
  · rw [zpow_neg, RatFunc.intDegree_inv, zpow_natCast, hnat]

/-- An affine function of a nonnegative integer is bounded by `C n + C`, `C = |a| + |b|`. -/
private theorem affine_le_abs_twsVal (a b : ℤ) {n : ℤ} (hn : 0 ≤ n) :
    a * n + b ≤ (|a| + |b|) * n + (|a| + |b|) := by
  nlinarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b,
    mul_nonneg (sub_nonneg.mpr (le_abs_self a)) hn, mul_nonneg (abs_nonneg b) hn]

/-- The order at `t = 0` is an order function with `σ = 1`. -/
theorem twsOrd_tOrder : TwsOrd pairQTOrder 1 where
  map_X_zpow := fun k ↦ by rw [pairQTOrder_X_zpow, one_mul]
  map_mul := fun hf hg ↦ pairQTOrder_mul hf hg
  map_sub := fun _ _ hfg ↦ pairQTOrder_sub_ge_twsVal hfg
  eval_le := fun {κ} hκ ↦ by
    obtain ⟨a, b, n₀, h⟩ := exists_intDegree_evalAtField_eq hκ
    refine ⟨|a| + |b|, max n₀ 0, fun n hn ↦ ?_⟩
    have hn0 : 0 ≤ n := (le_max_right _ _).trans hn
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
    have h1 := (h m ((le_max_left _ _).trans hn)).2
    have h2 := pairQTOrder_algebraMap_le_intDegree_twsVal
      ((κ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).eval (X ^ (2 * m)))
    rw [← evalAtField_natCast_eq_algebraMap_twsVal, h1] at h2
    exact h2.trans (affine_le_abs_twsVal a b hn0)

/-- Minus the degree is an order function with `σ = -1` (the order at `t = ∞`). -/
theorem twsOrd_negIntDegree : TwsOrd (fun f : RatFunc ℚ ↦ -f.intDegree) (-1) where
  map_X_zpow := fun k ↦ by rw [intDegree_ratFuncX_zpow_twsVal, neg_one_mul]
  map_mul := fun hf hg ↦ by rw [RatFunc.intDegree_mul hf hg, neg_add]
  map_sub := fun {f g} _ _ hfg ↦ by
    rw [sub_eq_add_neg] at hfg
    have h := RatFunc.intDegree_add_le hfg
    rw [RatFunc.intDegree_neg, ← sub_eq_add_neg] at h
    rw [min_neg_neg]
    exact neg_le_neg h
  eval_le := fun {κ} hκ ↦ by
    obtain ⟨a, b, n₀, h⟩ := exists_intDegree_evalAtField_eq hκ
    refine ⟨|-a| + |-b|, max n₀ 0, fun n hn ↦ ?_⟩
    have hn0 : 0 ≤ n := (le_max_right _ _).trans hn
    have h1 := (h n ((le_max_left _ _).trans hn)).2
    have h2 := affine_le_abs_twsVal (-a) (-b) hn0
    simp only [h1]
    linarith

/-- An order function vanishes at `1`. -/
private theorem twsOrd_map_one_twsVal {v : RatFunc ℚ → ℤ} {σ : ℤ} (hv : TwsOrd v σ) :
    v 1 = 0 := by
  have h := hv.map_X_zpow 0
  rwa [zpow_zero, mul_zero] at h

/-- An order function takes the same value at `g` and `-g`. -/
private theorem twsOrd_map_neg_twsVal {v : RatFunc ℚ → ℤ} {σ : ℤ} (hv : TwsOrd v σ)
    {g : RatFunc ℚ} (hg : g ≠ 0) : v (-g) = v g := by
  have hne : (-1 : RatFunc ℚ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have h1 := hv.map_mul hne hne
  rw [neg_one_mul, neg_neg, twsOrd_map_one_twsVal hv] at h1
  have h2 := hv.map_mul hne hg
  rw [neg_one_mul] at h2
  omega

/-- Enlarging the constant weakens the lower bound at nonnegative colours. -/
private theorem neg_quad_le_of_le_twsVal (p : ℤ) {C C' n : ℤ} (hC : C ≤ C') (hn : 0 ≤ n) :
    -(p * n ^ 2 + C' * n + C') ≤ -(p * n ^ 2 + C * n + C) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hC) hn]

/-- The valuation class is closed under subtraction. -/
private theorem twsValClass_sub_twsVal {v : RatFunc ℚ → ℤ} {σ : ℤ} (hv : TwsOrd v σ) (p : ℤ)
    {g₁ g₂ : ℤ → RatFunc ℚ} (h₁ : TwsValClass v p g₁) (h₂ : TwsValClass v p g₂) :
    TwsValClass v p fun n ↦ g₁ n - g₂ n := by
  obtain ⟨C₁, n₁, h₁⟩ := h₁
  obtain ⟨C₂, n₂, h₂⟩ := h₂
  refine ⟨max C₁ C₂, max (max n₁ n₂) 0, fun n hn ↦ ?_⟩
  beta_reduce
  have hn0 : 0 ≤ n := (le_max_right _ _).trans hn
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : n₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hb1 := neg_quad_le_of_le_twsVal p (le_max_left C₁ C₂) hn0
  have hb2 := neg_quad_le_of_le_twsVal p (le_max_right C₁ C₂) hn0
  by_cases hd : g₁ n - g₂ n = 0
  · exact Or.inl hd
  refine Or.inr ?_
  by_cases hg1 : g₁ n = 0
  · have hg2 : g₂ n ≠ 0 := fun h0 ↦ hd (by rw [hg1, h0, sub_zero])
    rw [hg1, zero_sub, twsOrd_map_neg_twsVal hv hg2]
    exact hb2.trans ((h₂ n hn2).resolve_left hg2)
  by_cases hg2 : g₂ n = 0
  · rw [hg2, sub_zero]
    exact hb1.trans ((h₁ n hn1).resolve_left hg1)
  exact (le_min (hb1.trans ((h₁ n hn1).resolve_left hg1))
    (hb2.trans ((h₂ n hn2).resolve_left hg2))).trans (hv.map_sub hg1 hg2 hd)

/-- The valuation class is closed under multiplication by `t^(i + 2 n j)`. -/
private theorem twsValClass_monomial_twsVal {v : RatFunc ℚ → ℤ} {σ : ℤ} (hv : TwsOrd v σ)
    (p : ℤ) {g : ℤ → RatFunc ℚ} (i j : ℤ) (h : TwsValClass v p g) :
    TwsValClass v p fun n ↦ (RatFunc.X : RatFunc ℚ) ^ (i + 2 * n * j) * g n := by
  obtain ⟨C, n₀, h⟩ := h
  refine ⟨C + (|-(σ * (2 * j))| + |-(σ * i)|), max n₀ 0, fun n hn ↦ ?_⟩
  beta_reduce
  have hn0 : 0 ≤ n := (le_max_right _ _).trans hn
  by_cases hg : g n = 0
  · exact Or.inl (by rw [hg, mul_zero])
  refine Or.inr ?_
  rw [hv.map_mul (zpow_ne_zero _ RatFunc.X_ne_zero) hg, hv.map_X_zpow]
  have h1 := (h n ((le_max_left _ _).trans hn)).resolve_left hg
  have h2 := affine_le_abs_twsVal (-(σ * (2 * j))) (-(σ * i)) hn0
  linarith

/-- The valuation class is closed under the shift. -/
private theorem twsValClass_shift_twsVal {v : RatFunc ℚ → ℤ} (p : ℤ) {g : ℤ → RatFunc ℚ}
    (h : TwsValClass v p g) : TwsValClass v p fun n ↦ g (n + 1) := by
  obtain ⟨C, n₀, h⟩ := h
  refine ⟨|2 * p + C| + |p + 2 * C|, max n₀ 0, fun n hn ↦ ?_⟩
  have hn0 : 0 ≤ n := (le_max_right _ _).trans hn
  rcases h (n + 1) (((le_max_left _ _).trans hn).trans (by omega)) with h0 | h1
  · exact Or.inl h0
  refine Or.inr ?_
  have h2 := affine_le_abs_twsVal (2 * p + C) (p + 2 * C) hn0
  linarith

/-- The class of sequences of order at least `-(p n² + O(n))` is a growth class. -/
theorem TwsValClass.growthClass {v : RatFunc ℚ → ℤ} {σ : ℤ} (hv : TwsOrd v σ) (p : ℤ) :
    TwsGrowthClass (TwsValClass v p) where
  zero_tail := fun {_ n₀} h ↦ ⟨0, n₀, fun n hn ↦ Or.inl (h n hn)⟩
  sub := fun h₁ h₂ ↦ twsValClass_sub_twsVal hv p h₁ h₂
  monomial := fun i j h ↦ twsValClass_monomial_twsVal hv p i j h
  shift := fun h ↦ twsValClass_shift_twsVal p h

/-- A sequence whose order is at most `-p' n² + B n + B` on a tail, with `p < p'`, does not lie
in the saturation of the class of order at least `-(p n² + O(n))`. -/
theorem tws_not_sat_valClass {v : RatFunc ℚ → ℤ} {σ : ℤ} (hv : TwsOrd v σ) {p p' : ℤ}
    (hpp : p < p') {F : ℤ → RatFunc ℚ}
    (hF : ∃ B n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → F n ≠ 0 ∧ v (F n) ≤ -(p' * n ^ 2) + B * n + B) :
    ¬ TwsSat (TwsValClass v p) F := by
  rintro ⟨κ, hκ, C, n₁, hU⟩
  obtain ⟨B, n₂, hF⟩ := hF
  obtain ⟨C₁, n₃, hκle⟩ := hv.eval_le hκ
  obtain ⟨n₄, hκne⟩ := exists_forall_ge_evalAtField_ne_zero hκ
  obtain ⟨n, hn, hK⟩ : ∃ n : ℤ, max (max n₁ n₂) (max n₃ n₄) ≤ n ∧ |C + C₁ + B| + 2 ≤ n :=
    ⟨max (max (max n₁ n₂) (max n₃ n₄)) (|C + C₁ + B| + 2), le_max_left _ _, le_max_right _ _⟩
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : n₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn3 : n₃ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn4 : n₄ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  rcases hU n hn1 with h0 | hle
  · exact mul_ne_zero (hκne n hn4) (hF n hn2).1 h0
  · rw [hv.map_mul (hκne n hn4) (hF n hn2).1] at hle
    have h1 := hκle n hn3
    have h2 := (hF n hn2).2
    have hK0 := abs_nonneg (C + C₁ + B)
    have hK1 := le_abs_self (C + C₁ + B)
    have hn0 : 0 ≤ n := by omega
    have h3 : (C + C₁ + B) * (n + 1) ≤ |C + C₁ + B| * (n + 1) :=
      mul_le_mul_of_nonneg_right hK1 (by omega)
    have h4 : (|C + C₁ + B| + 2) * n ≤ n * n := mul_le_mul_of_nonneg_right hK hn0
    have h5 : 1 * (n * n) ≤ (p' - p) * (n * n) :=
      mul_le_mul_of_nonneg_right (by omega) (mul_nonneg hn0 hn0)
    nlinarith

end AJConjecture
