import Mathlib
import AJConjecture.WhiteheadFormula
import AJConjecture.QAlgQParamBasic

/-!
# The order at `t = 0` of an element of `ℚ(t)`

`pairQTOrder f = ord_t(num f) - ord_t(denom f)`, the `t`-adic valuation of `f ≠ 0` (for `f = 0`
it is `0`, a junk value). It is used only for the valuation clause Q13 of T-TRANSFER
(`AJHandoff.TorusQuantum.PairQTOrderFormula`). Basic rules: multiplicativity, the order of
`t^k`, and the order of a sum with a unique term of least order (the analogue of
`intDegree_sum_eq_of_lt`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The order of vanishing at `t = 0`. -/
def pairQTOrder (f : RatFunc ℚ) : ℤ :=
  (f.num.natTrailingDegree : ℤ) - (f.denom.natTrailingDegree : ℤ)

/-- The order at `t = 0` of a quotient `p / q` of nonzero polynomials is
`ord_t p - ord_t q`. -/
private theorem pairQTOrder_algebraMap_div {p q : ℚ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    pairQTOrder (algebraMap ℚ[X] (RatFunc ℚ) p / algebraMap ℚ[X] (RatFunc ℚ) q) =
      (p.natTrailingDegree : ℤ) - (q.natTrailingDegree : ℤ) := by
  set x := algebraMap ℚ[X] (RatFunc ℚ) p / algebraMap ℚ[X] (RatFunc ℚ) q with hx
  have hx0 : x ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hp)
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hq)
  have h := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hx
  have h2 := congrArg Polynomial.natTrailingDegree h
  rw [natTrailingDegree_mul (RatFunc.num_ne_zero hx0) hq,
    natTrailingDegree_mul hp (RatFunc.denom_ne_zero x)] at h2
  unfold pairQTOrder
  omega

theorem pairQTOrder_mul {f g : RatFunc ℚ} (hf : f ≠ 0) (hg : g ≠ 0) :
    pairQTOrder (f * g) = pairQTOrder f + pairQTOrder g := by
  have h : f * g = algebraMap ℚ[X] (RatFunc ℚ) (f.num * g.num) /
      algebraMap ℚ[X] (RatFunc ℚ) (f.denom * g.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    rw [div_mul_div_comm, map_mul, map_mul]
  rw [h, pairQTOrder_algebraMap_div (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
    (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)),
    natTrailingDegree_mul (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg),
    natTrailingDegree_mul (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)]
  unfold pairQTOrder
  push_cast
  ring

theorem pairQTOrder_inv (f : RatFunc ℚ) : pairQTOrder f⁻¹ = -pairQTOrder f := by
  by_cases hf : f = 0
  · simp [hf, pairQTOrder]
  have h : f⁻¹ = algebraMap ℚ[X] (RatFunc ℚ) f.denom / algebraMap ℚ[X] (RatFunc ℚ) f.num := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [inv_div]
  rw [h, pairQTOrder_algebraMap_div (RatFunc.denom_ne_zero f) (RatFunc.num_ne_zero hf)]
  unfold pairQTOrder
  ring

theorem pairQTOrder_X_zpow (k : ℤ) : pairQTOrder ((RatFunc.X : RatFunc ℚ) ^ k) = k := by
  have hnat : ∀ m : ℕ, pairQTOrder ((RatFunc.X : RatFunc ℚ) ^ m) = m := by
    intro m
    have h : (RatFunc.X : RatFunc ℚ) ^ m = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.X ^ m) /
        algebraMap ℚ[X] (RatFunc ℚ) 1 := by
      rw [map_one, div_one, map_pow, RatFunc.algebraMap_X]
    rw [h, pairQTOrder_algebraMap_div (pow_ne_zero m Polynomial.X_ne_zero) one_ne_zero,
      natTrailingDegree_X_pow, natTrailingDegree_one]
    simp
  obtain ⟨m, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast, hnat]
  · rw [zpow_neg, pairQTOrder_inv, zpow_natCast, hnat]

/-- The order of a negative. -/
private theorem pairQTOrder_neg_aux (f : RatFunc ℚ) : pairQTOrder (-f) = pairQTOrder f := by
  rw [← neg_one_mul]
  by_cases hf : f = 0
  · simp [hf]
  have h1 : pairQTOrder (-1 : RatFunc ℚ) = 0 := by
    have h : (-1 : RatFunc ℚ) = algebraMap ℚ[X] (RatFunc ℚ) (-1) /
        algebraMap ℚ[X] (RatFunc ℚ) 1 := by
      rw [map_one, div_one, map_neg, map_one]
    rw [h, pairQTOrder_algebraMap_div (neg_ne_zero.mpr one_ne_zero) one_ne_zero,
      natTrailingDegree_neg, natTrailingDegree_one]
    simp
  rw [pairQTOrder_mul (neg_ne_zero.mpr one_ne_zero) hf, h1, zero_add]

/-- The order of a nonzero sum is at least the smaller of the two orders. -/
private theorem pairQTOrder_add_ge {f g : RatFunc ℚ} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (pairQTOrder f) (pairQTOrder g) ≤ pairQTOrder (f + g) := by
  set a := f.num * g.denom with ha
  set b := f.denom * g.num with hb
  have h : f + g = algebraMap ℚ[X] (RatFunc ℚ) (a + b) /
      algebraMap ℚ[X] (RatFunc ℚ) (f.denom * g.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    rw [div_add_div _ _ ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr
      (RatFunc.denom_ne_zero f)) ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr
      (RatFunc.denom_ne_zero g)), ha, hb, map_add, map_mul, map_mul, map_mul]
  have hab : a + b ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_div] at h
    exact hfg h
  have hfn := RatFunc.num_ne_zero hf
  have hgn := RatFunc.num_ne_zero hg
  have hfd := RatFunc.denom_ne_zero f
  have hgd := RatFunc.denom_ne_zero g
  have hle : min a.natTrailingDegree b.natTrailingDegree ≤ (a + b).natTrailingDegree := by
    refine le_natTrailingDegree hab fun m hm ↦ ?_
    rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hm (min_le_left _ _)),
      coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hm (min_le_right _ _)), add_zero]
  rw [h, pairQTOrder_algebraMap_div hab (mul_ne_zero hfd hgd), natTrailingDegree_mul hfd hgd]
  have ha' : a.natTrailingDegree = f.num.natTrailingDegree + g.denom.natTrailingDegree :=
    natTrailingDegree_mul hfn hgd
  have hb' : b.natTrailingDegree = f.denom.natTrailingDegree + g.num.natTrailingDegree :=
    natTrailingDegree_mul hfd hgn
  unfold pairQTOrder
  omega

/-- Strict dominance at `t = 0`: adding a term of larger order does not change the order. -/
private theorem pairQTOrder_add_eq_of_lt {d : ℤ} {f g : RatFunc ℚ}
    (hf : f ≠ 0 ∧ pairQTOrder f = d) (hg : g = 0 ∨ d < pairQTOrder g) :
    f + g ≠ 0 ∧ pairQTOrder (f + g) = d := by
  obtain ⟨hf0, rfl⟩ := hf
  rcases hg with rfl | hg
  · rw [add_zero]
    exact ⟨hf0, rfl⟩
  by_cases hg0 : g = 0
  · rw [hg0, add_zero]
    exact ⟨hf0, rfl⟩
  have hfg : f + g ≠ 0 := by
    intro h
    rw [eq_neg_of_add_eq_zero_left h, pairQTOrder_neg_aux] at hg
    exact lt_irrefl _ hg
  refine ⟨hfg, le_antisymm ?_ ?_⟩
  · have h1 : f + g + -g ≠ 0 := by rwa [add_neg_cancel_right]
    have h2 := pairQTOrder_add_ge hfg (neg_ne_zero.mpr hg0) h1
    rw [add_neg_cancel_right, pairQTOrder_neg_aux] at h2
    rcases min_le_iff.mp h2 with h | h
    · exact h
    · exact absurd h (not_le.mpr hg)
  · exact (le_min le_rfl hg.le).trans (pairQTOrder_add_ge hf0 hg0 hfg)

/-- A sum of elements that are zero or of order greater than `d` is zero or of order greater
than `d`. -/
private theorem pairQTOrder_sum_gt_of_gt {ι : Type*} {d : ℤ} (s : Finset ι)
    (f : ι → RatFunc ℚ) (h : ∀ i ∈ s, f i = 0 ∨ d < pairQTOrder (f i)) :
    ∑ i ∈ s, f i = 0 ∨ d < pairQTOrder (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (fun x ↦ x = 0 ∨ d < pairQTOrder x) ?_ (Or.inl rfl) h
  intro x y hx hy
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]
    exact Or.inr hx
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]
    exact Or.inr hy
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]
    exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  · exact Or.inr ((lt_min hx hy).trans_le (pairQTOrder_add_ge hx0 hy0 hxy))

/-- A finite sum with a unique nonzero term of least order has that order. -/
theorem pairQTOrder_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {d : ℤ} {s : Finset ι}
    {f : ι → RatFunc ℚ} {a : ι} (has : a ∈ s) (ha : f a ≠ 0 ∧ pairQTOrder (f a) = d)
    (h : ∀ i ∈ s, i ≠ a → f i = 0 ∨ d < pairQTOrder (f i)) :
    ∑ i ∈ s, f i ≠ 0 ∧ pairQTOrder (∑ i ∈ s, f i) = d := by
  rw [← Finset.add_sum_erase s f has]
  exact pairQTOrder_add_eq_of_lt ha (pairQTOrder_sum_gt_of_gt _ _ fun i hi ↦
    h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))

/-! ### Rules for nonzero elements of known order -/

/-- The order of a negative. -/
theorem pairQTOrder_neg (f : RatFunc ℚ) : pairQTOrder (-f) = pairQTOrder f :=
  pairQTOrder_neg_aux f

/-- The order of a product of nonzero elements of known order. -/
theorem pairQTOrder_mul_eq {d e : ℤ} {x y : RatFunc ℚ}
    (hx : x ≠ 0 ∧ pairQTOrder x = d) (hy : y ≠ 0 ∧ pairQTOrder y = e) :
    x * y ≠ 0 ∧ pairQTOrder (x * y) = d + e :=
  ⟨mul_ne_zero hx.1 hy.1, by rw [pairQTOrder_mul hx.1 hy.1, hx.2, hy.2]⟩

/-- The order of a quotient of nonzero elements of known order. -/
theorem pairQTOrder_div_eq {d e : ℤ} {x y : RatFunc ℚ}
    (hx : x ≠ 0 ∧ pairQTOrder x = d) (hy : y ≠ 0 ∧ pairQTOrder y = e) :
    x / y ≠ 0 ∧ pairQTOrder (x / y) = d - e := by
  refine ⟨div_ne_zero hx.1 hy.1, ?_⟩
  rw [div_eq_mul_inv, pairQTOrder_mul hx.1 (inv_ne_zero hy.1), pairQTOrder_inv, hx.2, hy.2]
  ring

/-- The order of a finite product of nonzero elements of known orders. -/
theorem pairQTOrder_prod_eq {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) (d : ι → ℤ)
    (h : ∀ i ∈ s, f i ≠ 0 ∧ pairQTOrder (f i) = d i) :
    ∏ i ∈ s, f i ≠ 0 ∧ pairQTOrder (∏ i ∈ s, f i) = ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨one_ne_zero, by simpa using pairQTOrder_X_zpow 0⟩
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has]
    exact pairQTOrder_mul_eq (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- An integer power of `t` is nonzero of order its exponent. -/
theorem pairQTOrder_X_zpow_eq (n : ℤ) :
    (RatFunc.X : RatFunc ℚ) ^ n ≠ 0 ∧ pairQTOrder ((RatFunc.X : RatFunc ℚ) ^ n) = n :=
  ⟨zpow_ne_zero n RatFunc.X_ne_zero, pairQTOrder_X_zpow n⟩

/-- An integer power of `q = t⁴` is nonzero of order `4n`. -/
theorem pairQTOrder_qParam_zpow_eq (n : ℤ) :
    qParam ^ n ≠ 0 ∧ pairQTOrder (qParam ^ n) = 4 * n := by
  rw [qParam_zpow_eq_ratFuncX_zpow]
  exact pairQTOrder_X_zpow_eq (4 * n)

/-- A natural power of `q = t⁴` is nonzero of order `4k`. -/
theorem pairQTOrder_qParam_pow_eq (k : ℕ) :
    qParam ^ k ≠ 0 ∧ pairQTOrder (qParam ^ k) = 4 * (k : ℤ) := by
  rw [← zpow_natCast]
  exact pairQTOrder_qParam_zpow_eq k

/-- A difference of distinct powers of `t` is nonzero of order the smaller exponent. -/
theorem pairQTOrder_X_zpow_sub_zpow {a b : ℤ} (hab : a ≠ b) :
    (RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b ≠ 0 ∧
      pairQTOrder ((RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b) = min a b := by
  have hlt : ∀ c d : ℤ, c < d → (RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d ≠ 0 ∧
      pairQTOrder ((RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d) = c := by
    intro c d hcd
    rw [sub_eq_add_neg]
    refine pairQTOrder_add_eq_of_lt (pairQTOrder_X_zpow_eq c) (Or.inr ?_)
    rwa [pairQTOrder_neg, pairQTOrder_X_zpow]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le]
    exact hlt a b h
  · have h1 := hlt b a h
    rw [min_eq_right h.le, ← neg_sub, pairQTOrder_neg]
    exact ⟨neg_ne_zero.mpr h1.1, h1.2⟩

/-- `1 - q^k`, `k > 0`, is nonzero of order `0`. -/
theorem pairQTOrder_one_sub_qParam_zpow_of_pos {k : ℤ} (hk : 0 < k) :
    1 - qParam ^ k ≠ 0 ∧ pairQTOrder (1 - qParam ^ k) = 0 := by
  have h := pairQTOrder_X_zpow_sub_zpow (a := 0) (b := 4 * k) (by omega)
  rw [zpow_zero, min_eq_left (by omega), ← qParam_zpow_eq_ratFuncX_zpow] at h
  exact h

/-- `1 - q^k`, `k < 0`, is nonzero of order `4k`. -/
theorem pairQTOrder_one_sub_qParam_zpow_of_neg {k : ℤ} (hk : k < 0) :
    1 - qParam ^ k ≠ 0 ∧ pairQTOrder (1 - qParam ^ k) = 4 * k := by
  have h := pairQTOrder_X_zpow_sub_zpow (a := 0) (b := 4 * k) (by omega)
  rw [zpow_zero, min_eq_right (by omega), ← qParam_zpow_eq_ratFuncX_zpow] at h
  exact h

/-- The quantum integer `[m]`, `m ≠ 0`, is nonzero of order `2 - 2|m|`. -/
theorem pairQTOrder_quantumInt {m : ℤ} (hm : m ≠ 0) :
    quantumInt m ≠ 0 ∧ pairQTOrder (quantumInt m) = min (2 * m) (-(2 * m)) + 2 := by
  have h1 := pairQTOrder_X_zpow_sub_zpow (a := 2 * m) (b := -(2 * m)) (by omega)
  have h2 := pairQTOrder_X_zpow_sub_zpow (a := 2) (b := -2) (by omega)
  have h := pairQTOrder_div_eq h1 h2
  refine ⟨h.1, h.2.trans ?_⟩
  rw [min_eq_right (show (-2 : ℤ) ≤ 2 by norm_num)]
  ring

/-- The `q`-Pochhammer symbol `(q; q)_k` is nonzero of order `0`. -/
theorem pairQTOrder_qPochhammer_qParam (k : ℕ) :
    qPochhammer qParam k ≠ 0 ∧ pairQTOrder (qPochhammer qParam k) = 0 := by
  have h := pairQTOrder_prod_eq (Finset.range k) (fun i ↦ 1 - qParam * qParam ^ i)
    (fun _ ↦ 0) fun i _ ↦ by
      have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := (i : ℤ) + 1) (by omega)
      rwa [zpow_add₀ qParam_ne_zero, zpow_one, zpow_natCast, mul_comm] at h1
  rw [Finset.sum_const_zero] at h
  exact h

end AJConjecture
