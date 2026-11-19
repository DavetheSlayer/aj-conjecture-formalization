import Mathlib
import AJConjecture.QAlgOpApplyFieldBasic
import AJConjecture.QAlgQParamBasic
import AJHandoff.LocalTheory.LocColourExpand
import AJHandoff.LocalTheory.LocCycloFormal
import AJHandoff.LocalTheory.LocInterpolationCore

/-!
# From the positive tail to every integer colour (formal-colour interpolation)

A signed colour sequence has a cyclotomic expansion if
`f(n) = [n] ∑_{j < |n|} C_j(n) D_j` for every integer `n` (with `C_j(-n) = C_j(n)`,
`[-n] = -[n]`, this is the odd extension, and `f(0) = 0`), where `(1 - q)^j D_j` is regular at
`t = 1`. Habiro's cyclotomic expansion of the coloured Jones function has this form; for the
family `W_k` the library's closed formula is literally of this form
(`hasCyclotomicExpansion_torusWhiteheadFormula`), so no external theorem is imported.

**Theorem.** For such `f`, every recurrence operator annihilating `f` on a positive tail
annihilates `f` at every integer.

Proof. `f(n) = ∑_j K_j(n) · (1 - q)^j D_j` with `K_j` the regularized cyclotomic term, which
vanishes for `|n| ≤ j`, including `n = 0`. For `Q = ∑ Q_i L^i`, `(Q f)(n)` expands at `t = e^u`
into `∑_j S_j(n)` with
`S_j = ∑_i colourExpand(Q_i) · T_j(x + i) · g_j ∈ ℚ[x][[u]]` (`exists_formal_cycloTerm`,
`colourExpand_eval`, `g_j` the expansion of `(1 - q)^j D_j`), divisible by `u^j` and vanishing at
`n` for `j ≥ |n| + deg Q + 1`. `sum_map_eval_eq_zero_of_eventually` propagates the vanishing from
the tail to every `n`, and `expandAtOne` is injective. This is the "tail-extension theorem" of
the source's `JONES_TAIL_EXTENSION.md`, there conditional on Habiro's theorem. It gives equality
of the localized tail and all-integer annihilator ideals, which the reflection/common-multiple
existence argument cannot (it may raise the order).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `f(n) = [n] ∑_{j < |n|} C_j(n) D_j` for every integer `n`, with `(1 - q)^j D_j` regular at
`t = 1`. -/
structure HasCyclotomicExpansion (f : ℤ → RatFunc ℚ) (D : ℕ → RatFunc ℚ) : Prop where
  eq : ∀ n : ℤ, f n = quantumInt n * ∑ j ∈ Finset.range n.natAbs, cyclotomicKernel j n * D j
  regular : ∀ j : ℕ, IsRegularAtOne ((1 - qParam) ^ j * D j)

/-- Every recurrence operator annihilating a positive tail of `f` annihilates `f` at every
integer. -/
def TailExtends (f : ℤ → RatFunc ℚ) : Prop :=
  ∀ Q : RecOp, (∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → opApplyField Q f n = 0) →
    ∀ n : ℤ, opApplyField Q f n = 0

/-- Shifting the formal colour by `i` and evaluating at `m` is evaluating at `m + i`. -/
private theorem map_evalRingHom_map_compRingHom (T : PowerSeries ℚ[X]) (m : ℤ) (i : ℕ) :
    (T.map (Polynomial.compRingHom (X + C (i : ℚ)))).map (Polynomial.evalRingHom (m : ℚ)) =
      T.map (Polynomial.evalRingHom ((m + i : ℤ) : ℚ)) := by
  ext k
  simp [PowerSeries.coeff_map, eval_comp]

/-- Constant series in the formal colour evaluate to themselves. -/
private theorem map_evalRingHom_map_C (g : PowerSeries ℚ) (a : ℚ) :
    (g.map Polynomial.C).map (Polynomial.evalRingHom a) = g := by
  ext k
  simp [PowerSeries.coeff_map]

/-- A cyclotomic expansion written with the regularized terms, summed over any range `N ≥ |m|`. -/
private theorem eq_sum_cycloTerm_of_hasCyclotomicExpansion {f : ℤ → RatFunc ℚ} {D : ℕ → RatFunc ℚ}
    (h : HasCyclotomicExpansion f D) {m : ℤ} {N : ℕ} (hN : m.natAbs ≤ N) :
    f m = ∑ j ∈ Finset.range N, cycloTerm j m * ((1 - qParam) ^ j * D j) := by
  have hq : (1 - qParam : RatFunc ℚ) ≠ 0 := by
    simpa using one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
  rw [h.eq m, Finset.mul_sum, ← Finset.sum_subset (Finset.range_subset_range.mpr hN)
    fun j _ hj ↦ by rw [cycloTerm_eq_zero (by simpa using hj), zero_mul]]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cycloTerm]
  field_simp

/-- **Tail extension.** -/
theorem tailExtends_of_hasCyclotomicExpansion {f : ℤ → RatFunc ℚ} {D : ℕ → RatFunc ℚ}
    (h : HasCyclotomicExpansion f D) : TailExtends f := by
  rintro Q ⟨n₀, hn₀⟩ n
  choose g hg using h.regular
  choose T hTord hTval using exists_formal_cycloTerm
  set d := Q.natDegree
  let S : ℕ → PowerSeries ℚ[X] := fun j ↦ ∑ i ∈ Finset.range (d + 1),
    colourExpand (Q.coeff i) * (T j).map (Polynomial.compRingHom (X + C (i : ℚ))) *
      (g j).map Polynomial.C
  have hS : ∀ (m : ℤ) (j : ℕ), HahnSeries.ofPowerSeries ℤ ℚ
      ((S j).map (Polynomial.evalRingHom (m : ℚ))) = ∑ i ∈ Finset.range (d + 1),
        expandAtOne (evalAtField m (Q.coeff i)) * expandAtOne (cycloTerm j (m + i)) *
          expandAtOne ((1 - qParam) ^ j * D j) := by
    intro m j
    simp only [S, map_sum, map_mul, map_evalRingHom_map_compRingHom, map_evalRingHom_map_C,
      colourExpand_eval, hTval, hg]
  have hf : ∀ (m : ℤ) (i : ℕ), i ≤ d → expandAtOne (f (m + i)) =
      ∑ j ∈ Finset.range (m.natAbs + (d + 1)),
        expandAtOne (cycloTerm j (m + i)) * expandAtOne ((1 - qParam) ^ j * D j) := by
    intro m i hi
    rw [eq_sum_cycloTerm_of_hasCyclotomicExpansion h (N := m.natAbs + (d + 1)) (by omega), map_sum]
    simp only [map_mul]
  have hexp : ∀ m : ℤ, expandAtOne (opApplyField Q f m) = HahnSeries.ofPowerSeries ℤ ℚ
      (∑ j ∈ Finset.range (m.natAbs + (d + 1)), (S j).map (Polynomial.evalRingHom (m : ℚ))) := by
    intro m
    rw [opApplyField_eq_sum_range, map_sum, map_sum]
    simp only [hS]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [map_mul, hf m i (by simpa [Nat.lt_succ_iff] using hi), Finset.mul_sum]
    simp only [mul_assoc]
  have hord : ∀ j r : ℕ, r < j → PowerSeries.coeff r (S j) = 0 := by
    intro j r hr
    have hT : PowerSeries.X ^ j ∣ T j := PowerSeries.X_pow_dvd_iff.mpr (hTord j)
    obtain ⟨T', hT'⟩ := hT
    refine PowerSeries.X_pow_dvd_iff.mp ?_ r hr
    refine Finset.dvd_sum fun i _ ↦ Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
    exact ⟨T'.map (Polynomial.compRingHom (X + C (i : ℚ))), by
      rw [hT', map_mul, map_pow, PowerSeries.map_X]⟩
  have hvan : ∀ (m : ℤ) (j : ℕ), m.natAbs + (d + 1) ≤ j →
      (S j).map (Polynomial.evalRingHom (m : ℚ)) = 0 := by
    intro m j hj
    refine HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_
    rw [hS, map_zero]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi' : i < d + 1 := Finset.mem_range.mp hi
    rw [cycloTerm_eq_zero (by omega), map_zero, mul_zero, zero_mul]
  have hzero : ∀ m : ℤ, n₀ ≤ m → ∑ j ∈ Finset.range (m.natAbs + (d + 1)),
      (S j).map (Polynomial.evalRingHom (m : ℚ)) = 0 := by
    intro m hm
    refine HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_
    rw [← hexp, hn₀ m hm, map_zero, map_zero]
  refine expandAtOne.injective ?_
  rw [hexp, sum_map_eval_eq_zero_of_eventually (d + 1) hord hvan hzero n, map_zero, map_zero]

end AJConjecture
