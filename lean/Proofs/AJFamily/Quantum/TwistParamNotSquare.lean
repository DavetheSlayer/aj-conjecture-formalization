import Mathlib
import AJFamily.Quantum.TwistParamK
import AJFamily.Quantum.TwistParamRoots

/-!
# The twist parameter is not a square

For `m ≥ 2` and `K = twistParamK m`, none of `K + 2`, `K - 2`, `(K + 2)(K - 2)` is a square in
`ℂ(z)`, by comparing orders at `2cos(π/m)` and `2cos(2π/(4m+1))`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `chebU X n` commutes with the coefficient map `ℤ[X] → ℂ[X]`. -/
private theorem map_chebU_X_intCast : ∀ n : ℕ,
    (chebU (X : ℤ[X]) n).map (Int.castRingHom ℂ) = chebU (X : ℂ[X]) n
  | 0 => by simp [chebU]
  | 1 => by simp [chebU]
  | n + 2 => by
    simp only [chebU, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
      map_chebU_X_intCast n, map_chebU_X_intCast (n + 1)]

/-- If `N / D` is a square in `ℂ(z)`, then the orders of `N` and `D` at any point have the same
parity. -/
private theorem even_rootMultiplicity_add_of_isSquare_div {N D : ℂ[X]} (hN : N ≠ 0)
    (hD : D ≠ 0)
    (h : IsSquare (algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D))
    (c : ℂ) :
    Even (N.rootMultiplicity c + D.rootMultiplicity c) := by
  obtain ⟨r, hr⟩ := h
  have hq : r.denom ≠ 0 := r.denom_ne_zero
  have hrr : r = algebraMap ℂ[X] (RatFunc ℂ) r.num / algebraMap ℂ[X] (RatFunc ℂ) r.denom :=
    (RatFunc.num_div_denom r).symm
  have hq' : algebraMap ℂ[X] (RatFunc ℂ) r.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr hq
  have hD' : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr hD
  have key : N * (r.denom * r.denom) = r.num * r.num * D := by
    apply RatFunc.algebraMap_injective ℂ
    rw [hrr] at hr
    field_simp at hr
    simp only [map_mul]
    linear_combination hr
  have hp : r.num ≠ 0 := by
    rintro hp
    rw [hp, zero_mul, zero_mul] at key
    exact mul_ne_zero hN (mul_ne_zero hq hq) key
  have h1 := rootMultiplicity_mul (x := c) (mul_ne_zero hN (mul_ne_zero hq hq))
  have h2 := rootMultiplicity_mul (x := c) (mul_ne_zero (mul_ne_zero hp hp) hD)
  rw [rootMultiplicity_mul (mul_ne_zero hq hq)] at h1
  rw [rootMultiplicity_mul (mul_ne_zero hp hp)] at h2
  rw [key] at h1
  refine ⟨r.num.rootMultiplicity c + D.rootMultiplicity c - r.denom.rootMultiplicity c, ?_⟩
  omega

/-- A polynomial that does not vanish at `c` has order `0` there. -/
private theorem rootMultiplicity_eq_zero_of_eval_ne {p : ℂ[X]} {c : ℂ} (h : p.eval c ≠ 0) :
    p.rootMultiplicity c = 0 :=
  rootMultiplicity_eq_zero (fun hr ↦ h hr)

theorem not_isSquare_twistParamK (m : ℕ) (hm : 2 ≤ m) :
    ¬ IsSquare (twistParamK m + 2) ∧ ¬ IsSquare (twistParamK m - 2) ∧
      ¬ IsSquare ((twistParamK m + 2) * (twistParamK m - 2)) := by
  obtain ⟨hB1, hAc⟩ := rootMultiplicity_chebU_pred m hm
  obtain ⟨hW1, hPc⟩ := rootMultiplicity_chebU_sum m (by omega)
  set A : ℂ[X] := chebU (X : ℂ[X]) (m - 1) - chebU (X : ℂ[X]) m with hA
  set B : ℂ[X] := chebU (X : ℂ[X]) (m - 1) with hB
  set P : ℂ[X] := A * B with hP
  set c : ℂ := ((2 * Real.cos (Real.pi / m) : ℝ) : ℂ)
  set d : ℂ := ((2 * Real.cos (2 * Real.pi / (4 * m + 1)) : ℝ) : ℂ)
  have hB0 : B ≠ 0 := by
    rintro h
    rw [h, rootMultiplicity_zero] at hB1
    exact zero_ne_one hB1
  have hA0 : A ≠ 0 := by
    rintro h
    rw [h, eval_zero] at hAc
    exact hAc rfl
  have hP0 : P ≠ 0 := mul_ne_zero hA0 hB0
  have hP0' : algebraMap ℂ[X] (RatFunc ℂ) P ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr hP0
  have hBc : B.eval c = 0 := by
    exact (rootMultiplicity_pos hB0).1 (by rw [hB1]; exact Nat.one_pos)
  have hPc0 : P.eval c = 0 := by rw [hP, eval_mul, hBc, mul_zero]
  have hPmult : P.rootMultiplicity c = 1 := by
    rw [hP, rootMultiplicity_mul hP0, rootMultiplicity_eq_zero_of_eval_ne hAc, hB1]
  -- the numerator identity
  have hid : (X + 2) * P - 1 = -(chebU (X : ℂ[X]) (2 * m) + chebU (X : ℂ[X]) (2 * m - 1)) := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℂ)) (twistParam_add_two_identity m
      (by omega))
    simpa only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_neg,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat, map_chebU_X_intCast] using h
  have hK : ∀ a : ℂ[X], twistParamK m + algebraMap ℂ[X] (RatFunc ℂ) a =
      algebraMap ℂ[X] (RatFunc ℂ) ((X + a) * P - 1) / algebraMap ℂ[X] (RatFunc ℂ) P := by
    intro a
    rw [twistParamK, ← hA, ← hB, ← hP, ← RatFunc.algebraMap_X]
    field_simp
    simp only [map_sub, map_mul, map_one, map_add]
    ring
  have hmap2 : algebraMap ℂ[X] (RatFunc ℂ) 2 = 2 := map_ofNat _ 2
  have hK2 : twistParamK m + 2 = algebraMap ℂ[X] (RatFunc ℂ) ((X + 2) * P - 1) /
      algebraMap ℂ[X] (RatFunc ℂ) P := by
    rw [← hK, hmap2]
  have hKm2 : twistParamK m - 2 = algebraMap ℂ[X] (RatFunc ℂ) ((X + -2) * P - 1) /
      algebraMap ℂ[X] (RatFunc ℂ) P := by
    rw [← hK, map_neg, hmap2, sub_eq_add_neg]
  have hne : ∀ a : ℂ[X], (X + a) * P - 1 ≠ 0 := by
    intro a h
    have := congrArg (Polynomial.eval c) h
    simp [hPc0] at this
  have hodd : ∀ a : ℂ[X], ¬ IsSquare (twistParamK m + algebraMap ℂ[X] (RatFunc ℂ) a) := by
    intro a hsq
    rw [hK] at hsq
    have h := even_rootMultiplicity_add_of_isSquare_div (hne a) hP0 hsq c
    rw [hPmult, rootMultiplicity_eq_zero_of_eval_ne (by simp [hPc0])] at h
    exact Nat.not_even_one h
  refine ⟨fun h ↦ hodd 2 (by rwa [hmap2]), fun h ↦ hodd (-2) ?_, ?_⟩
  · rwa [map_neg, hmap2, ← sub_eq_add_neg]
  · intro hsq
    rw [hK2, hKm2, div_mul_div_comm, ← map_mul, ← map_mul] at hsq
    have h := even_rootMultiplicity_add_of_isSquare_div (mul_ne_zero (hne 2) (hne (-2)))
      (mul_ne_zero hP0 hP0) hsq d
    have hW0 : chebU (X : ℂ[X]) (2 * m) + chebU (X : ℂ[X]) (2 * m - 1) ≠ 0 := by
      rintro h0
      rw [h0, rootMultiplicity_zero] at hW1
      exact zero_ne_one hW1
    have hWd : ((X + 2) * P - 1).eval d = 0 := by
      rw [hid, eval_neg, neg_eq_zero]
      exact (rootMultiplicity_pos hW0).1 (by rw [hW1]; exact Nat.one_pos)
    have hm2 : (X + -2) * P - 1 = ((X + 2) * P - 1) - 4 * P := by ring
    have hNm : ((X + -2) * P - 1).rootMultiplicity d = 0 := by
      refine rootMultiplicity_eq_zero_of_eval_ne ?_
      rw [hm2, eval_sub, hWd, eval_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero (by simp) hPc
    have hNp : ((X + 2) * P - 1).rootMultiplicity d = 1 := by
      rw [hid, neg_eq_neg_one_mul, ← C_1, ← C_neg, rootMultiplicity_C_mul (by norm_num), hW1]
    rw [rootMultiplicity_mul (mul_ne_zero (hne 2) (hne (-2))),
      rootMultiplicity_mul (mul_ne_zero hP0 hP0), rootMultiplicity_eq_zero_of_eval_ne hPc,
      hNm, hNp] at h
    exact Nat.not_even_one h

end AJConjecture
