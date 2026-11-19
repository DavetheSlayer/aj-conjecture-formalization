import Mathlib
import AJFamily.Skein.TorusSequenceIdentity
import AJHandoff.Geometry.GeoLongKnotLaurent
import AJHandoff.Geometry.GeoLongKnotScalar

/-!
# The reduced coloured Jones polynomial of `W_k` is a Laurent polynomial

For `k ≥ 1` and `N ≥ 1`, the reduced formula `F_N = J_{W_k}(N)/[N]` (`torusReducedFormula`) is the
image of an integral Laurent polynomial. Route: the cabled long knot `longKnotOp K (N-1)` has
Laurent-polynomial matrix entries and commutes with the Jones–Wenzl projector, which fixes the
highest-weight basis vector; so the scalar by which the long knot acts on the projector (the
reduced invariant up to the framing unit) is a diagonal matrix entry of the long knot, hence a
Laurent polynomial; compare with `laurentToField_coloredJones_whiteheadTorusKnot`.
-/

namespace AJConjecture

/-- An integer power of an element of `ℚ(t)` which is a unit of `ℤ[t, t⁻¹]` (it and its inverse
are Laurent polynomials) is a Laurent polynomial. -/
private theorem zpow_mem_laurentToField_range {x : RatFunc ℚ} (hx : x ∈ laurentToField.range)
    (hx' : x⁻¹ ∈ laurentToField.range) (n : ℤ) : x ^ n ∈ laurentToField.range := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact pow_mem hx m
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem hx' m

/-- Every integer power of the framing scalar `θ_c` is a Laurent polynomial. -/
private theorem kinkScalar_zpow_mem_range (c : ℕ) (n : ℤ) :
    kinkScalar c ^ n ∈ laurentToField.range := by
  refine zpow_mem_laurentToField_range ⟨(-1) ^ c * LaurentPolynomial.T ((c : ℤ) * ((c : ℤ) + 2)),
    ?_⟩ ⟨(-1) ^ c * LaurentPolynomial.T (-((c : ℤ) * ((c : ℤ) + 2))), ?_⟩ n
  · rw [map_mul, map_pow, map_neg, map_one, laurentToField_T, kinkScalar]
  · rw [map_mul, map_pow, map_neg, map_one, laurentToField_T, kinkScalar, mul_inv, ← inv_pow,
      inv_neg_one, zpow_neg]

/-- The reduced coloured Jones polynomial of `W_k` is integral: `F_N ∈ ℤ[t^±]`. -/
theorem exists_laurent_torusReducedFormula (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    ∃ P : LaurentPolynomial ℤ, laurentToField P = torusReducedFormula (2 * k + 1) N := by
  obtain ⟨c, rfl⟩ : ∃ c, N = c + 1 := ⟨N - 1, by omega⟩
  set K := whiteheadTorusKnot k hk
  set ℓ := longKnotOp K c (fun _ ↦ false) (fun _ ↦ false)
  have hJ : laurentToField (coloredJones K ((c + 1 : ℕ) : ℤ)) =
      quantumInt ((c + 1 : ℕ) : ℤ) * torusReducedFormula (2 * k + 1) (c + 1) := by
    rw [laurentToField_coloredJones_whiteheadTorusKnot, torusWhiteheadFormula,
      ite_eq_left (by omega : (0 : ℤ) < ((c + 1 : ℕ) : ℤ)), Int.toNat_natCast]
  have hC : coloredJones K ((c + 1 : ℕ) : ℤ) = coloredJonesPos K c := by
    rw [coloredJones, ite_eq_left (by omega : (0 : ℤ) < ((c + 1 : ℕ) : ℤ)), Int.toNat_natCast,
      Nat.add_sub_cancel]
  have hT : knotTrace K c (jwAt c 0 c) = ℓ * loopScalar c := by
    rw [knotTrace_eq_qtr_longKnotOp, longKnotOp_mul_jwAt_eq_smul, qtr_smul, qtr_jwAt]
  rw [hC, laurentToField_coloredJonesPos, hT, loopScalar] at hJ
  have hq : quantumInt ((c + 1 : ℕ) : ℤ) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h1 : ((-1 : RatFunc ℚ) ^ c) * (-1) ^ c = 1 := by
    rw [← mul_pow]
    norm_num
  have hF : torusReducedFormula (2 * k + 1) (c + 1) =
      kinkScalar c ^ (-writhe K.word) * ℓ := by
    apply mul_left_cancel₀ hq
    push_cast at hJ ⊢
    linear_combination (-1 : RatFunc ℚ) * hJ +
      (kinkScalar c ^ (-writhe K.word) * ℓ * quantumInt ((c : ℤ) + 1)) * h1
  obtain ⟨P, hP⟩ := mul_mem (kinkScalar_zpow_mem_range c (-writhe K.word))
    (longKnotOp_apply_mem_range K c (fun _ ↦ false) (fun _ ↦ false))
  exact ⟨P, hP.trans hF.symm⟩

/-- The coloured Jones polynomial of `W_k` is `[N]` times the reduced formula, `N ≥ 1`. -/
theorem laurentToField_coloredJones_whiteheadTorusKnot_eq (k : ℕ) (hk : 1 ≤ k) (N : ℕ)
    (hN : 1 ≤ N) :
    laurentToField (coloredJones (whiteheadTorusKnot k hk) N) =
      quantumInt N * torusReducedFormula (2 * k + 1) N := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [laurentToField_coloredJones_whiteheadTorusKnot, torusWhiteheadFormula, ite_eq_left hN',
    Int.toNat_natCast]

end AJConjecture
