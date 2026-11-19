import Mathlib
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.AbNodeNoSeparation
import AJConjecture.ExtraFactorPrime
import AJConjecture.QAlgPseudoFactorNormalize
import AJTwist.Factor.TwFOnePrime
import AJTwist.Factor.TwFOneWeyl
import AJTwist.Quantum.TwQTransferOp
import AJTwist.Factor.TwFBlockCount
import AJTwist.Factor.TwFRankOneRight
import AJTwist.Factor.TwFRankOneLeft
import AJTwist.Factor.TwFOneEbNoSeparation
import AJTwist.Factor.TwFOneAbNode

/-!
# `P_1` has no proper right factor (TwF, unit F3)

Source: revision 5, Section 5.5 (`operators.tex`, "The rank-one split at `a = 1`"): "The simple
crossing with `E` has already forced `E` and `B_1` into the same factor of any partition. The only
remaining split is the block `u - 1` against their product. … Both residues contradict
integrality, excluding the remaining partition. This proves irreducibility of the physical `P_1`."

`natDegree_eq_zero_or_of_oreMul_eq_famTransferOp_one`: in every pseudo-factorisation
`β · famTransferOp 1 = S ⋆ R` the right factor has degree `0` or `5`.

Route: normalise (`exists_normalized_pseudoFactor`, `specialize_famTransferOp_ne_zero 1`); then
`β̄ P₀ = S₀ R₀`, the degrees of `S₀`, `R₀` are those of `S`, `R` and add up to `5`
(`natDegree_specialize_famTransferOp 1`, `natDegree_famTransferOp 1`, `natDegree_oreMul`), and
`κ₁ P₀ = κ₂ (L - 1) E B_1` with three pairwise non-associated primes of the comparison ring
(`prime_toComparison_X_sub_one`, `prime_toComparison_extraFactor`,
`prime_toComparison_twistPoly_one`, `not_toComparison_dvd_twistPoly_one`). By
`toComparison_extraFactor_dvd_iff_twistPoly_one_dvd` the factor `R₀` contains both or neither of
`E`, `B_1`. Four cases:
* all three blocks divide `R₀`: degree `5`; none does: all divide `S₀`, degree `0`
  (`natDegree_le_of_toComparison_dvd`);
* only `L - 1` divides `R₀`: then `E B_1 ∣ S₀`, so `deg R = 1` and `R₀(M, 1) = 0`
  (`eval_one_eq_zero_of_toComparison_X_sub_one_dvd`): excluded by
  `not_rankOne_right_of_weylSymbol_eq_zero` at a point `m₀` with `(m₀²)² - 3 m₀² + 1 = 0`
  (`famOne_abNode_data`, `evalIntPoint_weylSymbol_famTransferOp_one_abNode`);
* only `E B_1` divides `R₀`: then `L - 1 ∣ S₀`, `deg S = 1`, `S₀(M, 1) = 0`: excluded by
  `not_rankOne_left_of_weylSymbol_eq_zero` at the same point.

`natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_one` restates it for `twTransferOp 1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- There is a point `m₀` of the degenerate abelian node `K = 3`. -/
private theorem exists_abNode_root_twfOneIrred :
    ∃ m₀ : ℂ, (m₀ ^ 2) ^ 2 - 3 * m₀ ^ 2 + 1 = 0 := by
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (one_ne_zero (α := ℂ))
    (IsAlgClosed.isSquare (discrim (1 : ℂ) (-3) 1))
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- The constant coefficient of `E` is not zero. -/
private theorem coeff_zero_extraFactor_ne_zero_twfOneIrred : extraFactor.coeff 0 ≠ 0 := by
  rw [extraFactor_coeff_zero]
  exact pow_ne_zero 4 X_ne_zero

/-- The constant coefficient of `B_1` is not zero. -/
private theorem coeff_zero_twistPoly_one_ne_zero_twfOneIrred : (twistPoly 1).coeff 0 ≠ 0 := by
  rw [coeff_zero_twistPoly]
  exact pow_ne_zero _ X_ne_zero

/-- The constant coefficient of `L - 1` is not zero. -/
private theorem coeff_zero_X_sub_one_ne_zero_twfOneIrred : (X - 1 : ℤ[X][X]).coeff 0 ≠ 0 := by
  simp

/-- A nonzero polynomial whose image in the comparison ring is divisible by `E` and `B_1` has
degree at least `4` in `L`. -/
private theorem four_le_natDegree_of_dvd_twfOneIrred {g : ℤ[X][X]} (hg : g ≠ 0)
    (h2 : toComparison extraFactor ∣ toComparison g)
    (h3 : toComparison (twistPoly 1) ∣ toComparison g) : 4 ≤ g.natDegree := by
  have hE0 : extraFactor ≠ 0 := fun h0 ↦ coeff_zero_extraFactor_ne_zero_twfOneIrred (by simp [h0])
  have hB0 : twistPoly 1 ≠ 0 := fun h0 ↦
    coeff_zero_twistPoly_one_ne_zero_twfOneIrred (by simp [h0])
  obtain ⟨q, hq⟩ := h2
  have h3' : toComparison (twistPoly 1) ∣ q := by
    rw [hq] at h3
    exact (prime_toComparison_twistPoly_one.dvd_or_dvd h3).resolve_left fun hdvd ↦
      not_toComparison_dvd_twistPoly_one.2
        ((prime_toComparison_twistPoly_one.dvd_prime_iff_associated
          prime_toComparison_extraFactor).mp hdvd).dvd'
  obtain ⟨q', rfl⟩ := h3'
  have hall : toComparison (extraFactor * twistPoly 1) ∣ toComparison g := by
    rw [hq, map_mul]
    exact ⟨q', by ring⟩
  have hc : (extraFactor * twistPoly 1).coeff 0 ≠ 0 := by
    rw [mul_coeff_zero]
    exact mul_ne_zero coeff_zero_extraFactor_ne_zero_twfOneIrred
      coeff_zero_twistPoly_one_ne_zero_twfOneIrred
  have hle := natDegree_le_of_toComparison_dvd hc hg hall
  rwa [natDegree_mul hE0 hB0, natDegree_extraFactor, natDegree_twistPoly] at hle

/-- A nonzero polynomial whose image in the comparison ring is divisible by `L - 1` has degree
at least `1` in `L`. -/
private theorem one_le_natDegree_of_dvd_twfOneIrred {g : ℤ[X][X]} (hg : g ≠ 0)
    (h1 : toComparison (X - 1) ∣ toComparison g) : 1 ≤ g.natDegree := by
  have hle := natDegree_le_of_toComparison_dvd coeff_zero_X_sub_one_ne_zero_twfOneIrred hg h1
  rwa [natDegree_X_sub_one] at hle

/-- In a normalised pseudo-factorisation of `P_1` the block `L - 1` is not separated from `E`:
the two remaining partitions are excluded by the rank-one tests at `K = 3`. -/
private theorem X_sub_one_dvd_iff_extraFactor_dvd_of_normalized_twfOneIrred {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S R : RecOp}
    (hS : specialize S ≠ 0) (hR : specialize R ≠ 0)
    (h : C β * famTransferOp 1 = oreMul coeffShift S R) :
    toComparison (X - 1) ∣ toComparison (specialize R) ↔
      toComparison extraFactor ∣ toComparison (specialize R) := by
  obtain ⟨m₀, hab⟩ := exists_abNode_root_twfOneIrred
  obtain ⟨hm0, hlead, hconst, hH0, hH1⟩ := famOne_abNode_data hab
  have hW := evalIntPoint_weylSymbol_famTransferOp_one_abNode hab
  have hd0 := natDegree_specialize_famTransferOp 1 le_rfl
  have hd1 := natDegree_famTransferOp 1 le_rfl
  have hdeg : (specialize (famTransferOp 1)).natDegree = (famTransferOp 1).natDegree := by
    rw [hd0, hd1]
  have hβ0 : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  have hS0 : S ≠ 0 := fun h0 ↦ hS (by rw [h0, map_zero])
  have hR0 : R ≠ 0 := fun h0 ↦ hR (by rw [h0, map_zero])
  have hsp : C (β.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize (famTransferOp 1) =
      specialize S * specialize R := by
    have hC : specialize (C β) = C (β.map (Polynomial.evalRingHom (-1 : ℤ))) :=
      Polynomial.map_C _
    rw [← specialize_oreMul, ← h, map_mul, hC]
  have hdegOre : S.natDegree + R.natDegree = 2 * 1 + 3 := by
    rw [← natDegree_oreMul coeffShift_injective hS0 hR0, ← h, natDegree_C_mul hβ0, hd1]
  have hdeg₀ : (specialize S).natDegree + (specialize R).natDegree = 2 * 1 + 3 := by
    rw [← natDegree_mul hS hR, ← hsp, natDegree_C_mul hβ, hd0]
  have hSle : (specialize S).natDegree ≤ S.natDegree := natDegree_map_le
  have hRle : (specialize R).natDegree ≤ R.natDegree := natDegree_map_le
  have hκ₁ : ((X ^ 2 - 1) ^ (2 * 1 + 3) * (X ^ 4 - 1) ^ (2 * 1 + 3) : ℤ[X]) ≠ 0 := fun h0 ↦ by
    have := eval_symbolLeft_ne_zero 1 (m₀ := 2) (by norm_num) (by norm_num)
    rw [h0, Polynomial.map_zero, eval_zero] at this
    exact this rfl
  have hprod : ∀ {p : ℤ[X][X]}, p ∣ (X - 1) * extraFactor * twistPoly 1 →
      toComparison p ∣ toComparison (specialize S) * toComparison (specialize R) := by
    intro p hp
    have hdvdP : toComparison p ∣ toComparison (specialize (famTransferOp 1)) := by
      rw [← (isUnit_toComparison_coeff_of_ne_zero hκ₁).dvd_mul_left, ← map_mul,
        specialize_famTransferOp_mul_eq 1 le_rfl, map_mul]
      exact (map_dvd toComparison hp).mul_left _
    rw [← map_mul, ← hsp, map_mul]
    exact hdvdP.mul_left _
  have hl23 := toComparison_extraFactor_dvd_iff_twistPoly_one_dvd hβ0 h
  constructor
  · intro h1
    by_contra hE
    have hSE := (prime_toComparison_extraFactor.dvd_or_dvd
      (hprod ⟨(X - 1) * twistPoly 1, by ring⟩)).resolve_right hE
    have hSB := (prime_toComparison_twistPoly_one.dvd_or_dvd
      (hprod ⟨(X - 1) * extraFactor, by ring⟩)).resolve_right fun hb ↦ hE (hl23.mpr hb)
    have h4 := four_le_natDegree_of_dvd_twfOneIrred hS hSE hSB
    have h1' := one_le_natDegree_of_dvd_twfOneIrred hR h1
    exact not_rankOne_right_of_weylSymbol_eq_zero hm0 hdeg hlead hconst hH0 hH1 hW hβ h
      (by omega) (eval_one_eq_zero_of_toComparison_X_sub_one_dvd h1)
  · intro hE
    by_contra h1
    have hS1 := (prime_toComparison_X_sub_one.dvd_or_dvd
      (hprod ⟨extraFactor * twistPoly 1, by ring⟩)).resolve_right h1
    have h4 := four_le_natDegree_of_dvd_twfOneIrred hR hE (hl23.mp hE)
    have h1' := one_le_natDegree_of_dvd_twfOneIrred hS hS1
    exact not_rankOne_left_of_weylSymbol_eq_zero hm0 hdeg hlead hconst hH0 hH1 hW hβ h
      (by omega) (eval_one_eq_zero_of_toComparison_X_sub_one_dvd hS1)

/-- No right pseudo-factor of `P_1` separates `L - 1` from `E`. -/
private theorem X_sub_one_dvd_iff_extraFactor_dvd_twfOneIrred {β : Coeff} (hβ : β ≠ 0)
    {S R : RecOp} (h : C β * famTransferOp 1 = oreMul coeffShift S R) :
    toComparison (X - 1) ∣ toComparison (specialize R) ↔
      toComparison extraFactor ∣ toComparison (specialize R) := by
  obtain ⟨β', S', R', hβ', hS', hR', -, -, h', a, ha⟩ :=
    exists_normalized_pseudoFactor (specialize_famTransferOp_ne_zero 1 le_rfl) hβ h
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · rw [ha0, pow_zero, map_one, map_one, one_mul] at ha
    subst ha
    exact X_sub_one_dvd_iff_extraFactor_dvd_of_normalized_twfOneIrred hβ' hS' hR' h'
  · have hspecC : ∀ c : Coeff, specialize (C c) = C (c.map (Polynomial.evalRingHom (-1))) :=
      fun c ↦ Polynomial.map_C _
    have h0 : specialize R = 0 := by
      rw [ha, map_mul, hspecC, Polynomial.map_C, coe_evalRingHom, eval_pow, eval_add, eval_X,
        eval_one, neg_add_cancel, zero_pow ha0.ne', map_zero, map_zero, zero_mul]
    rw [h0, map_zero]
    exact ⟨fun _ ↦ dvd_zero _, fun _ ↦ dvd_zero _⟩

/-- The operator `P_1 = famTransferOp 1` has no proper right factor over `ℚ(t, M)`: in every
pseudo-factorisation `β · P_1 = S ⋆ R` the right factor has degree `0` or `5`. -/
theorem natDegree_eq_zero_or_of_oreMul_eq_famTransferOp_one {β : Coeff} (hβ : β ≠ 0)
    {S R : RecOp} (h : C β * famTransferOp 1 = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = 5 := by
  have hκ₁ : ((X ^ 2 - 1) ^ (2 * 1 + 3) * (X ^ 4 - 1) ^ (2 * 1 + 3) : ℤ[X]) ≠ 0 := fun h0 ↦ by
    have := eval_symbolLeft_ne_zero 1 (m₀ := 2) (by norm_num) (by norm_num)
    rw [h0, Polynomial.map_zero, eval_zero] at this
    exact this rfl
  have hκ₂ : ((famDet 1 (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)) : ℤ[X]) ≠ 0 :=
    fun h0 ↦ by
      have := eval_symbolRight_ne_zero 1 (m₀ := 2) (by norm_num) (by norm_num)
      rw [h0, Polynomial.map_zero, eval_zero] at this
      exact this rfl
  have hdeg : (specialize (famTransferOp 1)).natDegree = (famTransferOp 1).natDegree := by
    rw [natDegree_specialize_famTransferOp 1 le_rfl, natDegree_famTransferOp 1 le_rfl]
  have h12 : ¬ toComparison (X - 1) ∣ toComparison extraFactor := fun hdvd ↦ by
    have h0 := eval_one_eq_zero_of_toComparison_X_sub_one_dvd hdvd
    have h1 := congrArg (Polynomial.eval 1) h0
    rw [extraFactor] at h1
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one,
      eval_ofNat, eval_zero] at h1
    norm_num at h1
  have key := natDegree_eq_zero_or_of_linked_blocks hκ₁ hκ₂
    (specialize_famTransferOp_mul_eq 1 le_rfl) hdeg prime_toComparison_X_sub_one
    prime_toComparison_extraFactor prime_toComparison_twistPoly_one
    coeff_zero_X_sub_one_ne_zero_twfOneIrred coeff_zero_extraFactor_ne_zero_twfOneIrred
    coeff_zero_twistPoly_one_ne_zero_twfOneIrred h12 not_toComparison_dvd_twistPoly_one.1
    not_toComparison_dvd_twistPoly_one.2
    @X_sub_one_dvd_iff_extraFactor_dvd_twfOneIrred
    @toComparison_extraFactor_dvd_iff_twistPoly_one_dvd hβ h
  rwa [natDegree_famTransferOp 1 le_rfl] at key

/-- The same statement for `twTransferOp 1`. -/
theorem natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_one {β : Coeff} (hβ : β ≠ 0)
    {S R : RecOp} (h : C β * twTransferOp 1 = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = (twTransferOp 1).natDegree := by
  have h1 : twTransferOp 1 = famTransferOp 1 := by
    have := twTransferOp_natCast 1 le_rfl
    simpa using this
  rw [h1] at h ⊢
  rw [natDegree_famTransferOp 1 le_rfl]
  exact natDegree_eq_zero_or_of_oreMul_eq_famTransferOp_one hβ h

end AJConjecture
