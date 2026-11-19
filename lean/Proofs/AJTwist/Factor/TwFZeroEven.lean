import Mathlib
import AJConjecture.QAlgOreMulMap
import AJTwist.Factor.TwFZeroUnique
import AJTwist.Factor.TwFZeroJet
import AJTwist.Factor.TwFZeroEvenDefs

/-!
# Descent of a right factor of order one of `P_0` to the variable `x = M²` (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`): "Suppose `u - r_0` is a right divisor over
`ℚ(t, M)`. The involution `M ↦ -M` commutes with the shift and fixes `P`; uniqueness implies
`r_0 ∈ ℚ(t, x)`. Only after this descent does the order-four automorphism `t ↦ i t` commute with
the shift. … Apply uniqueness over `ℂ(t, x)` and intersect the fixed field with `ℚ(t, x)` to get
`r_0 ∈ ℚ(q, x)`. Here `σ(x) = x/q`."

**Only the first descent is used.** After `M ↦ -M` the solution lives in `ℚ(t, x)` with the shift
`x ↦ t⁴ x = q x`; the rest of the argument (normal form over the principal ideal domain
`ℚ(t)[x]`, reduction at `t = -1`, value at `x = 0`, limit at infinity) works over the constant
field `ℚ(t)` as it stands, because the coefficients `b_i` lie in `ℚ(q)[x]`, the bad primes
`x`, `q^j x - 1` are defined over `ℚ(q)`, and the value at `x = 0` of the solution is forced to be
an exact power of `q`. So the second descent `t ↦ i t` of the paper (and with it the field `ℂ`)
is not needed. The first descent is needed: over `ℚ(t)[M]` the shift is `M ↦ t² M` and the same
count gives only a half-integer.

The maps `twfNegM`, `twfSq`, `twfShiftX` and the operator `twfZeroOpX` are in
`AJTwist/Factor/TwFZeroEvenDefs.lean`.

* `twf_zero_exists_even_solution` (the descent): a right pseudo-factor of degree one of `P_0`
  yields `e₀, e₁ ∈ ℤ[t][x]` with `e₁(-1, x) ≠ 0`, `e₀(-1, x) = -e₁(-1, x)`, solving the Riccati
  equation of `twfZeroOpX` for the shift `x ↦ t⁴ x`, and with logarithmic first jet
  `2 (x + 1)/(x - 1)`:
  `(ė₀ ē₁ - ē₀ ė₁)(x - 1) = ē₀ ē₁ · 2 (x + 1)`.

Route for the descent. Normalise the factorisation (`exists_normalized_pseudoFactor`,
`specialize_twTransferOp_ne_zero 0`): `R' = r₁ L + r₀`, `r̄₀ = -r̄₁ ≠ 0`
(`twf_zero_rightFactor_symbol`). The coefficients of `twTransferOp 0` are fixed by `twfNegM`
(they are `Polynomial.comp` with `C (X ^ 12) * X ^ 2`), so applying `Polynomial.map twfNegM`
(`map_oreMul`) gives a second right pseudo-factor `ν R'`; by `twf_zero_rightFactor_unique`,
`r₀ ν(r₁) = r₁ ν(r₀)`. Hence `ν(r₁) r₁` and `ν(r₁) r₀` are fixed by `ν`: they are `twfSq e₁`,
`twfSq e₀`. `C (ν r₁) * R'` is again a right pseudo-factor (multiply the cofactor coefficientwise
by `∏_{i ≠ j} τ^i(ν r₁)`), with scalar of nonzero value at `t = -1`, also for `twZeroExplicitOp`
(`exists_pseudoFactor_twZeroExplicitOp`; the determinant scalar is nonzero at `t = -1` by
`twDet_one_eval_ne_zero`). Then `oreRiccati_eq_zero_of_pseudoFactor`, `oreRiccati_map` along the
injective `twfSq`, and `nodeNumer_mul_of_rightFactor_twZeroExplicitOp` read through `twfSq`
(`coeffJet (twfSq e) = (coeffJet e).comp (X ^ 2)`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The involution `M ↦ -M` commutes with the shift. -/
private theorem twfNegM_coeffShift_twfZeroEven (c : Coeff) :
    twfNegM (coeffShift c) = coeffShift (twfNegM c) := by
  have hq : (C (X ^ 2) * X : Coeff).comp (-X) = (-X : Coeff).comp (C (X ^ 2) * X) := by
    rw [mul_comp, C_comp, X_comp, neg_comp, X_comp]
    ring
  change (c.comp (C (X ^ 2) * X)).comp (-X) = (c.comp (-X)).comp (C (X ^ 2) * X)
  rw [comp_assoc, comp_assoc, hq]

/-- `M ↦ -M` is an involution. -/
private theorem twfNegM_twfNegM_twfZeroEven (c : Coeff) : twfNegM (twfNegM c) = c :=
  comp_neg_X_comp_neg_X c

/-- `M ↦ -M` is injective. -/
private theorem twfNegM_injective_twfZeroEven : Function.Injective twfNegM :=
  Function.LeftInverse.injective twfNegM_twfNegM_twfZeroEven

/-- `M ↦ -M` fixes the operator `P_0`. -/
private theorem map_twfNegM_twTransferOp_zero_twfZeroEven :
    (twTransferOp 0).map twfNegM = twTransferOp 0 := by
  have hq : (C (X ^ (4 * 3)) * X ^ 2 : Coeff).comp (-X) = C (X ^ (4 * 3)) * X ^ 2 := by
    rw [mul_comp, C_comp, X_pow_comp]
    ring
  have hfix : ∀ b : Coeff, twfNegM (b.comp (C (X ^ (4 * 3)) * X ^ 2)) =
      b.comp (C (X ^ (4 * 3)) * X ^ 2) := by
    intro b
    change (b.comp (C (X ^ (4 * 3)) * X ^ 2)).comp (-X) = b.comp (C (X ^ (4 * 3)) * X ^ 2)
    rw [comp_assoc, hq]
  rw [twTransferOp_zero, twCramerOp, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, hfix]

/-- The value at `t = -1` commutes with `M ↦ -M`. -/
private theorem map_evalRingHom_twfNegM_twfZeroEven (c : Coeff) :
    (twfNegM c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      (c.map (Polynomial.evalRingHom (-1 : ℤ))).comp (-X) := by
  change (c.comp (-X)).map (Polynomial.evalRingHom (-1 : ℤ)) = _
  rw [map_comp, Polynomial.map_neg, map_X]

/-- The value at `t = -1` commutes with `x ↦ M²`. -/
private theorem map_evalRingHom_twfSq_twfZeroEven (c : Coeff) :
    (twfSq c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      (c.map (Polynomial.evalRingHom (-1 : ℤ))).comp (X ^ 2) := by
  change (c.comp (X ^ 2)).map (Polynomial.evalRingHom (-1 : ℤ)) = _
  rw [map_comp, Polynomial.map_pow, map_X]

/-- Base change `ℤ[M] → ℂ[M]` is injective. -/
private theorem map_intCast_injective_twfZeroEven :
    Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
  Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int

/-- The first jet of coefficients is additive. -/
private theorem coeffJet_add_twfZeroEven (a b : Coeff) :
    coeffJet (a + b) = coeffJet a + coeffJet b := by
  apply map_intCast_injective_twfZeroEven
  rw [← complexJet_coeffToComplex, map_add, complexJet_add, Polynomial.map_add,
    complexJet_coeffToComplex, complexJet_coeffToComplex]

/-- The Leibniz rule for the first jet of coefficients. -/
private theorem coeffJet_mul_twfZeroEven (a b : Coeff) :
    coeffJet (a * b) = coeffJet a * b.map (Polynomial.evalRingHom (-1)) +
      a.map (Polynomial.evalRingHom (-1)) * coeffJet b := by
  apply map_intCast_injective_twfZeroEven
  rw [← complexJet_coeffToComplex, map_mul, complexJet_mul, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_mul, complexJet_coeffToComplex,
    complexJet_coeffToComplex, complexSpec_coeffToComplex, complexSpec_coeffToComplex]

/-- The first jet commutes with `x ↦ M²`. -/
private theorem coeffJet_twfSq_twfZeroEven (c : Coeff) :
    coeffJet (twfSq c) = (coeffJet c).comp (X ^ 2) := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, coeffJet_add_twfZeroEven, hp, hq, coeffJet_add_twfZeroEven, add_comp]
  | monomial n a =>
    have h1 : twfSq (monomial n a) = monomial (2 * n) a := by
      change (monomial n a).comp (X ^ 2) = _
      rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial]
    have h2 : ∀ m : ℕ, coeffJet (monomial m a) = monomial m ((derivative a).eval (-1)) := by
      intro m
      rw [coeffJet, sum_monomial_index]
      rw [derivative_zero, eval_zero, monomial_zero_right]
    rw [h1, h2, h2, monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial]

/-- The determinant scalar of the explicit operator is nonzero at `t = -1`. -/
private theorem map_twDet_comp_ne_zero_twfZeroEven :
    ((twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)).map
      (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
  have hq : (Polynomial.evalRingHom (-1 : ℤ)) (X ^ 4) = 1 := by
    rw [coe_evalRingHom, eval_pow, eval_X]
    norm_num
  have hs : (C (X ^ 12) * X ^ 2 : Coeff).map (Polynomial.evalRingHom (-1 : ℤ)) = X ^ 2 := by
    rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, coe_evalRingHom, eval_pow,
      eval_X]
    norm_num
  rw [map_comp, map_twDet, hq, hs]
  intro h
  have h0 : twDet 3 (1 : ℤ) = 0 :=
    expand_injective (R := ℤ) two_pos (by rw [expand_eq_comp_X_pow, h, map_zero])
  have h1 := twDet_one_eval_ne_zero 3 (x₀ := 0) (by norm_num) (by norm_num)
  rw [h0, Polynomial.map_zero, eval_zero] at h1
  exact h1 rfl

/-- Normalisation: a right pseudo-factor of degree one of `P_0` with scalar nonzero at
`t = -1` and symbol proportional to `L - 1`. -/
private theorem exists_normalized_linear_twfZeroEven {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp 0 = oreMul coeffShift S R) (hR : R.natDegree = 1) :
    ∃ (β' : Coeff) (S' R' : RecOp), β'.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      R'.natDegree = 1 ∧ C β' * twTransferOp 0 = oreMul coeffShift S' R' ∧
      (R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      (R'.coeff 0).map (Polynomial.evalRingHom (-1 : ℤ)) =
        -(R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  obtain ⟨β', S', R', hβ', -, hR', -, hRdeg, h', -⟩ :=
    exists_normalized_pseudoFactor (specialize_twTransferOp_ne_zero 0) hβ h
  have hR'1 : R'.natDegree = 1 := hRdeg.trans hR
  have hsym := twf_zero_rightFactor_symbol hβ' h' hR'1
  have hdeg : (specialize R').natDegree < 2 := by
    have hle : (specialize R').natDegree ≤ R'.natDegree := by
      rw [specialize, coe_mapRingHom]
      exact natDegree_map_le
    omega
  rw [eval_eq_sum_range' hdeg] at hsym
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, mul_one,
    coeff_specialize] at hsym
  have h01 := eq_neg_of_add_eq_zero_left hsym
  refine ⟨β', S', R', hβ', hR'1, h', fun h1 ↦ hR' ?_, h01⟩
  rw [(specialize R').as_sum_range' 2 hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_specialize, h01, h1,
    neg_zero, monomial_zero_right, add_zero]

/-- By uniqueness, the right factor and its image under `M ↦ -M` are proportional. -/
private theorem twfNegM_proportional_twfZeroEven {β' : Coeff} (hβ' : β' ≠ 0) {S' R' : RecOp}
    (h' : C β' * twTransferOp 0 = oreMul coeffShift S' R') (hR' : R'.natDegree = 1) :
    R'.coeff 0 * twfNegM (R'.coeff 1) = R'.coeff 1 * twfNegM (R'.coeff 0) := by
  have hmap := congrArg (Polynomial.map twfNegM) h'
  rw [map_oreMul twfNegM coeffShift coeffShift twfNegM_coeffShift_twfZeroEven,
    Polynomial.map_mul, map_C, map_twfNegM_twTransferOp_zero_twfZeroEven] at hmap
  have hν : twfNegM β' ≠ 0 := (map_ne_zero_iff twfNegM twfNegM_injective_twfZeroEven).mpr hβ'
  have hdeg : (R'.map twfNegM).natDegree = 1 := by
    rw [natDegree_map_eq_of_injective twfNegM_injective_twfZeroEven, hR']
  have hu := twf_zero_rightFactor_unique hβ' hν h' hmap hR' hdeg
  rwa [coeff_map, coeff_map] at hu

/-- The coefficients of the right factor multiplied by `ν(r₁)` are polynomials in `M²`. -/
private theorem exists_twfSq_pair_twfZeroEven {r₀ r₁ : Coeff}
    (h : r₀ * twfNegM r₁ = r₁ * twfNegM r₀) :
    ∃ e₀ e₁ : Coeff, twfSq e₀ = twfNegM r₁ * r₀ ∧ twfSq e₁ = twfNegM r₁ * r₁ := by
  obtain ⟨e₀, he₀⟩ := exists_twfSq_eq_of_twfNegM_eq (c := twfNegM r₁ * r₀)
    (by rw [map_mul, twfNegM_twfNegM_twfZeroEven, ← h, mul_comm])
  obtain ⟨e₁, he₁⟩ := exists_twfSq_eq_of_twfNegM_eq (c := twfNegM r₁ * r₁)
    (by rw [map_mul, twfNegM_twfNegM_twfZeroEven, mul_comm])
  exact ⟨e₀, e₁, he₀, he₁⟩

/-- Every multiple of the right factor solves the Riccati equation of the explicit operator. -/
private theorem oreRiccati_twZeroExplicitOp_eq_zero_twfZeroEven {β' : Coeff} (hβ' : β' ≠ 0)
    {S' R' : RecOp} (h' : C β' * twTransferOp 0 = oreMul coeffShift S' R')
    (hR' : R'.natDegree = 1) (γ : Coeff) :
    oreRiccati coeffShift 3 twZeroExplicitOp (γ * R'.coeff 0) (γ * R'.coeff 1) = 0 := by
  have hP : (twTransferOp 0).natDegree ≤ 3 := by rw [natDegree_twTransferOp, twWindow_zero]
  have h0 := oreRiccati_eq_zero_of_pseudoFactor coeffShift_injective hβ' h' hR' hP
  have h1 := congrArg (fun P : RecOp ↦ oreRiccati coeffShift 3 P (R'.coeff 0) (R'.coeff 1))
    twZeroExplicitOp_mul_eq
  simp only [oreRiccati_C_mul, h0, mul_zero] at h1
  rw [oreRiccati_mul_left, (mul_eq_zero.mp h1).resolve_left twZero_scalars_ne_zero.1, mul_zero]

/-- The logarithmic first jet of the right factor, in the variable `M`. -/
private theorem jet_identity_twfZeroEven {β' : Coeff}
    (hβ' : β'.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S' R' : RecOp}
    (h' : C β' * twTransferOp 0 = oreMul coeffShift S' R') (hR' : R'.natDegree = 1) :
    (coeffJet (R'.coeff 0) * (R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) -
        (R'.coeff 0).map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet (R'.coeff 1)) *
        (X ^ 2 - 1) =
      (R'.coeff 0).map (Polynomial.evalRingHom (-1 : ℤ)) *
        (R'.coeff 1).map (Polynomial.evalRingHom (-1 : ℤ)) * (2 * (X ^ 2 + 1)) := by
  obtain ⟨S'', hS''⟩ := exists_pseudoFactor_twZeroExplicitOp h'
  have hsym := twf_zero_rightFactor_symbol hβ' h' hR'
  have hD : (β' * (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)).map
      (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    rw [Polynomial.map_mul]
    exact mul_ne_zero hβ' map_twDet_comp_ne_zero_twfZeroEven
  have hn := nodeNumer_mul_of_rightFactor_twZeroExplicitOp hD hS'' hR' hsym
  rwa [nodeNumer, nodeDenom, hR', coeff_specializeJet, coeff_specializeJet, coeff_specialize,
    coeff_specialize] at hn

/-- The descent: a right pseudo-factor of degree one of `P_0` yields a solution in `ℤ[t][x]` of
the Riccati equation of the explicit operator for the shift `x ↦ t⁴ x`, equal to `1` at `t = -1`
and with logarithmic first jet `2 (x + 1)/(x - 1)`. -/
theorem twf_zero_exists_even_solution {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp 0 = oreMul coeffShift S R) (hR : R.natDegree = 1) :
    ∃ e₀ e₁ : Coeff, e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ∧
      oreRiccati twfShiftX 3 twfZeroOpX e₀ e₁ = 0 ∧
      (coeffJet e₀ * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) -
          e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * coeffJet e₁) * (X - 1) =
        e₀.map (Polynomial.evalRingHom (-1 : ℤ)) * e₁.map (Polynomial.evalRingHom (-1 : ℤ)) *
          (2 * (X + 1)) := by
  obtain ⟨β', S', R', hβ', hR', h', hr₁, h01⟩ := exists_normalized_linear_twfZeroEven hβ h hR
  have hβ'0 : β' ≠ 0 := fun h0 ↦ hβ' (by rw [h0, Polynomial.map_zero])
  obtain ⟨e₀, e₁, he₀, he₁⟩ :=
    exists_twfSq_pair_twfZeroEven (twfNegM_proportional_twfZeroEven hβ'0 h' hR')
  have hric := oreRiccati_twZeroExplicitOp_eq_zero_twfZeroEven hβ'0 h' hR'
    (twfNegM (R'.coeff 1))
  have hjet := jet_identity_twfZeroEven hβ' h' hR'
  have hγ : (twfNegM (R'.coeff 1)).map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    rw [map_evalRingHom_twfNegM_twfZeroEven]
    exact comp_neg_X_eq_zero_iff.not.mpr hr₁
  have hs₀ := map_evalRingHom_twfSq_twfZeroEven e₀
  have hs₁ := map_evalRingHom_twfSq_twfZeroEven e₁
  rw [he₀, Polynomial.map_mul] at hs₀
  rw [he₁, Polynomial.map_mul] at hs₁
  have hj₀ := coeffJet_twfSq_twfZeroEven e₀
  have hj₁ := coeffJet_twfSq_twfZeroEven e₁
  rw [he₀, coeffJet_mul_twfZeroEven] at hj₀
  rw [he₁, coeffJet_mul_twfZeroEven] at hj₁
  have hinj : Function.Injective (expand ℤ 2) := expand_injective two_pos
  refine ⟨e₀, e₁, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, zero_comp] at hs₁
    exact mul_ne_zero hγ hr₁ hs₁
  · apply hinj
    rw [expand_eq_comp_X_pow, expand_eq_comp_X_pow, neg_comp, ← hs₀, ← hs₁, h01]
    ring
  · apply twfSq_injective
    rw [map_zero, oreRiccati_map twfSq twfShiftX coeffShift twfSq_twfShiftX,
      map_twfSq_twfZeroOpX, he₀, he₁]
    exact hric
  · apply hinj
    rw [expand_eq_comp_X_pow, expand_eq_comp_X_pow]
    simp only [mul_comp, sub_comp, add_comp, X_comp, one_comp, ofNat_comp, Nat.cast_ofNat]
    rw [← hs₀, ← hs₁, ← hj₀, ← hj₁, h01] at *
    linear_combination ((twfNegM (R'.coeff 1)).map (Polynomial.evalRingHom (-1 : ℤ))) ^ 2 * hjet

end AJConjecture
