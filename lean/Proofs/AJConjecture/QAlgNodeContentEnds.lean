import Mathlib
import AJConjecture.QAlgCoeffShiftBasic
import AJConjecture.QAlgNodeJet
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgOreMulZero

/-!
# The end coefficients of the primitive symbols of a pseudo-factorisation (fibre fact 1)

Let `β P = S ⋆ R`, `β₀ ≠ 0`, `deg P₀ = deg P`, the leading and constant coefficients of `P₀`
not vanishing at `m₀`, and `R₀ = μ^a R*`, `S₀ = μ^b S*`, `β* P₀ = S* R*`, `β*(m₀) ≠ 0` over
`ℂ[M][L]` (`μ = M - m₀`). Write `e = deg S`, `d = deg R`. Then `deg P = e + d`;
`β* p = s* r*` for the coefficients `p, s*, r*` of `P₀, S*, R*` in degrees `e + d, e, d`;
`s*(m₀) ≠ 0`, `r*(m₀) ≠ 0`, `R*(0)(m₀) ≠ 0`; the fibre of `R*` has degree `d`; `d > 0` if the
fibre of `R*` has a root; and `nodeDenom R = μ^(2a) R*(0) r*`.

Proof. `β, P ≠ 0`, so `S, R ≠ 0` and `deg P = e + d` (`natDegree_oreMul`, injectivity of
`coeffShift`, `Polynomial.natDegree_C_mul`). `deg R* ≤ d` and `deg S* ≤ e`
(`Polynomial.natDegree_map_le`; multiplying by `C (μ^a) ≠ 0` does not change the degree).
Compare the coefficients of degree `e + d` (`Polynomial.coeff_mul_add_eq_of_natDegree_le`) and
`0` (`Polynomial.mul_coeff_zero`) of `β* P₀ = S* R*` and evaluate at `m₀`. The coefficients of
`R₀ = μ^a R*` in degrees `0` and `d` give the last claim.
-/

open Polynomial

namespace AJConjecture

/-- The degree of the product in a pseudo-factorisation `β P = S ⋆ R`. -/
private theorem natDegree_eq_add_contentEnds {P S R : RecOp} {β : Coeff} (hβ : β ≠ 0)
    (hP : P ≠ 0) (h : C β * P = oreMul coeffShift S R) :
    P.natDegree = S.natDegree + R.natDegree := by
  have hne : oreMul coeffShift S R ≠ 0 := h ▸ mul_ne_zero (C_ne_zero.mpr hβ) hP
  have hS : S ≠ 0 := fun h0 ↦ hne (by rw [h0, oreMul_zero_left])
  have hR : R ≠ 0 := fun h0 ↦ hne (by rw [h0, oreMul_zero_right])
  rw [← natDegree_oreMul coeffShift_injective hS hR, ← h, natDegree_C_mul hβ]

/-- The primitive part of the symbol of `Q` has degree at most `deg Q`. -/
private theorem natDegree_le_of_map_specialize_eq_contentEnds {Q : RecOp} {m₀ : ℂ} {a : ℕ}
    {Qs : ℂ[X][X]}
    (hQ : (specialize Q).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      C ((X - C m₀) ^ a) * Qs) :
    Qs.natDegree ≤ Q.natDegree := by
  have h1 : (C ((X - C m₀) ^ a) * Qs).natDegree = Qs.natDegree :=
    natDegree_C_mul (pow_ne_zero a (X_sub_C_ne_zero m₀))
  rw [← h1, ← hQ]
  refine natDegree_map_le.trans ?_
  rw [specialize, coe_mapRingHom]
  exact natDegree_map_le

/-- The coefficients of the symbol of `Q` in terms of its primitive part. -/
theorem coeff_map_specialize_eq {Q : RecOp} {m₀ : ℂ} {a : ℕ}
    {Qs : ℂ[X][X]}
    (hQ : (specialize Q).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      C ((X - C m₀) ^ a) * Qs) (k : ℕ) :
    ((specialize Q).coeff k).map (Int.castRingHom ℂ) = (X - C m₀) ^ a * Qs.coeff k := by
  rw [← coeff_C_mul, ← hQ, coeff_map, coe_mapRingHom]

/-- The end coefficients of the primitive symbols `S*`, `R*` of a pseudo-factorisation do not
vanish at `m₀`, and `nodeDenom R = μ^(2a) R*(0) r*`. -/
theorem nodeContent_ends {P S R : RecOp} {β : Coeff} {m₀ l₀ : ℂ}
    (hβ : β.map (Polynomial.evalRingHom (-1)) ≠ 0) (h : C β * P = oreMul coeffShift S R)
    (hdeg : (specialize P).natDegree = P.natDegree)
    (hlead : ((specialize P).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hconst : (((specialize P).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    {a b : ℕ} {βs : ℂ[X]} {Ss Rs : ℂ[X][X]}
    (hR : (specialize R).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      C ((X - C m₀) ^ a) * Rs)
    (hS : (specialize S).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      C ((X - C m₀) ^ b) * Ss)
    (hβs : βs.eval m₀ ≠ 0)
    (hfac : C βs * (specialize P).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = Ss * Rs)
    (hroot : (Rs.map (Polynomial.evalRingHom m₀)).eval l₀ = 0) :
    P.natDegree = S.natDegree + R.natDegree ∧ 0 < R.natDegree ∧
      (Rs.map (Polynomial.evalRingHom m₀)).natDegree = R.natDegree ∧
      βs * ((specialize P).coeff P.natDegree).map (Int.castRingHom ℂ) =
        Ss.coeff S.natDegree * Rs.coeff R.natDegree ∧
      (Ss.coeff S.natDegree).eval m₀ ≠ 0 ∧ (Rs.coeff R.natDegree).eval m₀ ≠ 0 ∧
      (Rs.coeff 0).eval m₀ ≠ 0 ∧
      (nodeDenom R).map (Int.castRingHom ℂ) =
        (X - C m₀) ^ (2 * a) * (Rs.coeff 0 * Rs.coeff R.natDegree) := by
  have hP0 : specialize P ≠ 0 := fun h0 ↦
    hlead (by rw [h0, leadingCoeff_zero, Polynomial.map_zero, eval_zero])
  have hPne : P ≠ 0 := fun h0 ↦ hP0 (by rw [h0, map_zero])
  have hβne : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  have hn := natDegree_eq_add_contentEnds hβne hPne h
  have hRs := natDegree_le_of_map_specialize_eq_contentEnds hR
  have hSs := natDegree_le_of_map_specialize_eq_contentEnds hS
  have hlc : βs * ((specialize P).coeff P.natDegree).map (Int.castRingHom ℂ) =
      Ss.coeff S.natDegree * Rs.coeff R.natDegree := by
    have h2 := congrArg (fun q ↦ q.coeff (S.natDegree + R.natDegree)) hfac
    simp only [coeff_C_mul, coeff_mul_add_eq_of_natDegree_le hSs hRs, coeff_map,
      coe_mapRingHom] at h2
    rw [hn]
    exact h2
  have hc0 : βs * ((specialize P).coeff 0).map (Int.castRingHom ℂ) =
      Ss.coeff 0 * Rs.coeff 0 := by
    have h2 := congrArg (fun q ↦ q.coeff 0) hfac
    simpa only [mul_coeff_zero, coeff_C_zero, coeff_map, coe_mapRingHom] using h2
  have hlcm := congrArg (eval m₀) hlc
  rw [eval_mul, eval_mul, ← hdeg, coeff_natDegree] at hlcm
  have hlcne : eval m₀ (Ss.coeff S.natDegree) * eval m₀ (Rs.coeff R.natDegree) ≠ 0 :=
    hlcm ▸ mul_ne_zero hβs hlead
  have hc0m := congrArg (eval m₀) hc0
  rw [eval_mul, eval_mul] at hc0m
  have hc0ne : eval m₀ (Ss.coeff 0) * eval m₀ (Rs.coeff 0) ≠ 0 :=
    hc0m ▸ mul_ne_zero hβs hconst
  have hrs := right_ne_zero_of_mul hlcne
  have hdegR : (Rs.map (Polynomial.evalRingHom m₀)).natDegree = R.natDegree := by
    refine le_antisymm (natDegree_map_le.trans hRs) (le_natDegree_of_ne_zero ?_)
    rw [coeff_map, coe_evalRingHom]
    exact hrs
  have hpos : 0 < R.natDegree := by
    by_contra h0
    have hd0 : R.natDegree = 0 := by omega
    rw [hd0] at hdegR
    rw [eq_C_of_natDegree_eq_zero hdegR, eval_C, coeff_map, coe_evalRingHom] at hroot
    exact right_ne_zero_of_mul hc0ne hroot
  refine ⟨hn, hpos, hdegR, hlc, left_ne_zero_of_mul hlcne, hrs, right_ne_zero_of_mul hc0ne, ?_⟩
  rw [nodeDenom, Polynomial.map_mul, coeff_map_specialize_eq hR,
    coeff_map_specialize_eq hR]
  ring

end AJConjecture
