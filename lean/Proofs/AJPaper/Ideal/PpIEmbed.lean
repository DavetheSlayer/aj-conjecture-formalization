import Mathlib
import AJFamily.Classical.FamilyPolynomials
import AJPaper.Ideal.PpIMapOp

/-!
# Polynomial operators inside the quantum torus (Unit PpI, node `PpI_Embed`)

The library's operators `RecOp = ℤ[t][M][L]` are the elements of the quantum torus with
polynomial coefficients and non-negative exponents.

* `ppiOfRecOp Q`: the element `∑ c_{i,j}(t) M^j L^i` of the quantum torus over `ℤ[t^{±1}]`
  defined by `Q = ∑_i (∑_j c_{i,j}(t) M^j) L^i`.
* `ppiApply_ppiOfRecOp`: its action is the library's `opApply`
  (`evalAt n D = ∑_j c_j(t) t^{2jn}`).
* `ppiAnnihilates_ppiOfRecOp_iff`: it annihilates the coloured Jones function exactly when `Q`
  does (`ppiJones ℤ K = coloredJones K`).
* `ppiEval_ppiEps_ppiOfRecOp`: its specialization at `t = -1` is the library's `specialize Q`,
  at every point.

Route for all statements: both sides are additive in the operator (`Finsupp.sum_add_index'`,
`Polynomial.sum_def`), so it is enough to compare monomials.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The element of the quantum torus over `ℤ[t, t⁻¹]` given by a polynomial operator
`Q ∈ ℤ[t][M][L]`: the coefficient of `M^j L^i` is the coefficient of `M^j` in the coefficient of
`L^i` of `Q`. -/
def ppiOfRecOp (Q : RecOp) : PpiOp ℤ :=
  Q.sum fun i D ↦ D.sum fun j c ↦ Finsupp.single ((j : ℤ), (i : ℤ)) (Polynomial.toLaurent c)

/-- A sum over the coefficients of `ppiOfRecOp Q` is the double sum over the coefficients
of `Q`. -/
private theorem ppiOfRecOp_sum_Embed {N : Type} [AddCommMonoid N] (Q : RecOp)
    (h : ℤ × ℤ → LaurentPolynomial ℤ → N) (h0 : ∀ kl, h kl 0 = 0)
    (hadd : ∀ kl a b, h kl (a + b) = h kl a + h kl b) :
    (ppiOfRecOp Q).sum h =
      Q.sum fun i D ↦ D.sum fun j c ↦ h ((j : ℤ), (i : ℤ)) (Polynomial.toLaurent c) := by
  simp only [ppiOfRecOp, Polynomial.sum_def]
  rw [← Finsupp.sum_finsetSum_index h0 hadd]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finsupp.sum_finsetSum_index h0 hadd]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finsupp.sum_single_index (h0 _)]

/-- The evaluation of `ℤ[t]` at `t` in the Laurent polynomials is the inclusion. -/
private theorem eval₂RingHom_T_eq_toLaurent_Embed (c : ℤ[X]) :
    Polynomial.eval₂RingHom (Int.castRingHom (LaurentPolynomial ℤ)) (LaurentPolynomial.T 1) c =
      Polynomial.toLaurent c := by
  have h : Polynomial.eval₂RingHom (Int.castRingHom (LaurentPolynomial ℤ))
      (LaurentPolynomial.T 1) = Polynomial.toLaurent := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp
  rw [h]

/-- The value of a coefficient at a colour, as a sum over its monomials. -/
private theorem evalAt_eq_sum_Embed (n : ℤ) (D : Coeff) :
    evalAt n D =
      D.sum fun j c ↦ Polynomial.toLaurent c * LaurentPolynomial.T (2 * (j : ℤ) * n) := by
  unfold evalAt
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [eval₂RingHom_T_eq_toLaurent_Embed, LaurentPolynomial.T_pow]
  congr 2
  ring

/-- The value at a point of the specialization `t = -1`, as a sum over the coefficients. -/
private theorem ppiEval_ppiEps_ppiMapOp_eq_sum_Embed (P : PpiOp ℤ) (p : ℂ × ℂ) :
    ppiEval p (ppiEps (ppiMapOp (Int.castRingHom ℂ) P)) = P.sum fun kl c ↦
      LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (-1 : ℂˣ) c * p.1 ^ kl.1 * p.2 ^ kl.2 := by
  unfold ppiEval ppiEps ppiMapOp
  rw [AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapRange_index (fun kl ↦ by simp),
    Finsupp.sum_mapRange_index (fun kl ↦ by simp)]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  rw [LaurentPolynomial.eval₂_mapRingHom, RingHom.id_comp]

/-- The action of `ppiOfRecOp Q` is the library's action of `Q`. -/
theorem ppiApply_ppiOfRecOp (Q : RecOp) (f : ℤ → LaurentPolynomial ℤ) (n : ℤ) :
    ppiApply (ppiOfRecOp Q) f n = opApply Q f n := by
  unfold ppiApply opApply
  rw [ppiOfRecOp_sum_Embed Q _ (fun kl ↦ by simp) (fun kl a b ↦ by ring)]
  simp only [Polynomial.sum_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [evalAt_eq_sum_Embed, Polynomial.sum_def, Finset.sum_mul]

/-- `ppiOfRecOp Q` annihilates the coloured Jones function exactly when `Q` does. -/
theorem ppiAnnihilates_ppiOfRecOp_iff (Q : RecOp) (K : BraidKnot) :
    PpiAnnihilates (ppiOfRecOp Q) K ↔ Annihilates Q (coloredJones K) := by
  have hJ : ppiJones ℤ K = coloredJones K := by
    funext m
    have hc : Int.castRingHom ℤ = RingHom.id ℤ := RingHom.ext_int _ _
    simp only [ppiJones]
    rw [hc, AddMonoidAlgebra.mapRingHom_id, RingHom.id_apply]
  unfold PpiAnnihilates Annihilates
  refine forall_congr' fun n ↦ ?_
  rw [hJ, ppiApply_ppiOfRecOp]

/-- The specialization at `t = -1` of `ppiOfRecOp Q` is `specialize Q`, at every point. -/
theorem ppiEval_ppiEps_ppiOfRecOp (Q : RecOp) (p : ℂ × ℂ) :
    ppiEval p (ppiEps (ppiMapOp (Int.castRingHom ℂ) (ppiOfRecOp Q))) =
      evalPoint (mapC (specialize Q)) p := by
  rw [ppiEval_ppiEps_ppiMapOp_eq_sum_Embed,
    ppiOfRecOp_sum_Embed Q _ (fun kl ↦ by simp) (fun kl a b ↦ by rw [map_add]; ring)]
  unfold evalPoint mapC specialize
  rw [Polynomial.coe_mapRingHom, Polynomial.eval₂_map, Polynomial.eval₂_map,
    Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom]
  rw [Polynomial.eval_map, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hc : Polynomial.eval₂ (Int.castRingHom ℂ) (-1) ((Q.coeff i).coeff j) =
      ((Polynomial.eval (-1) ((Q.coeff i).coeff j) : ℤ) : ℂ) := by
    simpa using Polynomial.eval₂_at_apply (p := (Q.coeff i).coeff j) (Int.castRingHom ℂ) (-1)
  simp [LaurentPolynomial.eval₂_toLaurent, hc]

end AJConjecture
