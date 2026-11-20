import Mathlib
import AJPaper.Ideal.PpICoord
import AJPaper.Ideal.PpIRational

/-!
# Complex raw annihilators vanish on `G = 0` (Unit PpI, node `PpI_Complex`)

Source: Section 8.5 of the paper (`conclusion.tex`): "Multiplying the content back and summing
shows that every raw specialized annihilator vanishes at generic points of `G = 0`."

* `ppi_eval_eps_eq_zero_of_coord`: with a basis `b` of `ℂ` over `ℚ`
  (`Basis.ofVectorSpace ℚ ℂ`), `P = ∑_i b_i · (ppiCoord (b.coord i) P)` over the finitely many
  basis vectors occurring in the scalar coefficients of `P` (`Basis.sum_repr`), and
  `P ↦ ppiEval p (ppiEps P)` is `ℂ`-linear; so if the specializations of all rational
  coordinates vanish at `p`, so does that of `P`.
* `ppi_eval_eps_eq_zero`: **every raw annihilator with complex coefficients** has specialization
  vanishing at every point `(M, L)`, `M, L ≠ 0`, of `G = 0` (`ppiAnnihilates_ppiCoord`,
  `ppi_eval_eps_eq_zero_rat`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value at a point of the specialization `t = -1`, as a sum over the coefficients. -/
private theorem ppiEval_ppiEps_eq_sum_Complex (P : PpiOp ℂ) (p : ℂ × ℂ) :
    ppiEval p (ppiEps P) = P.sum fun kl c ↦
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (-1 : ℂˣ) c * p.1 ^ kl.1 * p.2 ^ kl.2 := by
  unfold ppiEval ppiEps
  rw [AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapRange_index (fun kl ↦ by simp)]

/-- The value at a point of the specialization `t = -1` of a rational coordinate, as a sum over
the coefficients. -/
private theorem ppiEval_ppiEps_ppiCoord_eq_sum_Complex (φ : ℂ →ₗ[ℚ] ℚ) (P : PpiOp ℂ)
    (p : ℂ × ℂ) :
    ppiEval p (ppiEps (ppiMapOp (algebraMap ℚ ℂ) (ppiCoord φ P))) = P.sum fun kl c ↦
      LaurentPolynomial.eval₂ (algebraMap ℚ ℂ) (-1 : ℂˣ)
        (AddMonoidAlgebra.ofCoeff (c.coeff.mapRange φ (map_zero φ))) *
          p.1 ^ kl.1 * p.2 ^ kl.2 := by
  unfold ppiEval ppiEps ppiMapOp ppiCoord
  rw [AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapRange_index (fun kl ↦ by simp),
    Finsupp.sum_mapRange_index (fun kl ↦ by simp),
    Finsupp.sum_mapRange_index (fun kl ↦ by simp)]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  rw [LaurentPolynomial.eval₂_mapRingHom, RingHom.id_comp]

/-- A complex Laurent polynomial at `t = -1` is the combination of its rational coordinates
in a `ℚ`-basis of `ℂ`, over every large enough finite set of basis vectors. -/
private theorem laurent_eval_eq_sum_coord_Complex {ι : Type} (b : Module.Basis ι ℚ ℂ)
    (c : LaurentPolynomial ℂ) :
    ∃ I₀ : Finset ι, ∀ I : Finset ι, I₀ ⊆ I →
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (-1 : ℂˣ) c = ∑ i ∈ I, b i *
        LaurentPolynomial.eval₂ (algebraMap ℚ ℂ) (-1 : ℂˣ)
          (AddMonoidAlgebra.ofCoeff (c.coeff.mapRange (b.coord i) (map_zero (b.coord i)))) := by
  classical
  induction c using LaurentPolynomial.induction_on' with
  | add x y hx hy =>
    obtain ⟨I₁, h₁⟩ := hx
    obtain ⟨I₂, h₂⟩ := hy
    refine ⟨I₁ ∪ I₂, fun I hI ↦ ?_⟩
    rw [map_add, h₁ I (Finset.union_subset_left hI), h₂ I (Finset.union_subset_right hI),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [AddMonoidAlgebra.coeff_add, Finsupp.mapRange_add (map_add (b.coord i)),
      AddMonoidAlgebra.ofCoeff_add, map_add, mul_add]
  | C_mul_T m r =>
    refine ⟨(b.repr r).support, fun I hI ↦ ?_⟩
    have hr : r = ∑ i ∈ I, b i * ((b.coord i r : ℚ) : ℂ) := by
      conv_lhs => rw [← b.linearCombination_repr r, Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ hI _ (fun i _ ↦ zero_smul ℚ (b i))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Rat.smul_def, mul_comm, b.coord_apply]
    rw [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply]
    conv_lhs => rw [hr, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.mapRange_single, AddMonoidAlgebra.ofCoeff_single,
      LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T, mul_assoc]
    rfl

/-- An element of the quantum torus over `ℂ[t, t⁻¹]` is a complex combination of its rational
coordinates: if the specializations of all coordinates vanish at `p`, so does that of `P`. -/
theorem ppi_eval_eps_eq_zero_of_coord {P : PpiOp ℂ} {p : ℂ × ℂ}
    (h : ∀ φ : ℂ →ₗ[ℚ] ℚ,
      ppiEval p (ppiEps (ppiMapOp (algebraMap ℚ ℂ) (ppiCoord φ P))) = 0) :
    ppiEval p (ppiEps P) = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ ℂ
  choose I₀ hI₀ using fun kl : ℤ × ℤ ↦ laurent_eval_eq_sum_coord_Complex b (P kl)
  have hsum : ppiEval p (ppiEps P) = ∑ i ∈ P.support.biUnion I₀, b i *
      ppiEval p (ppiEps (ppiMapOp (algebraMap ℚ ℂ) (ppiCoord (b.coord i) P))) := by
    rw [ppiEval_ppiEps_eq_sum_Complex]
    simp only [ppiEval_ppiEps_ppiCoord_eq_sum_Complex, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [hI₀ kl _ (Finset.subset_biUnion_of_mem I₀ hkl), Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [h, mul_zero]

/-- **Complex raw annihilators** (Section 8.5): if `G` divides the specialization of every
integral polynomial annihilator of the coloured Jones function of `K`, then for every element
`P` of the recurrence ideal of the quantum torus over `ℂ[t, t⁻¹]`, the specialization `ε(P)`
vanishes at every point `(M, L)` with `M, L ≠ 0` of the curve `G = 0`. -/
theorem ppi_eval_eps_eq_zero {K : BraidKnot} {G : ℤ[X][X]}
    (hG : ∀ Q : RecOp, Annihilates Q (coloredJones K) → G ∣ specialize Q) {P : PpiOp ℂ}
    (hP : PpiAnnihilates P K) {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hp : evalPoint (mapC G) p = 0) : ppiEval p (ppiEps P) = 0 :=
  ppi_eval_eps_eq_zero_of_coord fun φ ↦
    ppi_eval_eps_eq_zero_rat hG (ppiAnnihilates_ppiCoord φ hP) h1 h2 hp

end AJConjecture
