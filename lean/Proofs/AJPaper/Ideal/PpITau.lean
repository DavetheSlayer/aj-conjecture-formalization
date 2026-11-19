import Mathlib
import AJTwist.Knot.TwKMirrorGroup
import AJTwist.Classical.TwCReverse
import AJPaper.Ideal.PpIEval

/-!
# Polynomials on the torus and the simultaneous inversion (Unit PpI, node `PpI_Tau`)

Source: Section 8.5 of the paper (`conclusion.tex`): "that closure is invariant" (the closure of
the classical eigenvalue image, under the simultaneous inversion of `M` and `L`).

* `ppiOfPoly`: the inclusion `ℂ[M][L] → 𝔱 = ℂ[M^{±1}, L^{±1}]`, compatible with evaluation
  (`ppiEval_ppiOfPoly`).
* `ppi_exists_tauPoly`: for every `F ∈ ℂ[M][L]` there are a polynomial `F'` and exponents
  `a, b` with `F'(M, L) = M^a L^b F(M⁻¹, L⁻¹)` at all points with `M, L ≠ 0`. Route: induction
  on `F` (`Polynomial.induction_on'` twice); for a monomial `c M^j L^i` take `F' = c`,
  `a = j`, `b = i`; for a sum bring the two pairs of exponents to a common pair.
* `zariskiClosure_eigenvalueSet_symm`: the Zariski closure of the eigenvalue set of a knot is
  invariant under `(M, L) ↦ (M⁻¹, L⁻¹)` at points with `M, L ≠ 0`. Route: if `F` vanishes on
  the eigenvalue set, so does `F'` (`eigenvalueSet_symm`, `fst_ne_zero_of_mem_eigenvalueSet`,
  `snd_ne_zero_of_mem_eigenvalueSet`), hence `F'(p) = 0` and `F(p⁻¹) = 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The inclusion of `ℂ[M][L]` (inner variable `M`, outer variable `L`) into the torus algebra
`𝔱 = ℂ[M^{±1}, L^{±1}]`. -/
def ppiOfPoly (F : ℂ[X][X]) : PpiTorus :=
  F.sum fun i D ↦ D.sum fun j c ↦ AddMonoidAlgebra.single ((j : ℤ), (i : ℤ)) c

/-- The evaluation of the torus algebra at a point commutes with finite sums. -/
private theorem ppiEval_sum_ppiTau {ι : Type} (p : ℂ × ℂ) (s : Finset ι) (f : ι → PpiTorus) :
    ppiEval p (∑ i ∈ s, f i) = ∑ i ∈ s, ppiEval p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ppiEval, AddMonoidAlgebra.coeff_zero,
      Finsupp.sum_zero_index]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ppiEval_add, ih]

/-- The inclusion is compatible with evaluation at every point. -/
theorem ppiEval_ppiOfPoly (F : ℂ[X][X]) (p : ℂ × ℂ) :
    ppiEval p (ppiOfPoly F) = evalPoint F p := by
  rw [ppiOfPoly, evalPoint, eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def,
    ppiEval_sum_ppiTau]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.sum_def, ppiEval_sum_ppiTau, coe_evalRingHom, eval_eq_sum, Polynomial.sum_def,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ppiEval_single, zpow_natCast, zpow_natCast]

/-- The polynomials admitting an inverted companion are closed under addition: the two pairs
of exponents are brought to their sum. -/
private theorem exists_tauPoly_add_ppiTau {F G : ℂ[X][X]}
    (hF : ∃ (F' : ℂ[X][X]) (a b : ℕ), ∀ q : ℂ × ℂ, q.1 ≠ 0 → q.2 ≠ 0 →
      evalPoint F' q = q.1 ^ a * q.2 ^ b * evalPoint F (q.1⁻¹, q.2⁻¹))
    (hG : ∃ (G' : ℂ[X][X]) (a b : ℕ), ∀ q : ℂ × ℂ, q.1 ≠ 0 → q.2 ≠ 0 →
      evalPoint G' q = q.1 ^ a * q.2 ^ b * evalPoint G (q.1⁻¹, q.2⁻¹)) :
    ∃ (H' : ℂ[X][X]) (a b : ℕ), ∀ q : ℂ × ℂ, q.1 ≠ 0 → q.2 ≠ 0 →
      evalPoint H' q = q.1 ^ a * q.2 ^ b * evalPoint (F + G) (q.1⁻¹, q.2⁻¹) := by
  obtain ⟨F', a, b, hF⟩ := hF
  obtain ⟨G', c, d, hG⟩ := hG
  refine ⟨C (X ^ c) * X ^ d * F' + C (X ^ a) * X ^ b * G', a + c, b + d, fun q h1 h2 ↦ ?_⟩
  have e1 := hF q h1 h2
  have e2 := hG q h1 h2
  simp only [evalPoint] at e1 e2 ⊢
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X_pow, coe_evalRingHom, eval_pow, eval_X]
  rw [e1, e2]
  ring

/-- A monomial `c M^j L^i` has the inverted companion `c`, with exponents `j` and `i`. -/
private theorem exists_tauPoly_monomial_ppiTau (i j : ℕ) (c : ℂ) :
    ∃ (F' : ℂ[X][X]) (a b : ℕ), ∀ q : ℂ × ℂ, q.1 ≠ 0 → q.2 ≠ 0 →
      evalPoint F' q =
        q.1 ^ a * q.2 ^ b * evalPoint (monomial i (monomial j c)) (q.1⁻¹, q.2⁻¹) := by
  refine ⟨C (C c), j, i, fun q h1 h2 ↦ ?_⟩
  simp only [evalPoint, eval₂_C, eval₂_monomial, coe_evalRingHom, eval_C, eval_monomial, inv_pow]
  field_simp

/-- For every polynomial `F` there is a polynomial `F'` with
`F'(M, L) = M^a L^b F(M⁻¹, L⁻¹)` on the torus. -/
theorem ppi_exists_tauPoly (F : ℂ[X][X]) :
    ∃ (F' : ℂ[X][X]) (a b : ℕ), ∀ q : ℂ × ℂ, q.1 ≠ 0 → q.2 ≠ 0 →
      evalPoint F' q = q.1 ^ a * q.2 ^ b * evalPoint F (q.1⁻¹, q.2⁻¹) := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq => exact exists_tauPoly_add_ppiTau hp hq
  | monomial i D =>
    induction D using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact exists_tauPoly_add_ppiTau hp hq
    | monomial j c => exact exists_tauPoly_monomial_ppiTau i j c

/-- The Zariski closure of the eigenvalue set of a knot is invariant under the simultaneous
inversion `(M, L) ↦ (M⁻¹, L⁻¹)`, at points with nonzero coordinates. -/
theorem zariskiClosure_eigenvalueSet_symm (K : BraidKnot) {p : ℂ × ℂ} (h1 : p.1 ≠ 0)
    (h2 : p.2 ≠ 0) (hp : p ∈ zariskiClosure (eigenvalueSet K)) :
    (p.1⁻¹, p.2⁻¹) ∈ zariskiClosure (eigenvalueSet K) := by
  intro F hF
  obtain ⟨F', a, b, hF'⟩ := ppi_exists_tauPoly F
  have hvan : ∀ q ∈ eigenvalueSet K, evalPoint F' q = 0 := fun q hq ↦ by
    rw [hF' q (fst_ne_zero_of_mem_eigenvalueSet hq) (snd_ne_zero_of_mem_eigenvalueSet hq),
      hF _ (eigenvalueSet_symm K hq), mul_zero]
  have h0 := hp F' hvan
  rw [hF' p h1 h2] at h0
  exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (pow_ne_zero a h1) (pow_ne_zero b h2))

end AJConjecture
