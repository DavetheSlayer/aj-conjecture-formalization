import Mathlib
import AJFamily.Classical.FamilyEval
import AJTwist.Classical.TwCPolys
import AJTwist.Quantum.TwQTwistPolyNegFacts

/-!
# `C_b` through the homogenised Chebyshev sequence

The classical computation of the filling of negative index `-b` (relation `c^b a₁ = a c^b`,
`AJTwist.Classical.TwCTwistNFNeg`) produces the Riley equation `S_(b-1) = α' S_b` with
`α' = tr c - α`, that is, after homogenising with `k = x (L + x)²`, the polynomial
`(τ - A) Ŝ_b - k² Ŝ_(b-1)` in the notation of `AJFamily.Classical.FamilyPolynomials`
(`τ = famTau`, `A = famA`, `Ŝ = homCheb τ k`). It is `(L + x) C_b`:

* `twistPolyNeg_mul_famQ`: `C_b (L + x) = (τ - A) Ŝ_b - k² Ŝ_(b-1)`. Route: both sides satisfy
  `u_(b+2) = Z_num u_(b+1) - x² (L + x)⁴ u_b` (`twistPolyNeg_add_three`, `twistPolyNeg_two`,
  `homCheb`), with `famTau = zetaMoebiusM` and `famK ^ 2 = C (X ^ 4) * (C (X ^ 2) + X) ^ 4`
  (the private `famTau_eq`, `famK_sq_eq` of `AJHandoff.TorusKnot.PairKBmIdentity`, to be
  re-proved here), and `τ - A = (L + x)(L + x³)` at `b = 1`;
* `evalPoint_twistPolyNeg_mul`: the same identity at a point `(M, L) ∈ ℂ²`;
* `evalPoint_twistPolyNeg_neg_sq`: `C_b(x, -x) = x^b (x² - 1)^(2b-1)` at a complex point, from
  `eval_neg_twistPolyNeg` (it covers the points `L + x = 0`, where the first identity does not
  determine `C_b`).

Checked symbolically for `b ≤ 5` (`SCR/C/py/v1_polys.py`, `v1_negnf.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The classical `τ` is the quantum `Ẑ`. -/
private theorem famTau_eq_twCPolysCheb : famTau = zetaMoebiusM := by
  rw [zetaMoebiusM_eq_explicit]
  simp only [famTau, famX, famP, famQ, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  ring

/-- `k² = x² (L + x)⁴`. -/
private theorem famK_sq_eq_twCPolysCheb : famK ^ 2 = C (X ^ 4) * (C (X ^ 2) + X) ^ 4 := by
  simp only [famK, famX, famQ, map_pow]
  ring

/-- Evaluation at `(M, L)` of an integer bivariate polynomial, as a ring homomorphism. -/
private def evalHom_twCPolysCheb (M L : ℂ) : ℤ[X][X] →+* ℂ :=
  (eval₂RingHom (evalRingHom M) L).comp (mapRingHom (mapRingHom (Int.castRingHom ℂ)))

/-- `evalPoint ∘ mapC` is the ring homomorphism `evalHom_twCPolysCheb`. -/
private theorem evalPoint_mapC_eq_evalHom_twCPolysCheb (P : ℤ[X][X]) (M L : ℂ) :
    evalPoint (mapC P) (M, L) = evalHom_twCPolysCheb M L P := rfl

/-- `Q` evaluates to `M² + L`. -/
private theorem evalHom_famQ_twCPolysCheb (M L : ℂ) :
    evalHom_twCPolysCheb M L famQ = M ^ 2 + L := by
  simp [evalHom_twCPolysCheb, famQ, famX, eval₂_pow, eval₂_C]

/-- Evaluating at `(M, L)` is evaluating the inner polynomial `P(L := r)` at `M` when `r`
evaluates to `L`. -/
private theorem evalHom_eq_eval_eval_twCPolysCheb (P : ℤ[X][X]) (r : ℤ[X]) (M : ℂ) :
    evalHom_twCPolysCheb M ((r.map (Int.castRingHom ℂ)).eval M) P =
      ((P.eval r).map (Int.castRingHom ℂ)).eval M := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, eval_add, Polynomial.map_add, eval_add]
  | monomial n a =>
    simp [evalHom_twCPolysCheb, ← C_mul_X_pow_eq_monomial, eval₂_mul, eval₂_pow]

/-- `C_b (L + x) = (τ - A) Ŝ_b - k² Ŝ_(b-1)`. -/
theorem twistPolyNeg_mul_famQ (b : ℕ) (hb : 1 ≤ b) :
    twistPolyNeg b * famQ =
      (famTau - famA) * homCheb famTau famK b - famK ^ 2 * homCheb famTau famK (b - 1) := by
  have h1 : twistPolyNeg 1 * famQ = famTau - famA := by
    rw [twistPolyNeg_one, famTau_eq_twCPolysCheb, zetaMoebiusM_eq_explicit]
    simp only [famA, famX, famP, famQ, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    ring
  have h2 : twistPolyNeg 2 * famQ = (famTau - famA) * famTau - famK ^ 2 := by
    rw [twistPolyNeg_two, ← famTau_eq_twCPolysCheb, sub_mul, mul_assoc, h1,
      famK_sq_eq_twCPolysCheb, famQ, famX]
    ring
  have key : ∀ n, twistPolyNeg (n + 1) * famQ =
        (famTau - famA) * homCheb famTau famK (n + 1) - famK ^ 2 * homCheb famTau famK n ∧
      twistPolyNeg (n + 2) * famQ =
        (famTau - famA) * homCheb famTau famK (n + 2) - famK ^ 2 * homCheb famTau famK (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [h1]
        simp only [homCheb, mul_one, mul_zero, sub_zero]
      · rw [h2]
        simp only [homCheb, mul_one, mul_zero, sub_zero]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e : twistPolyNeg (n + 3) * famQ = famTau * (twistPolyNeg (n + 2) * famQ) -
          famK ^ 2 * (twistPolyNeg (n + 1) * famQ) := by
        rw [twistPolyNeg_add_three, ← famTau_eq_twCPolysCheb, ← famK_sq_eq_twCPolysCheb]
        ring
      rw [show n + 1 + 2 = n + 3 from rfl, e, ih.1, ih.2,
        show homCheb famTau famK (n + 3) =
          famTau * homCheb famTau famK (n + 2) - famK ^ 2 * homCheb famTau famK (n + 1) from rfl,
        show homCheb famTau famK (n + 1 + 1) =
          famTau * homCheb famTau famK (n + 1) - famK ^ 2 * homCheb famTau famK n from rfl]
      ring
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  exact (key n).1

/-- The value of `C_b (L + x)` at a complex point through the homogenised Chebyshev sequence. -/
theorem evalPoint_twistPolyNeg_mul (b : ℕ) (hb : 1 ≤ b) (M L : ℂ) :
    evalPoint (mapC (twistPolyNeg b)) (M, L) * (M ^ 2 + L) =
      (evalPoint (mapC famTau) (M, L) - evalPoint (mapC famA) (M, L)) *
          homCheb (evalPoint (mapC famTau) (M, L)) (evalPoint (mapC famK) (M, L)) b -
        evalPoint (mapC famK) (M, L) ^ 2 *
          homCheb (evalPoint (mapC famTau) (M, L)) (evalPoint (mapC famK) (M, L)) (b - 1) := by
  have h := congrArg (evalHom_twCPolysCheb M L) (twistPolyNeg_mul_famQ b hb)
  simp only [map_sub, map_mul, map_pow, map_homCheb, evalHom_famQ_twCPolysCheb] at h
  simpa only [evalPoint_mapC_eq_evalHom_twCPolysCheb] using h

/-- `C_b(x, -x) = x^b (x² - 1)^(2b-1)` at `x = M²`. -/
theorem evalPoint_twistPolyNeg_neg_sq (b : ℕ) (hb : 1 ≤ b) (M : ℂ) :
    evalPoint (mapC (twistPolyNeg b)) (M, -M ^ 2) = M ^ (2 * b) * (M ^ 4 - 1) ^ (2 * b - 1) := by
  have h := evalHom_eq_eval_eval_twCPolysCheb (twistPolyNeg b) (-(X ^ 2)) M
  rw [eval_neg_twistPolyNeg b hb] at h
  simpa [evalPoint_mapC_eq_evalHom_twCPolysCheb] using h

end AJConjecture
