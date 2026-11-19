import Mathlib
import AJConjecture.QAlgTransferJetMap
import AJFamily.Quantum.FamChebJet

/-!
# The family target polynomial to first order

`evalEval_famTarget_of_sq_eq_zero`: the value of `famTarget m q` when `(1 - q)² = 0`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The first-order value of the family Chebyshev operators commutes with ring
homomorphisms. -/
private theorem map_famChebJetValue {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (m : ℕ) (q x j : R) (k : ℕ) (v v' : R) :
    f (famChebJetValue m q x j k v v') =
      famChebJetValue m (f q) (f x) (f j) k (f v) (f v') := by
  simp only [famChebJetValue, famJetZeta, famJetZetaDeriv, famJetCubic,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_transferLucas,
    map_transferLucasDeriv, map_transferLucasHasse]

/-- If `(1 - q)² = 0`, the value at `(x, j)` of `Š_k n` is `famChebJetValue` of the
values of `n` and `∂_J n`. -/
private theorem evalEval_famCheb_of_sq_eq_zero {R : Type*} [CommRing R] {q : R}
    (hq : (1 - q) ^ 2 = 0) (m : ℕ) (x j : R) (k : ℕ) (n : R[X][X]) :
    (famCheb m q k n).evalEval x j =
      famChebJetValue m q x j k (n.evalEval x j) ((derivative n).evalEval x j) := by
  rw [famCheb_eq_of_sq_eq_zero hq, ← coe_evalEvalRingHom, map_famChebJetValue]
  simp only [coe_evalEvalRingHom, evalEval_C, evalEval_X, eval_C, eval_X]

/-- If `(1 - q)² = 0`, the value of `famTarget m q` at `(x, j)` is `famTargetJetValue m q x j`. -/
theorem evalEval_famTarget_of_sq_eq_zero {R : Type*} [CommRing R] {q : R} (hq : (1 - q) ^ 2 = 0)
    (m : ℕ) (x j : R) : (famTarget m q).evalEval x j = famTargetJetValue m q x j := by
  have h1 : (derivative (1 : R[X][X])) = 0 := derivative_one
  have h2 : derivative (1 - C (C q) * X : R[X][X]) = C (C (-q)) := by
    simp
  have h3 : derivative (C (C q) * X : R[X][X]) = C (C q) := by
    simp
  rw [famTarget, famTargetJetValue, ← coe_evalEvalRingHom, map_sub, map_add, map_mul,
    map_mul]
  simp only [coe_evalEvalRingHom, evalEval_famCheb_of_sq_eq_zero hq, h1, h2, h3]
  simp only [evalEval, eval_mul, eval_pow, eval_C, eval_X, eval_sub, eval_one, eval_zero]

end AJConjecture
