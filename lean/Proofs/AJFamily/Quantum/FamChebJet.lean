import Mathlib
import AJFamily.Quantum.FamAdjointJet

/-!
# The family Chebyshev operators to first order

If `(1 - q)² = 0`, `famCheb m q k` is the first-order operator `famChebJetValue`, built from the
Lucas sequence in `(ζ, q^(4m+5) x²)` and its derivatives.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The derivative in `J` of the family `ζ`. -/
private theorem derivative_famJetZeta {R : Type*} [CommRing R] (m : ℕ) (q : R) :
    derivative (famJetZeta m (C (C q)) (C X) X : R[X][X]) =
      famJetZetaDeriv m (C (C q)) (C X) X := by
  simp only [famJetZeta, famJetZetaDeriv, sq (X : R[X][X]), ← C_pow, ← C_mul, ← C_add,
    ← C_sub, ← C_1, derivative_add, derivative_mul, derivative_C, derivative_X]
  simp only [C_mul, C_pow, C_add, C_sub, C_1]
  ring

/-- If `(1 - q)² = 0`, then `famCheb m q k n` is `famChebJetValue` of `n` and `∂_J n`. -/
theorem famCheb_eq_of_sq_eq_zero {R : Type*} [CommRing R] {q : R} (hq : (1 - q) ^ 2 = 0) (m : ℕ) :
    ∀ (k : ℕ) (n : R[X][X]),
      famCheb m q k n = famChebJetValue m (C (C q)) (C X) X k n (derivative n)
  | 0, n => by
    rw [famCheb, famChebJetValue, transferLucas, transferLucasDeriv, transferLucasHasse]
    ring
  | 1, n => by
    rw [famCheb, famAdjoint_eq_of_sq_eq_zero hq, famChebJetValue, transferLucas,
      transferLucasDeriv, transferLucasHasse]
    simp only [C_sub, C_1]
    ring
  | k + 2, n => by
    have he : ((1 : R[X][X]) - C (C q)) ^ 2 = 0 := by
      rw [show (1 : R[X][X]) - C (C q) = C (C (1 - q)) by simp, ← C_pow, ← C_pow, hq, C_0, C_0]
    rw [famCheb, famCheb_eq_of_sq_eq_zero hq m (k + 1),
      famCheb_eq_of_sq_eq_zero hq m k, famAdjoint_eq_of_sq_eq_zero hq]
    simp only [famChebJetValue, transferLucas, transferLucasDeriv, transferLucasHasse,
      derivative_add, derivative_mul, derivative_famJetZeta, derivative_C, derivative_sub,
      derivative_one, sub_self, C_sub, C_1, C_mul, C_pow, zero_mul, zero_add]
    generalize famJetZeta m (C (C q)) (C X) (X : R[X][X]) = Z
    generalize famJetZetaDeriv m (C (C q)) (C X) (X : R[X][X]) = Z'
    generalize famJetCubic m (C (C q)) (C X) (X : R[X][X]) = A
    generalize derivative A = A'
    generalize derivative (derivative n) = n''
    generalize derivative n = n'
    generalize C (C q) ^ (4 * m + 5) * C (X : R[X]) ^ 2 = s
    generalize transferLucas Z s (k + 1) = S1
    generalize transferLucas Z s k = S0
    generalize transferLucasDeriv Z s (k + 1) = D1
    generalize transferLucasDeriv Z s k = D0
    generalize transferLucasHasse Z s (k + 1) = H1
    generalize transferLucasHasse Z s k = H0
    linear_combination (A * (D1 * (A' * n' + A * n'') + H1 * Z' * A * n')) * he

end AJConjecture
