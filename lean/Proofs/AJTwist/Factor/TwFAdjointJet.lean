import Mathlib
import AJConjecture.QAlgTransferJetData
import AJConjecture.QAlgCompScaleNilpotent
import AJConjecture.QAlgTransferAdjointJet
import AJConjecture.QAlgTransferJetMap
import AJTwist.Quantum.TwQWindowPoly

/-!
# The cleared adjoint and its trace polynomials to first order, for every window (TwF, generic)

Source: revision 5, Section 5.2 ("The fixed-`(x, J)` derivative of `Z^*` is `s + ω ∂_J`" and the
power formula `(n Z^(n-1) s + binom(n,2) Z^(n-2) ω Z_J) v + n Z^(n-1) ω v_J`), Section 5.4 (the
derivative `α_d + ω ∂_J` of the cleared map `𝒜_d`).

If `(1 - q)² = 0`, the cleared adjoint `twAdjoint d q` of the window `d ≥ 1` is the first-order
differential operator `ζ̃ + (1 - q) A ∂_J`, with `ζ̃ = twJetZeta d q x J` and
`A = twJetCubic d q x J = (1 - qJ)(x - qJ)(q^(d-1) - xJ)`, and `twCheb d q k` is the first-order
operator `twChebJetValue`, built from the Lucas sequence in `(ζ̃, q^(2d-1) x²)` and its first two
derivatives. For `d = 2m + 3` these are the library's `famJetZeta`, `famJetCubic`,
`famChebJetValue`, `famAdjoint_eq_of_sq_eq_zero`, `famCheb_eq_of_sq_eq_zero`
(`AJFamily/Quantum/FamJetData.lean`, `FamAdjointJet.lean`, `FamChebJet.lean`,
`FamTargetJetValue.lean`); the proofs are the same with `2m + 3 → d`, `2m + 2 → d - 1`,
`4m + 5 → 2d - 1` (the hypothesis `1 ≤ d` is used for `q^(d-1) q = q^d`).
Checked at random points for `d = 1, 2, 3, 4, 6` (scratch `check_generic_parts.py` (C)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `ζ̃(q, x, J)` for the window `d`: the multiplier of `n` in the first-order expansion of
`twAdjoint d q`. -/
def twJetZeta {R : Type*} [CommRing R] (d : ℕ) (q x j : R) : R :=
  x ^ 2 + q ^ d * (1 + x) + (q ^ d * x - q ^ (d + 1) - q * x * (1 + x)) * j + q ^ 2 * x * j ^ 2

/-- The `J`-derivative of `twJetZeta`. -/
def twJetZetaDeriv {R : Type*} [CommRing R] (d : ℕ) (q x j : R) : R :=
  q ^ d * x - q ^ (d + 1) - q * x * (1 + x) + 2 * (q ^ 2 * x * j)

/-- The cubic `A = (1 - qJ)(x - qJ)(q^(d-1) - xJ)` of the window `d`. -/
def twJetCubic {R : Type*} [CommRing R] (d : ℕ) (q x j : R) : R :=
  (1 - q * j) * (x - q * j) * (q ^ (d - 1) - x * j)

/-- The first-order value of `twCheb d q k` at `(x, j)` on a numerator with value `v` and
`J`-derivative `v'`. -/
def twChebJetValue {R : Type*} [CommRing R] (d : ℕ) (q x j : R) (k : ℕ) (v v' : R) : R :=
  transferLucas (twJetZeta d q x j) (q ^ (2 * d - 1) * x ^ 2) k * v +
    (1 - q) * twJetCubic d q x j *
      (transferLucasDeriv (twJetZeta d q x j) (q ^ (2 * d - 1) * x ^ 2) k * v' +
        transferLucasHasse (twJetZeta d q x j) (q ^ (2 * d - 1) * x ^ 2) k *
          twJetZetaDeriv d q x j * v)

/-- If `(1 - q)² = 0`, then `twAdjoint d q n = ζ̃ n + (1 - q) A ∂_J n`. -/
theorem twAdjoint_eq_of_sq_eq_zero {R : Type*} [CommRing R] {q : R} (hq : (1 - q) ^ 2 = 0)
    (d : ℕ) (hd : 1 ≤ d) (n : R[X][X]) :
    twAdjoint d q n = twJetZeta d (C (C q)) (C X) X * n +
      C (C (1 - q)) * twJetCubic d (C (C q)) (C X) X * derivative n := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hq' : ((1 : R[X]) - C q) ^ 2 = 0 := by
    rw [show (1 : R[X]) - C q = C (1 - q) by simp, ← C_pow, hq, C_0]
  have hinner : C (C (q ^ e) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ e)) - C X * X) *
        n.comp (C (C q) * X) =
      X * ((twJetZeta (e + 1) (C (C q)) (C X) X - C (C (q ^ (e + 1)) * X) * X) * n +
        C (C (1 - q)) * twJetCubic (e + 1) (C (C q)) (C X) X * derivative n) := by
    rw [comp_C_mul_X_of_sq_eq_zero hq', twJetZeta, twJetCubic, Nat.add_sub_cancel]
    simp only [C_mul, C_pow, C_sub, C_1]
    ring
  rw [twAdjoint, Nat.add_sub_cancel, hinner, divX_X_mul_jet]
  ring

/-- The derivative in `J` of `twJetZeta`. -/
private theorem derivative_twJetZeta_twfAdjointJet {R : Type*} [CommRing R] (d : ℕ) (q : R) :
    derivative (twJetZeta d (C (C q)) (C X) X : R[X][X]) =
      twJetZetaDeriv d (C (C q)) (C X) X := by
  simp only [twJetZeta, twJetZetaDeriv, sq (X : R[X][X]), ← C_pow, ← C_mul, ← C_add,
    ← C_sub, ← C_1, derivative_add, derivative_mul, derivative_C, derivative_X]
  simp only [C_mul, C_pow, C_add, C_sub, C_1]
  ring

/-- The first-order value of the adjoint trace polynomials commutes with ring homomorphisms. -/
private theorem map_twChebJetValue_twfAdjointJet {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : ℕ) (q x j : R) (k : ℕ) (v v' : R) :
    f (twChebJetValue d q x j k v v') =
      twChebJetValue d (f q) (f x) (f j) k (f v) (f v') := by
  simp only [twChebJetValue, twJetZeta, twJetZetaDeriv, twJetCubic,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_transferLucas,
    map_transferLucasDeriv, map_transferLucasHasse]

/-- If `(1 - q)² = 0`, then `twCheb d q k n` is `twChebJetValue` of `n` and `∂_J n`. -/
theorem twCheb_eq_of_sq_eq_zero {R : Type*} [CommRing R] {q : R} (hq : (1 - q) ^ 2 = 0)
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (n : R[X][X]) :
    twCheb d q k n = twChebJetValue d (C (C q)) (C X) X k n (derivative n) := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero =>
    rw [twCheb, twChebJetValue, transferLucas, transferLucasDeriv, transferLucasHasse]
    ring
  | one =>
    rw [twCheb, twAdjoint_eq_of_sq_eq_zero hq d hd, twChebJetValue, transferLucas,
      transferLucasDeriv, transferLucasHasse]
    simp only [C_sub, C_1]
    ring
  | more k ih0 ih1 =>
    have he : ((1 : R[X][X]) - C (C q)) ^ 2 = 0 := by
      rw [show (1 : R[X][X]) - C (C q) = C (C (1 - q)) by simp, ← C_pow, ← C_pow, hq, C_0, C_0]
    rw [twCheb, ih1, ih0, twAdjoint_eq_of_sq_eq_zero hq d hd]
    simp only [twChebJetValue, transferLucas, transferLucasDeriv, transferLucasHasse,
      derivative_add, derivative_mul, derivative_twJetZeta_twfAdjointJet, derivative_C,
      derivative_sub, derivative_one, sub_self, C_sub, C_1, C_mul, C_pow, zero_mul, zero_add]
    generalize twJetZeta d (C (C q)) (C X) (X : R[X][X]) = Z
    generalize twJetZetaDeriv d (C (C q)) (C X) (X : R[X][X]) = Z'
    generalize twJetCubic d (C (C q)) (C X) (X : R[X][X]) = A
    generalize derivative A = A'
    generalize derivative (derivative n) = n''
    generalize derivative n = n'
    generalize C (C q) ^ (2 * d - 1) * C (X : R[X]) ^ 2 = s
    generalize transferLucas Z s (k + 1) = S1
    generalize transferLucas Z s k = S0
    generalize transferLucasDeriv Z s (k + 1) = D1
    generalize transferLucasDeriv Z s k = D0
    generalize transferLucasHasse Z s (k + 1) = H1
    generalize transferLucasHasse Z s k = H0
    linear_combination (A * (D1 * (A' * n' + A * n'') + H1 * Z' * A * n')) * he

/-- If `(1 - q)² = 0`, the value at `(x, j)` of `twCheb d q k n` is `twChebJetValue` of the
values of `n` and `∂_J n`. -/
theorem evalEval_twCheb_of_sq_eq_zero {R : Type*} [CommRing R] {q : R} (hq : (1 - q) ^ 2 = 0)
    (d : ℕ) (hd : 1 ≤ d) (x j : R) (k : ℕ) (n : R[X][X]) :
    (twCheb d q k n).evalEval x j =
      twChebJetValue d q x j k (n.evalEval x j) ((derivative n).evalEval x j) := by
  rw [twCheb_eq_of_sq_eq_zero hq d hd, ← coe_evalEvalRingHom, map_twChebJetValue_twfAdjointJet]
  simp only [coe_evalEvalRingHom, evalEval_C, evalEval_X, eval_C, eval_X]

end AJConjecture
