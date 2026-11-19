import Mathlib
import AJFamily.Quantum.ChebU
import AJFamily.Quantum.TwistPolyEval
import AJTwist.Quantum.TwQTwistPolyNeg

/-!
# `C_b` in the trace coordinates `(K, J)` (TwF, unit F2)

Source: revision 5, Section 5.1 (`operators.tex`, "Irreducibility of the residual blocks"): "For
`a = -b < 0` take instead `B = 𝒰_(b-1)`, `D = 𝒰_(b-2)`, `A = B - D`. Then `T_(-b) = A - e B`,
including `b = 1`, where `A = B = 1`"; `e = 1 + J - K`, `Z = 1 + K - K J + J²`.

* `twfChebV z n = U_(n-1)(z)` is the Chebyshev sequence with `V_0 = 0`, `V_1 = 1` (the library's
  `chebU` shifted by one, so that `U_(-1) = 0` is available without a case distinction).
* `famTKNeg b K J = (K - J) V_b(Z) - V_(b-1)(Z)` is `T_(-b)(Z, e)` for `b ≥ 1`
  (`T_(-b) = (1 - e) U_(b-1) - U_(b-2)`, `1 - e = K - J`).
* `evalEval_twistPolyNeg`: over every field, `C_b(M₀, L₀) = (L₀ + x)^(2b-1) x^b T_(-b)(K, J)` with
  `x = M₀²`, `K = x + x⁻¹`, `J = (x L₀ + 1)/(L₀ + x)`.

Route: as `evalEval_twistPoly` (`AJFamily/Quantum/TwistPolyEval.lean`): induction along
`twistPolyNeg_one`, `twistPolyNeg_two`, `twistPolyNeg_add_three`, with the private
`evalEval_zetaMoebiusM_eq` of that file restated. Checked symbolically for `b ≤ 5` (scratch
`check_blocks.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Chebyshev sequence `V_0 = 0`, `V_1 = 1`, `V_(n+2) = z V_(n+1) - V_n`
(`V_n = U_(n-1)`). -/
def twfChebV {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => z * twfChebV z (n + 1) - twfChebV z n

theorem twfChebV_succ {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    twfChebV z (n + 1) = chebU z n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => simp [twfChebV, chebU]
    | k + 2, ih => rw [twfChebV, ih (k + 1) (by omega), ih k (by omega), chebU]

/-- `T_(-b)(Z, e)` as a function of `K` and `J`: `(K - J) U_(b-1)(Z) - U_(b-2)(Z)`,
`Z = 1 + K - K J + J²`. -/
def famTKNeg {F : Type*} [Field F] (b : ℕ) (K J : F) : F :=
  (K - J) * twfChebV (famZK K J) b - twfChebV (famZK K J) (b - 1)

/-- Evaluation of `zetaMoebiusM`: `(L + x)² x Z(K, J)` with `x = M²`. -/
private theorem evalEval_zetaMoebiusM_twfNegEval {F : Type*} [Field F] {M₀ L₀ : F} (hM : M₀ ≠ 0)
    (hL : L₀ + M₀ ^ 2 ≠ 0) :
    (zetaMoebiusM.map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      (L₀ + M₀ ^ 2) ^ 2 * M₀ ^ 2 *
        famZK (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) := by
  simp only [zetaMoebiusM, symbolZetaMoebius, famZK, famKQ]
  simp [evalEval_C]
  field_simp
  ring

/-- The three-step recursion of `famTKNeg`. -/
private theorem famTKNeg_add_three_twfNegEval {F : Type*} [Field F] (K J : F) (k : ℕ) :
    famTKNeg (k + 3) K J = famZK K J * famTKNeg (k + 2) K J - famTKNeg (k + 1) K J := by
  simp only [famTKNeg, show k + 3 - 1 = k + 2 from rfl, show k + 2 - 1 = k + 1 from rfl,
    show k + 1 - 1 = k from rfl, show k + 3 = k + 1 + 2 from rfl, twfChebV]
  ring

/-- The values of `twistPolyNeg` at the first two indices and its recursion, evaluated. -/
private theorem evalEval_twistPolyNeg_rec_twfNegEval {F : Type*} [Field F] {M₀ L₀ : F}
    (hM : M₀ ≠ 0) (hL : L₀ + M₀ ^ 2 ≠ 0) :
    ((twistPolyNeg 1).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
        L₀ + (M₀ ^ 2) ^ 3 ∧
      ((twistPolyNeg 2).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
        (L₀ + M₀ ^ 2) ^ 2 * M₀ ^ 2 *
            famZK (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) * (L₀ + (M₀ ^ 2) ^ 3) -
          (M₀ ^ 2) ^ 2 * (L₀ + M₀ ^ 2) ^ 3 ∧
      ∀ k : ℕ, ((twistPolyNeg (k + 3)).map
          (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
        (L₀ + M₀ ^ 2) ^ 2 * M₀ ^ 2 *
            famZK (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) *
            ((twistPolyNeg (k + 2)).map
              (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ -
          (M₀ ^ 2) ^ 2 * (L₀ + M₀ ^ 2) ^ 4 *
            ((twistPolyNeg (k + 1)).map
              (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ := by
  have hz := evalEval_zetaMoebiusM_twfNegEval hM hL
  have h1 : ((twistPolyNeg 1).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      L₀ + (M₀ ^ 2) ^ 3 := by
    rw [twistPolyNeg_one]
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      coe_mapRingHom, evalEval_add, evalEval_C, evalEval_X, eval_pow, eval_X]
    ring
  refine ⟨h1, ?_, fun k ↦ ?_⟩
  · rw [twistPolyNeg_two]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, evalEval_sub, evalEval_add,
      evalEval_mul, evalEval_pow, evalEval_C, evalEval_X, eval_pow, eval_X, hz, h1]
    ring
  · rw [twistPolyNeg_add_three]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, evalEval_sub, evalEval_add,
      evalEval_mul, evalEval_pow, evalEval_C, evalEval_X, eval_pow, eval_X, hz]
    ring

/-- The value of `twistPolyNeg b` at `(M₀, L₀)` in terms of `famTKNeg`. -/
theorem evalEval_twistPolyNeg {F : Type*} [Field F] {M₀ L₀ : F} (hM : M₀ ≠ 0)
    (hL : L₀ + M₀ ^ 2 ≠ 0) {b : ℕ} (hb : 1 ≤ b) :
    ((twistPolyNeg b).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      (L₀ + M₀ ^ 2) ^ (2 * b - 1) * (M₀ ^ 2) ^ b *
        famTKNeg b (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) := by
  obtain ⟨h1, h2, hrec⟩ := evalEval_twistPolyNeg_rec_twfNegEval hM hL
  have hx : M₀ ^ 2 ≠ 0 := pow_ne_zero 2 hM
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    match b, hb, ih with
    | 1, _, _ =>
      rw [h1]
      simp only [famTKNeg, famKQ, twfChebV, Nat.sub_self]
      field_simp
      ring
    | 2, _, _ =>
      rw [h2]
      simp only [famTKNeg, famKQ, twfChebV, show 2 - 1 = 1 from rfl]
      field_simp
      ring
    | k + 3, _, ih =>
      rw [hrec, ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega),
        famTKNeg_add_three_twfNegEval, show 2 * (k + 3) - 1 = 2 * k + 5 from rfl,
        show 2 * (k + 2) - 1 = 2 * k + 3 from rfl, show 2 * (k + 1) - 1 = 2 * k + 1 from rfl]
      ring

/-- `V_n(2) = n`. -/
private theorem twfChebV_two_twfNegEval {F : Type*} [Field F] (n : ℕ) :
    twfChebV (2 : F) n = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [twfChebV]
  | one => simp [twfChebV]
  | more n ih0 ih1 =>
    rw [twfChebV, ih0, ih1]
    push_cast
    ring

/-- `V_n(-2) = (-1)^(n+1) n`. -/
private theorem twfChebV_neg_two_twfNegEval {F : Type*} [Field F] (n : ℕ) :
    twfChebV (-2 : F) n = (-1) ^ (n + 1) * n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [twfChebV]
  | one => simp [twfChebV]
  | more n ih0 ih1 =>
    rw [twfChebV, ih0, ih1]
    push_cast
    ring

/-- `T_(-b)` on the line `J = 1` (`Z = 2`): `b K - 2b + 1`. -/
theorem famTKNeg_one {F : Type*} [Field F] (b : ℕ) (hb : 1 ≤ b) (K : F) :
    famTKNeg b K 1 = b * K - 2 * b + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  have hZ : famZK K 1 = 2 := by
    rw [famZK]
    ring
  rw [famTKNeg, hZ, twfChebV_two_twfNegEval, twfChebV_two_twfNegEval, Nat.add_sub_cancel]
  push_cast
  ring

/-- `T_(-b)` on the curve `Z = -2`: `(-1)^(b-1) (b (K - J) + b - 1)`. -/
theorem famTKNeg_of_famZK_eq_neg_two {F : Type*} [Field F] (b : ℕ) (hb : 1 ≤ b) {K J : F}
    (hZ : famZK K J = -2) :
    famTKNeg b K J = (-1) ^ (b - 1) * (b * (K - J) + b - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  rw [famTKNeg, hZ, twfChebV_neg_two_twfNegEval, twfChebV_neg_two_twfNegEval,
    Nat.add_sub_cancel]
  push_cast
  ring

end AJConjecture
