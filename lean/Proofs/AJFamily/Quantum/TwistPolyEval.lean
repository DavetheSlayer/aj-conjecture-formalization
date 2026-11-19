import Mathlib
import AJFamily.Quantum.ChebU
import AJFamily.Quantum.TwistPoly

/-!
# Evaluating the twist polynomial

`B_k(M₀, L₀) = (L₀ + x)^(2k) x^k T_k(Z, e)` with `x = M₀²`, `K = x + 1/x` and
`J = (x L₀ + 1)/(L₀ + x)`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `K(x) = x + x⁻¹`. -/
def famKQ {F : Type*} [Field F] (x : F) : F := x + x⁻¹

/-- `Z = 1 + K - K J + J²` as a function of `K` and `J`. -/
def famZK {F : Type*} [Field F] (K J : F) : F := 1 + K - K * J + J ^ 2

/-- `T_k(Z, e)` with `e - 1 = J - K`: `U_k(Z) + (J - K) U_(k-1)(Z)`. -/
def famTK {F : Type*} [Field F] (k : ℕ) (K J : F) : F :=
  chebU (famZK K J) k + (J - K) * chebU (famZK K J) (k - 1)

/-- Evaluation of `zetaMoebiusM`: `(L + x)² x Z(K, J)` with `x = M²`. -/
private theorem evalEval_zetaMoebiusM_eq {F : Type*} [Field F] {M₀ L₀ : F} (hM : M₀ ≠ 0)
    (hL : L₀ + M₀ ^ 2 ≠ 0) :
    (zetaMoebiusM.map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      (L₀ + M₀ ^ 2) ^ 2 * M₀ ^ 2 *
        famZK (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) := by
  simp only [zetaMoebiusM, symbolZetaMoebius, famZK, famKQ]
  simp [evalEval_C]
  field_simp
  ring

/-- Evaluation of `twistPoly 1`: `(L + x)² x (Z + J - K)` with `x = M²`. -/
private theorem evalEval_twistPoly_one_eq {F : Type*} [Field F] {M₀ L₀ : F} (hM : M₀ ≠ 0)
    (hL : L₀ + M₀ ^ 2 ≠ 0) :
    ((twistPoly 1).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      (L₀ + M₀ ^ 2) ^ 2 * M₀ ^ 2 *
        (famZK (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) +
          (M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2) - famKQ (M₀ ^ 2)) := by
  simp only [twistPoly, zetaMoebiusM, symbolZetaMoebius, famZK, famKQ]
  simp [evalEval_C]
  field_simp
  ring

/-- The two-step recursion of `famTK`. -/
private theorem famTK_add_two {F : Type*} [Field F] (K J : F) {k : ℕ} (hk : 1 ≤ k) :
    famTK (k + 2) K J = famZK K J * famTK (k + 1) K J - famTK k K J := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [famTK, show n + 1 + 2 - 1 = n + 2 from rfl, show n + 1 + 1 - 1 = n + 1 from rfl,
    show n + 1 - 1 = n from rfl, show n + 1 + 2 = n + 3 from rfl, chebU]
  ring

/-- The values of `twistPoly (k + 1)` and `twistPoly (k + 2)`. -/
private theorem evalEval_twistPoly_succ_and {F : Type*} [Field F] {M₀ L₀ : F} (hM : M₀ ≠ 0)
    (hL : L₀ + M₀ ^ 2 ≠ 0) (k : ℕ) :
    ((twistPoly (k + 1)).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      (L₀ + M₀ ^ 2) ^ (2 * (k + 1)) * (M₀ ^ 2) ^ (k + 1) *
        famTK (k + 1) (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) ∧
    ((twistPoly (k + 2)).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      (L₀ + M₀ ^ 2) ^ (2 * (k + 2)) * (M₀ ^ 2) ^ (k + 2) *
        famTK (k + 2) (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) := by
  have hz := evalEval_zetaMoebiusM_eq hM hL
  have h1 := evalEval_twistPoly_one_eq hM hL
  set K := famKQ (M₀ ^ 2)
  set J := (M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)
  set s := L₀ + M₀ ^ 2 with hs
  have hf1 : famTK 1 K J = famZK K J + J - K := by
    simp only [famTK, Nat.sub_self, chebU]
    ring
  have hf2 : famTK 2 K J = famZK K J * famTK 1 K J - 1 := by
    rw [hf1]
    simp [famTK, chebU]
    ring
  have hrec : ∀ n : ℕ, ((twistPoly (n + 2)).map
      (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      s ^ 2 * M₀ ^ 2 * famZK K J *
        ((twistPoly (n + 1)).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ -
      s ^ 4 * (M₀ ^ 2) ^ 2 *
        ((twistPoly n).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ := by
    intro n
    rw [twistPoly]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, evalEval_sub, evalEval_add,
      evalEval_mul, evalEval_pow, evalEval_C, evalEval_X, eval_pow, eval_X, hz, hs]
    ring
  induction k with
  | zero =>
    refine ⟨by rw [h1, hf1]; ring, ?_⟩
    rw [hrec, h1, hf2, hf1]
    simp [twistPoly]
    ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [hrec, ih.2, ih.1, famTK_add_two K J (by omega : 1 ≤ n + 1)]
    ring

/-- The value of `twistPoly k` at `(M₀, L₀)` in terms of `famTK`. -/
theorem evalEval_twistPoly {F : Type*} [Field F] {M₀ L₀ : F} (hM : M₀ ≠ 0)
    (hL : L₀ + M₀ ^ 2 ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    ((twistPoly k).map (Polynomial.mapRingHom (Int.castRingHom F))).evalEval M₀ L₀ =
      (L₀ + M₀ ^ 2) ^ (2 * k) * (M₀ ^ 2) ^ k *
        famTK k (famKQ (M₀ ^ 2)) ((M₀ ^ 2 * L₀ + 1) / (L₀ + M₀ ^ 2)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  exact (evalEval_twistPoly_succ_and hM hL n).1

end AJConjecture
