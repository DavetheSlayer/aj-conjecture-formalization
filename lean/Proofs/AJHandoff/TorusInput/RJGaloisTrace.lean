import Mathlib
import AJHandoff.TorusInput.RJEmbed
import AJHandoff.TorusQuantum.PairQCruxGalois

/-!
# The Galois step (node RA4.1)

Let `C`, `P` be matrices over `ℚ(t)` with `P² = P`, `C P = P C`, `C^r P = μ P`, both commuting
with a diagonal weight `W`, and let `ν` be an `r`-th root of `μ` after the embedding `t ↦ t^r`.
Then for `s ≥ 1` prime to `r`: `tr(W C^s P) = ν^(s-1) tr(W C P)` (after the embedding).
This replaces the `q → 1` continuity argument of Rosso–Jones.

Route. Map everything by `rjEmbed r` (`RingHom.map_matrix_mul`, `Matrix.trace_map`-type lemmas,
`Matrix.diagonal_map`). Put `A = ν⁻¹ C' P' + (1 - P')`. Then `A^r = 1` (`C'` and `P'` commute,
`P'` idempotent, `C'^r P' = ν^r P'`), `A` commutes with `W'`, and
`pairQ_trace_diagonal_mul_pow_eq` (with `pairQ_irreducible_cyclotomic_ratFunc` for all `d ∣ r`)
gives `tr(W' A^s) = tr(W' A)`. Since `A^s P' = ν^(-s) C'^s P'` and `A^s (1 - P') = 1 - P'`,
`tr(W' A^s) = ν^(-s) tr(W' C'^s P') + tr(W' (1 - P'))`; compare with `s = 1`. Estimate 100–150
lines.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The powers of `A = ν⁻¹ C P + (1 - P)` when `P` is idempotent and commutes with `C`. -/
private theorem rj_galois_pow_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C P : Matrix ι ι (RatFunc ℚ)) (ν : RatFunc ℚ) (hP : P * P = P) (hCP : C * P = P * C)
    (k : ℕ) : (ν⁻¹ • (C * P) + (1 - P)) ^ k = ν⁻¹ ^ k • (C ^ k * P) + (1 - P) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, one_mul, one_smul, add_sub_cancel]
  | succ k ih =>
    have h1 : C ^ k * P * (C * P) = C ^ (k + 1) * P := by
      rw [mul_assoc, ← mul_assoc P C P, ← hCP, mul_assoc, hP, ← mul_assoc, ← pow_succ]
    have h2 : C ^ k * P * (1 - P) = 0 := by rw [mul_sub, mul_one, mul_assoc, hP, sub_self]
    have h3 : (1 - P) * (C * P) = 0 := by
      rw [sub_mul, one_mul, ← mul_assoc, ← hCP, mul_assoc, hP, sub_self]
    have h4 : (1 - P) * (1 - P) = 1 - P := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h1, h2, h3, h4,
      smul_zero, add_zero, zero_add, pow_succ]
    rw [mul_comm ν⁻¹ (ν⁻¹ ^ k)]

/-- The Galois step over `ℚ(t)` itself, with `C^r P = ν^r P`. -/
private theorem rj_galois_trace_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → RatFunc ℚ) (C P : Matrix ι ι (RatFunc ℚ)) {r s : ℕ} (hr : 1 ≤ r) (hs1 : 1 ≤ s)
    (hs : Nat.Coprime s r) (ν : RatFunc ℚ) (hν0 : ν ≠ 0) (hP : P * P = P)
    (hCP : C * P = P * C) (hCr : C ^ r * P = ν ^ r • P)
    (hwC : Matrix.diagonal w * C = C * Matrix.diagonal w)
    (hwP : Matrix.diagonal w * P = P * Matrix.diagonal w) :
    Matrix.trace (Matrix.diagonal w * C ^ s * P) =
      ν ^ (s - 1) * Matrix.trace (Matrix.diagonal w * C * P) := by
  set A := ν⁻¹ • (C * P) + (1 - P) with hA
  have hAr : A ^ r = 1 := by
    rw [rj_galois_pow_eq C P ν hP hCP r, hCr, smul_smul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hν0), one_smul, add_sub_cancel]
  have hwA : Matrix.diagonal w * A = A * Matrix.diagonal w := by
    rw [hA, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hwC, mul_assoc, hwP,
      ← mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hwP]
  have key := pairQ_trace_diagonal_mul_pow_eq w A hwA hr hAr hs
    fun d hd ↦ pairQ_irreducible_cyclotomic_ratFunc (Nat.pos_of_dvd_of_pos hd hr)
  rw [rj_galois_pow_eq C P ν hP hCP s, hA] at key
  simp only [mul_add, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] at key
  have key' := add_right_cancel key
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel, mul_assoc, mul_assoc]
  have h : Matrix.trace (Matrix.diagonal w * (C ^ (t + 1) * P)) =
      ν ^ (t + 1) * (ν⁻¹ ^ (t + 1) * Matrix.trace (Matrix.diagonal w * (C ^ (t + 1) * P))) := by
    rw [inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hν0)]
  rw [h, key', pow_succ]
  field_simp

/-- The Galois step: traces of coprime powers on a part where `C^r` is scalar. -/
theorem rj_galois_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → RatFunc ℚ)
    (C P : Matrix ι ι (RatFunc ℚ)) {r s : ℕ} (hr : 1 ≤ r) (hs1 : 1 ≤ s) (hs : Nat.Coprime s r)
    (μ ν : RatFunc ℚ) (hν : ν ^ r = rjEmbed r μ) (hν0 : ν ≠ 0) (hP : P * P = P)
    (hCP : C * P = P * C) (hCr : C ^ r * P = μ • P)
    (hwC : Matrix.diagonal w * C = C * Matrix.diagonal w)
    (hwP : Matrix.diagonal w * P = P * Matrix.diagonal w) :
    rjEmbed r (Matrix.trace (Matrix.diagonal w * C ^ s * P)) =
      ν ^ (s - 1) * rjEmbed r (Matrix.trace (Matrix.diagonal w * C * P)) := by
  set φ := rjEmbed r
  have hmap : ∀ M : Matrix ι ι (RatFunc ℚ), φ (Matrix.trace M) = Matrix.trace (φ.mapMatrix M) :=
    fun M ↦ AddMonoidHom.map_trace φ M
  have hdiag : φ.mapMatrix (Matrix.diagonal w) = Matrix.diagonal fun i ↦ φ (w i) := by
    rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero φ)]
  rw [hmap, hmap, map_mul, map_mul, map_mul, map_mul, map_pow, hdiag]
  refine rj_galois_trace_core (fun i ↦ φ (w i)) (φ.mapMatrix C) (φ.mapMatrix P) hr hs1 hs ν hν0
    ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, hP]
  · rw [← map_mul, ← map_mul, hCP]
  · rw [← map_pow, ← map_mul, hCr, hν, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_smul' _ _ _ (map_mul φ)]
  · rw [← hdiag, ← map_mul, ← map_mul, hwC]
  · rw [← hdiag, ← map_mul, ← map_mul, hwP]

end AJConjecture
