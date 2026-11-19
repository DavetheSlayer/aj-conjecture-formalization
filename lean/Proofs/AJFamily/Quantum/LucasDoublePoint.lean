import Mathlib
import AJConjecture.QAlgTransferJetData

/-!
# Lucas sequences at a double point

Closed forms over the dual numbers of the Lucas sequence `transferLucas` and its `z`-derivatives
at `z = 2w + ε z₁`, `s = w² + ε s₁`, near the double point `z² = 4s`. They give the target jet
`famTargetJet` at a node.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The first component of the dual number `2` is `2`. -/
private lemma fst_two_dualNumber : (2 : DualNumber ℂ).fst = 2 := by
  rw [show (2 : DualNumber ℂ) = ((2 : ℕ) : DualNumber ℂ) by norm_cast, TrivSqZeroExt.fst_natCast]
  norm_num

/-- The second component of the dual number `2` is `0`. -/
private lemma snd_two_dualNumber : (2 : DualNumber ℂ).snd = 0 := by
  rw [show (2 : DualNumber ℂ) = ((2 : ℕ) : DualNumber ℂ) by norm_cast, TrivSqZeroExt.snd_natCast]

/-- `S_k = 2w^k + ε (k² w^(k-1) z₁ - k(k-1) w^(k-2) s₁)` at `z = 2w + ε z₁`, `s = w² + ε s₁`. -/
theorem transferLucas_dual_double (w z₁ s₁ : ℂ) (k : ℕ) :
    transferLucas (TrivSqZeroExt.inl (2 * w) + TrivSqZeroExt.inl z₁ * DualNumber.eps)
        (TrivSqZeroExt.inl (w ^ 2) + TrivSqZeroExt.inl s₁ * DualNumber.eps) k =
      TrivSqZeroExt.inl (2 * w ^ k) +
        TrivSqZeroExt.inl ((k : ℂ) ^ 2 * w ^ (k - 1) * z₁ - (k : ℂ) * ((k : ℂ) - 1) * w ^ (k - 2) * s₁) *
          DualNumber.eps := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => ext <;> simp [transferLucas, fst_two_dualNumber, snd_two_dualNumber]
    | 1, _ => ext <;> simp [transferLucas]
    | 2, _ => ext <;> simp [transferLucas, fst_two_dualNumber, snd_two_dualNumber] <;> ring
    | 3, _ => ext <;> simp [transferLucas, fst_two_dualNumber, snd_two_dualNumber] <;> ring
    | d + 4, ih =>
      rw [transferLucas, ih (d + 3) (by omega), ih (d + 2) (by omega)]
      ext <;> simp <;> ring

/-- The value part of `S_k'` at `z = 2w + ε z₁`, `s = w² + ε s₁` is `k² w^(k-1)`. -/
theorem fst_transferLucasDeriv_dual_double (w z₁ s₁ : ℂ) (k : ℕ) :
    (transferLucasDeriv (TrivSqZeroExt.inl (2 * w) + TrivSqZeroExt.inl z₁ * DualNumber.eps)
        (TrivSqZeroExt.inl (w ^ 2) + TrivSqZeroExt.inl s₁ * DualNumber.eps) k).fst =
      (k : ℂ) ^ 2 * w ^ (k - 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [transferLucasDeriv]
    | 1, _ => simp [transferLucasDeriv]
    | d + 2, ih =>
      rw [transferLucasDeriv]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
        ih (d + 1) (by omega), ih d (by omega), transferLucas_dual_double]
      rcases d with _ | d
      · simp; ring
      · simp; ring

/-- The value part of `S_k^[2]` at `z = 2w + ε z₁`, `s = w² + ε s₁` is `k²(k²-1)/12 · w^(k-2)`. -/
theorem fst_transferLucasHasse_dual_double (w z₁ s₁ : ℂ) (k : ℕ) :
    (transferLucasHasse (TrivSqZeroExt.inl (2 * w) + TrivSqZeroExt.inl z₁ * DualNumber.eps)
        (TrivSqZeroExt.inl (w ^ 2) + TrivSqZeroExt.inl s₁ * DualNumber.eps) k).fst =
      (k : ℂ) ^ 2 * ((k : ℂ) ^ 2 - 1) / 12 * w ^ (k - 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [transferLucasHasse]
    | 1, _ => simp [transferLucasHasse]
    | d + 2, ih =>
      rw [transferLucasHasse]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
        ih (d + 1) (by omega), ih d (by omega), fst_transferLucasDeriv_dual_double]
      rcases d with _ | _ | d
      · norm_num
      · simp; ring
      · simp; ring

end AJConjecture
