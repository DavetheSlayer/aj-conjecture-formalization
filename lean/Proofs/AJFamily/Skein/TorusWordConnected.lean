import Mathlib
import AJFamily.Skein.TorusWordPerm

/-!
# The family closed braid is a knot

`connected_whiteheadTorusWord`: the strand permutation of `whiteheadTorusWord k` is a single
`(4k+3)`-cycle, so its closure has one component.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The `t`-th point of the cycle of `whiteheadTorusPermNat k` starting at `0`. -/
private def whiteheadCycleEnum (k t : ℕ) : ℕ :=
  if t = 0 then 0
  else if t ≤ k + 1 then 4 * k + 3 - 2 * t
  else if t ≤ 3 * k then t - k - 1
  else if t ≤ 4 * k + 1 then 10 * k + 2 - 2 * t
  else 4 * k + 2

/-- The position of `j` on the cycle enumerated by `whiteheadCycleEnum k`. -/
private def whiteheadCycleIndex (k j : ℕ) : ℕ :=
  if j = 0 then 0
  else if j ≤ 2 * k - 1 then j + k + 1
  else if j = 4 * k + 2 then 4 * k + 2
  else if j % 2 = 1 then (4 * k + 3 - j) / 2
  else (10 * k + 2 - j) / 2

/-- One step of the permutation advances the cycle enumeration by one. -/
private theorem whiteheadTorusPermNat_cycleEnum (k t : ℕ) (hk : 1 ≤ k) (ht : t < 4 * k + 2) :
    whiteheadTorusPermNat k (whiteheadCycleEnum k t) = whiteheadCycleEnum k (t + 1) := by
  generalize hx : whiteheadCycleEnum k t = x
  generalize hy : whiteheadCycleEnum k (t + 1) = y
  unfold whiteheadCycleEnum at hx hy
  unfold whiteheadTorusPermNat
  split_ifs at hx hy ⊢ <;> (try contradiction) <;> omega

/-- The permutation sends the last point of the enumeration back to `0`. -/
private theorem whiteheadTorusPermNat_cycleEnum_last (k : ℕ) :
    whiteheadTorusPermNat k (whiteheadCycleEnum k (4 * k + 2)) = 0 := by
  have h : whiteheadCycleEnum k (4 * k + 2) = 4 * k + 2 := by
    unfold whiteheadCycleEnum
    split_ifs <;> omega
  rw [h]
  unfold whiteheadTorusPermNat
  split_ifs <;> omega

/-- `whiteheadCycleIndex` is a right inverse of the cycle enumeration on `[0, 4k+3)`. -/
private theorem whiteheadCycleEnum_index (k j : ℕ) (hk : 1 ≤ k) (hj : j < 4 * k + 3) :
    whiteheadCycleEnum k (whiteheadCycleIndex k j) = j ∧ whiteheadCycleIndex k j ≤ 4 * k + 2 := by
  unfold whiteheadCycleEnum whiteheadCycleIndex
  split_ifs <;> (try contradiction) <;> omega

/-- The iterates of the strand permutation on `0` follow the cycle enumeration. -/
private theorem strandPerm_whiteheadTorusWord_pow_zero (k : ℕ) (hk : 1 ≤ k) (t : ℕ)
    (ht : t ≤ 4 * k + 2) :
    (((strandPerm (4 * k + 3) (whiteheadTorusWord k) ^ t) ⟨0, by omega⟩ : Fin (4 * k + 3)) :
      ℕ) = whiteheadCycleEnum k t := by
  induction t with
  | zero => simp [whiteheadCycleEnum]
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, strandPerm_whiteheadTorusWord k hk, ih (by omega),
      whiteheadTorusPermNat_cycleEnum k t hk (by omega)]

theorem connected_whiteheadTorusWord (k : ℕ) (hk : 1 ≤ k) (i j : Fin (4 * k + 3)) :
    ∃ n : ℕ, (strandPerm (4 * k + 3) (whiteheadTorusWord k) ^ n) i = j := by
  set σ := strandPerm (4 * k + 3) (whiteheadTorusWord k) with hσ
  have hreach : ∀ x : Fin (4 * k + 3), (σ ^ whiteheadCycleIndex k x) ⟨0, by omega⟩ = x := by
    intro x
    obtain ⟨h1, h2⟩ := whiteheadCycleEnum_index k x hk x.isLt
    exact Fin.ext <| (strandPerm_whiteheadTorusWord_pow_zero k hk _ h2).trans h1
  have hloop : (σ ^ (4 * k + 3)) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    refine Fin.ext ?_
    rw [pow_succ', Equiv.Perm.mul_apply, hσ, strandPerm_whiteheadTorusWord k hk,
      strandPerm_whiteheadTorusWord_pow_zero k hk _ le_rfl, whiteheadTorusPermNat_cycleEnum_last]
  have hi := (whiteheadCycleEnum_index k i hk i.isLt).2
  refine ⟨whiteheadCycleIndex k j + (4 * k + 3 - whiteheadCycleIndex k i), ?_⟩
  have hback : (σ ^ (4 * k + 3 - whiteheadCycleIndex k i))
      ((σ ^ whiteheadCycleIndex k i) ⟨0, by omega⟩) = ⟨0, by omega⟩ := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega), hloop]
  rw [hreach i] at hback
  rw [pow_add, Equiv.Perm.mul_apply, hback, hreach j]

end AJConjecture
