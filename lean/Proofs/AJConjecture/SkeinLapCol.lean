import Mathlib
import AJConjecture.SkeinLap
import AJConjecture.SkeinStrandEnd
import AJConjecture.SkeinThickCableBasic

/-!
# The laps visit every column once

`lapCol w ℓ` is the `ℓ`-th iterate at `0` of the strand permutation
(`AJConjecture.strandEnd_eq_strandPerm_symm` and `AJConjecture.strandEnd_reverse_strandEnd`: on the
columns `< m` the map `strandEnd w.reverse` is the strand permutation of `w`). For a knot the
strand permutation is transitive, hence a single cycle of length `m` on the `m` columns
(`Equiv.Perm.IsCycleOn`, `Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply`): two laps end in the same
column exactly when their numbers are congruent modulo `m`. In particular the columns
`lapCol w 1, …, lapCol w m` are all the columns, and `lapCol w ℓ ≠ 0` for `0 < ℓ < m`.
-/

namespace AJConjecture

/-- One lap backwards: the strand that ends in the column of the lap `ℓ` starts in the column
of the lap `ℓ + 1`. -/
theorem strandEnd_lapCol_succ (w : BraidWord) (ℓ : ℕ) :
    strandEnd w (lapCol w (ℓ + 1)) = lapCol w ℓ := by
  rw [lapCol, Function.iterate_succ_apply', strandEnd_strandEnd_reverse, lapCol]

/-- On the columns of the braid, `strandEnd w.reverse` is the strand permutation. -/
private theorem strandEnd_reverse_eq_strandPerm_lapCol (m : ℕ) (w : BraidWord)
    (hw : IsOnStrands m w) (p : Fin m) :
    strandEnd w.reverse p = ((strandPerm m w p : Fin m) : ℕ) := by
  have h := strandEnd_eq_strandPerm_symm m w hw (strandPerm m w p)
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h
  rw [← h, strandEnd_reverse_strandEnd]

/-- The lap columns are the iterates of the strand permutation at the column `0`. -/
theorem lapCol_eq_strandPerm_pow (K : BraidKnot) (ℓ : ℕ) :
    lapCol K.word ℓ =
      (((strandPerm K.strands K.word ^ ℓ) ⟨0, K.strands_pos⟩ : Fin K.strands) : ℕ) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [lapCol, Function.iterate_succ_apply', ← lapCol, ih,
      strandEnd_reverse_eq_strandPerm_lapCol K.strands K.word K.isOnStrands, pow_succ',
      Equiv.Perm.mul_apply]

/-- The lap columns are columns of the braid. -/
theorem lapCol_lt (K : BraidKnot) (ℓ : ℕ) : lapCol K.word ℓ < K.strands := by
  rw [lapCol_eq_strandPerm_pow]
  exact Fin.is_lt _

/-- Two laps end in the same column exactly when their numbers are congruent modulo the number
of strands. -/
theorem lapCol_eq_iff (K : BraidKnot) (a b : ℕ) :
    lapCol K.word a = lapCol K.word b ↔ a ≡ b [MOD K.strands] := by
  have hc : (strandPerm K.strands K.word).IsCycleOn
      ((Finset.univ : Finset (Fin K.strands)) : Set (Fin K.strands)) := by
    refine ⟨by simp, fun x _ y _ ↦ ?_⟩
    obtain ⟨n, hn⟩ := K.connected x y
    exact ⟨n, by simpa using hn⟩
  have h := hc.pow_apply_eq_pow_apply (a := ⟨0, K.strands_pos⟩) (Finset.mem_univ _)
    (m := a) (n := b)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [lapCol_eq_strandPerm_pow, lapCol_eq_strandPerm_pow, ← h, Fin.val_inj]

end AJConjecture
