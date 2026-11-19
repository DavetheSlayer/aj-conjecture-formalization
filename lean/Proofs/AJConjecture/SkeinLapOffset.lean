import Mathlib
import AJConjecture.SkeinLapProfile

/-!
# The position of the cap at the bottom and at the top of the braid

For `ℓ + 1 < m` the column `q = lapCol w (ℓ + 1)` is not the column `0`. At the bottom, in the
profile after `ℓ + 1` laps, the thin columns on the left of `q` are among the columns of the laps
`1, …, ℓ`; at the top of the profile after `ℓ + 2` laps (`AJConjecture.profileEnd_strandEnd`: the
top thickness of the column `lapCol w i` is the bottom thickness of the column
`lapCol w (i + 1)`) they are the same columns and the column `0 = lapCol w 0`. Hence the two
offsets of `q` differ by `2`: this is the shift of the cap when it is moved across the matrix
`G`, which adds two strands to the column `0`. The column `0` is thick at the bottom, hence the
offset of `q` there is at least `k + 2`.
-/

namespace AJConjecture

/-- A lap `1 ≤ i < m` does not end in the column `0`. -/
private theorem lapCol_ne_zero_lapOffset (K : BraidKnot) (i : ℕ) (h1 : 1 ≤ i)
    (hi : i < K.strands) : lapCol K.word i ≠ 0 := by
  intro h0
  have hmod := (lapCol_eq_iff K i 0).mp h0
  rw [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.zero_mod] at hmod
  omega

/-- The top thickness of a column is the bottom thickness of the column one lap further. -/
private theorem profileEnd_apply_lapOffset (κ : ℕ → ℕ) (w : BraidWord) (x : ℕ) :
    profileEnd κ w x = κ (strandEnd w.reverse x) := by
  have h := profileEnd_strandEnd κ w (strandEnd w.reverse x)
  rwa [strandEnd_strandEnd_reverse] at h

/-- The column `0` is thick at the bottom after `ℓ + 1 < m` laps. -/
private theorem lapProfile_zero_col_lapOffset (K : BraidKnot) (k ℓ : ℕ)
    (h : ℓ + 1 < K.strands) : lapProfile K.word k (ℓ + 1) 0 = k + 2 := by
  have hmem : (0 : ℕ) ∉ (Finset.Icc 1 (ℓ + 1)).image (lapCol K.word) := by
    intro hmem
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_Icc] at hi
    exact lapCol_ne_zero_lapOffset K i hi.1 (by omega) hie
  simp only [lapProfile, hmem, ↓reduceIte]

/-- Away from the column `0`, the top of the profile after `ℓ + 2` laps is the bottom of the
profile after `ℓ + 1` laps. -/
private theorem profileEnd_lapProfile_of_ne_zero_lapOffset (w : BraidWord) (k ℓ x : ℕ)
    (hx : x ≠ 0) :
    profileEnd (lapProfile w k (ℓ + 2)) w x = lapProfile w k (ℓ + 1) x := by
  rw [profileEnd_apply_lapOffset]
  have hiff : strandEnd w.reverse x ∈ (Finset.Icc 1 (ℓ + 2)).image (lapCol w) ↔
      x ∈ (Finset.Icc 1 (ℓ + 1)).image (lapCol w) := by
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, hie⟩
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hxi : lapCol w i = x := by
        have h3 := congrArg (strandEnd w) hie
        rwa [strandEnd_lapCol_succ, strandEnd_strandEnd_reverse] at h3
      refine ⟨i, ⟨?_, by omega⟩, hxi⟩
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        exact absurd hxi.symm hx
      · exact h0
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      exact ⟨i + 1, ⟨by omega, by omega⟩, by
        rw [lapCol, Function.iterate_succ_apply', ← lapCol]⟩
  simp only [lapProfile, hiff]

/-- The offset of the column of the lap `ℓ + 1` at the top of the next profile is `2` less than
its offset at the bottom of the current profile. -/
theorem profileOffset_profileEnd_lapProfile (K : BraidKnot) (k ℓ : ℕ) (h : ℓ + 1 < K.strands) :
    profileOffset (profileEnd (lapProfile K.word k (ℓ + 2)) K.word) (lapCol K.word (ℓ + 1)) + 2 =
      profileOffset (lapProfile K.word k (ℓ + 1)) (lapCol K.word (ℓ + 1)) := by
  have hq := lapCol_ne_zero_lapOffset K (ℓ + 1) (by omega) h
  obtain ⟨q, hq'⟩ : ∃ q, lapCol K.word (ℓ + 1) = q + 1 := ⟨lapCol K.word (ℓ + 1) - 1, by omega⟩
  have h0 : profileEnd (lapProfile K.word k (ℓ + 2)) K.word 0 = k := by
    rw [profileEnd_apply_lapOffset]
    exact lapProfile_apply_lapCol K.word k (ℓ + 2) 1 le_rfl (by omega)
  rw [hq', profileOffset, profileOffset, Finset.sum_range_succ', Finset.sum_range_succ', h0,
    lapProfile_zero_col_lapOffset K k ℓ h,
    Finset.sum_congr rfl fun x _ ↦
      profileEnd_lapProfile_of_ne_zero_lapOffset K.word k ℓ (x + 1) (Nat.succ_ne_zero x),
    Nat.add_assoc]

/-- The column of the lap `ℓ + 1` is on the right of the thick column `0`. -/
theorem add_le_profileOffset_lapProfile (K : BraidKnot) (k ℓ : ℕ) (h : ℓ + 1 < K.strands) :
    k + 2 ≤ profileOffset (lapProfile K.word k (ℓ + 1)) (lapCol K.word (ℓ + 1)) := by
  have hq := lapCol_ne_zero_lapOffset K (ℓ + 1) (by omega) h
  obtain ⟨q, hq'⟩ : ∃ q, lapCol K.word (ℓ + 1) = q + 1 := ⟨lapCol K.word (ℓ + 1) - 1, by omega⟩
  rw [hq', profileOffset, Finset.sum_range_succ', lapProfile_zero_col_lapOffset K k ℓ h]
  exact Nat.le_add_left _ _

end AJConjecture
