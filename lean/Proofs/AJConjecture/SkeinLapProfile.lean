import Mathlib
import AJConjecture.SkeinLapCol

/-!
# The thickness profiles of the laps

Before the first lap every column has `k + 2` strands; the lap `ℓ + 1` thins the column
`lapCol w (ℓ + 1)`, which was still thick because the lap columns `1, …, m` are distinct
(`AJConjecture.lapCol_eq_iff`); after `m` laps every column has `k` strands; and after `ℓ ≤ m`
laps the total thickness is `(k + 2) m - 2 ℓ` (count the `ℓ` distinct thin columns, all `< m`).
-/

namespace AJConjecture

/-- Before the first lap every column is thick. -/
theorem lapProfile_zero (w : BraidWord) (k : ℕ) : lapProfile w k 0 = fun _ ↦ k + 2 := by
  funext x
  simp [lapProfile]

/-- The columns of the laps `1, …, ℓ` are thin after `ℓ` laps. -/
theorem lapProfile_apply_lapCol (w : BraidWord) (k ℓ i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ ℓ) :
    lapProfile w k ℓ (lapCol w i) = k := by
  have hmem : lapCol w i ∈ (Finset.Icc 1 ℓ).image (lapCol w) :=
    Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨h1, hi⟩)
  simp only [lapProfile, hmem, ↓reduceIte]

/-- The column of the lap `ℓ + 1 ≤ m` is not the column of an earlier lap `1, …, ℓ`. -/
private theorem lapCol_succ_notMem_image_lapProfile (K : BraidKnot) (ℓ : ℕ)
    (h : ℓ < K.strands) :
    lapCol K.word (ℓ + 1) ∉ (Finset.Icc 1 ℓ).image (lapCol K.word) := by
  intro hmem
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_Icc] at hi
  have hmod := (lapCol_eq_iff K i (ℓ + 1)).mp hie
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : i < K.strands)] at hmod
  rcases Nat.lt_or_ge (ℓ + 1) K.strands with h' | h'
  · rw [Nat.mod_eq_of_lt h'] at hmod
    omega
  · rw [show ℓ + 1 = K.strands from by omega, Nat.mod_self] at hmod
    omega

/-- Thickening the column of the lap `ℓ + 1` gives back the profile after `ℓ` laps. -/
theorem lapProfile_update (K : BraidKnot) (k ℓ : ℕ) (h : ℓ < K.strands) :
    Function.update (lapProfile K.word k (ℓ + 1)) (lapCol K.word (ℓ + 1)) (k + 2) =
      lapProfile K.word k ℓ := by
  funext x
  by_cases hx : x = lapCol K.word (ℓ + 1)
  · subst hx
    rw [Function.update_self]
    simp only [lapProfile, lapCol_succ_notMem_image_lapProfile K ℓ h, ↓reduceIte]
  · rw [Function.update_of_ne hx]
    have hiff : x ∈ (Finset.Icc 1 (ℓ + 1)).image (lapCol K.word) ↔
        x ∈ (Finset.Icc 1 ℓ).image (lapCol K.word) := by
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
        refine ⟨i, ⟨h1, ?_⟩, rfl⟩
        rcases Nat.lt_or_ge ℓ i with h3 | h3
        · exact absurd (by rw [show i = ℓ + 1 from by omega]) hx
        · exact h3
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
        exact ⟨i, ⟨h1, by omega⟩, rfl⟩
    simp only [lapProfile, hiff]

/-- After as many laps as there are strands, every column of the braid is thin. -/
theorem lapProfile_strands (K : BraidKnot) (k x : ℕ) (hx : x < K.strands) :
    lapProfile K.word k K.strands x = k := by
  obtain ⟨n, hn⟩ := K.connected ⟨0, K.strands_pos⟩ ⟨x, hx⟩
  have hxn : lapCol K.word n = x := by
    rw [lapCol_eq_strandPerm_pow, hn]
  have hpos := K.strands_pos
  rcases Nat.eq_zero_or_pos (n % K.strands) with h0 | h0
  · have hmod : lapCol K.word K.strands = lapCol K.word n := by
      rw [lapCol_eq_iff, Nat.ModEq, Nat.mod_self, h0]
    rw [← hxn, ← hmod]
    exact lapProfile_apply_lapCol K.word k K.strands K.strands hpos le_rfl
  · have hmod : lapCol K.word (n % K.strands) = lapCol K.word n := by
      rw [lapCol_eq_iff]
      exact Nat.mod_modEq n K.strands
    rw [← hxn, ← hmod]
    exact lapProfile_apply_lapCol K.word k K.strands (n % K.strands) h0
      (Nat.mod_lt n hpos).le

/-- The total thickness after `ℓ` laps. -/
theorem profileOffset_lapProfile (K : BraidKnot) (k ℓ : ℕ) (h : ℓ ≤ K.strands) :
    profileOffset (lapProfile K.word k ℓ) K.strands + 2 * ℓ = (k + 2) * K.strands := by
  induction ℓ with
  | zero =>
    rw [lapProfile_zero, profileOffset, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  | succ ℓ ih =>
    have ih' := ih (by omega)
    have hmem : lapCol K.word (ℓ + 1) ∈ Finset.range K.strands :=
      Finset.mem_range.mpr (lapCol_lt K (ℓ + 1))
    have hthin := lapProfile_apply_lapCol K.word k (ℓ + 1) (ℓ + 1) (by omega) le_rfl
    have hsum := Finset.add_sum_erase (Finset.range K.strands) (lapProfile K.word k (ℓ + 1)) hmem
    rw [← lapProfile_update K k ℓ (by omega), profileOffset, Finset.sum_update_of_mem hmem,
      Finset.sdiff_singleton_eq_erase] at ih'
    rw [profileOffset, ← hsum, hthin]
    omega

end AJConjecture
