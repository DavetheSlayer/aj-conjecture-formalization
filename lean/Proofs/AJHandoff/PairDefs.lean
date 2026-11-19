import Mathlib
import AJConjecture.BraidKnot

/-!
# Torus pairs and the positive torus braids

The admissible pairs of Theorem T are the coprime `2 ≤ r < s`. The right-handed torus knot
`T(r, s)` is the closure of the positive braid `(σ_0 σ_1 ⋯ σ_(r-2))^s` on `r` strands.
-/

namespace AJConjecture

/-- The admissible pairs of Theorem T: coprime integers `2 ≤ r < s`. -/
def IsTorusPair (r s : ℕ) : Prop :=
  2 ≤ r ∧ r < s ∧ Nat.Coprime r s

/-- The positive braid word `(σ_0 σ_1 ⋯ σ_(r-2))^s` on `r` strands. -/
def torusPairWord (r s : ℕ) : BraidWord :=
  (List.replicate s ((List.range (r - 1)).map fun i ↦ (i, true))).flatten

theorem isOnStrands_torusPairWord (r s : ℕ) : IsOnStrands r (torusPairWord r s) := by
  intro g hg
  simp only [torusPairWord, List.mem_flatten, List.mem_replicate] at hg
  obtain ⟨l, ⟨-, rfl⟩, hg⟩ := hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  rw [List.mem_range] at hi
  dsimp only
  omega

/-- The closure of `(σ_0 ⋯ σ_(r-2))^s` is connected when `r` and `s` are coprime: the strand
permutation is the `s`-th power of an `r`-cycle. -/
theorem connected_torusPairWord (r s : ℕ) (h : IsTorusPair r s) (i j : Fin r) :
    ∃ n : ℕ, (strandPerm r (torusPairWord r s) ^ n) i = j := by
  obtain ⟨hr, hrs, hcop⟩ := h
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  have happ : ∀ u v : BraidWord,
      strandPerm (p + 1) (u ++ v) = strandPerm (p + 1) u * strandPerm (p + 1) v := by
    intro u v
    simp [strandPerm, List.map_append, List.prod_append]
  -- `σ_0 ⋯ σ_(k-1)` acts as the cycle `0 ↦ 1 ↦ ⋯ ↦ k ↦ 0`
  have hclimb : ∀ k : ℕ, k < p + 1 → ∀ x : Fin (p + 1),
      ((strandPerm (p + 1) ((List.range k).map fun i ↦ (i, true))) x : ℕ) =
        if (x : ℕ) < k then (x : ℕ) + 1 else if (x : ℕ) = k then 0 else (x : ℕ) := by
    intro k
    induction k with
    | zero =>
      intro _ x
      simp only [List.range_zero, List.map_nil, strandPerm, List.prod_nil, Equiv.Perm.coe_one,
        id_eq, Nat.not_lt_zero, ite_false]
      split_ifs with h <;> omega
    | succ k ih =>
      intro hk x
      rw [List.range_succ, List.map_append, happ, Equiv.Perm.mul_apply]
      have hs : strandPerm (p + 1) [(k, true)] = Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩ := by
        simp only [strandPerm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, strandSwap, hk, ↓reduceDIte]
      simp only [List.map_cons, List.map_nil]
      rw [hs]
      by_cases h1 : (x : ℕ) = k
      · have hx : x = ⟨k, by omega⟩ := Fin.ext h1
        rw [hx, Equiv.swap_apply_left, ih (by omega)]
        simp
      · by_cases h2 : (x : ℕ) = k + 1
        · have hx : x = ⟨k + 1, hk⟩ := Fin.ext h2
          rw [hx, Equiv.swap_apply_right, ih (by omega)]
          simp
        · rw [Equiv.swap_apply_of_ne_of_ne (fun h ↦ h1 (by rw [h])) (fun h ↦ h2 (by rw [h])),
            ih (by omega)]
          split_ifs <;> omega
  have hδ : ∀ x : Fin (p + 1),
      ((strandPerm (p + 1) ((List.range p).map fun i ↦ (i, true))) x : ℕ) =
        ((x : ℕ) + 1) % (p + 1) := by
    intro x
    rw [hclimb p (by omega)]
    split_ifs with h1 h2
    · rw [Nat.mod_eq_of_lt (by omega)]
    · rw [h2, Nat.mod_self]
    · omega
  have hw : ∀ t : ℕ, strandPerm (p + 1)
      (List.replicate t ((List.range p).map fun i ↦ (i, true))).flatten =
        strandPerm (p + 1) ((List.range p).map fun i ↦ (i, true)) ^ t := by
    intro t
    induction t with
    | zero => simp [strandPerm]
    | succ t ih => rw [List.replicate_succ, List.flatten_cons, happ, ih, pow_succ']
  have hpow : ∀ (n : ℕ) (x : Fin (p + 1)),
      (((strandPerm (p + 1) ((List.range p).map fun i ↦ (i, true))) ^ n) x : ℕ) =
        ((x : ℕ) + n) % (p + 1) := by
    intro n
    induction n with
    | zero => intro x; simp [Nat.mod_eq_of_lt x.isLt]
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, hδ, ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        add_assoc]
  -- the `s`-th power of an `(p + 1)`-cycle with `s` prime to `p + 1` is transitive
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm (by omega)
  refine ⟨a * ((j : ℕ) + (p + 1) - i), Fin.ext ?_⟩
  rw [torusPairWord, Nat.add_sub_cancel, hw, ← pow_mul, hpow]
  have h1 :
      s * (a * ((j : ℕ) + (p + 1) - i)) % (p + 1) = ((j : ℕ) + (p + 1) - i) % (p + 1) := by
    rw [← mul_assoc, Nat.mul_mod, ha, one_mul, Nat.mod_mod]
  have h2 : (i : ℕ) + ((j : ℕ) + (p + 1) - i) = j + (p + 1) := by omega
  rw [Nat.add_mod, h1, ← Nat.add_mod, h2, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- The right-handed torus knot `T(r, s)` as the closure of `(σ_0 ⋯ σ_(r-2))^s`. -/
def torusPairKnot (r s : ℕ) (h : IsTorusPair r s) : BraidKnot where
  strands := r
  word := torusPairWord r s
  strands_pos := by obtain ⟨hr, -⟩ := h; omega
  isOnStrands := isOnStrands_torusPairWord r s
  connected := connected_torusPairWord r s h

end AJConjecture
