import Mathlib
import AJPaper.Filling.PpATwistBlocks

/-!
# The twist knots as closed braids (PpA, Section 7.6, claim 1: the knots)

Source: arXiv:2611.24826v1, Section 2 (`marking.tex`): "Write `Z_ℓ = Z_ℓ(U)` for the pure
closure, where `U` is the unknot and the patterned solid torus is embedded with zero framing".

`ppaTwistKnot ℓ` is the closure of `ppaTwistWord ℓ` (`AJPaper.Filling.PpATwistBlocks`) on
`3 + twExtra ℓ` strands: the twist knot `Z_ℓ = W_(-,ℓ)(U)` (knot type checked by computer, see
there).

`connected_ppaTwistWord`: the closure is a knot. Route: the strand map of a block word is
`stPerm` (`artinWord_blocksWord_fst`; `strandPerm` and `artinWord` agree, as in
`AJTwist.Knot.TwKConnected`). The tail `[σ_1⁻¹, σ_0⁻¹, σ_1⁻¹]` maps the top positions
`0, 1, 2` to `2, 1, 0` and fixes the new ones; by `twChain_detour` (applied in the trivial
group, where its hypothesis is void) the chain fixes `2`, leads from `1` through new positions
to `0` and from `0` through the other new positions to `1`, every new position being met
once. So the orbit of `0` is `0, 2, (new), 1, (new), 0`: one cycle through all strands.
Checked for `|ℓ| ≤ 5` on the Lean word (`SCR/A/lean/TestTwist.lean`).
-/

namespace AJConjecture

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_ppaTwistKnot (m : ℕ) (w : BraidWord) (k : Fin m) :
    (artinWord m w k).1 = strandPerm m w k := by
  induction w with
  | nil => simp [artinWord, strandPerm]
  | cons g w ih =>
    rw [strandPerm, List.map_cons, List.prod_cons, ← strandPerm, Equiv.Perm.mul_apply, ← ih]
    simp only [artinWord]
    generalize (artinWord m w k).1 = l
    by_cases h : g.1 + 1 < m
    · simp only [artinGen, strandSwap, h, dite_true, Equiv.swap_apply_def]
      split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
    · simp [artinGen, strandSwap, h]

/-- The powers of the strand permutation of a block word are the iterates of `stPerm`. -/
private theorem strandPerm_pow_val_ppaTwistKnot {m : ℕ} (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (n : ℕ) (x : Fin m) :
    (((strandPerm m (blocksWord bs) ^ n) x : Fin m) : ℕ) = (stPerm bs)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ← artinWord_fst_eq_strandPerm_ppaTwistKnot,
      artinWord_blocksWord_fst _ hv, ih, Function.iterate_succ_apply']

/-- The strand map of the tail exchanges the positions `0` and `2`. -/
private theorem stPerm_ppaTwistTail_ppaTwistKnot (t : ℕ) :
    stPerm ppaTwistTail t = if t = 0 then 2 else if t = 2 then 0 else t := by
  obtain rfl | rfl | rfl | ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ 3 ≤ t := by omega
  · rfl
  · rfl
  · rfl
  · have h1 : (SBlock.neg 1).perm t = t := by
      simp only [SBlock.perm]
      split_ifs <;> omega
    have h0 : (SBlock.neg 0).perm t = t := by
      simp only [SBlock.perm]
      split_ifs <;> omega
    simp only [ppaTwistTail, stPerm, h1, h0]
    split_ifs <;> omega

/-- The orbit of `0` under a map `σ` that sends `0` to `2`, `2` to `c 0` and agrees with `c`
elsewhere, when `c` leads from `0` to `1` and from `1` to `0` through positions `≥ 3`. -/
private theorem iterate_orbit_ppaTwistKnot (c σ : ℕ → ℕ) (k₁ k₂ : ℕ) (hk₂ : 0 < k₂)
    (hσ0 : σ 0 = 2) (hσ1 : σ 1 = c 1) (hσ2 : σ 2 = c 0) (hσ : ∀ t, 3 ≤ t → σ t = c t)
    (h1 : ∀ i, 0 < i → i < k₁ → 3 ≤ c^[i] 1) (h2 : c^[k₂] 0 = 1)
    (h2' : ∀ i, 0 < i → i < k₂ → 3 ≤ c^[i] 0) :
    (∀ i, 0 < i → i ≤ k₂ → σ^[1 + i] 0 = c^[i] 0) ∧
      ∀ i, i ≤ k₁ → σ^[1 + k₂ + i] 0 = c^[i] 1 := by
  have hA : ∀ i, 0 < i → i ≤ k₂ → σ^[1 + i] 0 = c^[i] 0 := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      intro _
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_zero,
        id, hσ0, hσ2]
      rfl
    | succ i hi ih =>
      intro hik
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega),
        hσ _ (h2' i hi (by omega)), Function.iterate_succ_apply']
  refine ⟨hA, fun i ↦ ?_⟩
  induction i with
  | zero =>
    intro _
    rw [Nat.add_zero, hA k₂ hk₂ le_rfl, h2]
    rfl
  | succ i ih =>
    intro hik
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega),
      Function.iterate_succ_apply']
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact hσ1
    · exact hσ _ (h1 i hi (by omega))

/-- Every position is reached from `0` by the strand map of the blocks. -/
private theorem exists_iterate_stPerm_ppaTwistKnot (ℓ : ℤ) {x : ℕ} (hx : x < 3 + twExtra ℓ) :
    ∃ n : ℕ, (stPerm (ppaTwistBlocks ℓ))^[n] 0 = x := by
  obtain ⟨hold, k₁, k₂, -, hk₂, -, -, h1', -, h2, h2', -, hcov⟩ :=
    twChain_detour (M := 3) (j₀ := 1) (by norm_num) (by norm_num) ℓ
      (fun _ : Fin (3 + twExtra ℓ) ↦ ()) (fun _ _ ↦ rfl)
  have hσ : ∀ t, stPerm (ppaTwistBlocks ℓ) t =
      stPerm (twChain 3 1 ℓ) (if t = 0 then 2 else if t = 2 then 0 else t) := fun t ↦ by
    rw [ppaTwistBlocks, stPerm_append, stPerm_ppaTwistTail_ppaTwistKnot]
  obtain ⟨hA, hB⟩ := iterate_orbit_ppaTwistKnot (stPerm (twChain 3 1 ℓ))
    (stPerm (ppaTwistBlocks ℓ)) k₁ k₂ hk₂
    (by rw [hσ, ite_eq_left rfl]; exact (hold 2 (by norm_num) (by norm_num) (by norm_num)).1)
    (by rw [hσ, ite_eq_right (by norm_num), ite_eq_right (by norm_num)])
    (by rw [hσ, ite_eq_right (by norm_num), ite_eq_left rfl])
    (fun t ht ↦ by rw [hσ, ite_eq_right (by omega), ite_eq_right (by omega)]) h1' h2 h2'
  by_cases h3 : 3 ≤ x
  · rcases hcov x h3 hx with ⟨i, hi, hik, rfl⟩ | ⟨i, hi, hik, rfl⟩
    · exact ⟨_, hB i hik.le⟩
    · exact ⟨_, hA i hi hik.le⟩
  · obtain rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    · exact ⟨0, rfl⟩
    · exact ⟨_, (hB 0 (Nat.zero_le _)).trans rfl⟩
    · refine ⟨1, ?_⟩
      rw [Function.iterate_one, hσ, ite_eq_left rfl]
      exact (hold 2 (by norm_num) (by norm_num) (by norm_num)).1

/-- The closure of the word is connected. -/
theorem connected_ppaTwistWord (ℓ : ℤ) (i j : Fin (3 + twExtra ℓ)) :
    ∃ k : ℕ, (strandPerm (3 + twExtra ℓ) (ppaTwistWord ℓ) ^ k) i = j := by
  have hpos : 0 < 3 + twExtra ℓ := i.pos
  have key : ∀ x : Fin (3 + twExtra ℓ),
      (strandPerm (3 + twExtra ℓ) (ppaTwistWord ℓ)).SameCycle ⟨0, hpos⟩ x := by
    intro x
    obtain ⟨n, hn⟩ := exists_iterate_stPerm_ppaTwistKnot ℓ x.isLt
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Fin.ext ((strandPerm_pow_val_ppaTwistKnot _ (ppaTwistBlocks_valid ℓ) n ⟨0, hpos⟩).trans
      hn)
  exact ((key i).symm.trans (key j)).exists_nat_pow_eq

/-- The twist knot `Z_ℓ = W_(-,ℓ)(U)` as a closed braid. -/
def ppaTwistKnot (ℓ : ℤ) : BraidKnot where
  strands := 3 + twExtra ℓ
  word := ppaTwistWord ℓ
  strands_pos := Nat.add_pos_left (by norm_num) _
  isOnStrands := isOnStrands_ppaTwistWord ℓ
  connected := connected_ppaTwistWord ℓ

end AJConjecture
