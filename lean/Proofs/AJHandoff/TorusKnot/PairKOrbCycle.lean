import Mathlib
import AJHandoff.TorusKnot.PairKOrbPerm
import AJHandoff.TorusKnot.PairKKnot

/-!
# The orbit of `0` is one cycle through all positions

`pairOrbT r s k = (stPerm (pairBlocks r s))^[k] 0`: the orbit stays among the positions, returns
to `0` after `m = 2c + 1` steps, is injective on `[0, m)` and meets every position; so a sum along
the orbit is the sum over all positions, and `pairOrbIdx r s t` is the orbit index of `t`.

Route: the closure is connected (`connected_pairWhiteheadWord`); the strand permutation of the
word is `stPerm (pairBlocks r s)` on values (`artinWord_blocksWord_fst` with a copy of the private
`artinWord_fst_eq_strandPerm_peri` of `AJHandoff.TorusKnot.PairKPeriGeneric`); then copy
`minimalPeriod_eq_of_transitive` and `sum_orbit_eq_sum` from there (private) and
`Function.iterate_injOn_Iio_minimalPeriod`. `pairOrbT_strands` is `iterate_stPerm_strands`.
For `pairOrbIdx`: `List.findIdx_lt_length_of_exists`, `List.findIdx_getElem`.
-/

namespace AJConjecture

/-! ### The strand permutation of the word and its orbit of `0` -/

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_cyc (m : ℕ) (w : BraidWord) (k : Fin m) :
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

/-- A permutation of `Fin m` whose powers move `x` everywhere has minimal period `m` at `x`. -/
private theorem minimalPeriod_eq_of_transitive_cyc {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin m)
    (h : ∀ j, ∃ k : ℕ, (σ ^ k) x = j) : Function.minimalPeriod σ x = m := by
  have hx : x ∈ Function.periodicPts σ := σ.injective.mem_periodicPts x
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts hx
  refine le_antisymm (by simpa using Function.minimalPeriod_le_card (f := σ) (x := x)) ?_
  have hs : Function.Surjective fun i : Fin (Function.minimalPeriod σ x) ↦ σ^[i] x := by
    intro j
    obtain ⟨k, hk⟩ := h j
    refine ⟨⟨k % Function.minimalPeriod σ x, Nat.mod_lt _ hp⟩, ?_⟩
    simp only
    rw [Function.iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hk]
  simpa using Fintype.card_le_of_surjective _ hs

/-- The strand permutation of `pairWhiteheadWord r s`. -/
private abbrev pairOrbSigma (r s : ℕ) : Equiv.Perm (Fin (pairStrands r s)) :=
  strandPerm (pairStrands r s) (pairWhiteheadWord r s)

/-- The iterates of the strand permutation from `0` are the strands of the orbit. -/
private theorem pairOrbSigma_iterate {r s : ℕ} (h : IsTorusPair r s) (k : ℕ) :
    (((pairOrbSigma r s)^[k] ⟨0, Nat.succ_pos _⟩ : Fin (pairStrands r s)) : ℕ) =
      pairOrbT r s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', pairOrbT, Function.iterate_succ_apply', ← pairOrbT, ← ih,
      pairOrbSigma, ← artinWord_fst_eq_strandPerm_cyc, pairWhiteheadWord,
      artinWord_blocksWord_fst _ (pairBlocks_valid h)]

/-- The strand permutation has minimal period `m` at `0`. -/
private theorem pairOrbSigma_minimalPeriod {r s : ℕ} (h : IsTorusPair r s) :
    Function.minimalPeriod (pairOrbSigma r s) ⟨0, Nat.succ_pos _⟩ = pairStrands r s :=
  minimalPeriod_eq_of_transitive_cyc _ _ (connected_pairWhiteheadWord h _)

/-- The `k`-th strand of the orbit is the `(k mod m)`-th. -/
private theorem pairOrbT_mod {r s : ℕ} (h : IsTorusPair r s) (k : ℕ) :
    pairOrbT r s (k % pairStrands r s) = pairOrbT r s k := by
  have e := Function.iterate_mod_minimalPeriod_eq (f := pairOrbSigma r s)
    (x := ⟨0, Nat.succ_pos _⟩) (n := k)
  rw [pairOrbSigma_minimalPeriod h] at e
  rw [← pairOrbSigma_iterate h, ← pairOrbSigma_iterate h, e]

/-! ### The orbit of `0` -/

/-- One more step along the orbit. -/
theorem pairOrbT_succ (r s k : ℕ) :
    pairOrbT r s (k + 1) = stPerm (pairBlocks r s) (pairOrbT r s k) := by
  rw [pairOrbT, pairOrbT, Function.iterate_succ_apply']

/-- The orbit stays among the positions. -/
theorem pairOrbT_lt {r s : ℕ} (h : IsTorusPair r s) (k : ℕ) : pairOrbT r s k < pairStrands r s := by
  rw [← pairOrbSigma_iterate h]
  exact Fin.isLt _

/-- The orbit returns to `0` after `m` steps. -/
theorem pairOrbT_strands {r s : ℕ} (h : IsTorusPair r s) : pairOrbT r s (pairStrands r s) = 0 := by
  rw [← pairOrbT_mod h, Nat.mod_self]
  rfl

/-- The orbit is injective on `[0, m)`. -/
theorem pairOrbT_injOn {r s : ℕ} (h : IsTorusPair r s) {i j : ℕ} (hi : i < pairStrands r s)
    (hj : j < pairStrands r s) (he : pairOrbT r s i = pairOrbT r s j) : i = j := by
  rw [← pairOrbSigma_iterate h, ← pairOrbSigma_iterate h] at he
  have hp := pairOrbSigma_minimalPeriod h
  exact Function.iterate_injOn_Iio_minimalPeriod (f := pairOrbSigma r s)
    (x := ⟨0, Nat.succ_pos _⟩) (by rw [hp]; exact Set.mem_Iio.2 hi)
    (by rw [hp]; exact Set.mem_Iio.2 hj) (Fin.ext he)

/-- Every position is on the orbit of `0`. -/
private theorem pairOrbT_surj {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (ht : t < pairStrands r s) : ∃ k, k < pairStrands r s ∧ pairOrbT r s k = t := by
  obtain ⟨n, hn⟩ := connected_pairWhiteheadWord h ⟨0, Nat.succ_pos _⟩ ⟨t, ht⟩
  refine ⟨n % pairStrands r s, Nat.mod_lt _ (Nat.succ_pos _), ?_⟩
  rw [pairOrbT_mod h, ← pairOrbSigma_iterate h, Equiv.Perm.iterate_eq_pow, hn]

/-- The orbit index of a position. -/
theorem pairOrbIdx_spec {r s : ℕ} (h : IsTorusPair r s) {t : ℕ} (ht : t < pairStrands r s) :
    pairOrbIdx r s t < pairStrands r s ∧ pairOrbT r s (pairOrbIdx r s t) = t := by
  obtain ⟨k, hk, hkt⟩ := pairOrbT_surj h ht
  have hex : ∃ x ∈ List.range (pairStrands r s), decide (pairOrbT r s x = t) = true :=
    ⟨k, List.mem_range.2 hk, by simpa using hkt⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  rw [List.length_range] at hlt
  refine ⟨hlt, ?_⟩
  have hget := List.findIdx_getElem (w := by rw [List.length_range]; exact hlt)
  rw [List.getElem_range] at hget
  unfold pairOrbIdx
  simpa using hget

/-- A sum along the orbit of `0` is the sum over all positions. -/
theorem pairOrb_sum_orbit {r s : ℕ} (h : IsTorusPair r s) (F : ℕ → ℤ) :
    ∑ k ∈ Finset.range (pairStrands r s), F (pairOrbT r s k) =
      ∑ t ∈ Finset.range (pairStrands r s), F t := by
  have hinj : Function.Injective fun j : Fin (pairStrands r s) ↦
      (⟨pairOrbT r s j, pairOrbT_lt h j⟩ : Fin (pairStrands r s)) := fun i j hij ↦
    Fin.ext (pairOrbT_injOn h i.isLt j.isLt (congrArg Fin.val hij))
  have hbij := (Finite.injective_iff_bijective).1 hinj
  have e := Equiv.sum_comp (Equiv.ofBijective _ hbij) fun t : Fin (pairStrands r s) ↦ F t
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun t ↦ F t), ← e]
  rfl

end AJConjecture
