import Mathlib
import AJHandoff.TorusKnot.PairKOrbCycle

/-!
# The order of the orbit of `0` (crux)

With `iT = pairOrbIdx r s T` and `iH = pairOrbIdx r s (pairOrbH1 r s)`: the `k`-th strand of the
orbit lies in the top block exactly for `iT ≤ k ≤ iH`, and the strand after `pairOrbH1` is `2c`.
So the orbit runs `0 → (bottom block) → T → (top block) → pairOrbH1 → 2c → (bottom block) → 0`,
without enumerating it.

Route: `0` and `2c` are not in the top block, `T` and `pairOrbH1` are (`pairOrbTop_basic`).
Let `k₀` be the least index with the strand in the top block (`Nat.find`; it exists since
`T = pairOrbT iT`); `k₀ > 0`, and the strand before it is outside and is sent inside, so
`pairOrbT k₀ = T` (`pairOrbPerm_enter`, `stPerm_pairBlocks_orb`), hence `k₀ = iT`
(`pairOrbT_injOn`). From `iT` on the orbit stays in the top block until `pairOrbH1`
(`pairOrbPerm_top`); it must leave it (it returns to `0`, `pairOrbT_strands`), and the only exit
is `pairOrbH1 ↦ 2c` (`pairOrbPerm_H1`), so the first exit index is `iH`. After `iH` it cannot
re-enter: the only entry is `T`, already visited at `iT < iH` (injectivity).
Checked by `pairOrbCheckOrder`.
-/

namespace AJConjecture

/-- One step along the orbit is `pairOrbPerm`. -/
private theorem pairOrbT_succ_perm {r s : ℕ} (h : IsTorusPair r s) (k : ℕ) :
    pairOrbT r s (k + 1) = pairOrbPerm r s (pairOrbT r s k) := by
  rw [pairOrbT_succ, stPerm_pairBlocks_orb h (pairOrbT_lt h k)]

/-- The only way into the top block is through `T`, at the index `iT`. -/
private theorem pairOrb_entry {r s : ℕ} (h : IsTorusPair r s) {k : ℕ}
    (hout : ¬ PairOrbTop r s (pairOrbT r s k)) (hin : PairOrbTop r s (pairOrbT r s (k + 1)))
    (hk : k + 1 < pairStrands r s) : k + 1 = pairOrbIdx r s (pairTop r s) := by
  have hT := pairOrbIdx_spec h (show pairTop r s < pairStrands r s by
    unfold pairTop pairStrands; omega)
  rw [pairOrbT_succ_perm h] at hin
  have he := pairOrbPerm_enter h (pairOrbT_lt h k) hout hin
  rw [← pairOrbT_succ_perm h, ← hT.2] at he
  exact pairOrbT_injOn h hk hT.1 he

/-- Before `iT` the orbit is outside the top block. -/
private theorem pairOrb_before {r s : ℕ} (h : IsTorusPair r s) :
    ∀ k, k < pairOrbIdx r s (pairTop r s) → ¬ PairOrbTop r s (pairOrbT r s k) := by
  have hT := pairOrbIdx_spec h (show pairTop r s < pairStrands r s by
    unfold pairTop pairStrands; omega)
  intro k
  induction k with
  | zero => exact fun _ ↦ (pairOrbTop_basic h).2.2.1
  | succ k ih =>
    intro hk hin
    exact absurd (pairOrb_entry h (ih (by omega)) hin (by omega)) (by omega)

/-- From `iT` on, the orbit stays in the top block until it meets `pairOrbH1`. -/
private theorem pairOrb_stay {r s : ℕ} (h : IsTorusPair r s) :
    ∀ n, (∀ j, pairOrbIdx r s (pairTop r s) ≤ j → j < pairOrbIdx r s (pairTop r s) + n →
      pairOrbT r s j ≠ pairOrbH1 r s) →
      PairOrbTop r s (pairOrbT r s (pairOrbIdx r s (pairTop r s) + n)) := by
  have hT := pairOrbIdx_spec h (show pairTop r s < pairStrands r s by
    unfold pairTop pairStrands; omega)
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.add_zero, hT.2]
    exact (pairOrbTop_basic h).1
  | succ n ih =>
    intro hne
    rw [← Nat.add_assoc, pairOrbT_succ_perm h]
    exact pairOrbPerm_top h (ih fun j h1 h2 ↦ hne j h1 (by omega)) (hne _ le_self_add (by omega))

/-- The order of the indices of `T`, `pairOrbH1` and `2c`. -/
private theorem pairOrb_order_aux {r s : ℕ} (h : IsTorusPair r s) :
    pairOrbIdx r s (pairTop r s) < pairOrbIdx r s (pairOrbH1 r s) ∧
      pairOrbIdx r s (pairOrbH1 r s) + 1 < pairStrands r s ∧
      pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s) + 1) = 2 * pairC r s := by
  obtain ⟨hTt, hHt, h0, h2c, hHT, h2cm⟩ := pairOrbTop_basic h
  have hT := pairOrbIdx_spec h (show pairTop r s < pairStrands r s by
    unfold pairTop pairStrands; omega)
  have hH := pairOrbIdx_spec h (show pairOrbH1 r s < pairStrands r s by
    unfold pairOrbH1 pairStrands; omega)
  have hle : pairOrbIdx r s (pairTop r s) ≤ pairOrbIdx r s (pairOrbH1 r s) := by
    by_contra hlt
    exact pairOrb_before h (pairOrbIdx r s (pairOrbH1 r s)) (by omega) (by rw [hH.2]; exact hHt)
  have hne : pairOrbIdx r s (pairTop r s) ≠ pairOrbIdx r s (pairOrbH1 r s) := fun he ↦
    hHT (by rw [← hH.2, ← he, hT.2])
  have h2 : pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s) + 1) = 2 * pairC r s := by
    rw [pairOrbT_succ_perm h, hH.2, pairOrbPerm_H1 h]
  refine ⟨by omega, ?_, h2⟩
  rcases Nat.lt_or_ge (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) with hlt | hge
  · exact hlt
  · have he : pairOrbIdx r s (pairOrbH1 r s) + 1 = pairStrands r s := by omega
    rw [he, pairOrbT_strands h] at h2
    have := pairOrb_arith h
    omega

/-- After `pairOrbH1` the orbit is outside the top block. -/
private theorem pairOrb_after {r s : ℕ} (h : IsTorusPair r s) :
    ∀ n, pairOrbIdx r s (pairOrbH1 r s) + 1 + n < pairStrands r s →
      ¬ PairOrbTop r s (pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s) + 1 + n)) := by
  obtain ⟨hlt, -, h2⟩ := pairOrb_order_aux h
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.add_zero, h2]
    exact (pairOrbTop_basic h).2.2.2.1
  | succ n ih =>
    intro hk hin
    rw [← Nat.add_assoc] at hin hk
    exact absurd (pairOrb_entry h (ih (by omega)) hin hk) (by omega)

/-- The orbit is in the top block exactly between the indices of `T` and of `pairOrbH1`. -/
theorem pairOrb_top_iff {r s : ℕ} (h : IsTorusPair r s) {k : ℕ} (hk : k < pairStrands r s) :
    PairOrbTop r s (pairOrbT r s k) ↔
      pairOrbIdx r s (pairTop r s) ≤ k ∧ k ≤ pairOrbIdx r s (pairOrbH1 r s) := by
  have hH := pairOrbIdx_spec h (show pairOrbH1 r s < pairStrands r s by
    unfold pairOrbH1 pairStrands; omega)
  constructor
  · intro hin
    refine ⟨?_, ?_⟩
    · by_contra hlt
      exact pairOrb_before h k (by omega) hin
    · by_contra hlt
      have := pairOrb_after h (k - (pairOrbIdx r s (pairOrbH1 r s) + 1)) (by omega)
      rw [show pairOrbIdx r s (pairOrbH1 r s) + 1 + (k - (pairOrbIdx r s (pairOrbH1 r s) + 1)) =
        k by omega] at this
      exact this hin
  · rintro ⟨h1, h2⟩
    have := pairOrb_stay h (k - pairOrbIdx r s (pairTop r s)) fun j hj1 hj2 he ↦ by
      rw [← hH.2] at he
      have := pairOrbT_injOn h (by omega) hH.1 he
      omega
    rwa [show pairOrbIdx r s (pairTop r s) + (k - pairOrbIdx r s (pairTop r s)) = k by
      omega] at this

/-- `T` comes before `pairOrbH1` on the orbit, and `pairOrbH1` is followed by `2c`. -/
theorem pairOrb_idx_order {r s : ℕ} (h : IsTorusPair r s) :
    0 < pairOrbIdx r s (pairTop r s) ∧
      pairOrbIdx r s (pairTop r s) < pairOrbIdx r s (pairOrbH1 r s) ∧
      pairOrbIdx r s (pairOrbH1 r s) + 1 < pairStrands r s ∧
      pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s) + 1) = 2 * pairC r s := by
  have hT := pairOrbIdx_spec h (show pairTop r s < pairStrands r s by
    unfold pairTop pairStrands; omega)
  refine ⟨?_, pairOrb_order_aux h⟩
  rcases Nat.eq_zero_or_pos (pairOrbIdx r s (pairTop r s)) with h0 | h0
  · have e := hT.2
    rw [h0, show pairOrbT r s 0 = 0 from rfl] at e
    exact absurd (by rw [e]; exact (pairOrbTop_basic h).1) (pairOrbTop_basic h).2.2.1
  · exact h0

end AJConjecture
