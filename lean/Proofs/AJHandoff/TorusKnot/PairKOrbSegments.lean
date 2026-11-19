import Mathlib
import AJHandoff.TorusKnot.PairKOrbStrand
import AJHandoff.TorusKnot.PairKOrbChain
import AJHandoff.TorusKnot.PairKOrbSum
import AJHandoff.TorusKnot.PairKOrbSumVal

/-!
# The orbit segments in closed form (crux)

For a tuple `f` whose block loops `L = loopAt m (pairBlocks r s) f` satisfy the gap relations,
with `iT = pairOrbIdx r s T`, `iH = pairOrbIdx r s (pairOrbH1 r s)`, the bottom pieces
`Gg = pairOrbSeg f 0 iT`, `U = pairOrbSeg f (iH + 1) m` and the top piece
`M = H₂⁻¹ · pairOrbSeg f iT iH` satisfy, in the frame of `y_0`:

* `y_0 U y_0⁻¹ = K ^ W y_1 ^ N` with `y_0 = K ^ W y_1 K ^ (-W)` (some `W`, `N`);
* `y_0 (Gg U) y_0⁻¹ = K ^ s y_1 ^ (-rs)` and `y_0 (U Gg) y_0⁻¹ = K ^ s y_0 ^ (-rs)`;
* `y_0 M y_0⁻¹ = K ^ (-s) y_0 ^ (rs)`.

Route: on each piece the strands avoid `pairOrbH1` and, except at `iT`, `T` (`pairOrb_top_iff`,
`pairOrb_idx_order`, `pairOrbIdx_spec`), so `stLoop_pairBlocks_core`, `pairOrbConj_prod` and
`pairOrb_step` make every factor a pure step with labels `Y k = y_(ℓ(pairOrbT k))`; at `iT` the
`H₂⁻¹` of `M` cancels the `H₂` of `T`. `pairOrb_pure_prod` multiplies each piece, and
`pairOrb_pure_mul` joins `Gg` and `U` (both junction labels are `0`: `ℓ(T) = ℓ(2c) = 0`,
`pairOrbT (iH + 1) = 2c`, `pairOrbT m = 0` with `ℓ(0) = 1`). The exponent sums are
`pairOrb_sum_top`/`pairOrb_sum_bot` with `pairOrb_sum_top_val`/`pairOrb_sum_bot_val`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Strand loops along the orbit that avoid `T` are the core loops. -/
private theorem pairOrbSeg_eq_coreProd {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {a b : ℕ}
    (hT : ∀ k, a ≤ k → k < b → pairOrbT r s k ≠ pairTop r s) :
    pairOrbSeg r s f a b = ((List.range (b - a)).map fun k ↦
      pairOrbCore r s (loopAt (pairStrands r s) (pairBlocks r s) f)
        (pairOrbT r s (a + k))).prod := by
  unfold pairOrbSeg
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [stLoop_pairBlocks_core h f (pairOrbT_lt h _),
    ite_eq_right_iff.mpr (fun h' ↦ absurd h' (hT _ (by omega) (by omega))), one_mul]

/-- A product of core loops along the orbit avoiding `pairOrbH1` is a pure step. -/
private theorem pairOrb_coreProd_pure {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {a b : ℕ} (hab : a ≤ b)
    (hH : ∀ k, a ≤ k → k < b → pairOrbT r s k ≠ pairOrbH1 r s) :
    pairOrbConj r s L
        ((List.range (b - a)).map fun k ↦ pairOrbCore r s L (pairOrbT r s (a + k))).prod =
        pairOrbK r s L ^ (∑ k ∈ Finset.Ico a b, pairOrbW r s (pairOrbT r s k)) *
          pairOrbY r s L (pairOrbLab r s (pairOrbT r s b)) ^
            (∑ k ∈ Finset.Ico a b, pairOrbN r s (pairOrbT r s k)) ∧
      pairOrbY r s L (pairOrbLab r s (pairOrbT r s a)) =
        pairOrbK r s L ^ (∑ k ∈ Finset.Ico a b, pairOrbW r s (pairOrbT r s k)) *
          pairOrbY r s L (pairOrbLab r s (pairOrbT r s b)) *
          pairOrbK r s L ^ (-∑ k ∈ Finset.Ico a b, pairOrbW r s (pairOrbT r s k)) := by
  rw [pairOrbConj_prod, List.map_map]
  exact pairOrb_pure_prod (pairOrbK r s L)
    (fun k ↦ pairOrbConj r s L (pairOrbCore r s L (pairOrbT r s k)))
    (fun k ↦ pairOrbY r s L (pairOrbLab r s (pairOrbT r s k)))
    (fun k ↦ pairOrbW r s (pairOrbT r s k)) (fun k ↦ pairOrbN r s (pairOrbT r s k)) hab
    (fun k h1 h2 ↦ (pairOrb_step h hL k (hH k h1 h2)).1)
    (fun k h1 h2 ↦ (pairOrb_step h hL k (hH k h1 h2)).2)

/-- The labels at the ends of the orbit pieces. -/
private theorem pairOrb_seg_labs {r s : ℕ} (h : IsTorusPair r s) :
    pairOrbLab r s (pairOrbT r s 0) = 1 ∧ pairOrbLab r s (pairOrbT r s (pairStrands r s)) = 1 ∧
      pairOrbLab r s (pairOrbT r s (pairOrbIdx r s (pairTop r s))) = 0 ∧
      pairOrbLab r s (pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s))) = 0 ∧
      pairOrbLab r s (pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s) + 1)) = 0 := by
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hTm : pairTop r s < pairStrands r s := by simp only [pairTop, pairStrands]; omega
  have hHm : pairOrbH1 r s < pairStrands r s := by simp only [pairOrbH1, pairStrands]; omega
  have h0 : pairOrbT r s 0 = 0 := rfl
  rw [pairOrbT_strands h, (pairOrbIdx_spec h hTm).2, (pairOrbIdx_spec h hHm).2,
    (pairOrb_idx_order h).2.2.2, h0]
  have hTd : pairTop r s = 2 * pairC r s - 1 := rfl
  have hHd : pairOrbH1 r s = 2 * pairC r s - s - 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold pairOrbLab <;> split_ifs <;> omega

/-- The pieces `Gg` and `U` of the bottom of the orbit as pure steps. -/
private theorem pairOrb_bot_pieces {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G)
    (hL : PairGapRels r s (loopAt (pairStrands r s) (pairBlocks r s) f)) :
    let L := loopAt (pairStrands r s) (pairBlocks r s) f
    let W1 := ∑ k ∈ Finset.range (pairOrbIdx r s (pairTop r s)), pairOrbW r s (pairOrbT r s k)
    let N1 := ∑ k ∈ Finset.range (pairOrbIdx r s (pairTop r s)), pairOrbN r s (pairOrbT r s k)
    let W2 := ∑ k ∈ Finset.Ico (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s),
      pairOrbW r s (pairOrbT r s k)
    let N2 := ∑ k ∈ Finset.Ico (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s),
      pairOrbN r s (pairOrbT r s k)
    (pairOrbConj r s L (pairOrbSeg r s f 0 (pairOrbIdx r s (pairTop r s))) =
        pairOrbK r s L ^ W1 * pairOrbY r s L 0 ^ N1 ∧
      pairOrbY r s L 1 = pairOrbK r s L ^ W1 * pairOrbY r s L 0 * pairOrbK r s L ^ (-W1)) ∧
    (pairOrbConj r s L
          (pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) =
        pairOrbK r s L ^ W2 * pairOrbY r s L 1 ^ N2 ∧
      pairOrbY r s L 0 = pairOrbK r s L ^ W2 * pairOrbY r s L 1 * pairOrbK r s L ^ (-W2)) := by
  intro L W1 N1 W2 N2
  obtain ⟨l0, lm, lT, -, lH1⟩ := pairOrb_seg_labs h
  obtain ⟨-, hiTH, hiHm, -⟩ := pairOrb_idx_order h
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hTm : pairTop r s < pairStrands r s := by simp only [pairTop, pairStrands]; omega
  have hHm : pairOrbH1 r s < pairStrands r s := by simp only [pairOrbH1, pairStrands]; omega
  obtain ⟨hiT, hTs⟩ := pairOrbIdx_spec h hTm
  obtain ⟨hiH, hHs⟩ := pairOrbIdx_spec h hHm
  have neT : ∀ k, k < pairStrands r s → k ≠ pairOrbIdx r s (pairTop r s) →
      pairOrbT r s k ≠ pairTop r s := fun k hk hne he ↦
    hne (pairOrbT_injOn h hk hiT (he.trans hTs.symm))
  have neH : ∀ k, k < pairStrands r s → k ≠ pairOrbIdx r s (pairOrbH1 r s) →
      pairOrbT r s k ≠ pairOrbH1 r s := fun k hk hne he ↦
    hne (pairOrbT_injOn h hk hiH (he.trans hHs.symm))
  have hG := pairOrb_coreProd_pure h hL (Nat.zero_le (pairOrbIdx r s (pairTop r s)))
    (fun k _ hk ↦ neH k (by omega) (by omega))
  have hU := pairOrb_coreProd_pure h hL (le_of_lt hiHm)
    (fun k hk _ ↦ neH k (by omega) (by omega))
  rw [l0, lT] at hG
  rw [lm, lH1] at hU
  rw [← Finset.range_eq_Ico] at hG
  rw [pairOrbSeg_eq_coreProd h f (fun k _ hk ↦ neT k (by omega) (by omega)),
    pairOrbSeg_eq_coreProd h f (fun k hk _ ↦ neT k (by omega) (by omega))]
  exact ⟨by exact_mod_cast hG, by exact_mod_cast hU⟩

/-- The bottom piece from `2c` to `0` carries `y_1` to `y_0`. -/
theorem pairOrb_seg_U {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (hL : PairGapRels r s (loopAt (pairStrands r s) (pairBlocks r s) f)) :
    ∃ W N : ℤ,
      pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
          (pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) =
        pairOrbK r s (loopAt (pairStrands r s) (pairBlocks r s) f) ^ W *
          pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) f) 1 ^ N ∧
      pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) f) 0 =
        pairOrbK r s (loopAt (pairStrands r s) (pairBlocks r s) f) ^ W *
          pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) f) 1 *
          pairOrbK r s (loopAt (pairStrands r s) (pairBlocks r s) f) ^ (-W) := by
  obtain ⟨-, hU⟩ := pairOrb_bot_pieces h f hL
  exact ⟨_, _, hU⟩

/-- The bottom of the orbit, from `0` around to `0`. -/
theorem pairOrb_seg_GU {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (hL : PairGapRels r s (loopAt (pairStrands r s) (pairBlocks r s) f)) :
    pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
        (pairOrbSeg r s f 0 (pairOrbIdx r s (pairTop r s)) *
          pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) =
      pairOrbK r s (loopAt (pairStrands r s) (pairBlocks r s) f) ^ (s : ℤ) *
        pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) f) 1 ^ (-((r * s : ℕ) : ℤ)) := by
  obtain ⟨⟨hG, -⟩, ⟨hU, hy0⟩⟩ := pairOrb_bot_pieces h f hL
  have hc : pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
      (pairOrbSeg r s f 0 (pairOrbIdx r s (pairTop r s)) *
        pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) =
      pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
          (pairOrbSeg r s f 0 (pairOrbIdx r s (pairTop r s))) *
        pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
          (pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) := by
    unfold pairOrbConj
    group
  rw [hc, hG, hU, pairOrb_pure_mul _ _ _ _ _ _ _ hy0, pairOrb_sum_bot h, pairOrb_sum_bot h,
    (pairOrb_sum_bot_val h).1, (pairOrb_sum_bot_val h).2]

/-- The bottom of the orbit, from `2c` around to `T`. -/
theorem pairOrb_seg_UG {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (hL : PairGapRels r s (loopAt (pairStrands r s) (pairBlocks r s) f)) :
    pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
        (pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) *
          pairOrbSeg r s f 0 (pairOrbIdx r s (pairTop r s))) =
      pairOrbK r s (loopAt (pairStrands r s) (pairBlocks r s) f) ^ (s : ℤ) *
        pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) f) 0 ^ (-((r * s : ℕ) : ℤ)) := by
  obtain ⟨⟨hG, hy1⟩, ⟨hU, -⟩⟩ := pairOrb_bot_pieces h f hL
  have hc : pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
      (pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) *
        pairOrbSeg r s f 0 (pairOrbIdx r s (pairTop r s))) =
      pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
          (pairOrbSeg r s f (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) *
        pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
          (pairOrbSeg r s f 0 (pairOrbIdx r s (pairTop r s))) := by
    unfold pairOrbConj
    group
  rw [hc, hG, hU, pairOrb_pure_mul _ _ _ _ _ _ _ hy1,
    add_comm (∑ k ∈ Finset.Ico _ _, pairOrbW r s _),
    add_comm (∑ k ∈ Finset.Ico _ _, pairOrbN r s _),
    pairOrb_sum_bot h, pairOrb_sum_bot h, (pairOrb_sum_bot_val h).1, (pairOrb_sum_bot_val h).2]

/-- The top of the orbit, from `T` (without `H₂`) to the strand before `pairOrbH1`. -/
theorem pairOrb_seg_M {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (hL : PairGapRels r s (loopAt (pairStrands r s) (pairBlocks r s) f)) :
    pairOrbConj r s (loopAt (pairStrands r s) (pairBlocks r s) f)
        ((loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s))⁻¹ *
          pairOrbSeg r s f (pairOrbIdx r s (pairTop r s)) (pairOrbIdx r s (pairOrbH1 r s))) =
      pairOrbK r s (loopAt (pairStrands r s) (pairBlocks r s) f) ^ (-(s : ℤ)) *
        pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) f) 0 ^ ((r * s : ℕ) : ℤ) := by
  obtain ⟨-, -, -, lH1, -⟩ := pairOrb_seg_labs h
  obtain ⟨-, hiTH, hiHm, -⟩ := pairOrb_idx_order h
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hTm : pairTop r s < pairStrands r s := by simp only [pairTop, pairStrands]; omega
  have hHm : pairOrbH1 r s < pairStrands r s := by simp only [pairOrbH1, pairStrands]; omega
  obtain ⟨hiT, hTs⟩ := pairOrbIdx_spec h hTm
  obtain ⟨hiH, hHs⟩ := pairOrbIdx_spec h hHm
  have neT : ∀ k, k < pairStrands r s → k ≠ pairOrbIdx r s (pairTop r s) →
      pairOrbT r s k ≠ pairTop r s := fun k hk hne he ↦
    hne (pairOrbT_injOn h hk hiT (he.trans hTs.symm))
  have neH : ∀ k, k < pairStrands r s → k ≠ pairOrbIdx r s (pairOrbH1 r s) →
      pairOrbT r s k ≠ pairOrbH1 r s := fun k hk hne he ↦
    hne (pairOrbT_injOn h hk hiH (he.trans hHs.symm))
  set L := loopAt (pairStrands r s) (pairBlocks r s) f with hLd
  set iT := pairOrbIdx r s (pairTop r s) with hiTd
  set iH := pairOrbIdx r s (pairOrbH1 r s) with hiHd
  have hS := pairOrb_coreProd_pure h hL (show iT + 1 ≤ iH by omega)
    (fun k hk hk' ↦ neH k (by omega) (by omega))
  have hstep := pairOrb_step h hL iT (neH iT hiT (by omega))
  rw [lH1] at hS
  have hsplit : (L (pairIdxH2 r s))⁻¹ * pairOrbSeg r s f iT iH =
      pairOrbCore r s L (pairOrbT r s iT) *
        ((List.range (iH - (iT + 1))).map fun k ↦
          pairOrbCore r s L (pairOrbT r s (iT + 1 + k))).prod := by
    rw [pairOrbSeg_split r s f (Nat.le_succ iT) (show iT + 1 ≤ iH by omega), pairOrbSeg_one,
      pairOrbSeg_eq_coreProd h f (fun k hk hk' ↦ neT k (by omega) (by omega)),
      stLoop_pairBlocks_core h f (pairOrbT_lt h _),
      ite_eq_left_iff.mpr (fun h' ↦ absurd hTs h'), mul_assoc, inv_mul_cancel_left]
  have hc : ∀ x y : G, pairOrbConj r s L (x * y) = pairOrbConj r s L x * pairOrbConj r s L y := by
    intro x y
    unfold pairOrbConj
    group
  rw [hsplit, hc, hstep.1, hS.1, pairOrb_pure_mul _ _ _ _ _ _ _ hS.2,
    ← Finset.sum_eq_sum_Ico_succ_bot hiTH (fun k ↦ pairOrbW r s (pairOrbT r s k)),
    ← Finset.sum_eq_sum_Ico_succ_bot hiTH (fun k ↦ pairOrbN r s (pairOrbT r s k)),
    pairOrb_sum_top h, pairOrb_sum_top h, (pairOrb_sum_top_val h).1, (pairOrb_sum_top_val h).2]
  rfl

end AJConjecture
