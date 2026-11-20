import Mathlib
import AJHandoff.TorusKnot.PairKRevSolveLoop
import AJHandoff.TorusKnot.PairKRevGapConv
import AJTwist.Classical.TwCBlocks
import AJTwist.Classical.TwCGapForward

/-!
# The gap products below the top-right climb and the two Hopf letters (PpA)

The three blocks of `pairBlocks r s` that close the clasp are the top-right climb
`C = b(T - s, T)` (`T = 2c - 1`, position `pairIdxC r s`) and the two Hopf letters on the levels
`T, T + 1` (positions `pairIdxH1 r s`, `pairIdxH2 r s`). Their loop equations read the gap
products of the earlier prescribed loops (`gapPrefix`) at a few levels. For the prescribed loops
`pairRevLoop r s y H` of a tuple `y` with the torus relation these values are:

* below `C` (`ppa_gapPrefix_at_C`): `H` at the level `2c`, `y_(r-1)` at the levels `T` and
  `T - s + 1`, and `1` at the level `T - s`;
* below the first Hopf letter (`ppa_gapPrefix_at_H1`): `y_(r-1)` at the level `T` and `1` at
  every level `≥ 2c`;
* below the second Hopf letter (`ppa_gapPrefix_at_H2`): `1` at the level `T`, `H` at the level
  `2c` and `1` at the level `2c + 1`.

These are the private lemmas `rvC_lev2c`, `rvC_levT`, `rvC_values`, `rvH1_levT`, `rvH1_high`,
`rvH2_levT`, `rvH2_lev2c`, `rvH2_high` of `AJHandoff.TorusKnot.PairKRevSolveEdge`, restated (with
the loops evaluated: `pairRevLoop_H1`, `pairRevLoop_C`, `pairRevLoop_R` at `t = 0`,
`pairRevRound_zero`) so that both clasp signs can use them; the proofs there
(`gapPrefix_take_pairBlocks`, `gapRevProd_pair_peelRv`, `pairBlk_lohiRv`) carry over verbatim.

`ppa_gapPrefix_take_twcBase`: the list `twcBase r s σ` with Hopf letters of the other sign has
the same gap intervals, hence the same gap products of prefixes (as the private
`gapPrefix_map_twClaspBlock_twCGapForward` of `AJTwist.Classical.TwCGapForward`:
`List.map_take`, and `twClaspBlock σ` keeps `lo` and `hi`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

section Corrections

variable {r s : ℕ}

/-- The gap product below `C` at the level `2c`. -/
private theorem rvC_lev2c_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxC r s)) L (2 * pairC r s) =
      L (pairIdxB r s + 2) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxC, pairIdxB]; omega)]
  simp only [pairIdxC, pairIdxB]
  rw [← hb, gapRevProd_pair_peelRv r s L (2 * pairC r s) (b + 2) 1 (b + s + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s) 0 0 (b + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, descProd_zero_gapRv, descProd_one_gapRv, mul_one, mul_one]

/-- The gap product below `C` at the level `T`. -/
private theorem rvC_levT_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxC r s)) L (2 * pairC r s - 1) =
      L (pairIdxB r s + 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxC, pairIdxB]; omega)]
  simp only [pairIdxC, pairIdxB]
  rw [← hb, gapRevProd_pair_peelRv r s L (2 * pairC r s - 1) (b + 1) 1 (b + s + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1) 0 0 (b + 1) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, descProd_zero_gapRv, descProd_one_gapRv, mul_one, mul_one]

/-- The gap product below `C` at the level `T - s + 1`. -/
private theorem rvC_levTs1_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxC r s)) L (2 * pairC r s - 1 - s + 1) =
      descProd L (pairIdxB r s + 2 + (s - r)) r *
        (L (pairIdxB r s) * descProd L 0 (r - 2)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxC, pairIdxB]; omega)]
  simp only [pairIdxC, pairIdxB]
  rw [← hb, gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - s + 1) (b + 2 + (s - r)) r
      (b + s + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - s + 1) b 1 (b + 2 + (s - r)) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - s + 1) 0 (r - 2) b (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv]

/-- The gap product below `C` at the level `T - s`. -/
private theorem rvC_levTs_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxC r s)) L (2 * pairC r s - 1 - s) =
      descProd L (pairIdxB r s + 2 + (s + 1 - r)) (r - 1) *
        (L (pairIdxB r s) * descProd L 0 (r - 2)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxC, pairIdxB]; omega)]
  simp only [pairIdxC, pairIdxB]
  rw [← hb, gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - s) (b + 2 + (s + 1 - r)) (r - 1)
      (b + s + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - s) b 1 (b + 2 + (s + 1 - r)) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - s) 0 (r - 2) b (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv]

/-- The gap product below the first Hopf letter at the level `T`. -/
private theorem rvH1_levT_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxH1 r s)) L (2 * pairC r s - 1) =
      L (pairIdxB r s + 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxH1, pairIdxB]; omega)]
  simp only [pairIdxH1, pairIdxB]
  rw [← hb, gapRevProd_pair_peelRv r s L (2 * pairC r s - 1) (b + 1) 1 (b + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1) 0 0 (b + 1) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, descProd_zero_gapRv, descProd_one_gapRv, mul_one, mul_one]

/-- The gap products below the first Hopf letter at the levels `≥ 2c`. -/
private theorem rvH1_high_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) (n : ℕ)
    (hn : 2 * pairC r s ≤ n) :
    gapPrefix ((pairBlocks r s).take (pairIdxH1 r s)) L n = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxH1, pairIdxB]; omega),
    gapRevProd_skipRv (pairGapFRv r s L n) 0 _ (Nat.zero_le _) fun q' h1 h2 ↦
      ite_eq_right (by have := hl q'; simp only [pairIdxH1, pairIdxB] at h2; omega),
    gapRevProd_zeroRv]

/-- The gap product below the second Hopf letter at the level `T`. -/
private theorem rvH2_levT_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxH2 r s)) L (2 * pairC r s - 1) =
      L (pairIdxB r s + s + 2) * L (pairIdxB r s + 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxH2]; omega)]
  simp only [pairIdxH2, pairIdxB]
  rw [← hb, gapRevProd_pair_peelRv r s L (2 * pairC r s - 1) (b + s + 2) 1 (2 * pairC r s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1) (b + 1) 1 (b + s + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1) 0 0 (b + 1) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, descProd_zero_gapRv, descProd_one_gapRv, descProd_one_gapRv,
    mul_one, mul_one]

/-- The gap product below the second Hopf letter at the level `2c`. -/
private theorem rvH2_lev2c_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxH2 r s)) L (2 * pairC r s) =
      L (pairIdxB r s + 2) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxH2]; omega)]
  simp only [pairIdxH2, pairIdxB]
  rw [← hb, gapRevProd_pair_peelRv r s L (2 * pairC r s) (b + 2) 1 (2 * pairC r s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s) 0 0 (b + 2) (by omega)
      (fun q h1 h2 ↦ by have := hl q; omega) (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, descProd_zero_gapRv, descProd_one_gapRv, mul_one, mul_one]

/-- The gap product below the second Hopf letter at the level `2c + 1`. -/
private theorem rvH2_high_ppaClaspGap (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxH2 r s)) L (2 * pairC r s + 1) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxH2]; omega),
    gapRevProd_skipRv (pairGapFRv r s L _) 0 _ (Nat.zero_le _) fun q' h1 h2 ↦
      ite_eq_right (by have := hl q'; omega), gapRevProd_zeroRv]

/-- The two corrections of `C` in terms of `y`: `y_(r-1)` at `T - s + 1` and `1` at `T - s`. -/
private theorem rvC_values_ppaClaspGap (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) :
    gapPrefix ((pairBlocks r s).take (pairIdxC r s)) (pairRevLoop r s y H)
        (2 * pairC r s - 1 - s + 1) = y (r - 1) ∧
      gapPrefix ((pairBlocks r s).take (pairIdxC r s)) (pairRevLoop r s y H)
        (2 * pairC r s - 1 - s) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hAf := pairRevLoop_Aprod (s := s) y H (r - 2) le_rfl
  have hLb := pairRevLoop_B h y H
  have hRs : ∀ a' n, 1 ≤ a' → a' + n ≤ s →
      descProd (pairRevLoop r s y H) (pairIdxB r s + 2 + a') n =
        pairRevPu r y (a' + n) * (pairRevPu r y a')⁻¹ := by
    intro a' n ha' han
    rw [← pairRevLoop_Rprod h y H a' n han, descProd_round_shiftRv r s _ a' n ha']
    simp only [pairIdxR, show a' ≠ 0 by omega, ite_false]
  have hPr : pairRevPu r y r = y (r - 1) * pairRevAsc y 0 (r - 1) := by
    rw [show r = r - 1 + 1 by omega, pairRevPu_succ_low (by omega) y _ (by omega)]
    simp
  have hAB : (y (r - 2))⁻¹ * (pairRevAsc y 0 (r - 2))⁻¹ = (pairRevAsc y 0 (r - 1))⁻¹ := by
    rw [show r - 1 = r - 2 + 1 by omega, pairRevAsc_succ, mul_inv_rev, Nat.zero_add]
  constructor
  · rw [rvC_levTs1_ppaClaspGap h, hRs _ _ (by omega) (by omega), hLb, hAf, hAB,
      show s - r + r = r + (s - r) by omega, pairRevPu_add_r, hPr]
    group
  · rw [rvC_levTs_ppaClaspGap h, hRs _ _ (by omega) (by omega), hLb, hAf, hAB,
      show s + 1 - r + (r - 1) = s by omega, show s + 1 - r = s - (r - 1) by omega,
      pairRevPu_climb (by omega) (by omega) y hy _ (by omega) (by omega)]
    have hW : pairRevAsc (fun i ↦ y ((i + r - 1) % r)) (r - (r - 1)) (r - 1) =
        pairRevAsc y 0 (r - 1) := by
      refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
      have := List.mem_range.1 hi
      dsimp only
      rw [show r - (r - 1) + i + r - 1 = i + r by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega), Nat.zero_add]
    rw [hW, mul_inv_cancel]

/-- The loops of `R_0` and `C` at their positions. -/
private theorem rvLoop_R0_ppaClaspGap (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    pairRevLoop r s y H (pairIdxB r s + 1) = y (r - 1) := by
  have := pairRevLoop_R h y H 0 (by have := h.2.1; omega)
  simp only [pairIdxR, ite_true] at this
  rw [this, pairRevRound_zero (by have := h.1; omega)]

end Corrections

/-- Changing the sign of the Hopf letters does not change the gap products. -/
private theorem gapPrefix_map_twClaspBlock_ppaClaspGap (σ : Bool) (bs : List SBlock)
    (L : ℕ → G) (n : ℕ) : gapPrefix (bs.map (twClaspBlock σ)) L n = gapPrefix bs L n := by
  induction bs generalizing L with
  | nil => rfl
  | cons b bs ih =>
    have hlo : (twClaspBlock σ b).lo = b.lo := by
      cases b with
      | band i j => rfl
      | neg i => cases σ <;> rfl
    have hhi : (twClaspBlock σ b).hi = b.hi := by
      cases b with
      | band i j => rfl
      | neg i => cases σ <;> rfl
    rw [List.map_cons, gapPrefix, gapPrefix, ih, hlo, hhi]

/-- The gap products below the top-right climb `C`. -/
theorem ppa_gapPrefix_at_C {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) :
    gapPrefix ((pairBlocks r s).take (pairIdxC r s)) (pairRevLoop r s y H) (2 * pairC r s) = H ∧
      gapPrefix ((pairBlocks r s).take (pairIdxC r s)) (pairRevLoop r s y H)
        (2 * pairC r s - 1) = y (r - 1) ∧
      gapPrefix ((pairBlocks r s).take (pairIdxC r s)) (pairRevLoop r s y H)
        (2 * pairC r s - 1 - s + 1) = y (r - 1) ∧
      gapPrefix ((pairBlocks r s).take (pairIdxC r s)) (pairRevLoop r s y H)
        (2 * pairC r s - 1 - s) = 1 := by
  obtain ⟨v1, v0⟩ := rvC_values_ppaClaspGap h y hy H
  exact ⟨(rvC_lev2c_ppaClaspGap h _).trans (pairRevLoop_H1 h y H),
    (rvC_levT_ppaClaspGap h _).trans (rvLoop_R0_ppaClaspGap h y H), v1, v0⟩

/-- The gap products below the first Hopf letter. -/
theorem ppa_gapPrefix_at_H1 {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    gapPrefix ((pairBlocks r s).take (pairIdxH1 r s)) (pairRevLoop r s y H)
        (2 * pairC r s - 1) = y (r - 1) ∧
      ∀ n, 2 * pairC r s ≤ n →
        gapPrefix ((pairBlocks r s).take (pairIdxH1 r s)) (pairRevLoop r s y H) n = 1 := by
  exact ⟨(rvH1_levT_ppaClaspGap h _).trans (rvLoop_R0_ppaClaspGap h y H),
    fun n hn ↦ rvH1_high_ppaClaspGap h _ n hn⟩

/-- The gap products below the second Hopf letter. -/
theorem ppa_gapPrefix_at_H2 {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    gapPrefix ((pairBlocks r s).take (pairIdxH2 r s)) (pairRevLoop r s y H)
        (2 * pairC r s - 1) = 1 ∧
      gapPrefix ((pairBlocks r s).take (pairIdxH2 r s)) (pairRevLoop r s y H)
        (2 * pairC r s) = H ∧
      gapPrefix ((pairBlocks r s).take (pairIdxH2 r s)) (pairRevLoop r s y H)
        (2 * pairC r s + 1) = 1 := by
  refine ⟨?_, (rvH2_lev2c_ppaClaspGap h _).trans (pairRevLoop_H1 h y H),
    rvH2_high_ppaClaspGap h _⟩
  have hLC : pairRevLoop r s y H (pairIdxB r s + s + 2) = (y (r - 1))⁻¹ := by
    rw [← pairRevRound_zero (by have := h.1; omega) y]
    exact pairRevLoop_C h y H
  rw [rvH2_levT_ppaClaspGap h, hLC, rvLoop_R0_ppaClaspGap h, inv_mul_cancel]

/-- The prefixes of the base list with Hopf letters of sign `σ` have the gap products of the
prefixes of `pairBlocks r s`. -/
theorem ppa_gapPrefix_take_twcBase (r s : ℕ) (σ : Bool) (q : ℕ) (L : ℕ → G) (n : ℕ) :
    gapPrefix ((twcBase r s σ).take q) L n = gapPrefix ((pairBlocks r s).take q) L n := by
  rw [twcBase, ← List.map_take, gapPrefix_map_twClaspBlock_ppaClaspGap]

end AJConjecture
