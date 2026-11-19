import Mathlib
import AJHandoff.TorusKnot.PairKRevSolveAnnulus
import AJFamily.Classical.SatelliteData

/-!
# The edge meridians of the reverse construction

`exists_pairRevEdge`: for `y` satisfying the torus relation and `a` with
`y_0 = compMer a (Λ⁻¹ a Λ)`, `Λ = (y_0 ⋯ y_(r-1))^s y_0^(-rs)`, there are a Hopf loop `H` and
bottom edge meridians `e_0 = a, e_1, …, e_(2c)` solving the loop equation of every block of
`pairBlocks r s` for the prescribed loops `pairRevLoop r s y H`
(`AJHandoff.TorusKnot.PairKRevSolveLoop`), read on the chamber products
`P(n) = e_(n-1) ⋯ e_0` corrected by the earlier prescribed loops (`gapPrefix`), as in
`loopAt_eq_of_prescribed`.

Proof from the annulus edge meridians `exists_pairRevEdge_annulus` (with `T = 2c - 1`,
`α = e_(T-s) y_(r-1)`, `β = e_T`): the top-right climb `C` reads `H β = e_(T-s) y_(r-1)`, which
defines `H = α β⁻¹`; the second Hopf letter reads `e_(2c) = H β`, which defines `e_(2c) = α`;
the first Hopf letter reads `H = R_0 β⁻¹ e_(2c)`, i.e. the clasp `R_0 = α β⁻¹ α⁻¹ β`, which is
`hmer` conjugated by `U` (`U⁻¹ R_0 U = y_0`, `α = U a U⁻¹`, `β = U (Λ⁻¹ a Λ) U⁻¹`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The loop of a valid block only reads the chamber products up to one above its gap. -/
private theorem loopPr_congr_hi {m : ℕ} (b : SBlock) (hb : b.Valid m) (P Q : ℕ → G)
    (hPQ : ∀ n, n ≤ b.hi + 1 → P n = Q n) : loopPr b P = loopPr b Q := by
  cases b with
  | band i j =>
    simp only [SBlock.Valid] at hb
    simp only [SBlock.hi] at hPQ
    simp only [loopPr, hPQ (j + 1) le_rfl, hPQ j (by omega), hPQ i (by omega),
      hPQ (i + 1) (by omega)]
  | neg i =>
    simp only [SBlock.hi] at hPQ
    simp only [loopPr, hPQ i (by omega), hPQ (i + 1) (by omega), hPQ (i + 2) (by omega)]

/-- Changing an edge meridian at level `N` does not change the chamber products up to `N`. -/
private theorem descProd_update_rv (e : ℕ → G) (N : ℕ) (x : G) (n : ℕ) (hn : n ≤ N) :
    descProd (fun k ↦ if k = N then x else e k) 0 n = descProd e 0 n := by
  simp only [descProd]
  refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
  have := List.mem_range.1 (List.mem_reverse.1 hi)
  simp only [Nat.zero_add, show i ≠ N by omega, ite_false]

/-! ### The corrections at the top-right climb and the Hopf letters -/

section Corrections

variable {r s : ℕ}

private theorem rvC_lev2c (h : IsTorusPair r s) (L : ℕ → G) :
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

private theorem rvC_levT (h : IsTorusPair r s) (L : ℕ → G) :
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

private theorem rvC_levTs1 (h : IsTorusPair r s) (L : ℕ → G) :
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

private theorem rvC_levTs (h : IsTorusPair r s) (L : ℕ → G) :
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

private theorem rvH1_levT (h : IsTorusPair r s) (L : ℕ → G) :
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

private theorem rvH1_high (h : IsTorusPair r s) (L : ℕ → G) (n : ℕ) (hn : 2 * pairC r s ≤ n) :
    gapPrefix ((pairBlocks r s).take (pairIdxH1 r s)) L n = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxH1, pairIdxB]; omega),
    gapRevProd_skipRv (pairGapFRv r s L n) 0 _ (Nat.zero_le _) fun q' h1 h2 ↦
      ite_eq_right (by have := hl q'; simp only [pairIdxH1, pairIdxB] at h2; omega),
    gapRevProd_zeroRv]

private theorem rvH2_levT (h : IsTorusPair r s) (L : ℕ → G) :
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

private theorem rvH2_lev2c (h : IsTorusPair r s) (L : ℕ → G) :
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

private theorem rvH2_high (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxH2 r s)) L (2 * pairC r s + 1) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxH2]; omega),
    gapRevProd_skipRv (pairGapFRv r s L _) 0 _ (Nat.zero_le _) fun q' h1 h2 ↦
      ite_eq_right (by have := hl q'; omega), gapRevProd_zeroRv]

/-- The two corrections of `C` in terms of `y`: `y_(r-1)` at `T - s + 1` and `1` at `T - s`. -/
private theorem rvC_values (h : IsTorusPair r s) (y : ℕ → G)
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
  · rw [rvC_levTs1 h, hRs _ _ (by omega) (by omega), hLb, hAf, hAB,
      show s - r + r = r + (s - r) by omega, pairRevPu_add_r, hPr]
    group
  · rw [rvC_levTs h, hRs _ _ (by omega) (by omega), hLb, hAf, hAB,
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
private theorem rvLoop_R0 (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    pairRevLoop r s y H (pairIdxB r s + 1) = y (r - 1) := by
  have := pairRevLoop_R h y H 0 (by have := h.2.1; omega)
  simp only [pairIdxR, ite_true] at this
  rw [this, pairRevRound_zero (by have := h.1; omega)]

end Corrections

/-- Edge meridians solving the loop equations of the prescribed loops. -/
theorem exists_pairRevEdge {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) (hmer : y 0 = compMer a ((pairRevLam r s y)⁻¹ * a * pairRevLam r s y)) :
    ∃ (H : G) (e : ℕ → G), e 0 = a ∧ ∀ q, q < 2 * pairC r s + 2 →
      pairRevLoop r s y H q = loopPr ((pairBlocks r s).getD q (SBlock.neg 0))
        (fun n ↦ gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s y H) n *
          descProd e 0 n) := by
  obtain ⟨e, U, he0, hU, hTs, hT, heq⟩ := exists_pairRevEdge_annulus h y hy a
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hA : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hB := pairRev_idxB h
  have hR0 : pairRevRound r y 0 = y (r - 1) := pairRevRound_zero (by omega) y
  have hLH : ∀ H, pairRevLoop r s y H (pairIdxB r s + 2) = H := fun H ↦ pairRevLoop_H1 h y H
  refine ⟨e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹,
    fun n ↦ if n = 2 * pairC r s then e (2 * pairC r s - 1 - s) * y (r - 1) else e n, ?_,
    fun q hq ↦ ?_⟩
  · simp only [show (0 : ℕ) ≠ 2 * pairC r s by omega, ite_false, he0]
  have hlt : ∀ n, n < 2 * pairC r s →
      (if n = 2 * pairC r s then e (2 * pairC r s - 1 - s) * y (r - 1) else e n) = e n :=
    fun n hn ↦ by simp only [show n ≠ 2 * pairC r s by omega, ite_false]
  by_cases hqC : q = pairIdxC r s
  · -- the top-right climb `C`: it defines `H`
    subst hqC
    have hblk : (pairBlocks r s).getD (pairIdxC r s) (SBlock.neg 0) =
        SBlock.band (2 * pairC r s - 1 - s) (2 * pairC r s - 1) := by
      rw [pairBlocks_getDRv h _ hq]
      exact pairBlkAt_reg9Rv hA (by simp only [pairIdxC, pairIdxB]; omega)
    obtain ⟨v1, v0⟩ := rvC_values h y hy
      (e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹)
    rw [pairRevLoop_C h, hblk, loopPr_band_edge, show 2 * pairC r s - 1 + 1 = 2 * pairC r s by
      omega, rvC_lev2c h, rvC_levT h, v1, v0, hLH, rvLoop_R0 h,
      hlt _ (by omega), hlt _ (by omega), hR0]
    group
  by_cases hqH1 : q = pairIdxH1 r s
  · -- the first Hopf letter: the clasp, from `hmer`
    subst hqH1
    have hblk : (pairBlocks r s).getD (pairIdxH1 r s) (SBlock.neg 0) =
        SBlock.neg (2 * pairC r s - 1) := by
      rw [pairBlocks_getDRv h _ hq]
      exact pairBlkAt_reg6Rv hA (by simp only [pairIdxH1, pairIdxB])
    rw [pairRevLoop_H1 h, hblk, loopPr_neg_edge, rvH1_levT h, rvH1_high h _ _ (by omega),
      rvH1_high h _ _ (by omega), rvLoop_R0 h, show 2 * pairC r s - 1 + 1 = 2 * pairC r s by
      omega, ite_eq_left rfl, hlt _ (by omega), hTs, hT]
    -- the clasp `y_(r-1) β⁻¹ α = α β⁻¹` is `hmer` conjugated by `U`
    have hy1 : y (r - 1) = U * y 0 * U⁻¹ := by rw [← hU]; group
    rw [hy1, hmer, compMer]
    group
  by_cases hqH2 : q = pairIdxH2 r s
  · -- the second Hopf letter: it defines `e_(2c)`
    subst hqH2
    have hblk : (pairBlocks r s).getD (pairIdxH2 r s) (SBlock.neg 0) =
        SBlock.neg (2 * pairC r s - 1) := by
      rw [pairBlocks_getDRv h _ hq]
      exact pairBlkAt_reg11Rv hA (by simp only [pairIdxH2]; omega)
    have hLC : pairRevLoop r s y
        (e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹)
        (pairIdxB r s + s + 2) = (y (r - 1))⁻¹ := by
      rw [← hR0]
      exact pairRevLoop_C h _ _
    rw [pairRevLoop_H2 h, hblk, loopPr_neg_edge, rvH2_levT h,
      show 2 * pairC r s - 1 + 1 = 2 * pairC r s by omega, rvH2_lev2c h,
      show 2 * pairC r s - 1 + 2 = 2 * pairC r s + 1 by omega, rvH2_high h, hLC, rvLoop_R0 h,
      hLH, ite_eq_left rfl, hlt _ (by omega)]
    group
  · -- the annulus bands
    rw [heq _ q hq hqC hqH1 hqH2]
    have hmem : (pairBlocks r s).getD q (SBlock.neg 0) ∈ pairBlocks r s := by
      rw [List.getD_eq_getElem _ _ (by rw [length_pairBlocks_rev h]; omega)]
      exact List.getElem_mem _
    have hhi : ((pairBlocks r s).getD q (SBlock.neg 0)).hi + 1 ≤ 2 * pairC r s := by
      rw [pairBlocks_getDRv h q hq]
      have := pairBlk_lohiRv h q
      have h1 : q ≠ pairIdxB r s + 2 := hqH1
      have h2 : q ≠ 2 * pairC r s + 1 := hqH2
      simp only [pairIdxB] at h1
      omega
    refine loopPr_congr_hi _ (pairBlocks_valid h _ hmem) _ _ fun n hn ↦ ?_
    rw [descProd_update_rv e (2 * pairC r s) _ n (by omega)]

end AJConjecture
