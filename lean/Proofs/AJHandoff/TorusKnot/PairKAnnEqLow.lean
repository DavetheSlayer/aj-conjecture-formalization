import Mathlib
import AJHandoff.TorusKnot.PairKAnnGapLow
import AJHandoff.TorusKnot.PairKAnnHurwitz

/-!
# The band equations of the left climbs, the runs and `B`

The loop equation of a band `b(i, j)` at position `q` (`PairAnnEq`, `loopPr_band_edge`) reads
`ℓ_q = G(j+1) e_j G(j)⁻¹ G(i) e_i⁻¹ G(i+1)⁻¹`, i.e. `e_j = X e_i Y` with
`X = G(j+1)⁻¹ ℓ_q G(i+1)` and `Y = G(i)⁻¹ G(j)`. With `A = (y_0 ⋯ y_(r-3))⁻¹`
(`pairRevLoop_Aprod`) and the corrections of `AJHandoff.TorusKnot.PairKAnnGapLow`:

* `A_k` (`q = k < r - 2`, band `b(k, 2c - 2 - k)`): all four corrections are
  `(y_0 ⋯ y_(k-1))⁻¹` (`pairAnnGap_A`), `ℓ = y_k⁻¹`, so `X = P(k) y_k⁻¹ P(k)⁻¹ = R'_k⁻¹`,
  `Y = 1` (`pairAnnHur_lt`);
* decreasing run `D_j`, `j ≥ 1` (`q = r - 2 + j`, band `b(n - 1, n)`, `n = r + E - 2 - j`):
  `G(n - 1) = G(n) = A`, `G(n + 1) = D_(j-1) A` (`pairAnnGap_run`, `pairAnnGap_runHit`), and all
  run loops agree (`pairRevLoop_run`), so `X = Y = 1`;
* `D_0` (`q = r - 2`): `G = A` at all levels, `ℓ = R_(s-1)⁻¹ = y_(r-2)⁻¹`
  (`pairRevRound_last`), so `X = A⁻¹ y_(r-2)⁻¹ A = R'_(r-2)⁻¹`, `Y = 1`;
* increasing run `U_j` and `B`: `G(i) = (run loop) A`, the other corrections are `A`, so
  `X = R'_(r-2)⁻¹` and `Y = R'_(r-2)`.

Route for each lemma: unfold `PairAnnEq`; rewrite the block (`pairBlocks_getDRv`,
`pairBlkAt_reg1Rv`/`reg2Rv`/`reg3Rv`/`reg4Rv`), `loopPr_band_edge`, the four corrections, the loop
(`pairRevLoop_A`, `pairRevLoop_run`, `pairRevLoop_B`), `pairRevLoop_Aprod`, the hypothesis `he`,
`pairAnnHur_lt` (and `pairRevRound_last`); close with `group`. The transitions were checked exactly
(`SCR/ANN/validate.py`, check `trans`).
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- The left climb `A_k`: `e(2c - 2 - k) = R'_k⁻¹ e_k`. -/
theorem pairAnnEq_A (h : IsTorusPair r s) (y : ℕ → G) (H : G) (e : ℕ → G) (k : ℕ)
    (hk : k < r - 2) (he : e (2 * pairC r s - 2 - k) = (pairAnnHur r y k)⁻¹ * e k) :
    PairAnnEq r s y H e k := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hblk : (pairBlocks r s).getD k (SBlock.neg 0) =
      SBlock.band k (2 * pairC r s - 2 - k) := by
    rw [pairBlocks_getDRv h _ (by omega)]
    exact pairBlkAt_reg1Rv hk
  have hG : ∀ n, k ≤ n → n ≤ 2 * pairC r s - 1 - k →
      gapPrefix ((pairBlocks r s).take k) (pairRevLoop r s y H) n = (pairRevAsc y 0 k)⁻¹ :=
    fun n h1 h2 ↦ by
      rw [pairAnnGap_A h _ k n (by omega) h1 h2, pairRevLoop_Aprod (s := s) y H k (by omega)]
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge, hG (2 * pairC r s - 2 - k + 1) (by omega) (by omega),
    hG (2 * pairC r s - 2 - k) (by omega) (by omega), hG k le_rfl (by omega),
    hG (k + 1) (by omega) (by omega), pairRevLoop_A (s := s) y H k hk, he,
    pairAnnHur_lt r y k (by omega)]
  group

/-- The decreasing run below its top: `e_n = e_(n-1)`. -/
theorem pairAnnEq_down (h : IsTorusPair r s) (y : ℕ → G) (H : G) (e : ℕ → G) (j : ℕ)
    (hj1 : 1 ≤ j) (hj2 : j < pairRunDown r s)
    (he : e (r + pairRunDown r s - 2 - j) = e (r + pairRunDown r s - 3 - j)) :
    PairAnnEq r s y H e (r - 2 + j) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hblk : (pairBlocks r s).getD (r - 2 + j) (SBlock.neg 0) =
      SBlock.band (r + pairRunDown r s - 3 - j) (r + pairRunDown r s - 2 - j) := by
    rw [pairBlocks_getDRv h _ (by omega), pairBlkRv, pairBlkAt_reg2Rv (by omega) (by omega)]
    congr 1 <;> omega
  have hrun : pairIdxRun r s (r + pairRunDown r s - 2 - j + 1) = r - 2 + j - 1 := by
    simp only [pairIdxRun]; split_ifs <;> omega
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge, show r + pairRunDown r s - 3 - j + 1 =
      r + pairRunDown r s - 2 - j by omega,
    pairAnnGap_runHit h _ _ _ (by omega) (by omega) (by rw [hrun]; omega) (by omega), hrun,
    pairAnnGap_run h _ _ (r + pairRunDown r s - 2 - j) (by omega) (by omega) (by omega)
      (by omega) (fun _ _ ↦ by simp only [pairIdxRun]; split_ifs <;> omega),
    pairAnnGap_run h _ _ (r + pairRunDown r s - 3 - j) (by omega) (by omega) (by omega)
      (by omega) (fun _ _ ↦ by simp only [pairIdxRun]; split_ifs <;> omega),
    pairRevLoop_run y H _ (by omega) (by omega), pairRevLoop_run y H (r - 2 + j - 1) (by omega)
      (by omega), he]
  group

/-- The top `D_0` of the decreasing run: `e(r + E - 2) = R'_(r-2)⁻¹ e(r + E - 3)`. -/
theorem pairAnnEq_downTop (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) (e : ℕ → G)
    (he : e (r + pairRunDown r s - 2) =
      (pairAnnHur r y (r - 2))⁻¹ * e (r + pairRunDown r s - 3)) :
    PairAnnEq r s y H e (r - 2) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hblk : (pairBlocks r s).getD (r - 2) (SBlock.neg 0) =
      SBlock.band (r + pairRunDown r s - 3) (r + pairRunDown r s - 2) := by
    rw [pairBlocks_getDRv h _ (by omega), pairBlkRv, pairBlkAt_reg2Rv (by omega) (by omega)]
    congr 1 <;> omega
  have hG : ∀ m, r - 2 ≤ m → m ≤ r + pairRunDown r s - 1 →
      gapPrefix ((pairBlocks r s).take (r - 2)) (pairRevLoop r s y H) m =
        (pairRevAsc y 0 (r - 2))⁻¹ := fun m h1 h2 ↦ by
    rw [pairAnnGap_run h _ _ m le_rfl (by omega) h1 (by omega)
      (fun _ _ ↦ by simp only [pairIdxRun]; split_ifs <;> omega),
      pairRevLoop_Aprod (s := s) y H _ le_rfl]
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge, show r + pairRunDown r s - 3 + 1 = r + pairRunDown r s - 2 by
      omega, hG (r + pairRunDown r s - 2 + 1) (by omega) (by omega),
    hG (r + pairRunDown r s - 2) (by omega) (by omega),
    hG (r + pairRunDown r s - 3) (by omega) (by omega),
    pairRevLoop_run y H _ le_rfl (by omega), pairRevRound_last h y hy, he,
    pairAnnHur_lt r y (r - 2) (by omega)]
  group

/-- The increasing run: `e(n + 1) = R'_(r-2)⁻¹ e_n R'_(r-2)`. -/
theorem pairAnnEq_up (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) (e : ℕ → G) (j : ℕ) (hj : j < pairRunUp r s)
    (he : e (r - 1 + pairRunDown r s + j) =
      (pairAnnHur r y (r - 2))⁻¹ * e (r - 2 + pairRunDown r s + j) * pairAnnHur r y (r - 2)) :
    PairAnnEq r s y H e (r - 2 + pairRunDown r s + j) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hblk : (pairBlocks r s).getD (r - 2 + pairRunDown r s + j) (SBlock.neg 0) =
      SBlock.band (r - 2 + pairRunDown r s + j) (r - 1 + pairRunDown r s + j) := by
    rw [pairBlocks_getDRv h _ (by omega), pairBlkRv, pairBlkAt_reg3Rv (by omega) (by omega)]
    congr 1; omega
  have hA := pairRevLoop_Aprod (s := s) y H (r - 2) le_rfl
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge,
    show r - 2 + pairRunDown r s + j + 1 = r - 1 + pairRunDown r s + j by omega,
    pairAnnGap_run h _ _ (r - 1 + pairRunDown r s + j + 1) (by omega) (by omega) (by omega)
      (by omega) (fun _ _ ↦ by simp only [pairIdxRun]; split_ifs <;> omega),
    pairAnnGap_run h _ _ (r - 1 + pairRunDown r s + j) (by omega) (by omega) (by omega)
      (by omega) (fun _ _ ↦ by simp only [pairIdxRun]; split_ifs <;> omega),
    pairAnnGap_runHit h _ _ (r - 2 + pairRunDown r s + j) (by omega) (by omega)
      (by simp only [pairIdxRun]; split_ifs <;> omega) (by omega),
    pairRevLoop_run y H _ (by omega) (by omega),
    pairRevLoop_run y H (pairIdxRun r s _) (by simp only [pairIdxRun]; split_ifs <;> omega)
      (by simp only [pairIdxRun]; split_ifs <;> omega),
    pairRevRound_last h y hy, hA, he, pairAnnHur_lt r y (r - 2) (by omega)]
  group

/-- The big climb `B`: `e(2c - r) = R'_(r-2)⁻¹ e(b₀) R'_(r-2)`. -/
theorem pairAnnEq_B (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) (e : ℕ → G)
    (he : e (2 * pairC r s - r) =
      (pairAnnHur r y (r - 2))⁻¹ * e (pairIdxB r s) * pairAnnHur r y (r - 2)) :
    PairAnnEq r s y H e (pairIdxB r s) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hAr : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hblk : (pairBlocks r s).getD (pairIdxB r s) (SBlock.neg 0) =
      SBlock.band (pairIdxB r s) (2 * pairC r s - r) := by
    rw [pairBlocks_getDRv h _ (by omega)]
    exact pairBlkAt_reg4Rv hAr rfl
  have hA := pairRevLoop_Aprod (s := s) y H (r - 2) le_rfl
  have hG : ∀ m, pairIdxB r s < m → m ≤ 2 * pairC r s + 1 - r →
      gapPrefix ((pairBlocks r s).take (pairIdxB r s)) (pairRevLoop r s y H) m =
        (pairRevAsc y 0 (r - 2))⁻¹ := fun m h1 h2 ↦ by
    rw [pairAnnGap_run h _ _ m (by omega) le_rfl (by omega) h2 (fun _ h3 ↦ by omega), hA]
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge, hG (2 * pairC r s - r + 1) (by omega) (by omega),
    hG (2 * pairC r s - r) (by omega) (by omega), hG (pairIdxB r s + 1) (by omega) (by omega),
    pairAnnGap_runHit h _ _ (pairIdxB r s) (by omega) le_rfl
      (by simp only [pairIdxRun]; split_ifs <;> omega) (by omega),
    pairRevLoop_run y H (pairIdxRun r s _) (by simp only [pairIdxRun]; split_ifs <;> omega)
      (by simp only [pairIdxRun]; split_ifs <;> omega),
    pairRevLoop_B h, pairRevRound_last h y hy, hA, he, pairAnnHur_lt r y (r - 2) (by omega)]
  group

end AJConjecture
