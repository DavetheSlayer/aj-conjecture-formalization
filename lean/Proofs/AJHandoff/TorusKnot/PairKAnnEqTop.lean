import Mathlib
import AJHandoff.TorusKnot.PairKAnnGapLow
import AJHandoff.TorusKnot.PairKAnnGapSuf
import AJHandoff.TorusKnot.PairKAnnHurwitz

/-!
# The band equations of the rounds and the right descents

As in `AJHandoff.TorusKnot.PairKAnnEqLow`, the equation at position `q` of a band `b(i, j)` is
`e_j = X e_i Y`, `X = G(j+1)⁻¹ ℓ_q G(i+1)`, `Y = G(i)⁻¹ G(j)`. With `BA = (y_0 ⋯ y_(r-2))⁻¹ =
P(r-1)⁻¹ = y_(r-1) Π⁻¹` (`pairRevLoop_B`, `pairRevLoop_Aprod`, `pairAnnPi_eq`), `R_0 = y_(r-1) =
R'_(s-1)` (`pairRevRound_zero`, `pairAnn_y_last`), `C = R_0⁻¹` (`pairRevLoop_C`) and
`R_τ = y_(r-1) R'_(τ-1) y_(r-1)⁻¹` (`pairRevRound_eq_hur`):

* `R_0` (`q = b₀ + 1`, band `b(T_r, T_0)`): `G(T_r) = G(T_(r-1)) = BA` (`pairAnnGap_BA`),
  `G(T_0) = G(2c) = 1` (`pairAnnGap_top0`); so `X = R_0 P(r-1)⁻¹ = R'_(s-1) Φ₀`,
  `Y = P(r-1) = Φ₀⁻¹` with `Φ₀ = R'_(s-1) Π⁻¹`;
* `R_τ`, `1 ≤ τ ≤ s - 2` (`q = b₀ + 2 + τ`, band `b(T_(r+τ), T_τ)`): `G(T_(r+τ)) =
  G(T_(r+τ-1)) = BA` (`pairAnnGap_BA`), `G(T_τ) = (C R_τ)⁻¹`, `G(T_(τ-1)) = C⁻¹`
  (`pairAnnGap_sufR`); so `X = R_0⁻¹ R_τ P(r-1)⁻¹ = R'_(τ-1) Π⁻¹ = Φ_τ`, `Y = Φ_τ⁻¹`;
* `R_(s-1)` (`q = b₀ + s + 1`, band `b(r - 2, T_(s-1))`): `G(r - 2) = A` (`pairAnnGap_bot`),
  `G(r - 1) = (run loop) A = P(r-1)⁻¹` (`pairAnnGap_runHit`, `pairRevRound_last`), `G(T_(s-1)) =
  (C R_(s-1))⁻¹`, `G(T_(s-2)) = C⁻¹` (`pairAnnGap_sufR`), `ℓ = R_(s-1) = y_(r-2)`; so
  `X = y_(r-1)⁻¹ P(r-2)⁻¹ = R'_(s-2) Π⁻¹ = Φ` and `Y = P(r-2) y_(r-2)⁻¹ y_(r-1) = Φ⁻¹ R'_(s-2)⁻¹`
  (`pairAnnHur_s_two`);
* `D'_j` (`q = b₀ + s + 3 + j`, band `b(k, b₀ + 1 + j)`, `k = r - 3 - j`): `G(k) = P(k)⁻¹`,
  `G(k + 1) = P(k+1)⁻¹` (`pairAnnGap_bot`), `G(b₀ + 1 + j) = P(k+1)⁻¹`, `G(b₀ + 2 + j) = P(k)⁻¹`
  (`pairAnnGap_sufD`, `pairRevLoop_Dprod`), `ℓ = y_k` (`pairRevLoop_Dp`); so `X = 1`,
  `Y = P(k) P(k+1)⁻¹ = R'_k⁻¹`.

The suffix corrections need the gap relations: `pairGapRels_pairRevLoop`. Route for each lemma as in
`PairKAnnEqLow` (blocks: `pairBlkAt_reg5Rv`, `reg7Rv`, `reg8Rv`, `reg10Rv`); the transitions were
checked exactly (`SCR/ANN/validate.py`, check `trans`).
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- `B A = (y_0 ⋯ y_(r-2))⁻¹`. -/
private theorem pairAnn_BA (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    pairRevLoop r s y H (pairIdxB r s) * descProd (pairRevLoop r s y H) 0 (r - 2) =
      (pairRevAsc y 0 (r - 1))⁻¹ := by
  have hr := h.1
  rw [pairRevLoop_B h, pairRevLoop_Aprod (s := s) y H (r - 2) le_rfl,
    show r - 1 = r - 2 + 1 by omega, pairRevAsc_succ, Nat.zero_add, mul_inv_rev]

/-- The round `R_0`: `e(T_0) = R'_(s-1) Φ₀ e(T_r) Φ₀⁻¹`, `Φ₀ = R'_(s-1) Π⁻¹`. -/
theorem pairAnnEq_R0 (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) (e : ℕ → G)
    (he : e (2 * pairC r s - 1) =
      pairAnnHur r y (s - 1) * (pairAnnHur r y (s - 1) * (pairAnnPi r y)⁻¹) *
        e (2 * pairC r s - 1 - r) * (pairAnnHur r y (s - 1) * (pairAnnPi r y)⁻¹)⁻¹) :
    PairAnnEq r s y H e (pairIdxB r s + 1) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hAr : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hblk : (pairBlocks r s).getD (pairIdxB r s + 1) (SBlock.neg 0) =
      SBlock.band (2 * pairC r s - 1 - r) (2 * pairC r s - 1) := by
    rw [pairBlocks_getDRv h _ (by omega)]
    exact pairBlkAt_reg5Rv hAr (by simp only [pairIdxB])
  obtain ⟨g0, g1⟩ := pairAnnGap_top0 h (pairRevLoop r s y H)
  have hloop : pairRevLoop r s y H (pairIdxB r s + 1) = y (r - 1) := by
    have := pairRevLoop_R h y H 0 (by omega)
    simp only [pairIdxR, ite_true] at this
    rw [this, pairRevRound_zero (by omega)]
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge, show 2 * pairC r s - 1 + 1 = 2 * pairC r s by omega, g1, g0,
    show 2 * pairC r s - 1 - r + 1 = 2 * pairC r s - 1 - (r - 1) by omega,
    pairAnnGap_BA h _ _ r (by omega) (by omega) (by omega)
      (by simp only [pairIdxR]; split_ifs <;> omega),
    pairAnnGap_BA h _ _ (r - 1) le_rfl (by omega) (by omega)
      (by simp only [pairIdxR]; split_ifs <;> omega),
    pairAnn_BA h, hloop, he, ← pairAnn_y_last h y hy, pairAnnPi_eq (by omega)]
  group

/-- The rounds `R_τ`, `1 ≤ τ ≤ s - 2`: `e(T_τ) = Φ_τ e(T_(r+τ)) Φ_τ⁻¹`, `Φ_τ = R'_(τ-1) Π⁻¹`. -/
theorem pairAnnEq_R (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) (e : ℕ → G) (τ : ℕ) (h1 : 1 ≤ τ) (h2 : τ ≤ s - 2)
    (he : e (2 * pairC r s - 1 - τ) =
      (pairAnnHur r y (τ - 1) * (pairAnnPi r y)⁻¹) * e (2 * pairC r s - 1 - r - τ) *
        (pairAnnHur r y (τ - 1) * (pairAnnPi r y)⁻¹)⁻¹) :
    PairAnnEq r s y H e (pairIdxB r s + 2 + τ) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hAr : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hblk : (pairBlocks r s).getD (pairIdxB r s + 2 + τ) (SBlock.neg 0) =
      SBlock.band (2 * pairC r s - 1 - (r + τ)) (2 * pairC r s - 1 - τ) := by
    rw [pairBlocks_getDRv h _ (by omega), pairBlkRv,
      pairBlkAt_reg7Rv hAr (by simp only [pairIdxB] at *; omega)
        (by simp only [pairIdxB] at *; omega)]
    congr 1 <;> simp only [pairIdxB] at * <;> omega
  have hq : pairIdxR r s τ = pairIdxB r s + 2 + τ := by
    simp only [pairIdxR]; split_ifs <;> omega
  obtain ⟨g1, g2⟩ := pairAnnGap_sufR h _ (pairGapRels_pairRevLoop h y hy H) τ h1 (by omega)
  rw [hq] at g1 g2
  have hloop := pairRevLoop_R h y H τ (by omega)
  rw [hq] at hloop
  rw [show 2 * pairC r s - 1 - r - τ = 2 * pairC r s - 1 - (r + τ) by omega] at he
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge, show 2 * pairC r s - 1 - τ + 1 = 2 * pairC r s - τ by omega, g1,
    g2, show 2 * pairC r s - 1 - (r + τ) + 1 = 2 * pairC r s - 1 - (r + τ - 1) by omega,
    pairAnnGap_BA h _ _ (r + τ) (by omega) (by omega) (by omega)
      (by simp only [pairIdxR]; split_ifs <;> omega),
    pairAnnGap_BA h _ _ (r + τ - 1) (by omega) (by omega) (by omega)
      (by simp only [pairIdxR]; split_ifs <;> omega),
    pairAnn_BA h, pairRevLoop_C h, hloop, pairRevRound_zero (by omega),
    pairRevRound_eq_hur (by omega) y τ h1, he, pairAnnPi_eq (by omega)]
  group

/-- The last round `R_(s-1)`: `e(T_(s-1)) = Φ e(r - 2) Φ⁻¹ R'_(s-2)⁻¹`, `Φ = R'_(s-2) Π⁻¹`. -/
theorem pairAnnEq_Rlast (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) (e : ℕ → G)
    (he : e (2 * pairC r s - s) =
      (pairAnnHur r y (s - 2) * (pairAnnPi r y)⁻¹) * e (r - 2) *
        (pairAnnHur r y (s - 2) * (pairAnnPi r y)⁻¹)⁻¹ * (pairAnnHur r y (s - 2))⁻¹) :
    PairAnnEq r s y H e (pairIdxB r s + s + 1) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hAr : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hblk : (pairBlocks r s).getD (pairIdxB r s + s + 1) (SBlock.neg 0) =
      SBlock.band (r - 2) (2 * pairC r s - s) := by
    rw [pairBlocks_getDRv h _ (by omega)]
    exact pairBlkAt_reg8Rv hAr (by simp only [pairIdxB] at *; omega)
  have hq : pairIdxR r s (s - 1) = pairIdxB r s + s + 1 := by
    simp only [pairIdxR]; split_ifs <;> omega
  obtain ⟨g1, g2⟩ :=
    pairAnnGap_sufR h _ (pairGapRels_pairRevLoop h y hy H) (s - 1) (by omega) le_rfl
  rw [hq] at g1 g2
  rw [show 2 * pairC r s - 1 - (s - 1) = 2 * pairC r s - s by omega] at g1
  rw [show 2 * pairC r s - (s - 1) = 2 * pairC r s - s + 1 by omega] at g2
  have hloop := pairRevLoop_R h y H (s - 1) le_rfl
  rw [hq] at hloop
  have hrun : pairIdxRun r s (r - 1) = r + pairRunDown r s - 3 := by
    simp only [pairIdxRun]; split_ifs <;> omega
  have hasc : pairRevAsc y 0 (r - 1) = pairRevAsc y 0 (r - 2) * y (r - 2) := by
    rw [show r - 1 = r - 2 + 1 by omega, pairRevAsc_succ, Nat.zero_add]
  unfold PairAnnEq
  rw [hblk, loopPr_band_edge, g1, g2, show r - 2 + 1 = r - 1 by omega,
    pairAnnGap_runHit h _ _ (r - 1) le_rfl (by omega) (by rw [hrun]; omega) (by omega), hrun,
    pairAnnGap_bot h _ _ (r - 2) le_rfl (by omega), min_eq_right (by omega), hloop,
    pairRevLoop_run y H (r + pairRunDown r s - 3) (by omega) (by omega), pairRevLoop_C h,
    pairRevRound_zero (by omega), pairRevRound_last h y hy,
    pairRevLoop_Aprod (s := s) y H (r - 2) le_rfl, he, pairAnnHur_s_two h y hy,
    pairAnnPi_eq (by omega), hasc]
  group

/-- The right descent `D'_j`: `e(b₀ + 1 + j) = e(r - 3 - j) R'_(r-3-j)⁻¹`. -/
theorem pairAnnEq_Dp (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) (e : ℕ → G) (j : ℕ) (hj : j < r - 2)
    (he : e (pairIdxB r s + 1 + j) = e (r - 3 - j) * (pairAnnHur r y (r - 3 - j))⁻¹) :
    PairAnnEq r s y H e (pairIdxB r s + s + 3 + j) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hAr : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hblk : (pairBlocks r s).getD (pairIdxDp r s j) (SBlock.neg 0) =
      SBlock.band (r - 3 - j) (pairIdxB r s + 1 + j) := by
    rw [pairBlocks_getDRv h _ (by simp only [pairIdxDp]; omega), pairBlkRv,
      pairBlkAt_reg10Rv hAr (by simp only [pairIdxDp, pairIdxB] at *; omega)
        (by simp only [pairIdxDp, pairIdxB] at *; omega)]
    congr 1 <;> simp only [pairIdxDp, pairIdxB] at * <;> omega
  obtain ⟨g1, g2⟩ := pairAnnGap_sufD h _ (pairGapRels_pairRevLoop h y hy H) j hj
  have hD1 : descProd (pairRevLoop r s y H) (pairIdxDp r s j) (r - 2 - j) =
      pairRevAsc y 0 (r - 2 - j) := by
    rw [← descProd_dp_shiftRv, pairRevLoop_Dprod h y H j (r - 2 - j) (by omega),
      show r - 2 - j - (r - 2 - j) = 0 by omega]
  have hD2 : descProd (pairRevLoop r s y H) (pairIdxDp r s j + 1) (r - 3 - j) =
      pairRevAsc y 0 (r - 3 - j) := by
    rw [show pairIdxDp r s j + 1 = pairIdxDp r s (j + 1) by simp only [pairIdxDp]; omega,
      ← descProd_dp_shiftRv, pairRevLoop_Dprod h y H (j + 1) (r - 3 - j) (by omega),
      show r - 2 - (j + 1) - (r - 3 - j) = 0 by omega]
  rw [hD1] at g1
  rw [hD2] at g2
  have hloop := pairRevLoop_Dp h y H j hj
  have hasc : pairRevAsc y 0 (r - 2 - j) = pairRevAsc y 0 (r - 3 - j) * y (r - 3 - j) := by
    rw [show r - 2 - j = r - 3 - j + 1 by omega, pairRevAsc_succ, Nat.zero_add]
  unfold PairAnnEq
  rw [show pairIdxB r s + s + 3 + j = pairIdxDp r s j from rfl, hblk, loopPr_band_edge,
    show pairIdxB r s + 1 + j + 1 = pairIdxB r s + 2 + j by omega, g1, g2,
    show r - 3 - j + 1 = r - 2 - j by omega,
    pairAnnGap_bot h _ _ (r - 3 - j) (by omega) (by simp only [pairIdxDp]; omega),
    pairAnnGap_bot h _ _ (r - 2 - j) (by omega) (by simp only [pairIdxDp]; omega),
    min_eq_right (by simp only [pairIdxDp]; omega), min_eq_right (by simp only [pairIdxDp]; omega),
    pairRevLoop_Aprod (s := s) y H (r - 3 - j) (by omega),
    pairRevLoop_Aprod (s := s) y H (r - 2 - j) (by omega), hloop, he,
    pairAnnHur_lt r y (r - 3 - j) (by omega), hasc]
  group

end AJConjecture
