import Mathlib
import AJFamily.Classical.SatelliteData
import AJPaper.Filling.PpAClaspGap

/-!
# Closing the positive clasp (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`) for the negative clasp; the positive
clasp is its mirror image (Section 8.2, `conclusion.tex`, eq. (mirror-marked)). In the library
the positive-clasp doubles over `T(r, s)` are closed braids of their own
(`twBlocks r s ℓ false`: the two Hopf letters `σ_T⁻¹` are replaced by `σ_T`), so the clasp has to
be closed for the list `twcBase r s false` too.

`ppa_exists_edge_clasp_pos`: the statement of `ppa_exists_edge_clasp_neg` for the base list
`twcBase r s false`, with the clasp relation `y_0 = compMer (Λ⁻¹ a Λ) a` (for `Λ` commuting with
`y_0` it is `y_0 = compMer a (Λ a Λ⁻¹)`, the relation of `IsTwWhSatelliteP`).

Route. `H = e_(T-s) y_(r-1) e_T⁻¹` as for the negative clasp, `e' n = e n` for `n ≠ 2c` and
`e' (2c) = e_T H`. The gap products are those of `pairBlocks r s`
(`ppa_gapPrefix_take_twcBase`), and the blocks off the Hopf positions are those of
`pairBlocks r s` (`twcBase`, `List.getD_map`-type lemma; `twClaspBlock false` fixes bands).
* `q = pairIdxC r s`: as for the negative clasp.
* `q = pairIdxH1 r s`, now the band `b(T, T + 1)`: `loopPr_band_edge`, `ppa_gapPrefix_at_H1`:
  the equation is `H = e'_(2c) y_(r-1) e_T⁻¹`, i.e. `e_T⁻¹ H e_T = H y_(r-1)`; after `hTs`, `hT`,
  `y_(r-1) = U y_0 U⁻¹` it is `y_0 = α a⁻¹ α⁻¹ a` with `α = Λ⁻¹ a Λ`, which is `hmer`.
* `q = pairIdxH2 r s`, the band `b(T, T + 1)` with loop `H⁻¹`: `loopPr_band_edge`,
  `ppa_gapPrefix_at_H2`: the equation is `H⁻¹ = e'_(2c) H⁻¹ e_T⁻¹ H⁻¹`, true by the choice of
  `e'_(2c)`.
* the other positions: the hypothesis.

Checked numerically in the application (`SCR/A/py/clasp.py`: `H = e_(T-s) c e_T⁻¹`,
`e_(2c) = e_T H` on the companion-abelian tuples of the positive-clasp lists of `(2,3)`,
`(2,5)`, `(3,4)`, `|ℓ| ≤ 2`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The loop of a valid block only reads the chamber products up to one above its gap. -/
private theorem loopPr_congr_hi_ppaClaspPos {m : ℕ} (b : SBlock) (hb : b.Valid m) (P Q : ℕ → G)
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
private theorem descProd_update_ppaClaspPos (e : ℕ → G) (N : ℕ) (x : G) (n : ℕ) (hn : n ≤ N) :
    descProd (fun k ↦ if k = N then x else e k) 0 n = descProd e 0 n := by
  simp only [descProd]
  refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
  have := List.mem_range.1 (List.mem_reverse.1 hi)
  simp only [Nat.zero_add, show i ≠ N by omega, ite_false]

/-- The block at position `q` of the positive-clasp base list. -/
private theorem twcBase_getD_ppaClaspPos {r s : ℕ} (h : IsTorusPair r s) (q : ℕ)
    (hq : q < 2 * pairC r s + 2) (d : SBlock) :
    (twcBase r s false).getD q d = twClaspBlock false (pairBlkRv r s q) := by
  rw [twcBase, pairBlocks_eq_mapRv h, List.map_map, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hq]
  rfl

/-- Off the Hopf positions the blocks are bands, unchanged by the clasp sign. -/
private theorem twClaspBlock_pairBlkRv_ppaClaspPos {r s : ℕ} (h : IsTorusPair r s) (q : ℕ)
    (hq : q < 2 * pairC r s + 2) (h1 : q ≠ pairIdxH1 r s) (h2 : q ≠ pairIdxH2 r s) :
    twClaspBlock false (pairBlkRv r s q) = pairBlkRv r s q := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  simp only [pairIdxH1, pairIdxH2, pairIdxB] at h1 h2
  unfold pairBlkRv pairBlkAtRv
  split_ifs <;> first | rfl | omega

/-- The Hopf loop and the edge meridian of the Hopf level closing the positive clasp. -/
theorem ppa_exists_edge_clasp_pos {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a Λ U : G) (e : ℕ → G) (hU : U⁻¹ * y (r - 1) * U = y 0)
    (hTs : e (2 * pairC r s - 1 - s) = U * a * (y 0)⁻¹ * U⁻¹)
    (hT : e (2 * pairC r s - 1) = U * (Λ⁻¹ * a * Λ) * U⁻¹)
    (hmer : y 0 = compMer (Λ⁻¹ * a * Λ) a)
    (heq : ∀ (H : G) (q : ℕ), 1 ≤ q → q < 2 * pairC r s + 2 → q ≠ pairIdxC r s →
      q ≠ pairIdxH1 r s → q ≠ pairIdxH2 r s →
      pairRevLoop r s y H q = loopPr ((pairBlocks r s).getD q (SBlock.neg 0))
        (fun n ↦ gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s y H) n *
          descProd e 0 n)) :
    ∃ (H : G) (e' : ℕ → G), (∀ n, n < 2 * pairC r s → e' n = e n) ∧
      ∀ q, 1 ≤ q → q < 2 * pairC r s + 2 →
        pairRevLoop r s y H q = loopPr ((twcBase r s false).getD q (SBlock.neg 0))
          (fun n ↦ gapPrefix ((twcBase r s false).take q) (pairRevLoop r s y H) n *
            descProd e' 0 n) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hA : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hB := pairRev_idxB h
  have hR0 : pairRevRound r y 0 = y (r - 1) := pairRevRound_zero (by omega) y
  have hy1 : y (r - 1) = U * y 0 * U⁻¹ := by
    rw [← hU]
    group
  obtain ⟨H, hH⟩ : ∃ H, H = e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹ :=
    ⟨_, rfl⟩
  have hlt : ∀ n, n < 2 * pairC r s →
      (if n = 2 * pairC r s then e (2 * pairC r s - 1) * H else e n) = e n :=
    fun n hn ↦ by simp only [show n ≠ 2 * pairC r s by omega, ite_false]
  refine ⟨H, fun n ↦ if n = 2 * pairC r s then e (2 * pairC r s - 1) * H else e n, hlt,
    fun q hq1 hq ↦ ?_⟩
  simp only [ppa_gapPrefix_take_twcBase]
  rw [twcBase_getD_ppaClaspPos h q hq]
  by_cases hqC : q = pairIdxC r s
  · -- the top-right climb `C`: it defines `H`
    subst hqC
    have hblk : twClaspBlock false (pairBlkRv r s (pairIdxC r s)) =
        SBlock.band (2 * pairC r s - 1 - s) (2 * pairC r s - 1) := by
      rw [pairBlkRv, pairBlkAt_reg9Rv hA (by simp only [pairIdxC, pairIdxB]; omega)]
      rfl
    obtain ⟨g2c, gT, gTs1, gTs⟩ := ppa_gapPrefix_at_C h y hy H
    rw [pairRevLoop_C h, hblk, loopPr_band_edge, show 2 * pairC r s - 1 + 1 = 2 * pairC r s by
      omega, g2c, gT, gTs1, gTs, hlt _ (by omega), hlt _ (by omega), hR0, hH]
    group
  by_cases hqH1 : q = pairIdxH1 r s
  · -- the first Hopf band: the clasp, from `hmer`
    subst hqH1
    have hblk : twClaspBlock false (pairBlkRv r s (pairIdxH1 r s)) =
        SBlock.band (2 * pairC r s - 1) (2 * pairC r s) := by
      rw [pairBlkRv, pairBlkAt_reg6Rv hA (by simp only [pairIdxH1, pairIdxB]),
        show 2 * pairC r s = 2 * pairC r s - 1 + 1 by omega]
      rfl
    obtain ⟨gT, ghigh⟩ := ppa_gapPrefix_at_H1 h y H
    rw [pairRevLoop_H1 h, hblk, loopPr_band_edge,
      show 2 * pairC r s - 1 + 1 = 2 * pairC r s by omega, gT, ghigh _ (by omega),
      ghigh _ (by omega), ite_eq_left rfl, hlt _ (by omega), hH, hTs, hT, hy1, hmer, compMer]
    group
  by_cases hqH2 : q = pairIdxH2 r s
  · -- the second Hopf band: it defines `e_(2c)`
    subst hqH2
    have hblk : twClaspBlock false (pairBlkRv r s (pairIdxH2 r s)) =
        SBlock.band (2 * pairC r s - 1) (2 * pairC r s) := by
      rw [pairBlkRv, pairBlkAt_reg11Rv hA (by simp only [pairIdxH2]; omega),
        show 2 * pairC r s = 2 * pairC r s - 1 + 1 by omega]
      rfl
    obtain ⟨gT, g2c, ghigh⟩ := ppa_gapPrefix_at_H2 h y H
    rw [pairRevLoop_H2 h, hblk, loopPr_band_edge,
      show 2 * pairC r s - 1 + 1 = 2 * pairC r s by omega, gT, g2c, ghigh, ite_eq_left rfl,
      hlt _ (by omega)]
    group
  · -- the annulus bands
    rw [twClaspBlock_pairBlkRv_ppaClaspPos h q hq hqH1 hqH2,
      ← pairBlocks_getDRv h q hq (SBlock.neg 0), heq _ q hq1 hq hqC hqH1 hqH2]
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
    refine loopPr_congr_hi_ppaClaspPos _ (pairBlocks_valid h _ hmem) _ _ fun n hn ↦ ?_
    rw [descProd_update_ppaClaspPos e (2 * pairC r s) _ n (by omega)]

end AJConjecture
