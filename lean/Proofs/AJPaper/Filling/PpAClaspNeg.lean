import Mathlib
import AJFamily.Classical.SatelliteData
import AJPaper.Filling.PpAClaspGap

/-!
# Closing the negative clasp: the top-right climb and the Hopf letters (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`): "The pattern relator … holds because
`Y = W^k`. The filling relation holds by construction."

`ppa_exists_edge_clasp_neg`: let `y` be a tuple with the torus relation and `e` edge meridians on
the levels of the braided annulus solving the loop equations of the annulus bands of
`pairBlocks r s` (every position `q ≥ 1` other than `C` and the Hopf letters), with the ends
`e_(T-s) = U a y_0⁻¹ U⁻¹`, `e_T = U (Λ⁻¹ a Λ) U⁻¹`, `U⁻¹ y_(r-1) U = y_0`, for some element `Λ`.
If `y_0 = compMer a (Λ⁻¹ a Λ)` (the clasp relation of the negative-clasp pattern with axis
meridian `Λ`), there are a Hopf loop `H` and an edge meridian of the Hopf level `2c` such that
the loop equations of *all* positions `q ≥ 1` hold.

This is the second half of the proof of `exists_pairRevEdge`
(`AJHandoff.TorusKnot.PairKRevSolveEdge`) with the element `pairRevLam r s y` replaced by an
arbitrary `Λ` (that proof uses it only through `hT` and `hmer`), and without the head position
`q = 0`. In the application `y` is constant `c` and `Λ = c^ℓ`.

Route (verbatim from there). `H = e_(T-s) y_(r-1) e_T⁻¹`, `e' n = e n` for `n ≠ 2c` and
`e' (2c) = e_(T-s) y_(r-1)`.
* `q = pairIdxC r s`, the band `b(T - s, T)` (`pairBlocks_getDRv`, `pairBlkAt_reg9Rv`):
  `loopPr_band_edge`, `ppa_gapPrefix_at_C`, `pairRevLoop_C`, `pairRevRound_zero`; `group`.
* `q = pairIdxH1 r s`, the letter `σ_T⁻¹` (`pairBlkAt_reg6Rv`): `loopPr_neg_edge`,
  `ppa_gapPrefix_at_H1`, `pairRevLoop_H1`; after `hTs`, `hT`, `y_(r-1) = U y_0 U⁻¹` the equation
  is `hmer` conjugated by `U` (`group`).
* `q = pairIdxH2 r s` (`pairBlkAt_reg11Rv`): `loopPr_neg_edge`, `ppa_gapPrefix_at_H2`,
  `pairRevLoop_H2`; `group`.
* the other positions: the hypothesis, since the block only reads levels `≤ 2c - 1`
  (`pairBlk_lohiRv`; the private `loopPr_congr_hi`, `descProd_update_rv` there).

Checked numerically in the application (`SCR/A/py/clasp.py`: `H = e_(T-s) c e_T⁻¹`,
`e_(2c) = H e_T` on the companion-abelian tuples of `(2,3)`, `(2,5)`, `(3,4)`, `|ℓ| ≤ 2`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The loop of a valid block only reads the chamber products up to one above its gap. -/
private theorem loopPr_congr_hi_ppaClaspNeg {m : ℕ} (b : SBlock) (hb : b.Valid m) (P Q : ℕ → G)
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
private theorem descProd_update_ppaClaspNeg (e : ℕ → G) (N : ℕ) (x : G) (n : ℕ) (hn : n ≤ N) :
    descProd (fun k ↦ if k = N then x else e k) 0 n = descProd e 0 n := by
  simp only [descProd]
  refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
  have := List.mem_range.1 (List.mem_reverse.1 hi)
  simp only [Nat.zero_add, show i ≠ N by omega, ite_false]

/-- The Hopf loop and the edge meridian of the Hopf level closing the negative clasp. -/
theorem ppa_exists_edge_clasp_neg {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a Λ U : G) (e : ℕ → G) (hU : U⁻¹ * y (r - 1) * U = y 0)
    (hTs : e (2 * pairC r s - 1 - s) = U * a * (y 0)⁻¹ * U⁻¹)
    (hT : e (2 * pairC r s - 1) = U * (Λ⁻¹ * a * Λ) * U⁻¹)
    (hmer : y 0 = compMer a (Λ⁻¹ * a * Λ))
    (heq : ∀ (H : G) (q : ℕ), 1 ≤ q → q < 2 * pairC r s + 2 → q ≠ pairIdxC r s →
      q ≠ pairIdxH1 r s → q ≠ pairIdxH2 r s →
      pairRevLoop r s y H q = loopPr ((pairBlocks r s).getD q (SBlock.neg 0))
        (fun n ↦ gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s y H) n *
          descProd e 0 n)) :
    ∃ (H : G) (e' : ℕ → G), (∀ n, n < 2 * pairC r s → e' n = e n) ∧
      ∀ q, 1 ≤ q → q < 2 * pairC r s + 2 →
        pairRevLoop r s y H q = loopPr ((pairBlocks r s).getD q (SBlock.neg 0))
          (fun n ↦ gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s y H) n *
            descProd e' 0 n) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hA : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hB := pairRev_idxB h
  have hR0 : pairRevRound r y 0 = y (r - 1) := pairRevRound_zero (by omega) y
  have hy1 : y (r - 1) = U * y 0 * U⁻¹ := by
    rw [← hU]
    group
  have hlt : ∀ n, n < 2 * pairC r s →
      (if n = 2 * pairC r s then e (2 * pairC r s - 1 - s) * y (r - 1) else e n) = e n :=
    fun n hn ↦ by simp only [show n ≠ 2 * pairC r s by omega, ite_false]
  refine ⟨e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹,
    fun n ↦ if n = 2 * pairC r s then e (2 * pairC r s - 1 - s) * y (r - 1) else e n, hlt,
    fun q hq1 hq ↦ ?_⟩
  by_cases hqC : q = pairIdxC r s
  · -- the top-right climb `C`: it defines `H`
    subst hqC
    have hblk : (pairBlocks r s).getD (pairIdxC r s) (SBlock.neg 0) =
        SBlock.band (2 * pairC r s - 1 - s) (2 * pairC r s - 1) := by
      rw [pairBlocks_getDRv h _ hq]
      exact pairBlkAt_reg9Rv hA (by simp only [pairIdxC, pairIdxB]; omega)
    obtain ⟨g2c, gT, gTs1, gTs⟩ := ppa_gapPrefix_at_C h y hy
      (e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹)
    rw [pairRevLoop_C h, hblk, loopPr_band_edge, show 2 * pairC r s - 1 + 1 = 2 * pairC r s by
      omega, g2c, gT, gTs1, gTs, hlt _ (by omega), hlt _ (by omega), hR0]
    group
  by_cases hqH1 : q = pairIdxH1 r s
  · -- the first Hopf letter: the clasp, from `hmer`
    subst hqH1
    have hblk : (pairBlocks r s).getD (pairIdxH1 r s) (SBlock.neg 0) =
        SBlock.neg (2 * pairC r s - 1) := by
      rw [pairBlocks_getDRv h _ hq]
      exact pairBlkAt_reg6Rv hA (by simp only [pairIdxH1, pairIdxB])
    obtain ⟨gT, ghigh⟩ := ppa_gapPrefix_at_H1 h y
      (e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹)
    rw [pairRevLoop_H1 h, hblk, loopPr_neg_edge, gT, ghigh _ (by omega), ghigh _ (by omega),
      show 2 * pairC r s - 1 + 1 = 2 * pairC r s by omega, ite_eq_left rfl, hlt _ (by omega),
      hTs, hT, hy1, hmer, compMer]
    group
  by_cases hqH2 : q = pairIdxH2 r s
  · -- the second Hopf letter: it defines `e_(2c)`
    subst hqH2
    have hblk : (pairBlocks r s).getD (pairIdxH2 r s) (SBlock.neg 0) =
        SBlock.neg (2 * pairC r s - 1) := by
      rw [pairBlocks_getDRv h _ hq]
      exact pairBlkAt_reg11Rv hA (by simp only [pairIdxH2]; omega)
    obtain ⟨gT, g2c, ghigh⟩ := ppa_gapPrefix_at_H2 h y
      (e (2 * pairC r s - 1 - s) * y (r - 1) * (e (2 * pairC r s - 1))⁻¹)
    rw [pairRevLoop_H2 h, hblk, loopPr_neg_edge, gT,
      show 2 * pairC r s - 1 + 1 = 2 * pairC r s by omega, g2c,
      show 2 * pairC r s - 1 + 2 = 2 * pairC r s + 1 by omega, ghigh, ite_eq_left rfl,
      hlt _ (by omega)]
    group
  · -- the annulus bands
    rw [heq _ q hq1 hq hqC hqH1 hqH2]
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
    refine loopPr_congr_hi_ppaClaspNeg _ (pairBlocks_valid h _ hmem) _ _ fun n hn ↦ ?_
    rw [descProd_update_ppaClaspNeg e (2 * pairC r s) _ n (by omega)]

end AJConjecture
