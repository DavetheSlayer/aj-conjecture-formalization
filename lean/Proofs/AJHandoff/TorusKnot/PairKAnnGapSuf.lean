import Mathlib
import AJHandoff.TorusKnot.PairKAnnDefs

/-!
# Corrected chamber products below a block (suffix side)

For loops with trivial gap products (`PairGapRels`, `gapPrefix_pairBlocks_eq_one`) the prefix
`G_q(n) = gapPrefix ((pairBlocks r s).take q) L n` is the inverse of the product of the loops of
the blocks at positions `≥ q` whose gap contains `n`. This is short at the upper staircase and
right-descent levels:

* `pairAnnGap_sufR`: below the round `R_τ` (`1 ≤ τ ≤ s - 1`), the level `T_τ` is contained only
  in `R_τ` and `C` among the later blocks, and `T_(τ-1)` only in `C`;
* `pairAnnGap_sufD`: below the descent `D'_j`, the level `b₀ + 1 + j` is contained exactly in
  `D'_j, …, D'_(r-3)` (consecutive positions), and `b₀ + 2 + j` in `D'_(j+1), …, D'_(r-3)`.

Route: `gapPrefix_take_pairBlocks` with `q = 2c + 2` (`List.take_of_length_le`,
`length_pairBlocks_rev`) turns the full product into `gapRevProdRv (pairGapFRv r s L n) (2c+2)`,
which is `1`; peel the top with `gapRevProd_pair_peelRv` (one or two peels: `C`, then `R_τ`; or
the run of descents) down to position `q`, and solve for the prefix. Checked position by position
by `pairAnnCheckGap` (`#guard` in `AJHandoff.TorusKnot.PairKAnnDefs`).
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- The full gap products of loops satisfying the gap relations, by position. -/
private theorem pairAnnGap_full (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L)
    (n : ℕ) : gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1 := by
  rw [← gapPrefix_take_pairBlocks h L _ n le_rfl,
    List.take_of_length_le (by rw [length_pairBlocks_rev h]), gapPrefix_pairBlocks_eq_one h L hL n]

/-- Below `R_τ`, the level `T_τ`. -/
private theorem pairAnnGap_sufR_top (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L)
    (τ : ℕ) (h1 : 1 ≤ τ) (h2 : τ ≤ s - 1) :
    gapRevProdRv (pairGapFRv r s L (2 * pairC r s - 1 - τ)) (pairIdxB r s + 2 + τ) =
      (L (pairIdxC r s) * L (pairIdxB r s + 2 + τ))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  have hB0 : pairIdxB r s = 2 * pairC r s - s - r := rfl
  have hC0 : pairIdxC r s = pairIdxB r s + s + 2 := rfl
  have hfull := pairAnnGap_full h L hL (2 * pairC r s - 1 - τ)
  rw [gapRevProd_pair_peelRv r s L _ (pairIdxC r s) 1 (2 * pairC r s + 2) (by omega)
      (fun q hq1 hq2 ↦ by have := hl q; omega) (fun q hq1 hq2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L _ (pairIdxB r s + 2 + τ) 1 (pairIdxC r s) (by omega)
      (fun q hq1 hq2 ↦ by have := hl q; omega) (fun q hq1 hq2 ↦ by have := hl q; omega),
    descProd_one_gapRv, descProd_one_gapRv, ← mul_assoc] at hfull
  exact eq_inv_of_mul_eq_one_right hfull

/-- Below `R_τ`, the level `T_(τ-1)`. -/
private theorem pairAnnGap_sufR_up (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L)
    (τ : ℕ) (h1 : 1 ≤ τ) (h2 : τ ≤ s - 1) :
    gapRevProdRv (pairGapFRv r s L (2 * pairC r s - τ)) (pairIdxB r s + 2 + τ) =
      (L (pairIdxC r s))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  have hB0 : pairIdxB r s = 2 * pairC r s - s - r := rfl
  have hC0 : pairIdxC r s = pairIdxB r s + s + 2 := rfl
  have hfull := pairAnnGap_full h L hL (2 * pairC r s - τ)
  rw [gapRevProd_pair_peelRv r s L _ (pairIdxC r s) 1 (2 * pairC r s + 2) (by omega)
      (fun q hq1 hq2 ↦ by have := hl q; omega) (fun q hq1 hq2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L _ (pairIdxB r s + 2 + τ) 0 (pairIdxC r s) (by omega)
      (fun q hq1 hq2 ↦ by omega) (fun q hq1 hq2 ↦ by have := hl q; omega),
    descProd_one_gapRv, descProd_zero_gapRv, one_mul] at hfull
  exact eq_inv_of_mul_eq_one_right hfull

/-- Below `R_τ`: `G(T_τ) = (C R_τ)⁻¹` and `G(T_(τ-1)) = C⁻¹`. -/
theorem pairAnnGap_sufR (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L) (τ : ℕ)
    (h1 : 1 ≤ τ) (h2 : τ ≤ s - 1) :
    gapPrefix ((pairBlocks r s).take (pairIdxR r s τ)) L (2 * pairC r s - 1 - τ) =
        (L (pairIdxC r s) * L (pairIdxR r s τ))⁻¹ ∧
      gapPrefix ((pairBlocks r s).take (pairIdxR r s τ)) L (2 * pairC r s - τ) =
        (L (pairIdxC r s))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hq : pairIdxR r s τ = pairIdxB r s + 2 + τ := by
    simp only [pairIdxR]; split_ifs <;> omega
  rw [hq, gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxB]; omega),
    gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxB]; omega)]
  exact ⟨pairAnnGap_sufR_top h L hL τ h1 h2, pairAnnGap_sufR_up h L hL τ h1 h2⟩

/-- Below `D'_j`: `G(b₀ + 1 + j) = (D'_(r-3) ⋯ D'_j)⁻¹` and
`G(b₀ + 2 + j) = (D'_(r-3) ⋯ D'_(j+1))⁻¹`. -/
theorem pairAnnGap_sufD (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L) (j : ℕ)
    (hj : j < r - 2) :
    gapPrefix ((pairBlocks r s).take (pairIdxDp r s j)) L (pairIdxB r s + 1 + j) =
        (descProd L (pairIdxDp r s j) (r - 2 - j))⁻¹ ∧
      gapPrefix ((pairBlocks r s).take (pairIdxDp r s j)) L (pairIdxB r s + 2 + j) =
        (descProd L (pairIdxDp r s j + 1) (r - 3 - j))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  have hB0 : pairIdxB r s = 2 * pairC r s - s - r := rfl
  have hD0 : pairIdxDp r s j = pairIdxB r s + s + 3 + j := rfl
  rw [gapPrefix_take_pairBlocks h L _ _ (by omega), gapPrefix_take_pairBlocks h L _ _ (by omega)]
  constructor
  · have h1 := pairAnnGap_full h L hL (pairIdxB r s + 1 + j)
    rw [gapRevProd_pair_peelRv r s L _ (pairIdxDp r s j) (r - 2 - j) (2 * pairC r s + 2)
        (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
        (fun q h1 h2 ↦ by have := hl q; omega)] at h1
    exact eq_inv_of_mul_eq_one_right h1
  · have h1 := pairAnnGap_full h L hL (pairIdxB r s + 2 + j)
    rw [gapRevProd_pair_peelRv r s L _ (pairIdxDp r s j + 1) (r - 3 - j) (2 * pairC r s + 2)
        (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
        (fun q h1 h2 ↦ by have := hl q; omega),
      gapRevProd_pair_peelRv r s L _ (pairIdxDp r s j) 0 (pairIdxDp r s j + 1) (by omega)
        (fun q h1 h2 ↦ by omega) (fun q h1 h2 ↦ by have := hl q; omega),
      descProd_zero_gapRv, one_mul] at h1
    exact eq_inv_of_mul_eq_one_right h1

end AJConjecture
