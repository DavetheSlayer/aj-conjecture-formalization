import Mathlib
import AJHandoff.TorusKnot.PairKAnnDefs

/-!
# Corrected chamber products below a block (prefix side)

`G_q(n) = gapPrefix ((pairBlocks r s).take q) L n` is the product of the loops `L q'`, `q' < q`
(later ones on the left), of the blocks whose gap contains the level `n`. Write
`A = A_(r-3) ⋯ A_0 = descProd L 0 (r - 2)`, `b₀ = pairIdxB r s`. The gaps (`pairBlk_lohiRv`):
`A_k : [k + 1, 2c - 2 - k]`, the run blocks have one-level gaps `{n}`, `n ∈ [r - 1, b₀]` (block
position `pairIdxRun r s n`), `B : [b₀ + 1, 2c - r]`, `R_0 : [2c - r, 2c - 1]`, `H₁ : {2c}`,
`R_τ : [2c - r - τ, 2c - 1 - τ]`, `R_(s-1) : [r - 1, 2c - s]`, `C : [2c - s, 2c - 1]`,
`D'_j : [r - 2 - j, b₀ + 1 + j]`, `H₂ : {2c}`.

* `pairAnnGap_A`: below a left climb (`q ≤ r - 2`) every level of `[q, 2c - 1 - q]` lies in all
  earlier gaps;
* `pairAnnGap_bot`: a level `m ≤ r - 2` lies in the gaps of `A_0, …, A_(m-1)` and, among the
  later blocks, first in `D'_(r-2-m)` at position `b₀ + s + 1 + r - m`;
* `pairAnnGap_run`, `pairAnnGap_runHit`: a level of `[r - 2, 2c + 1 - r]` below a run block or `B`
  sees `A` and the run block with gap `{m}` if it comes earlier; for the run levels this stays
  true up to the last round `R_(s-1)` at `b₀ + s + 1`;
* `pairAnnGap_BA`: a top level `T_t`, `t ≥ r - 1`, below a position before its first round
  `R_(t+1-r)` sees exactly `B` and `A`;
* `pairAnnGap_top0`: below `R_0` no gap contains `T_0 = 2c - 1` or `2c`.

Route: `gapPrefix_take_pairBlocks`, then `gapRevProd_pair_peelRv` once per run of consecutive
contributing positions (at most three peels: `A`, the run block, nothing else), with the side
conditions from `pairBlk_lohiRv` and `omega`, exactly as `rvC_levT` in
`AJHandoff.TorusKnot.PairKRevSolveEdge`. Every statement is checked position by position by
`pairAnnCheckGap` (`#guard` in `AJHandoff.TorusKnot.PairKAnnDefs`).
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- Below a left climb `A_q` every level of `[q, 2c - 1 - q]` sees `A_(q-1) ⋯ A_0`. -/
theorem pairAnnGap_A (h : IsTorusPair r s) (L : ℕ → G) (q n : ℕ) (hq : q ≤ r - 2)
    (h1 : q ≤ n) (h2 : n ≤ 2 * pairC r s - 1 - q) :
    gapPrefix ((pairBlocks r s).take q) L n = descProd L 0 q := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  rw [gapPrefix_take_pairBlocks h L q n (by omega),
    gapRevProd_pair_peelRv r s L n 0 q q (by omega) (fun q' h1 h2 ↦ by have := hl q'; omega)
      (fun q' h1 h2 ↦ by omega), gapRevProd_zeroRv, mul_one]

/-- A bottom level `m ≤ r - 2` sees `A_(m-1) ⋯ A_0` up to the descent `D'_(r-2-m)`. -/
theorem pairAnnGap_bot (h : IsTorusPair r s) (L : ℕ → G) (q m : ℕ) (hm : m ≤ r - 2)
    (hq : q ≤ pairIdxB r s + s + 1 + r - m) :
    gapPrefix ((pairBlocks r s).take q) L m = descProd L 0 (min q m) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  have hB0 : pairIdxB r s = 2 * pairC r s - s - r := rfl
  rw [gapPrefix_take_pairBlocks h L q m (by omega),
    gapRevProd_pair_peelRv r s L m 0 (min q m) q (by omega)
      (fun q' h1 h2 ↦ by have := hl q'; omega) (fun q' h1 h2 ↦ by have := hl q'; omega),
    gapRevProd_zeroRv, mul_one]

/-- Below a run block or `B`, a level of `[r - 2, 2c + 1 - r]` that is not the gap of an earlier
run block sees `A`. -/
theorem pairAnnGap_run (h : IsTorusPair r s) (L : ℕ → G) (q m : ℕ) (hq1 : r - 2 ≤ q)
    (hq2 : q ≤ pairIdxB r s) (hm1 : r - 2 ≤ m) (hm2 : m ≤ 2 * pairC r s + 1 - r)
    (hm : r - 1 ≤ m → m ≤ pairIdxB r s → q ≤ pairIdxRun r s m) :
    gapPrefix ((pairBlocks r s).take q) L m = descProd L 0 (r - 2) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  have hB0 : pairIdxB r s = 2 * pairC r s - s - r := rfl
  have hm' : r - 1 ≤ m → m ≤ pairIdxB r s →
      (m ≤ r + pairRunDown r s - 2 ∧ q ≤ 2 * r + pairRunDown r s - 4 - m) ∨
        (r + pairRunDown r s - 2 < m ∧ q ≤ m - 1) := fun h1 h2 ↦ by
    have := hm h1 h2
    unfold pairIdxRun at this
    split_ifs at this <;> omega
  rw [gapPrefix_take_pairBlocks h L q m (by omega),
    gapRevProd_pair_peelRv r s L m 0 (r - 2) q (by omega)
      (fun q' h1 h2 ↦ by have := hl q'; omega) (fun q' h1 h2 ↦ by have := hl q'; omega),
    gapRevProd_zeroRv, mul_one]

/-- A run level whose run block comes earlier sees that block and `A`, up to `R_(s-1)`. -/
theorem pairAnnGap_runHit (h : IsTorusPair r s) (L : ℕ → G) (q m : ℕ) (hm1 : r - 1 ≤ m)
    (hm2 : m ≤ pairIdxB r s) (hq1 : pairIdxRun r s m < q) (hq2 : q ≤ pairIdxB r s + s + 1) :
    gapPrefix ((pairBlocks r s).take q) L m = L (pairIdxRun r s m) * descProd L 0 (r - 2) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  have hB0 : pairIdxB r s = 2 * pairC r s - s - r := rfl
  have hp : (m ≤ r + pairRunDown r s - 2 ∧ pairIdxRun r s m = 2 * r + pairRunDown r s - 4 - m) ∨
      (r + pairRunDown r s - 2 < m ∧ pairIdxRun r s m = m - 1) := by
    unfold pairIdxRun; split_ifs <;> omega
  rw [gapPrefix_take_pairBlocks h L q m (by omega),
    gapRevProd_pair_peelRv r s L m (pairIdxRun r s m) 1 q (by omega)
      (fun q' h1 h2 ↦ by have := hl q'; omega) (fun q' h1 h2 ↦ by have := hl q'; omega),
    gapRevProd_pair_peelRv r s L m 0 (r - 2) (pairIdxRun r s m) (by omega)
      (fun q' h1 h2 ↦ by have := hl q'; omega) (fun q' h1 h2 ↦ by have := hl q'; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv]

/-- A top level `T_t`, `t ≥ r - 1`, below a position before its first round sees `B A`. -/
theorem pairAnnGap_BA (h : IsTorusPair r s) (L : ℕ → G) (q t : ℕ) (ht1 : r - 1 ≤ t)
    (ht2 : t ≤ s + r - 2) (hq1 : pairIdxB r s < q) (hq2 : q ≤ pairIdxR r s (t + 1 - r)) :
    gapPrefix ((pairBlocks r s).take q) L (2 * pairC r s - 1 - t) =
      L (pairIdxB r s) * descProd L 0 (r - 2) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  have hB0 : pairIdxB r s = 2 * pairC r s - s - r := rfl
  have hR : (t + 1 - r = 0 ∧ pairIdxR r s (t + 1 - r) = pairIdxB r s + 1) ∨
      (t + 1 - r ≠ 0 ∧ pairIdxR r s (t + 1 - r) = pairIdxB r s + 2 + (t + 1 - r)) := by
    unfold pairIdxR; split_ifs <;> omega
  rw [gapPrefix_take_pairBlocks h L q _ (by omega),
    gapRevProd_pair_peelRv r s L _ (pairIdxB r s) 1 q (by omega)
      (fun q' h1 h2 ↦ by have := hl q'; omega) (fun q' h1 h2 ↦ by have := hl q'; omega),
    gapRevProd_pair_peelRv r s L _ 0 (r - 2) (pairIdxB r s) (by omega)
      (fun q' h1 h2 ↦ by have := hl q'; omega) (fun q' h1 h2 ↦ by have := hl q'; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv]

/-- Below `R_0` no gap contains `T_0 = 2c - 1` or `2c`. -/
theorem pairAnnGap_top0 (h : IsTorusPair r s) (L : ℕ → G) :
    gapPrefix ((pairBlocks r s).take (pairIdxB r s + 1)) L (2 * pairC r s - 1) = 1 ∧
      gapPrefix ((pairBlocks r s).take (pairIdxB r s + 1)) L (2 * pairC r s) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  constructor <;>
  · rw [gapPrefix_take_pairBlocks h L _ _ (by simp only [pairIdxB]; omega),
      gapRevProd_skipRv (pairGapFRv r s L _) 0 _ (Nat.zero_le _) fun q' h1 h2 ↦
        ite_eq_right (by have := hl q'; simp only [pairIdxB] at h2; omega), gapRevProd_zeroRv]

end AJConjecture
