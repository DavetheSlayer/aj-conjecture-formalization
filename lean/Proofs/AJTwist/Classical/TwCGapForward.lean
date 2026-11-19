import Mathlib
import AJHandoff.TorusKnot.PairKRevGapConv
import AJTwist.Classical.TwCBlocks

/-!
# The gap relations from the gap products of abstract loops

`PairGapRels r s L` (`AJHandoff.TorusKnot.PairKPeriGapRel`) lists the relations "the product of
the loops of the blocks whose gap contains the level `n` is `1`" of `pairBlocks r s`, regime by
regime. The library proves it for the block loops of a representation of the knot group
(`pairGapRels_of_hom`) and proves the converse for abstract loops
(`gapPrefix_pairBlocks_eq_one`). Here is the direct implication for abstract loops, which is
what the twisted block lists need: their loops are not the loops of a run of `pairBlocks r s`.

* `pairGapRels_of_gapPrefix`: if `gapPrefix (pairBlocks r s) L n = 1` for all `n`, then
  `PairGapRels r s L`. Route: `gapPrefix_take_pairBlocks` at `q = 2c + 2` turns the hypothesis
  into `gapRevProdRv (pairGapFRv r s L n) (2c + 2) = 1`; then, level by level, the proofs of the
  private `pairGap_bot`, `pairGap_run`, `pairGap_climb`, `pairGap_stairLow`, `pairGap_stairHigh`,
  `pairGap_top` of `PairKPeriGapRel` with the public `…Rv` copies of their tools
  (`pairBlk_lohiRv`, `gapRevProd_pair_peelRv`, `descProd_…Rv`).
* `gapPrefix_twcBase`: the positive Hopf letters have the gap interval of the negative ones
  (`twClaspBlock` keeps `SBlock.lo` and `SBlock.hi`), so `gapPrefix` does not see the clasp
  sign.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The bottom levels. -/
private theorem pairGap_bot_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn1 : 1 ≤ n) (hn2 : n ≤ r - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - n) n * descProd L 0 n = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key n
  rw [
    gapRevProd_pair_peelRv r s L n (b + s + 3 + (r - 2 - n)) (n) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (0) (n) (b + s + 3 + (r - 2 - n))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one] at k
  subst hb
  rw [descProd_dp_shiftRv]
  exact k

/-- The run levels of the decreasing run. -/
private theorem pairGap_run_down_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn1 : r - 1 ≤ n) (hn2 : n ≤ 2 * pairC r s - s - r) (hn : n ≤ r + pairRunDown r s - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s n) * descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have hri : pairIdxRun r s n = 2 * r + pairRunDown r s - 4 - n := ite_eq_left hn
  have k := key n
  rw [
    gapRevProd_pair_peelRv r s L n (b + s + 3) (r - 2) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (b + s + 1) (1) (b + s + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (pairIdxRun r s n) (1) (b + s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (0) (r - 2) (pairIdxRun r s n)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv] at k
  subst hb
  have hR : pairIdxR r s (s - 1) = 2 * pairC r s - s - r + s + 1 := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    unfold pairIdxB
    omega
  rw [descProd_dp_shiftRv, hR]
  simp only [mul_assoc] at k ⊢
  exact k

/-- The run levels of the increasing run. -/
private theorem pairGap_run_up_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn2 : n ≤ 2 * pairC r s - s - r) (hn : ¬n ≤ r + pairRunDown r s - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s n) * descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have hri : pairIdxRun r s n = n - 1 := ite_eq_right hn
  have k := key n
  rw [
    gapRevProd_pair_peelRv r s L n (b + s + 3) (r - 2) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (b + s + 1) (1) (b + s + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (pairIdxRun r s n) (1) (b + s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (0) (r - 2) (pairIdxRun r s n)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv] at k
  subst hb
  have hR : pairIdxR r s (s - 1) = 2 * pairC r s - s - r + s + 1 := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    unfold pairIdxB
    omega
  rw [descProd_dp_shiftRv, hR]
  simp only [mul_assoc] at k ⊢
  exact k

/-- The run levels. -/
private theorem pairGap_run_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn1 : r - 1 ≤ n) (hn2 : n ≤ 2 * pairC r s - s - r) :
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s n) * descProd L 0 (r - 2) = 1 := by
  by_cases hn : n ≤ r + pairRunDown r s - 2
  · exact pairGap_run_down_twCGapForward h L key n hn1 hn2 hn
  · exact pairGap_run_up_twCGapForward h L key n hn2 hn

/-- The climb levels. -/
private theorem pairGap_climb_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht1 : s ≤ t) (ht2 : t ≤ s + r - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) (s + r - 2 - t) (t - s) *
      descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) (s + r - 1 - t) * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + s + 3 + (s + r - 2 - t)) (t - s)
      (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + 2 + (t + 1 - r)) (s + r - 1 - t)
      (b + s + 3 + (s + r - 2 - t))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b) (1) (b + 2 + (t + 1 - r))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (0) (r - 2) (b)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv] at k
  subst hb
  have hR : pairIdxR r s (t + 1 - r) = 2 * pairC r s - s - r + 2 + (t + 1 - r) := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    rfl
  rw [descProd_dp_shiftRv, descProd_round_shiftRv r s L _ _ (by omega), hR]
  simp only [mul_assoc] at k ⊢
  exact k

/-- The lower staircase levels. -/
private theorem pairGap_stairLow_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht : t ≤ r - 2) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) 0 (t + 1) * descProd L 0 t = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + s + 2) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + 3) (t) (b + s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + 1) (1) (b + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (0) (t) (b + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv] at k
  subst hb
  rw [descProd_succ_bot_gapRv, Nat.zero_add, descProd_round_shiftRv r s L 1 t le_rfl]
  simp only [pairIdxR, pairIdxC, pairIdxB, one_ne_zero, ↓reduceIte, mul_assoc] at k ⊢
  exact k

/-- The first upper staircase level `t = r - 1`. -/
private theorem pairGap_stairHigh_first_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht1 : r - 1 ≤ t) (htr : t < r) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + s + 2) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + 3) (r - 1) (b + s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + 1) (1) (b + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b) (1) (b + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (0) (r - 2) (b)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv, descProd_one_gapRv] at k
  subst hb
  rw [show descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r =
      descProd (fun u ↦ L (pairIdxR r s u)) 0 (r - 1 + 1) by congr 1 <;> omega,
    descProd_succ_bot_gapRv, Nat.zero_add, descProd_round_shiftRv r s L 1 _ le_rfl]
  simp only [pairIdxR, pairIdxC, pairIdxB, one_ne_zero, ↓reduceIte, mul_assoc] at k ⊢
  exact k

/-- The upper staircase levels `r ≤ t ≤ s - 1`. -/
private theorem pairGap_stairHigh_rest_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (htr : r ≤ t) (ht2 : t ≤ s - 1) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + s + 2) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b + 2 + (t + 1 - r)) (r) (b + s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (b) (1) (b + 2 + (t + 1 - r))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s - 1 - t) (0) (r - 2) (b)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv] at k
  subst hb
  have hR : pairIdxR r s (t + 1 - r) = 2 * pairC r s - s - r + 2 + (t + 1 - r) := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    rfl
  rw [descProd_round_shiftRv r s L _ _ (by omega), hR]
  simp only [pairIdxC, pairIdxB, mul_assoc] at k ⊢
  exact k

/-- The upper staircase levels. -/
private theorem pairGap_stairHigh_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht1 : r - 1 ≤ t) (ht2 : t ≤ s - 1) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  rcases Nat.lt_or_ge t r with htr | htr
  · exact pairGap_stairHigh_first_twCGapForward h L key t ht1 htr
  · exact pairGap_stairHigh_rest_twCGapForward h L key t htr ht2

/-- The Hopf level. -/
private theorem pairGap_top_twCGapForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1) :
    L (pairIdxH2 r s) * L (pairIdxH1 r s) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s)
  rw [
    gapRevProd_pair_peelRv r s L (2 * pairC r s) (2 * pairC r s + 1) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s) (b + 2) (1) (2 * pairC r s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L (2 * pairC r s) (0) (0) (b + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one, descProd_zero_gapRv, mul_one, descProd_one_gapRv,
    descProd_one_gapRv] at k
  subst hb
  exact k

/-- Loops whose gap products over `pairBlocks r s` are all `1` satisfy the gap relations. -/
theorem pairGapRels_of_gapPrefix {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : ∀ n, gapPrefix (pairBlocks r s) L n = 1) : PairGapRels r s L := by
  have key : ∀ n, gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1 := fun n ↦ by
    rw [← gapPrefix_take_pairBlocks h L _ n le_rfl,
      List.take_of_length_le (length_pairBlocksRv h).le]
    exact hL n
  exact ⟨pairGap_bot_twCGapForward h _ key, pairGap_run_twCGapForward h _ key,
    pairGap_climb_twCGapForward h _ key, pairGap_stairLow_twCGapForward h _ key,
    pairGap_stairHigh_twCGapForward h _ key, pairGap_top_twCGapForward h _ key⟩

/-- Changing the sign of the Hopf letters does not change the gap products of abstract
loops. -/
private theorem gapPrefix_map_twClaspBlock_twCGapForward (σ : Bool) (bs : List SBlock)
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

/-- The gap products of abstract loops do not depend on the sign of the Hopf letters. -/
theorem gapPrefix_twcBase (r s : ℕ) (σ : Bool) (L : ℕ → G) (n : ℕ) :
    gapPrefix (twcBase r s σ) L n = gapPrefix (pairBlocks r s) L n :=
  gapPrefix_map_twClaspBlock_twCGapForward σ (pairBlocks r s) L n

end AJConjecture
