import Mathlib
import AJHandoff.TorusKnot.PairKOrbRounds

/-!
# The companion tuple in terms of the rounds

For block loops with the gap relations: `z_0 = y_0⁻¹ y_1 y_0` and
`Λ = (z_0 ⋯ z_(r-1))^s z_0^(-rs) = y_0⁻¹ K^s y_1^(-rs) y_0`
(`pairCompFun`, `pairCompLong` of `AJHandoff.TorusKnot.PairKPeriComp`).

Route: the window is `w_j = y_(-j)` for `1 ≤ j ≤ r - 1` and `w_0 = y_0` (this is
`pairWin_eq_roundSeq` of `AJHandoff.TorusKnot.PairKPeriComp`, private there: copy
`pairWin_prefix`, `pairRound_suffix`, `pairWin_prefix_eq_round` with `pairOrbY_add_period`).
Then `z_0 = (w_1 ⋯ w_(r-2)) w_(r-1) (⋯)⁻¹ = y_0⁻¹ y_1 y_0` by the window relation
`y_1 = (y_0 y_(-1) ⋯ y_(2-r)) y_(1-r) (⋯)⁻¹` (`pairOrb_window`); and
`z_k ⋯ z_(r-2) = w_1 ⋯ w_(r-1-k)` (induction on `r - 2 - k`), so
`z_0 ⋯ z_(r-1) = w_1 ⋯ w_(r-1) w_0 = y_0⁻¹ K y_0` (`K = y_0 y_(-1) ⋯ y_(1-r)`).
Checked exactly in the torus knot group.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Descending products -/

/-- The empty descending product. -/
private theorem descProd_zero_ocmp (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

/-- Splitting off the top factor of a descending product. -/
private theorem descProd_succ_top_ocmp (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- Splitting off the bottom factor of a descending product. -/
private theorem descProd_succ_bot_ocmp (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_ocmp, ih, descProd_succ_top_ocmp, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- Splitting a descending product into an upper and a lower part. -/
private theorem descProd_add_ocmp (g : ℕ → G) (a n k : ℕ) :
    descProd g a (n + k) = descProd g (a + k) n * descProd g a k := by
  induction n with
  | zero => simp [descProd_zero_ocmp]
  | succ n ih =>
    rw [show n + 1 + k = n + k + 1 by omega, descProd_succ_top_ocmp, ih, descProd_succ_top_ocmp,
      mul_assoc, show a + (n + k) = a + k + n by omega]

/-- A descending product read in increasing order of the list index. -/
private theorem descProd_eq_prod_range_ocmp (g : ℕ → G) (a n : ℕ) :
    descProd g a n = ((List.range n).map fun i ↦ g (a + n - 1 - i)).prod := by
  induction n with
  | zero => simp [descProd_zero_ocmp]
  | succ n ih =>
    rw [descProd_succ_top_ocmp, ih, List.range_succ_eq_map, List.map_cons, List.prod_cons,
      List.map_map]
    congr 2
    · refine List.map_congr_left fun i hi ↦ ?_
      simp only [Function.comp_apply]
      congr 1
      have := List.mem_range.1 hi
      omega

/-! ### The window in terms of the rounds (from `AJHandoff.TorusKnot.PairKPeriComp`) -/

/-- The products `w_1 ⋯ w_n` of the window. -/
private theorem pairWin_prefix_ocmp {r s : ℕ} (L : ℕ → G) (n : ℕ) (hn : 1 ≤ n)
    (hnr : n ≤ r - 1) :
    ((List.range n).map fun i ↦ pairWin r s L (i + 1)).prod =
      (descProd L (r - 1 - n) (n - 1))⁻¹ * (L (pairIdxB r s))⁻¹ := by
  induction n, hn using Nat.le_induction with
  | base => simp [pairWin, descProd_zero_ocmp]
  | succ n hn ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.map_singleton,
      List.prod_singleton]
    simp only [pairWin, show n + 1 ≠ 0 by omega, show n + 1 ≠ 1 by omega, ↓reduceIte]
    rw [show r - (n + 1) = r - 1 - n by omega, show n + 1 - 2 = n - 1 by omega,
      show r - 1 - (n + 1) = r - 2 - n by omega, show n + 1 - 1 = n - 1 + 1 by omega,
      descProd_succ_bot_ocmp, show r - 2 - n + 1 = r - 1 - n by omega]
    group

/-- The products `R_(s-1) ⋯ R_(s-n)` of the last rounds. -/
private theorem pairRound_suffix_ocmp {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (n : ℕ) (hn : 1 ≤ n) (hnr : n ≤ r - 1) :
    descProd (fun u ↦ L (pairIdxR r s u)) (s - n) n =
      (descProd L (r - 1 - n) (n - 1))⁻¹ * (L (pairIdxB r s))⁻¹ := by
  obtain ⟨hr, hrs, -⟩ := h
  have h2 := hL.climb (s + (r - 1 - n)) (by omega) (by omega)
  rw [show s + r - 2 - (s + (r - 1 - n)) = n - 1 by omega,
    show s + (r - 1 - n) - s = r - 1 - n by omega,
    show s + (r - 1 - n) + 1 - r = s - n by omega,
    show s + r - 1 - (s + (r - 1 - n)) = n by omega,
    show r - 2 = (n - 1) + (r - 1 - n) by omega, descProd_add_ocmp, Nat.zero_add] at h2
  have h3 : descProd (fun j ↦ L (pairIdxDp r s j)) (n - 1) (r - 1 - n) *
      descProd L 0 (r - 1 - n) = 1 := by
    rcases Nat.eq_zero_or_pos (r - 1 - n) with h0 | h0
    · rw [h0]
      simp [descProd_zero_ocmp]
    · have := hL.bot (r - 1 - n) h0 (by omega)
      rwa [show r - 2 - (r - 1 - n) = n - 1 by omega] at this
  have hd := eq_inv_of_mul_eq_one_left h3
  rw [hd] at h2
  calc _ = descProd L 0 (r - 1 - n) * ((descProd L 0 (r - 1 - n))⁻¹ *
        descProd (fun u ↦ L (pairIdxR r s u)) (s - n) n * L (pairIdxB r s) *
        (descProd L (r - 1 - n) (n - 1) * descProd L 0 (r - 1 - n))) *
        (descProd L 0 (r - 1 - n))⁻¹ * (descProd L (r - 1 - n) (n - 1))⁻¹ *
        (L (pairIdxB r s))⁻¹ := by group
    _ = _ := by rw [h2]; group

/-- The products `w_1 ⋯ w_n` are the products `R_(s-1) ⋯ R_(s-n)`. -/
private theorem pairWin_prefix_eq_round_ocmp {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (n : ℕ) (hnr : n ≤ r - 1) :
    ((List.range n).map fun i ↦ pairWin r s L (i + 1)).prod =
      descProd (fun u ↦ L (pairIdxR r s u)) (s - n) n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp [descProd_zero_ocmp]
  · rw [pairWin_prefix_ocmp L n h0 hnr, pairRound_suffix_ocmp h L hL n h0 hnr]

/-- The window entries are the rounds `w_j = y_(-j)`, `1 ≤ j ≤ r - 1`. -/
private theorem pairWin_eq_pairOrbY {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ r - 1) :
    pairWin r s L j = pairOrbY r s L (-(j : ℤ)) := by
  have hrs := h.2.1
  have hA := pairWin_prefix_eq_round_ocmp h L hL j hj
  have hB := pairWin_prefix_eq_round_ocmp h L hL (j - 1) (by omega)
  rw [show j = j - 1 + 1 by omega, List.range_succ, List.map_append, List.prod_append, hB,
    List.map_singleton, List.prod_singleton, descProd_succ_bot_ocmp,
    show s - (j - 1 + 1) + 1 = s - (j - 1) by omega] at hA
  rw [show j = j - 1 + 1 by omega, mul_left_cancel hA, ← pairOrbY_add_period,
    ← pairOrbY_natCast L (show s - (j - 1 + 1) < s by omega)]
  congr 1
  push_cast [Nat.cast_sub (show j - 1 + 1 ≤ s by omega)]
  ring

/-- The window entry `w_0 = y_0`. -/
private theorem pairWin_zero_eq {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) :
    pairWin r s L 0 = pairOrbY r s L 0 := by
  have hs : 0 < s := by have := h.2.1; omega
  rw [pairWin, ite_eq_left rfl]
  exact (pairOrbY_natCast L hs).symm

/-! ### The prefixes of the window -/

/-- The prefix `y_(-1) ⋯ y_(-n)` of the window. -/
private def winPre (r s : ℕ) (L : ℕ → G) (n : ℕ) : G :=
  ((List.range n).map fun i : ℕ ↦ pairOrbY r s L (-((i : ℤ) + 1))).prod

/-- The products `w_1 ⋯ w_n` are the prefixes `y_(-1) ⋯ y_(-n)`. -/
private theorem pairWin_prefix_eq_winPre {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (n : ℕ) (hn : n ≤ r - 1) :
    ((List.range n).map fun i ↦ pairWin r s L (i + 1)).prod = winPre r s L n := by
  unfold winPre
  congr 1
  refine List.map_congr_left fun i hi ↦ ?_
  have := List.mem_range.1 hi
  rw [pairWin_eq_pairOrbY h L hL (i + 1) (by omega) (by omega)]
  push_cast
  rfl

/-- The windows `y_0 y_(-1) ⋯ y_(1-r)` and `y_1 y_0 y_(-1) ⋯ y_(2-r)` give `K`. -/
private theorem pairOrbK_winPre {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbK r s L = pairOrbY r s L 0 * winPre r s L (r - 1) ∧
      pairOrbK r s L = pairOrbY r s L 1 * pairOrbY r s L 0 * winPre r s L (r - 2) := by
  have hr : 2 ≤ r := h.1
  have key : ∀ p : ℤ, pairOrbK r s L =
      ((List.range r).map fun i : ℕ ↦ pairOrbY r s L (p + r - 1 - i)).prod := fun p ↦ by
    rw [← pairOrb_window h hL p, descProd_eq_prod_range_ocmp]
    congr 1
    refine List.map_congr_left fun i hi ↦ ?_
    have := List.mem_range.1 hi
    congr 1
    omega
  have hr1 : List.range r = List.range (r - 1 + 1) := by congr 1; omega
  have hr2 : List.range r = List.range (r - 2 + 1 + 1) := by congr 1; omega
  unfold winPre
  refine ⟨?_, ?_⟩
  · rw [key (1 - r), hr1, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    simp only [Function.comp_def, Nat.succ_eq_add_one]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      refine List.map_congr_left fun i _ ↦ ?_
      congr 1
      push_cast
      ring
  · rw [key (2 - r), hr2, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map,
      List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, ← mul_assoc]
    simp only [Function.comp_def, Nat.succ_eq_add_one]
    congr 1
    · congr 1
      · congr 1
        push_cast
        ring
      · congr 1
        push_cast
        ring
    · congr 1
      refine List.map_congr_left fun i _ ↦ ?_
      congr 1
      push_cast
      ring

/-! ### The companion tuple -/

/-- The first entry of the companion tuple is `z_0 = y_0⁻¹ y_1 y_0`. -/
theorem pairOrb_compFun_zero {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairCompFun r s L 0 = (pairOrbY r s L 0)⁻¹ * pairOrbY r s L 1 * pairOrbY r s L 0 := by
  have hr : 2 ≤ r := h.1
  obtain ⟨h1, h2⟩ := pairOrbK_winPre h hL
  have hlast : winPre r s L (r - 1) =
      winPre r s L (r - 2) * pairOrbY r s L (-((r - 1 : ℕ) : ℤ)) := by
    unfold winPre
    rw [show r - 1 = r - 2 + 1 by omega, List.range_succ, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]
    congr 2
  rw [pairCompFun, Nat.sub_zero, Nat.sub_zero, pairWin_prefix_eq_winPre h L hL _ (by omega),
    pairWin_eq_pairOrbY h L hL _ (by omega) le_rfl]
  rw [hlast, h2] at h1
  have e : winPre r s L (r - 2) * pairOrbY r s L (-((r - 1 : ℕ) : ℤ)) =
      (pairOrbY r s L 0)⁻¹ * pairOrbY r s L 1 * pairOrbY r s L 0 * winPre r s L (r - 2) := by
    calc _ = (pairOrbY r s L 0)⁻¹ * (pairOrbY r s L 0 *
          (winPre r s L (r - 2) * pairOrbY r s L (-((r - 1 : ℕ) : ℤ)))) := by group
      _ = _ := by rw [← h1]; group
  calc _ = winPre r s L (r - 2) * pairOrbY r s L (-((r - 1 : ℕ) : ℤ)) *
        (winPre r s L (r - 2))⁻¹ := by group
    _ = _ := by rw [e]; group

/-- The entries `z_k = W_(r-1-k) W_(r-2-k)⁻¹` for `k ≤ r - 2`, `W_n = w_1 ⋯ w_n`. -/
private theorem pairCompFun_telescope {r s : ℕ} (L : ℕ → G) {k : ℕ} (hk : k + 2 ≤ r) :
    pairCompFun r s L k =
      ((List.range (r - 1 - k)).map fun i ↦ pairWin r s L (i + 1)).prod *
        (((List.range (r - 2 - k)).map fun i ↦ pairWin r s L (i + 1)).prod)⁻¹ := by
  rw [pairCompFun, show r - 1 - k = r - 2 - k + 1 by omega, List.range_succ, List.map_append,
    List.prod_append, List.map_singleton, List.prod_singleton]

/-- The product `z_0 ⋯ z_(n-1)` telescopes. -/
private theorem pairCompFun_prod_range {r s : ℕ} (L : ℕ → G) (hr : 2 ≤ r) {n : ℕ}
    (hn : n ≤ r - 1) :
    ((List.range n).map (pairCompFun r s L)).prod =
      ((List.range (r - 1)).map fun i ↦ pairWin r s L (i + 1)).prod *
        (((List.range (r - 1 - n)).map fun i ↦ pairWin r s L (i + 1)).prod)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.map_singleton,
      List.prod_singleton, pairCompFun_telescope L (by omega),
      show r - 2 - n = r - 1 - (n + 1) by omega]
    group

/-- The product of the companion tuple is `y_0⁻¹ K y_0`. -/
private theorem pairCompTuple_prod {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    ((List.finRange r).map (pairCompTuple r s L)).prod =
      (pairOrbY r s L 0)⁻¹ * pairOrbK r s L * pairOrbY r s L 0 := by
  have hr : 2 ≤ r := h.1
  have hmap : (List.finRange r).map (pairCompTuple r s L) =
      (List.range r).map (pairCompFun r s L) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [hmap, show List.range r = List.range (r - 1 + 1) by congr 1; omega, List.range_succ,
    List.map_append, List.prod_append, pairCompFun_prod_range L hr le_rfl, List.map_singleton,
    List.prod_singleton, Nat.sub_self, List.range_zero, List.map_nil, List.prod_nil,
    inv_one, mul_one, pairWin_prefix_eq_winPre h L hL _ le_rfl, (pairOrbK_winPre h hL).1]
  have hz : pairCompFun r s L (r - 1) = pairOrbY r s L 0 := by
    rw [pairCompFun, show r - 2 - (r - 1) = 0 by omega, Nat.sub_self, pairWin_zero_eq h L]
    simp
  rw [hz]
  group

/-- Powers of a conjugate by an inverse. -/
private theorem inv_conj_zpow_ocmp (a b : G) (i : ℤ) : (a⁻¹ * b * a) ^ i = a⁻¹ * b ^ i * a := by
  simpa only [inv_inv] using (conj_zpow : (a⁻¹ * b * a⁻¹⁻¹) ^ i = _)

/-- The companion longitude is `Λ = y_0⁻¹ K^s y_1^(-rs) y_0`. -/
theorem pairOrb_compLong {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L) :
    pairCompLong r s L = (pairOrbY r s L 0)⁻¹ * pairOrbK r s L ^ (s : ℤ) *
      pairOrbY r s L 1 ^ (-((r * s : ℕ) : ℤ)) * pairOrbY r s L 0 := by
  rw [pairCompLong, pairCompTuple_prod h hL, pairOrb_compFun_zero h hL, ← zpow_natCast,
    inv_conj_zpow_ocmp, inv_conj_zpow_ocmp]
  group

end AJConjecture
