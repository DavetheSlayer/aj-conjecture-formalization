import Mathlib
import AJHandoff.TorusKnot.PairKOrbRounds

/-!
# Pure forms of the strand loops: runs, window and staircase

For block loops with the gap relations, every strand loop `pairOrbCore r s L t` with
`r - 1 ≤ t ≤ T`, `t ≠ pairOrbH1`, is pure in the frame of `y_0`:
`y_0 · core(t) · y_0⁻¹ = K ^ w(t) * y_(ℓ(P t)) ^ n(t)`. Region by region (`Q = y_(r-2) ⋯ y_1`,
`D = Q y_0`, so `K = y_(r-1) D` and `D y_(-1) D⁻¹ = y_(r-1)`):

* decreasing run: `1` (the gap relation `run`);
* increasing run and `b₀`: `Q y_0 y_(-1) y_0⁻¹ Q⁻¹ = y_(r-1)`;
* window foot `b₀ + p`: `y_(r-1-p)`;
* bottom `2c - s` of the staircase: `y_(-1) D⁻¹ = K⁻¹ y_(r-1)²`;
* staircase `T - u`, `1 ≤ u ≤ s - 2`: `y_u K⁻¹ = K⁻¹ y_(u+r)`;
* `T` (without `H₂`): `y_0 y_0 K⁻¹ = K⁻¹ y_r²`.

Route: unfold `pairOrbCore`, `pairOrbW`, `pairOrbN`, `pairOrbLab`, `pairOrbPerm` on the region
(`split_ifs` with `omega` and the arithmetic of the pair), rewrite with `pairOrb_climbs`,
`pairOrb_runs`, `pairOrb_window` / `pairOrbK_zpow_conj`, and close with `group`. Checked exactly
in the torus knot group (`AJHandoff.TorusKnot.PairKOrbDefs`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Descending products and the window -/

/-- Splitting off the top factor of a descending product. -/
private theorem descProd_succ_top_ptop (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- Splitting off the bottom factor of a descending product. -/
private theorem descProd_succ_bot_ptop (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_ptop, ih, descProd_succ_top_ptop, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_ptop (g g' : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = g' (b + i)) : descProd g a n = descProd g' b n := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_ptop, descProd_succ_top_ptop, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-- A descending product from `0` of length `n + 2`, top and bottom factors split off. -/
private theorem descProd_two_ptop (g : ℕ → G) (n : ℕ) :
    descProd g 0 (n + 2) = g (n + 1) * descProd g 1 n * g 0 := by
  rw [descProd_succ_top_ptop, descProd_succ_bot_ptop, zero_add, mul_assoc]

/-- A descending product from `0` of length `n + 2`, two bottom factors split off. -/
private theorem descProd_two_bot_ptop (g : ℕ → G) (n : ℕ) :
    descProd g 0 (n + 2) = descProd g 2 n * g 1 * g 0 := by
  rw [descProd_succ_bot_ptop, descProd_succ_bot_ptop]

/-- The two windows `y_(r-1) ⋯ y_0` and `y_(r-2) ⋯ y_0 y_(-1)` give `K`. -/
private theorem pairOrbK_windows_ptop {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbK r s L = pairOrbY r s L ((r - 1 : ℕ) : ℤ) *
        descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0 ∧
      pairOrbK r s L = descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0 *
        pairOrbY r s L (-1) := by
  have hr : 2 ≤ r := h.1
  refine ⟨?_, ?_⟩
  · have e := descProd_two_ptop (fun k : ℕ ↦ pairOrbY r s L ((0 : ℤ) + k)) (r - 2)
    rw [show r - 2 + 2 = r by omega, pairOrb_window h hL 0, show r - 2 + 1 = r - 1 by omega] at e
    rw [e]
    simp only [zero_add, Nat.cast_zero]
  · have e := descProd_two_bot_ptop (fun k : ℕ ↦ pairOrbY r s L ((-1 : ℤ) + k)) (r - 2)
    rw [show r - 2 + 2 = r by omega, pairOrb_window h hL (-1)] at e
    rw [e]
    congr 1
    · congr 1
      · refine descProd_congr_ptop _ _ _ _ _ fun i _ ↦ ?_
        congr 1
        push_cast
        ring

/-- The window relation `y_(r-1) = D y_(-1) D⁻¹` with `D = y_(r-2) ⋯ y_0`. -/
private theorem pairOrbY_window_ptop {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbY r s L ((r - 1 : ℕ) : ℤ) =
      descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0 * pairOrbY r s L (-1) *
        (descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0)⁻¹ := by
  obtain ⟨h0, h1⟩ := pairOrbK_windows_ptop h hL
  rw [← h1, h0]
  group

/-- The round `R_(s-1)` is `y_(-1)`. -/
private theorem pairOrbY_last_ptop {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) :
    L (pairIdxR r s (s - 1)) = pairOrbY r s L (-1) := by
  have hs : 1 ≤ s := by have := h.2.1; omega
  rw [← pairOrbY_natCast L (show s - 1 < s by omega), ← pairOrbY_add_period r s L (-1)]
  congr 1
  push_cast [Nat.cast_sub hs]
  ring

/-- The arithmetic facts used for the region analysis. -/
private theorem pureTop_arith {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ s + r ≤ pairC r s + 2 ∧ pairTop r s = 2 * pairC r s - 1 ∧
      pairOrbH1 r s = 2 * pairC r s - s - 1 := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have : 1 ≤ pairRunDown r s := by unfold pairRunDown; omega
  exact ⟨hr, hrs, by omega, rfl, rfl⟩

/-! ### The regions -/

/-- The decreasing run. -/
private theorem pureTop_decRun {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {t : ℕ} (h1 : r ≤ t + 1) (h3 : t + s ≤ pairC r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
  obtain ⟨hr, hrs, hsc, hT, hH⟩ := pureTop_arith h
  have hc : pairOrbCore r s L t = descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) *
      L (pairIdxR r s (s - 1)) * L (pairIdxRun r s t) * descProd L 0 (r - 2) := by
    unfold pairOrbCore
    split_ifs <;> first | omega | rfl
  have hW : pairOrbW r s t = 0 := by
    unfold pairOrbW
    split_ifs <;> omega
  have hN : pairOrbN r s t = 0 := by
    unfold pairOrbN
    split_ifs <;> omega
  rw [hc, hL.run t (by omega) (by omega), hW, hN]
  simp [pairOrbConj]

/-- The increasing run and `b₀`. -/
private theorem pureTop_incRun {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {t : ℕ} (h3 : pairC r s < t + s) (h4 : t + s + r ≤ 2 * pairC r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
  obtain ⟨hr, hrs, hsc, hT, hH⟩ := pureTop_arith h
  have hc : pairOrbCore r s L t = descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) *
      L (pairIdxR r s (s - 1)) * descProd L 0 (r - 2) := by
    unfold pairOrbCore
    split_ifs <;> first | omega | rfl
  have hW : pairOrbW r s t = 0 := by
    unfold pairOrbW
    split_ifs <;> omega
  have hN : pairOrbN r s t = 1 := by
    unfold pairOrbN
    split_ifs <;> omega
  have hP : pairOrbLab r s (pairOrbPerm r s t) = r - 1 := by
    unfold pairOrbPerm
    split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
  obtain ⟨-, hA, hD⟩ := pairOrb_climbs h hL
  have hD' := hD (r - 2) le_rfl
  rw [Nat.sub_self] at hD'
  rw [hc, hW, hN, hP, hD', hA (r - 2) le_rfl, pairOrbY_last_ptop h L, pairOrbY_window_ptop h hL]
  unfold pairOrbConj
  group

/-- The feet of the window. -/
private theorem pureTop_foot {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {t : ℕ} (h4 : 2 * pairC r s < t + s + r)
    (h5 : t + s + 2 ≤ 2 * pairC r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
  obtain ⟨hr, hrs, hsc, hT, hH⟩ := pureTop_arith h
  have hc : pairOrbCore r s L t = descProd (fun j ↦ L (pairIdxDp r s j))
      (pairOrbFoot r s t - 1) (r - 1 - pairOrbFoot r s t) *
      descProd L 0 (r - 2 - pairOrbFoot r s t) := by
    unfold pairOrbCore
    split_ifs <;> first | omega | rfl
  have hW : pairOrbW r s t = 0 := by
    unfold pairOrbW
    split_ifs <;> omega
  have hN : pairOrbN r s t = 1 := by
    unfold pairOrbN
    split_ifs <;> omega
  have hp : pairOrbFoot r s t = t + s + r - 2 * pairC r s := rfl
  have hP : pairOrbLab r s (pairOrbPerm r s t) = 1 + (r - 2 - pairOrbFoot r s t) := by
    unfold pairOrbPerm
    split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
  obtain ⟨-, hA, hD⟩ := pairOrb_climbs h hL
  have hD' := hD (r - 1 - pairOrbFoot r s t) (by omega)
  rw [show r - 2 - (r - 1 - pairOrbFoot r s t) = pairOrbFoot r s t - 1 by omega] at hD'
  rw [hc, hW, hN, hP, hD', hA _ (by omega),
    show r - 1 - pairOrbFoot r s t = r - 2 - pairOrbFoot r s t + 1 by omega,
    descProd_succ_top_ptop]
  unfold pairOrbConj
  push_cast
  group

/-- The bottom `2c - s` of the staircase. -/
private theorem pureTop_stairBot {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {t : ℕ} (h6 : t + s = 2 * pairC r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
  obtain ⟨hr, hrs, hsc, hT, hH⟩ := pureTop_arith h
  have hc : pairOrbCore r s L t =
      L (pairIdxC r s) * L (pairIdxR r s (s - 1)) * descProd L 0 (r - 2) := by
    unfold pairOrbCore
    split_ifs <;> first | omega | rfl
  have hW : pairOrbW r s t = -1 := by
    unfold pairOrbW
    split_ifs <;> omega
  have hN : pairOrbN r s t = 2 := by
    unfold pairOrbN
    split_ifs <;> omega
  have hP : pairOrbLab r s (pairOrbPerm r s t) = r - 1 := by
    unfold pairOrbPerm
    split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
  obtain ⟨hC, hA, -⟩ := pairOrb_climbs h hL
  rw [hc, hW, hN, hP, hC, hA (r - 2) le_rfl, pairOrbY_last_ptop h L,
    (pairOrbK_windows_ptop h hL).2, pairOrbY_window_ptop h hL, conj_zpow]
  unfold pairOrbConj
  group

/-- The inner staircase `T - u`, `1 ≤ u ≤ s - 2`. -/
private theorem pureTop_stair {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {t : ℕ} (h6 : 2 * pairC r s < t + s) (h7 : t + 1 < 2 * pairC r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
  obtain ⟨hr, hrs, hsc, hT, hH⟩ := pureTop_arith h
  have hc : pairOrbCore r s L t = L (pairIdxC r s) * L (pairIdxR r s (pairTop r s - t)) *
      L (pairIdxB r s) * descProd L 0 (r - 2) := by
    unfold pairOrbCore
    split_ifs <;> first | omega | rfl
  have hW : pairOrbW r s t = -1 := by
    unfold pairOrbW
    split_ifs <;> omega
  have hN : pairOrbN r s t = 1 := by
    unfold pairOrbN
    split_ifs <;> omega
  have hPt : pairOrbPerm r s t = t - r := by
    unfold pairOrbPerm
    split_ifs <;> omega
  have hlab : pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) =
      pairOrbY r s L (((pairTop r s - t : ℕ) : ℤ) + r * 1) := by
    rw [hPt]
    unfold pairOrbLab
    split_ifs with c1 c2 c3 c4
    · omega
    · omega
    · rw [← pairOrbY_add_period r s L]
      congr 1
      have e : 2 * pairC r s - s - 1 - (t - r) + s = pairTop r s - t + r := by omega
      rw [mul_one]
      exact_mod_cast e
    · congr 1
      have e : pairTop r s - (t - r) = pairTop r s - t + r := by omega
      rw [mul_one]
      exact_mod_cast e
    · omega
  obtain ⟨hC, hA, -⟩ := pairOrb_climbs h hL
  rw [hc, hW, hN, hlab, ← pairOrbK_zpow_conj h hL, hC, hA (r - 2) le_rfl, (pairOrb_runs h hL).1,
    pairOrbY_natCast L (show pairTop r s - t < s by omega), (pairOrbK_windows_ptop h hL).2]
  unfold pairOrbConj
  group

/-- The top strand `T` (without the second Hopf loop). -/
private theorem pureTop_top {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {t : ℕ} (h8 : t = pairTop r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
  obtain ⟨hr, hrs, hsc, hT, hH⟩ := pureTop_arith h
  have hc : pairOrbCore r s L t =
      L (pairIdxR r s 0) * L (pairIdxB r s) * descProd L 0 (r - 2) := by
    unfold pairOrbCore
    split_ifs <;> first | omega | rfl
  have hW : pairOrbW r s t = -1 := by
    unfold pairOrbW
    split_ifs <;> omega
  have hN : pairOrbN r s t = 2 := by
    unfold pairOrbN
    split_ifs <;> omega
  have hP : pairOrbLab r s (pairOrbPerm r s t) = r := by
    unfold pairOrbPerm
    split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
  have hY : pairOrbY r s L (r : ℕ) = pairOrbK r s L * pairOrbY r s L 0 *
      (pairOrbK r s L)⁻¹ := by
    have e := pairOrbK_zpow_conj h hL 0 1
    rw [zpow_one, zpow_neg_one] at e
    rw [e]
    simp
  have hR0 : L (pairIdxR r s 0) = pairOrbY r s L 0 :=
    (pairOrbY_natCast L (show 0 < s by omega)).symm
  obtain ⟨-, hA, -⟩ := pairOrb_climbs h hL
  rw [hc, hW, hN, hP, hY, conj_zpow, hA (r - 2) le_rfl, (pairOrb_runs h hL).1, hR0,
    (pairOrbK_windows_ptop h hL).2]
  unfold pairOrbConj
  simp only [zpow_two]
  group

/-- The strand loops of the runs, the window and the staircase are pure. -/
theorem pairOrb_pure_top {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L)
    {t : ℕ} (h1 : r ≤ t + 1) (h2 : t ≤ pairTop r s) (hH : t ≠ pairOrbH1 r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
  obtain ⟨hr, hrs, hsc, hT, hH1⟩ := pureTop_arith h
  rw [hH1] at hH
  rw [hT] at h2
  by_cases h3 : t + s ≤ pairC r s
  · exact pureTop_decRun h hL h1 h3
  by_cases h4 : t + s + r ≤ 2 * pairC r s
  · exact pureTop_incRun h hL (by omega) h4
  by_cases h5 : t + s + 2 ≤ 2 * pairC r s
  · exact pureTop_foot h hL (by omega) h5
  by_cases h6 : t + s = 2 * pairC r s
  · exact pureTop_stairBot h hL h6
  by_cases h7 : t + 1 < 2 * pairC r s
  · exact pureTop_stair h hL (by omega) h7
  · exact pureTop_top h hL (by omega)

end AJConjecture
