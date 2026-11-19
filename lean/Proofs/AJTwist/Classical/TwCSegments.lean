import Mathlib
import AJHandoff.TorusKnot.PairKOrbSegments
import AJTwist.Classical.TwCBlocks

/-!
# The twisted orbit segments for abstract loops

In the twisted block lists the two strands that pass the head block collect a power of the chain
loop `L = L 0` that differs from the untwisted one: the strand that climbs from the level `0` to
`j₀ = twHeadTop r s` collects `L^(1-ℓ)` instead of `L`, the strand that descends from `j₀` to `0`
collects `L^ℓ` instead of `1` (`twChain_detour`). The head block is the first block, so its
loop is the last factor of every strand loop: the two strand loops are multiplied on the right
by `L^(-ℓ)` and `L^ℓ` (`twcDefect`). The first strand is the last one of the orbit of `0` (in
the bottom block of positions), the second one lies in the top block.

In the frame of the round `y_0` (`pairOrbConj`), `L 0` is `y_1⁻¹` (`twcHead_conj`), and `1` is
the label of both `0` and `j₀`; so the two pure forms `K ^ w(t) y ^ n(t)` of
`AJHandoff.TorusKnot.PairKOrbStrand` keep their shape with `n(t)` replaced by `n(t) + ℓ` and
`n(t) - ℓ`. The sums over the bottom and the top block become `-rs + ℓ` and `rs - ℓ`:

* `twcSeg_GU`, `twcSeg_UG`: the bottom block gives `K^s y_1^(-rs+ℓ)`, resp. `K^s y_0^(-rs+ℓ)`;
* `twcSeg_M`: the top block gives `K^(-s) y_0^(rs-ℓ)`;
* `twcSeg_U`: the last piece is pure.

These are `pairOrb_seg_GU`, `pairOrb_seg_UG`, `pairOrb_seg_M`, `pairOrb_seg_U`
(`AJHandoff.TorusKnot.PairKOrbSegments`) for abstract loops satisfying the gap relations, with
the defect. Route: as there, with `pairOrb_step` for every strand, `pairOrb_pure_prod`,
`pairOrb_sum_top/bot`, `pairOrb_sum_top_val/bot_val`. The two modified strands are the unique
positions `t` with `pairOrbPerm r s t = 0` (not in `PairOrbTop`) and with
`pairOrbPerm r s t = j₀` (`t = 2c - s - 2` for `r ≥ 3`, `t = 2c - s` for `r = 2`; in
`PairOrbTop`, different from `pairOrbH1`); `pairOrbLab r s 0 = 1 = pairOrbLab r s j₀`. For
`twcHead_conj`: for `r ≥ 3` the head block is the first left climb, `L 0 = y_0⁻¹ y_1⁻¹ y_0`
(`pairOrb_climbs` at `n = 1`); for `r = 2` it is the run letter, `L 0 = y_(-1)⁻¹`
(`pairOrb_runs`) and `y_1 y_0 = K = y_0 y_(-1)` (`pairOrb_window`).

Checked numerically with the loops of `SU(2)` representations of the groups of `twBlocks`
(`SCR/C/py/w2_twk_all.py`: `(2,3)`, `ℓ ∈ {-2, -1, 1}`; `(3,4)`, `ℓ ∈ {-2, -1, 1, 2}`; both
clasp signs among them): the four displayed identities to `10⁻¹³`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The correction of the strand loop of the position `t` in a twisted block list: `L^(-ℓ)` for
the strand whose bottom position is `0`, `L^ℓ` for the one whose bottom position is the upper
level `j₀` of the head block; `L = L 0` is the loop of the chain. -/
def twcDefect (r s : ℕ) (ℓ : ℤ) (L : ℕ → G) (t : ℕ) : G :=
  if pairOrbPerm r s t = 0 then L 0 ^ (-ℓ)
  else if pairOrbPerm r s t = twHeadTop r s then L 0 ^ ℓ else 1

/-- The strand loop of the position `t` of a twisted block list, without the Hopf loops. -/
def twcCore (r s : ℕ) (ℓ : ℤ) (L : ℕ → G) (t : ℕ) : G :=
  pairOrbCore r s L t * twcDefect r s ℓ L t

/-- The product of the twisted strand loops along the orbit of `0` of `pairBlocks r s`, from
the index `a` to `b - 1`. -/
def twcSeg (r s : ℕ) (ℓ : ℤ) (L : ℕ → G) (a b : ℕ) : G :=
  ((List.range (b - a)).map fun k ↦ twcCore r s ℓ L (pairOrbT r s (a + k))).prod

/-- In the frame of `y_0` the loop of the head block is `y_1⁻¹`. -/
theorem twcHead_conj {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L) :
    pairOrbConj r s L (L 0) = (pairOrbY r s L 1)⁻¹ := by
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  by_cases h2 : r = 2
  · subst h2
    have hc : pairC 2 s = s := by simp [pairC]
    have hrun : pairIdxRun 2 s 1 = 0 := by simp [pairIdxRun, pairRunDown]
    have hL0 := (pairOrb_runs h hL).2 1 (by omega) (by omega)
    rw [hrun] at hL0
    have w0 := pairOrb_window h hL 0
    have w1 := pairOrb_window h hL (-1)
    simp only [descProd, List.range_succ, List.range_zero, List.nil_append, List.reverse_cons,
      List.reverse_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Nat.cast_zero, Nat.cast_one, add_zero, zero_add, List.singleton_append,
      neg_add_cancel] at w0 w1
    have hy : pairOrbY 2 s L 1 = pairOrbY 2 s L 0 * pairOrbY 2 s L (-1) * (pairOrbY 2 s L 0)⁻¹ := by
      rw [← w0] at w1
      rw [w1]
      group
    rw [pairOrbConj, hL0, hy]
    group
  · have hA := (pairOrb_climbs h hL).2.1 1 (by omega)
    simp only [descProd, List.range_one, List.reverse_singleton, List.map_singleton,
      List.prod_singleton, Nat.add_zero, Nat.cast_one] at hA
    rw [pairOrbConj, hA]
    group

/-- The position `j₀` on the orbit: it is not `0`, lies in the top block off `T`, and has the
label `1`, as `0`. -/
private theorem twHeadTop_orb_twCSegments {r s : ℕ} (h : IsTorusPair r s) :
    twHeadTop r s ≠ 0 ∧ twHeadTop r s < pairStrands r s ∧ PairOrbTop r s (twHeadTop r s) ∧
      twHeadTop r s ≠ pairTop r s ∧ pairOrbLab r s (twHeadTop r s) = 1 ∧
      pairOrbLab r s 0 = 1 := by
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hl0 : pairOrbLab r s 0 = 1 := by
    unfold pairOrbLab
    rw [ite_eq_left (by omega)]
  by_cases h2 : r = 2
  · subst h2
    have hc : pairC 2 s = s := by simp [pairC]
    have hj : twHeadTop 2 s = 1 := by simp [twHeadTop]
    rw [hj]
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega, ?_, hl0⟩
    unfold pairOrbLab
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  · have hj : twHeadTop r s = 2 * pairC r s - 2 := by
      rw [twHeadTop, ite_eq_right h2, hT]
      omega
    rw [hj]
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega, ?_, hl0⟩
    unfold pairOrbLab
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
    omega

/-- The power of the round in the pure form of the twisted strand loop of the `k`-th strand of
the orbit. -/
private def twcOrbN_twCSegments (r s : ℕ) (ℓ : ℤ) (k : ℕ) : ℤ :=
  pairOrbN r s (pairOrbT r s k) +
    if pairOrbT r s (k + 1) = 0 then ℓ
    else if pairOrbT r s (k + 1) = twHeadTop r s then -ℓ else 0

/-- The pure step of the twisted loop of the `k`-th strand of the orbit. -/
private theorem twc_step_twCSegments {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) (k : ℕ) (hk : pairOrbT r s k ≠ pairOrbH1 r s) :
    pairOrbConj r s L (twcCore r s ℓ L (pairOrbT r s k)) =
      pairOrbK r s L ^ pairOrbW r s (pairOrbT r s k) *
        pairOrbY r s L (pairOrbLab r s (pairOrbT r s (k + 1))) ^
          twcOrbN_twCSegments r s ℓ k := by
  obtain ⟨-, -, -, -, hlabJ, hlab0⟩ := twHeadTop_orb_twCSegments h
  have hstep := (pairOrb_step h hL k hk).1
  have hperm : pairOrbPerm r s (pairOrbT r s k) = pairOrbT r s (k + 1) := by
    rw [pairOrbT_succ, stPerm_pairBlocks_orb h (pairOrbT_lt h k)]
  have hhead := twcHead_conj h hL
  have hc : ∀ x y : G, pairOrbConj r s L (x * y) = pairOrbConj r s L x * pairOrbConj r s L y := by
    intro x y
    unfold pairOrbConj
    group
  have hz : ∀ (x : G) (n : ℤ), pairOrbConj r s L (x ^ n) = pairOrbConj r s L x ^ n := by
    intro x n
    unfold pairOrbConj
    rw [conj_zpow]
  rw [twcCore, hc, hstep, twcDefect, hperm, twcOrbN_twCSegments]
  by_cases h0 : pairOrbT r s (k + 1) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, hz, hhead, h0, hlab0, zpow_add, inv_zpow, zpow_neg,
      inv_inv, mul_assoc]
    rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hj : pairOrbT r s (k + 1) = twHeadTop r s
    · rw [ite_eq_left hj, ite_eq_left hj, hz, hhead, hj, hlabJ, zpow_add, inv_zpow, zpow_neg,
        mul_assoc]
      rfl
    · rw [ite_eq_right hj, ite_eq_right hj, add_zero]
      unfold pairOrbConj
      group

/-- A product of twisted strand loops along the orbit avoiding `pairOrbH1` is a pure step. -/
private theorem twcSeg_pure_twCSegments {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) {a b : ℕ} (hab : a ≤ b)
    (hH : ∀ k, a ≤ k → k < b → pairOrbT r s k ≠ pairOrbH1 r s) :
    pairOrbConj r s L (twcSeg r s ℓ L a b) =
        pairOrbK r s L ^ (∑ k ∈ Finset.Ico a b, pairOrbW r s (pairOrbT r s k)) *
          pairOrbY r s L (pairOrbLab r s (pairOrbT r s b)) ^
            (∑ k ∈ Finset.Ico a b, twcOrbN_twCSegments r s ℓ k) ∧
      pairOrbY r s L (pairOrbLab r s (pairOrbT r s a)) =
        pairOrbK r s L ^ (∑ k ∈ Finset.Ico a b, pairOrbW r s (pairOrbT r s k)) *
          pairOrbY r s L (pairOrbLab r s (pairOrbT r s b)) *
          pairOrbK r s L ^ (-∑ k ∈ Finset.Ico a b, pairOrbW r s (pairOrbT r s k)) := by
  rw [twcSeg, pairOrbConj_prod, List.map_map]
  exact pairOrb_pure_prod (pairOrbK r s L)
    (fun k ↦ pairOrbConj r s L (twcCore r s ℓ L (pairOrbT r s k)))
    (fun k ↦ pairOrbY r s L (pairOrbLab r s (pairOrbT r s k)))
    (fun k ↦ pairOrbW r s (pairOrbT r s k)) (fun k ↦ twcOrbN_twCSegments r s ℓ k) hab
    (fun k h1 h2 ↦ twc_step_twCSegments h ℓ hL k (hH k h1 h2))
    (fun k h1 h2 ↦ (pairOrb_step h hL k (hH k h1 h2)).2)

/-- The index of `j₀` on the orbit lies strictly after that of `T` and not after that of
`pairOrbH1`. -/
private theorem twHeadTop_idx_twCSegments {r s : ℕ} (h : IsTorusPair r s) :
    pairOrbIdx r s (pairTop r s) < pairOrbIdx r s (twHeadTop r s) ∧
      pairOrbIdx r s (twHeadTop r s) ≤ pairOrbIdx r s (pairOrbH1 r s) := by
  obtain ⟨-, hJm, hJtop, hJT, -, -⟩ := twHeadTop_orb_twCSegments h
  obtain ⟨hiJ, hJs⟩ := pairOrbIdx_spec h hJm
  have htop := (pairOrb_top_iff h hiJ).1 (by rw [hJs]; exact hJtop)
  refine ⟨lt_of_le_of_ne htop.1 fun he ↦ hJT ?_, htop.2⟩
  have hTm : pairTop r s < pairStrands r s := by simp only [pairTop, pairStrands]; omega
  rw [← hJs, ← he, (pairOrbIdx_spec h hTm).2]

/-- The sum of the exponents of the twisted strand loops along a piece of the orbit. -/
private theorem twc_sum_twCSegments {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {a b : ℕ}
    (hb : b ≤ pairStrands r s) :
    ∑ k ∈ Finset.Ico a b, twcOrbN_twCSegments r s ℓ k =
      ∑ k ∈ Finset.Ico a b, pairOrbN r s (pairOrbT r s k) +
        ((if pairStrands r s - 1 ∈ Finset.Ico a b then ℓ else 0) +
          if pairOrbIdx r s (twHeadTop r s) - 1 ∈ Finset.Ico a b then -ℓ else 0) := by
  obtain ⟨hJ0, hJm, -, -, -, -⟩ := twHeadTop_orb_twCSegments h
  obtain ⟨hiJ, hJs⟩ := pairOrbIdx_spec h hJm
  have hiJ1 := (twHeadTop_idx_twCSegments h).1
  have hm : 0 < pairStrands r s := Nat.succ_pos _
  have hδ : ∀ k ∈ Finset.Ico a b,
      (if pairOrbT r s (k + 1) = 0 then ℓ
        else if pairOrbT r s (k + 1) = twHeadTop r s then -ℓ else 0) =
      (if k = pairStrands r s - 1 then ℓ else 0) +
        if k = pairOrbIdx r s (twHeadTop r s) - 1 then -ℓ else 0 := by
    intro k hk
    have hkm : k < pairStrands r s := by
      rw [Finset.mem_Ico] at hk
      omega
    have hA : pairOrbT r s (k + 1) = 0 ↔ k = pairStrands r s - 1 := by
      constructor
      · intro he
        by_contra hne
        exact absurd (pairOrbT_injOn h (show k + 1 < pairStrands r s by omega) hm he)
          (Nat.succ_ne_zero k)
      · intro he
        rw [show k + 1 = pairStrands r s by omega, pairOrbT_strands h]
    have hB : pairOrbT r s (k + 1) = twHeadTop r s ↔
        k = pairOrbIdx r s (twHeadTop r s) - 1 := by
      constructor
      · intro he
        by_cases hk1 : k + 1 = pairStrands r s
        · rw [hk1, pairOrbT_strands h] at he
          exact absurd he.symm hJ0
        · have := pairOrbT_injOn h (show k + 1 < pairStrands r s by omega) hiJ (he.trans hJs.symm)
          omega
      · intro he
        rw [show k + 1 = pairOrbIdx r s (twHeadTop r s) by omega, hJs]
    simp only [hA, hB]
    split_ifs <;> omega
  simp only [twcOrbN_twCSegments]
  rw [Finset.sum_add_distrib, Finset.sum_congr rfl hδ, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- The labels at the ends of the orbit pieces. -/
private theorem twc_seg_labs_twCSegments {r s : ℕ} (h : IsTorusPair r s) :
    pairOrbLab r s (pairOrbT r s 0) = 1 ∧ pairOrbLab r s (pairOrbT r s (pairStrands r s)) = 1 ∧
      pairOrbLab r s (pairOrbT r s (pairOrbIdx r s (pairTop r s))) = 0 ∧
      pairOrbLab r s (pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s))) = 0 ∧
      pairOrbLab r s (pairOrbT r s (pairOrbIdx r s (pairOrbH1 r s) + 1)) = 0 := by
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hTm : pairTop r s < pairStrands r s := by simp only [pairTop, pairStrands]; omega
  have hHm : pairOrbH1 r s < pairStrands r s := by simp only [pairOrbH1, pairStrands]; omega
  have h0 : pairOrbT r s 0 = 0 := rfl
  rw [pairOrbT_strands h, (pairOrbIdx_spec h hTm).2, (pairOrbIdx_spec h hHm).2,
    (pairOrb_idx_order h).2.2.2, h0]
  have hTd : pairTop r s = 2 * pairC r s - 1 := rfl
  have hHd : pairOrbH1 r s = 2 * pairC r s - s - 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold pairOrbLab <;> split_ifs <;> omega

/-- The orbit meets `pairOrbH1` only at its index. -/
private theorem twc_ne_H1_twCSegments {r s : ℕ} (h : IsTorusPair r s) (k : ℕ)
    (hk : k < pairStrands r s) (hne : k ≠ pairOrbIdx r s (pairOrbH1 r s)) :
    pairOrbT r s k ≠ pairOrbH1 r s := by
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hHm : pairOrbH1 r s < pairStrands r s := by simp only [pairOrbH1, pairStrands]; omega
  obtain ⟨hiH, hHs⟩ := pairOrbIdx_spec h hHm
  exact fun he ↦ hne (pairOrbT_injOn h hk hiH (he.trans hHs.symm))

/-- The two bottom pieces of the orbit as pure steps, with the sums of their exponents. -/
private theorem twc_bot_pieces_twCSegments {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    ∃ W1 N1 W2 N2 : ℤ, W1 + W2 = (s : ℤ) ∧ N1 + N2 = -((r * s : ℕ) : ℤ) + ℓ ∧
      (pairOrbConj r s L (twcSeg r s ℓ L 0 (pairOrbIdx r s (pairTop r s))) =
          pairOrbK r s L ^ W1 * pairOrbY r s L 0 ^ N1 ∧
        pairOrbY r s L 1 = pairOrbK r s L ^ W1 * pairOrbY r s L 0 * pairOrbK r s L ^ (-W1)) ∧
      (pairOrbConj r s L
            (twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) =
          pairOrbK r s L ^ W2 * pairOrbY r s L 1 ^ N2 ∧
        pairOrbY r s L 0 = pairOrbK r s L ^ W2 * pairOrbY r s L 1 * pairOrbK r s L ^ (-W2)) := by
  obtain ⟨l0, lm, lT, -, lH1⟩ := twc_seg_labs_twCSegments h
  obtain ⟨hiT0, hiTH, hiHm, -⟩ := pairOrb_idx_order h
  obtain ⟨hJ1, hJ2⟩ := twHeadTop_idx_twCSegments h
  have hG := twcSeg_pure_twCSegments h ℓ hL (Nat.zero_le (pairOrbIdx r s (pairTop r s)))
    (fun k _ hk ↦ twc_ne_H1_twCSegments h k (by omega) (by omega))
  have hU := twcSeg_pure_twCSegments h ℓ hL (le_of_lt hiHm)
    (fun k hk hk' ↦ twc_ne_H1_twCSegments h k hk' (by omega))
  rw [l0, lT] at hG
  rw [lm, lH1] at hU
  refine ⟨_, _, _, _, ?_, ?_, by exact_mod_cast hG, by exact_mod_cast hU⟩
  · rw [← Finset.range_eq_Ico, pairOrb_sum_bot h, (pairOrb_sum_bot_val h).1]
  · rw [twc_sum_twCSegments h ℓ (le_of_lt (by omega)), twc_sum_twCSegments h ℓ le_rfl,
      ite_eq_right (by rw [Finset.mem_Ico]; omega), ite_eq_right (by rw [Finset.mem_Ico]; omega),
      ite_eq_left (by rw [Finset.mem_Ico]; omega), ite_eq_right (by rw [Finset.mem_Ico]; omega),
      ← Finset.range_eq_Ico]
    have hs := pairOrb_sum_bot h (pairOrbN r s)
    rw [(pairOrb_sum_bot_val h).2] at hs
    linarith

/-- The bottom block, cut at `0`: `y_0 (G U) y_0⁻¹ = K^s y_1^(-rs+ℓ)`. -/
theorem twcSeg_GU {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbConj r s L
        (twcSeg r s ℓ L 0 (pairOrbIdx r s (pairTop r s)) *
          twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) =
      pairOrbK r s L ^ (s : ℤ) * pairOrbY r s L 1 ^ (-((r * s : ℕ) : ℤ) + ℓ) := by
  obtain ⟨W1, N1, W2, N2, hW, hN, ⟨hG, -⟩, ⟨hU, hy0⟩⟩ := twc_bot_pieces_twCSegments h ℓ hL
  have hc : ∀ x y : G, pairOrbConj r s L (x * y) = pairOrbConj r s L x * pairOrbConj r s L y := by
    intro x y
    unfold pairOrbConj
    group
  rw [hc, hG, hU, pairOrb_pure_mul _ _ _ _ _ _ _ hy0, hW, hN]

/-- The bottom block, cut at `T`: `y_0 (U G) y_0⁻¹ = K^s y_0^(-rs+ℓ)`. -/
theorem twcSeg_UG {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbConj r s L
        (twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) *
          twcSeg r s ℓ L 0 (pairOrbIdx r s (pairTop r s))) =
      pairOrbK r s L ^ (s : ℤ) * pairOrbY r s L 0 ^ (-((r * s : ℕ) : ℤ) + ℓ) := by
  obtain ⟨W1, N1, W2, N2, hW, hN, ⟨hG, hy1⟩, ⟨hU, -⟩⟩ := twc_bot_pieces_twCSegments h ℓ hL
  have hc : ∀ x y : G, pairOrbConj r s L (x * y) = pairOrbConj r s L x * pairOrbConj r s L y := by
    intro x y
    unfold pairOrbConj
    group
  rw [hc, hG, hU, pairOrb_pure_mul _ _ _ _ _ _ _ hy1, add_comm W2, add_comm N2, hW, hN]

/-- The top block: `y_0 M y_0⁻¹ = K^(-s) y_0^(rs-ℓ)`. -/
theorem twcSeg_M {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbConj r s L
        (twcSeg r s ℓ L (pairOrbIdx r s (pairTop r s)) (pairOrbIdx r s (pairOrbH1 r s))) =
      pairOrbK r s L ^ (-(s : ℤ)) * pairOrbY r s L 0 ^ (((r * s : ℕ) : ℤ) - ℓ) := by
  obtain ⟨-, -, -, lH, -⟩ := twc_seg_labs_twCSegments h
  obtain ⟨hiT0, hiTH, hiHm, -⟩ := pairOrb_idx_order h
  obtain ⟨hJ1, hJ2⟩ := twHeadTop_idx_twCSegments h
  have hS := (twcSeg_pure_twCSegments h ℓ hL (le_of_lt hiTH)
    (fun k _ hk ↦ twc_ne_H1_twCSegments h k (by omega) (by omega))).1
  rw [lH, twc_sum_twCSegments h ℓ (le_of_lt (by omega)),
    ite_eq_right (by rw [Finset.mem_Ico]; omega), ite_eq_left (by rw [Finset.mem_Ico]; omega),
    pairOrb_sum_top h, pairOrb_sum_top h, (pairOrb_sum_top_val h).1,
    (pairOrb_sum_top_val h).2] at hS
  rw [hS, zero_add, sub_eq_add_neg]
  rfl

/-- The last piece of the orbit is pure and carries `y_1` to `y_0`. -/
theorem twcSeg_U {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    ∃ W N : ℤ,
      pairOrbConj r s L
          (twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) =
        pairOrbK r s L ^ W * pairOrbY r s L 1 ^ N ∧
      pairOrbY r s L 0 = pairOrbK r s L ^ W * pairOrbY r s L 1 * pairOrbK r s L ^ (-W) := by
  obtain ⟨W1, N1, W2, N2, -, -, -, hU⟩ := twc_bot_pieces_twCSegments h ℓ hL
  exact ⟨W2, N2, hU⟩

end AJConjecture
