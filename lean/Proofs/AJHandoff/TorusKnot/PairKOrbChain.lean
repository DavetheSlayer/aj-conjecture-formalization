import Mathlib
import AJHandoff.TorusKnot.PairKOrbCycle

/-!
# Products along the orbit

Generic tools for the orbit split:

* `pairOrb_pure_mul`, `pairOrb_pure_prod`: pure steps `K ^ w * Y_(k+1) ^ n` with the label
  condition `Y_k = K ^ w Y_(k+1) K ^ (-w)` multiply to `K ^ (∑ w) * Y_b ^ (∑ n)`, and the labels of
  the ends satisfy the label condition with `∑ w` (induction on `b - a`, `conj_zpow`, `zpow_add`);
* `pairOrbSeg_split`, `pairOrbSeg_one`, `orbitLoop_eq_pairOrbSeg`, `pairOrbConj_prod`: bookkeeping
  for orbit segments (`List.range_add`, `List.prod_append`, `List.prod_map_hom`-style);
* `pairOrb_edgeMer_seg`: in the knot group, the edge meridian of the `k`-th strand of the orbit is
  the meridian conjugated by the product of the first `k` strand loops (induction on `k` with
  `edgeMer_fixed` for `pairWhiteheadKnot r s h`, `pairBlocks r s`, `rfl`, `pairBlocks_valid h`,
  `MonoidHom.id`; `edgeMer_zero` and `meridian` for `k = 0`; `pairOrbT_lt`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The generators of the knot group of `pairWhiteheadKnot r s h` (as `pairKGen`). -/
abbrev pairOrbGen {r s : ℕ} (h : IsTorusPair r s) :
    Fin (pairStrands r s) → KnotGroup (pairWhiteheadKnot r s h) :=
  fun t ↦ PresentedGroup.of t

/-- Two pure steps multiply. -/
theorem pairOrb_pure_mul (K a b : G) (w W n N : ℤ) (hab : a = K ^ W * b * K ^ (-W)) :
    K ^ w * a ^ n * (K ^ W * b ^ N) = K ^ (w + W) * b ^ (n + N) := by
  rw [hab, zpow_neg, conj_zpow]
  group

/-- A product of pure steps. -/
theorem pairOrb_pure_prod (K : G) (x Y : ℕ → G) (w n : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b)
    (hx : ∀ k, a ≤ k → k < b → x k = K ^ w k * Y (k + 1) ^ n k)
    (hY : ∀ k, a ≤ k → k < b → Y k = K ^ w k * Y (k + 1) * K ^ (-w k)) :
    ((List.range (b - a)).map fun k ↦ x (a + k)).prod =
        K ^ (∑ k ∈ Finset.Ico a b, w k) * Y b ^ (∑ k ∈ Finset.Ico a b, n k) ∧
      Y a = K ^ (∑ k ∈ Finset.Ico a b, w k) * Y b * K ^ (-∑ k ∈ Finset.Ico a b, w k) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  clear hab
  induction d generalizing a with
  | zero => simp
  | succ d ih =>
    obtain ⟨ih1, ih2⟩ := ih (a := a + 1) (fun k h1 h2 ↦ hx k (by omega) (by omega))
      (fun k h1 h2 ↦ hY k (by omega) (by omega))
    rw [show a + 1 + d = a + (d + 1) by omega, show a + (d + 1) - (a + 1) = d by omega] at ih1
    rw [show a + 1 + d = a + (d + 1) by omega] at ih2
    rw [Nat.add_sub_cancel_left, List.range_succ_eq_map, List.map_cons, List.prod_cons,
      List.map_map, Finset.sum_eq_sum_Ico_succ_bot (show a < a + (d + 1) by omega) w,
      Finset.sum_eq_sum_Ico_succ_bot (show a < a + (d + 1) by omega) n]
    have hmap : ((List.range d).map ((fun k ↦ x (a + k)) ∘ Nat.succ)).prod =
        ((List.range d).map fun k ↦ x (a + 1 + k)).prod := by
      congr 1
      refine List.map_congr_left fun k _ ↦ ?_
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [hmap, ih1, Nat.add_zero, hx a le_rfl (by omega)]
    refine ⟨pairOrb_pure_mul _ _ _ _ _ _ _ ih2, ?_⟩
    rw [hY a le_rfl (by omega), ih2]
    group

/-- An orbit segment splits at an intermediate index. -/
theorem pairOrbSeg_split (r s : ℕ) (f : Fin (pairStrands r s) → G) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) : pairOrbSeg r s f a c = pairOrbSeg r s f a b * pairOrbSeg r s f b c := by
  unfold pairOrbSeg
  rw [show c - a = (b - a) + (c - b) by omega, List.range_add, List.map_append,
    List.prod_append, List.map_map]
  congr 2
  refine List.map_congr_left fun k _ ↦ ?_
  simp only [Function.comp_apply]
  congr 2
  omega

/-- An orbit segment of length one is a strand loop. -/
theorem pairOrbSeg_one (r s : ℕ) (f : Fin (pairStrands r s) → G) (a : ℕ) :
    pairOrbSeg r s f a (a + 1) =
      stLoop (pairStrands r s) (pairBlocks r s) f (pairOrbT r s a) := by
  unfold pairOrbSeg
  rw [Nat.add_sub_cancel_left, List.range_one, List.map_singleton, List.prod_singleton,
    Nat.add_zero]

/-- The orbit loop is the whole orbit segment. -/
theorem orbitLoop_eq_pairOrbSeg (r s : ℕ) (f : Fin (pairStrands r s) → G) :
    orbitLoop (pairStrands r s) (pairBlocks r s) f = pairOrbSeg r s f 0 (pairStrands r s) := by
  unfold orbitLoop pairOrbSeg pairOrbT
  simp only [Nat.sub_zero, Nat.zero_add]

/-- Conjugation by `y_0` is multiplicative. -/
theorem pairOrbConj_prod (r s : ℕ) (L : ℕ → G) (l : List G) :
    pairOrbConj r s L l.prod = (l.map (pairOrbConj r s L)).prod := by
  induction l with
  | nil => simp [pairOrbConj]
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    unfold pairOrbConj
    group

/-- The edge meridian of the `k`-th strand of the orbit, for the generators of the knot group. -/
theorem pairOrb_edgeMer_seg {r s : ℕ} (h : IsTorusPair r s) {k : ℕ}
    (hk : k ≤ pairStrands r s) :
    edgeMer (pairOrbGen h) (pairOrbT r s k) =
      (pairOrbSeg r s (pairOrbGen h) 0 k)⁻¹ * meridian (pairWhiteheadKnot r s h) *
        pairOrbSeg r s (pairOrbGen h) 0 k := by
  induction k with
  | zero =>
    unfold pairOrbSeg
    rw [show pairOrbT r s 0 = 0 from rfl,
      edgeMer_zero (pairOrbGen h) (by unfold pairStrands; omega)]
    simp only [Nat.sub_zero, List.range_zero, List.map_nil, List.prod_nil, inv_one, one_mul,
      mul_one]
    rfl
  | succ k ih =>
    have e := edgeMer_fixed (pairWhiteheadKnot r s h) (pairBlocks r s) rfl (pairBlocks_valid h)
      (MonoidHom.id _) (pairOrbT r s k) (pairOrbT_lt h k)
    change edgeMer (pairOrbGen h) (pairOrbT r s k) =
      stLoop (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairOrbT r s k) *
        edgeMer (pairOrbGen h) (stPerm (pairBlocks r s) (pairOrbT r s k)) *
        (stLoop (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairOrbT r s k))⁻¹ at e
    rw [pairOrbT_succ, pairOrbSeg_split r s _ (Nat.zero_le k) (Nat.le_succ k), pairOrbSeg_one]
    rw [ih (by omega)] at e
    calc _ = (stLoop (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairOrbT r s k))⁻¹ *
          (stLoop (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairOrbT r s k) *
            edgeMer (pairOrbGen h) (stPerm (pairBlocks r s) (pairOrbT r s k)) *
            (stLoop (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairOrbT r s k))⁻¹) *
          stLoop (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairOrbT r s k) := by group
      _ = _ := by rw [← e]; group

end AJConjecture
