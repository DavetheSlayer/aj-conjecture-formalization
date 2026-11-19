import Mathlib
import AJHandoff.TorusKnot.PairKOrbPatLoop

/-!
# The stages of `pairBlocks r s`

`pairBlocks r s` is the append of eleven stages (`pairOrbStage r s k`), numbered in the order in
which they act on a strand from the top: `0` the second Hopf letter, `1` the right descents,
`2` the top-right climb `C`, `3` the last round, `4` the rounds `R_1 … R_(s-2)` (a staircase), `5`
the first Hopf letter, `6` the round `R_0`, `7` the big climb `B`, `8` the increasing run, `9` the
decreasing run, `10` the left climbs (as `pairStage` in `AJHandoff.TorusKnot.PairKConnected`).

`stLoop_pairBlocks_stages`: the strand loop of `t` is the product over the stages, top first, of
the strand loop of stage `k` at the position `pairOrbPos r s k t` where the strand enters it, read
on the tuple below the stage; `loopAt_pairOrbStage` rewrites the loops of the blocks of stage `k`
as block loops of `pairBlocks r s` at the offset `pairOrbStageOff r s k`. With the pattern lemmas
(`AJHandoff.TorusKnot.PairKOrbPatLoop`, `AJHandoff.TorusKnot.PairKOrbPatPerm`) this computes every
strand loop (`AJHandoff.TorusKnot.PairKOrbLoopRun`, `PairKOrbLoopStair`, `PairKOrbLoopLow`).

Route: `pairBlocks_eq_stages` by unfolding (the lists agree up to `pairTop`); then
`stLoop_append` eleven times (an induction on `k` over `pairOrbPre`); `loopAt_append_left`,
`loopAt_append_right` and `runTop_append` for the offsets; the lengths by `List.length_map`,
`List.length_range` and `pairBlocks_arith`-style arithmetic.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The stage `k` of `pairBlocks r s` (stage `0` on top). -/
def pairOrbStage (r s : ℕ) : ℕ → List SBlock
  | 0 => [SBlock.neg (pairTop r s)]
  | 1 => (List.range (r - 2)).map fun j ↦ SBlock.band (r - 3 - j) (pairTop r s + 2 - s - r + j)
  | 2 => [SBlock.band (pairTop r s - s) (pairTop r s)]
  | 3 => [SBlock.band (r - 2) (pairTop r s + 1 - s)]
  | 4 => (List.range (s - 2)).map fun j ↦
      SBlock.band (pairTop r s - r - 1 - j) (pairTop r s - 1 - j)
  | 5 => [SBlock.neg (pairTop r s)]
  | 6 => [SBlock.band (pairTop r s - r) (pairTop r s)]
  | 7 => [SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r)]
  | 8 => (List.range (pairRunUp r s)).map fun j ↦
      SBlock.band (r - 2 + pairRunDown r s + j) (r - 1 + pairRunDown r s + j)
  | 9 => (List.range (pairRunDown r s)).map fun j ↦
      SBlock.band (r + pairRunDown r s - 3 - j) (r + pairRunDown r s - 2 - j)
  | 10 => (List.range (r - 2)).map fun i ↦ SBlock.band i (pairTop r s - 1 - i)
  | _ => []

/-- The stages below stage `k`, in block order: stages `10, 9, …, k + 1`. -/
def pairOrbPre (r s k : ℕ) : List SBlock :=
  ((List.range (10 - k)).map fun i ↦ pairOrbStage r s (10 - i)).flatten

/-- The stages above stage `k`, in block order: stages `k - 1, …, 0`. -/
def pairOrbPost (r s k : ℕ) : List SBlock :=
  ((List.range k).reverse.map fun i ↦ pairOrbStage r s i).flatten

/-- The position at which the strand at top position `t` enters stage `k` from above. -/
def pairOrbPos (r s k t : ℕ) : ℕ := stPerm (pairOrbPost r s k) t

/-- The position in `pairBlocks r s` of the first block of stage `k`. -/
def pairOrbStageOff (r s : ℕ) : ℕ → ℕ
  | 0 => 2 * pairC r s + 1
  | 1 => 2 * pairC r s - r + 3
  | 2 => 2 * pairC r s - r + 2
  | 3 => 2 * pairC r s - r + 1
  | 4 => 2 * pairC r s - s - r + 3
  | 5 => 2 * pairC r s - s - r + 2
  | 6 => 2 * pairC r s - s - r + 1
  | 7 => 2 * pairC r s - s - r
  | 8 => r - 2 + pairRunDown r s
  | 9 => r - 2
  | _ => 0

/-- `pairBlocks r s` is the append of its stages. -/
theorem pairBlocks_eq_stages (r s : ℕ) :
    pairBlocks r s = pairOrbPre r s 0 ++ pairOrbStage r s 0 := by
  simp only [pairBlocks, pairOrbPre, pairOrbStage, List.range_succ, List.range_zero,
    List.map_nil, List.map_cons, List.flatten_cons, List.flatten_nil, List.nil_append,
    List.append_nil, List.append_assoc, List.cons_append]

/-- No stage lies above stage `0`. -/
theorem pairOrbPost_zero (r s : ℕ) : pairOrbPost r s 0 = [] := rfl

/-- The stages above stage `k + 1` are stage `k` and the stages above it. -/
theorem pairOrbPost_succ (r s k : ℕ) :
    pairOrbPost r s (k + 1) = pairOrbStage r s k ++ pairOrbPost r s k := by
  simp only [pairOrbPost, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, List.flatten_cons]

/-- No stage lies below stage `10`. -/
theorem pairOrbPre_ten (r s : ℕ) : pairOrbPre r s 10 = [] := rfl

/-- The stages below stage `k < 10` are the stages below stage `k + 1` and stage `k + 1`. -/
theorem pairOrbPre_succ (r s : ℕ) {k : ℕ} (hk : k < 10) :
    pairOrbPre r s k = pairOrbPre r s (k + 1) ++ pairOrbStage r s (k + 1) := by
  unfold pairOrbPre
  rw [show 10 - k = 10 - (k + 1) + 1 by omega, List.range_succ, List.map_append,
    List.flatten_append, List.map_singleton, List.flatten_singleton,
    show 10 - (10 - (k + 1)) = k + 1 by omega]

/-- The entry position of stage `0` is the top position. -/
theorem pairOrbPos_zero (r s t : ℕ) : pairOrbPos r s 0 t = t := rfl

/-- The entry position of stage `k + 1` is the exit position of stage `k`. -/
theorem pairOrbPos_succ (r s k t : ℕ) :
    pairOrbPos r s (k + 1) t = stPerm (pairOrbStage r s k) (pairOrbPos r s k t) := by
  rw [pairOrbPos, pairOrbPost_succ, stPerm_append, pairOrbPos]

/-- `pairBlocks r s` splits around stage `k ≤ 10`. -/
theorem pairBlocks_eq_pre_post (r s : ℕ) {k : ℕ} (hk : k ≤ 10) :
    pairBlocks r s = pairOrbPre r s k ++ (pairOrbStage r s k ++ pairOrbPost r s k) := by
  induction k with
  | zero => rw [pairOrbPost_zero, List.append_nil, pairBlocks_eq_stages]
  | succ k ih =>
    rw [ih (by omega), pairOrbPre_succ r s (by omega), pairOrbPost_succ, List.append_assoc]

/-- The stages below stage `k ≤ 10` fill the positions before `pairOrbStageOff r s k`. -/
theorem pairOrbPre_length {r s : ℕ} (h : IsTorusPair r s) {k : ℕ} (hk : k ≤ 10) :
    (pairOrbPre r s k).length = pairOrbStageOff r s k := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  interval_cases k <;>
    simp (disch := omega) only [pairOrbPre_succ, pairOrbPre_ten, pairOrbStageOff, pairOrbStage,
      List.length_append, List.length_map, List.length_range, List.length_nil,
      List.length_singleton, pairTop, pairRunUp, Nat.reduceAdd] <;>
    omega

/-- The strand loop of `pairBlocks r s` as the product, top stage first, of the strand loops of
the stages. -/
theorem stLoop_pairBlocks_stages (r s : ℕ) (f : Fin (pairStrands r s) → G) (t : ℕ) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      ((List.range 11).map fun k ↦ stLoop (pairStrands r s) (pairOrbStage r s k)
        (runTop (pairStrands r s) (pairOrbPre r s k) f) (pairOrbPos r s k t)).prod := by
  have key : ∀ k, k ≤ 10 → stLoop (pairStrands r s) (pairBlocks r s) f t =
      ((List.range (k + 1)).map fun i ↦ stLoop (pairStrands r s) (pairOrbStage r s i)
        (runTop (pairStrands r s) (pairOrbPre r s i) f) (pairOrbPos r s i t)).prod *
        stLoop (pairStrands r s) (pairOrbPre r s k) f (pairOrbPos r s (k + 1) t) := by
    intro k hk
    induction k with
    | zero =>
      rw [pairBlocks_eq_stages, stLoop_append]
      simp only [Nat.zero_add, List.range_one, List.map_singleton, List.prod_singleton, pairOrbPos,
        pairOrbPost_succ, pairOrbPost_zero, stPerm, List.append_nil]
    | succ k ih =>
      rw [ih (by omega), pairOrbPre_succ r s (by omega), stLoop_append,
        List.range_succ (n := k + 1), List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc,
        pairOrbPos_succ r s (k + 1)]
  rw [key 10 le_rfl]
  simp only [pairOrbPre_ten, stLoop, mul_one]

/-- The loops of the blocks of stage `k`, read on the tuple below the stage, are block loops of
`pairBlocks r s`. -/
theorem loopAt_pairOrbStage {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    {k j : ℕ} (hk : k ≤ 10) (hj : j < (pairOrbStage r s k).length) :
    loopAt (pairStrands r s) (pairOrbStage r s k)
        (runTop (pairStrands r s) (pairOrbPre r s k) f) j =
      loopAt (pairStrands r s) (pairBlocks r s) f (pairOrbStageOff r s k + j) := by
  rw [pairBlocks_eq_pre_post r s hk, ← pairOrbPre_length h hk, loopAt_append_right,
    loopAt_append_left _ _ _ _ _ hj]

/-! ### Evaluation tools for the strand loops -/

/-- The empty descending product. -/
theorem descProd_zero_orb (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

/-- Splitting off the top factor of a descending product. -/
theorem descProd_succ_orb (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- A descending product of one factor. -/
theorem descProd_one_orb (g : ℕ → G) (a : ℕ) : descProd g a 1 = g a := by
  simp [descProd]

/-- Descending products with the same factors agree. -/
theorem descProd_congr_orb (g g' : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = g' (b + i)) : descProd g a n = descProd g' b n := by
  induction n with
  | zero => simp [descProd_zero_orb]
  | succ n ih =>
    rw [descProd_succ_orb, descProd_succ_orb, H n (by omega), ih fun i hi ↦ H i (by omega)]

/-- A filtered descending product over `range n` whose filter is an interval. -/
theorem prod_range_ite_eq_descProd (g : ℕ → G) (c : ℕ → Prop) [DecidablePred c]
    {n lo len : ℕ} (hle : lo + len ≤ n) (hc : ∀ j, j < n → (c j ↔ lo ≤ j ∧ j < lo + len)) :
    ((List.range n).reverse.map fun j ↦ if c j then g j else 1).prod = descProd g lo len := by
  induction n generalizing lo len with
  | zero =>
    rw [show len = 0 by omega, descProd_zero_orb]
    rfl
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, List.prod_cons]
    by_cases hn : lo + len = n + 1 ∧ 0 < len
    · obtain ⟨l, rfl⟩ : ∃ l, len = l + 1 := ⟨len - 1, by omega⟩
      have hcn : c n := (hc n (by omega)).2 ⟨by omega, by omega⟩
      have hl : lo + l = n := by omega
      rw [ite_eq_left hcn, descProd_succ_orb, hl,
        ih (lo := lo) (len := l) (by omega) fun j hj ↦ by rw [hc j (by omega)]; omega]
    · have hcn : ¬ c n := fun h' ↦ by have := (hc n (by omega)).1 h'; omega
      rw [ite_eq_right hcn, one_mul]
      by_cases hl0 : len = 0
      · subst hl0
        rw [ih (lo := 0) (len := 0) (by omega) fun j hj ↦ by rw [hc j (by omega)]; omega,
          descProd_zero_orb, descProd_zero_orb]
      · exact ih (by omega) fun j hj ↦ hc j (by omega)

/-- The strand loop of a one-block stage. -/
theorem stLoop_pairOrbStage_single {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {k : ℕ} (hk : k ≤ 10) {b : SBlock}
    (hb : pairOrbStage r s k = [b]) (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s k) (runTop (pairStrands r s) (pairOrbPre r s k) f)
        p = if b.carries p then
          loopAt (pairStrands r s) (pairBlocks r s) f (pairOrbStageOff r s k) else 1 := by
  have hl := loopAt_pairOrbStage h f hk (j := 0) (by rw [hb]; simp)
  rw [hb, Nat.add_zero] at hl
  rw [hb, stLoop_singleton_orb, SBlock.strandLoop, ← hl]
  simp only [loopAt, List.getD_cons_zero, List.take_zero, runTop_nil]

/-- The loops of the blocks of a stage that is a mapped range, filtered by a condition. -/
theorem prod_loopAt_pairOrbStage {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {k n : ℕ} (hk : k ≤ 10) (gb : ℕ → SBlock)
    (hst : pairOrbStage r s k = (List.range n).map gb) (c : ℕ → Prop) [DecidablePred c]
    (g : ℕ → G)
    (hg : ∀ j, j < n → loopAt (pairStrands r s) (pairBlocks r s) f (pairOrbStageOff r s k + j) =
      g j) :
    ((List.range n).reverse.map fun j ↦ if c j then
      loopAt (pairStrands r s) ((List.range n).map gb)
        (runTop (pairStrands r s) (pairOrbPre r s k) f) j else 1).prod =
      ((List.range n).reverse.map fun j ↦ if c j then g j else 1).prod := by
  congr 1
  refine List.map_congr_left fun j hj ↦ ?_
  rw [List.mem_reverse, List.mem_range] at hj
  have hj' : j < (pairOrbStage r s k).length := by
    rw [hst, List.length_map, List.length_range]
    exact hj
  have hl := loopAt_pairOrbStage h f hk hj'
  rw [hst] at hl
  rw [hl, hg j hj]

/-! ### The strand map of each stage -/

/-- The arithmetic of an admissible pair, with `1 ≤ E`. -/
theorem pairOrbStage_arith {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ 1 ≤ pairRunDown r s ∧ pairRunDown r s + s + r = pairC r s + 3 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  exact ⟨hr, hrs, by unfold pairRunDown; omega, hE⟩

/-- Stage `0` (the second Hopf letter) of the strand map. -/
theorem stPerm_pairOrbStage_zero {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 0) t = if t + 1 = 2 * pairC r s then 2 * pairC r s
      else if t = 2 * pairC r s then 2 * pairC r s - 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, stPerm, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `1` (the right descents) of the strand map. -/
theorem stPerm_pairOrbStage_one {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 1) t =
      if t + 3 ≤ r ∨ (2 * pairC r s + 1 ≤ t + s + r ∧ t + s + 1 < 2 * pairC r s)
      then 2 * pairC r s - s - 2 - t else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, pairTop]
  rw [stPerm_orbSpread _ _ _ _ (by omega) (by omega)]
  split_ifs <;> omega

/-- Stage `2` (the top-right climb) of the strand map. -/
theorem stPerm_pairOrbStage_two {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 2) t = if t + s + 1 = 2 * pairC r s then 2 * pairC r s - 1
      else if t + 1 = 2 * pairC r s then 2 * pairC r s - 1 - s else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, stPerm, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `3` (the last round) of the strand map. -/
theorem stPerm_pairOrbStage_three {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 3) t = if t + 2 = r then 2 * pairC r s - s
      else if t + s = 2 * pairC r s then r - 2 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, stPerm, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `4` (the staircase rounds) of the strand map. -/
theorem stPerm_pairOrbStage_four {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 4) t =
      if 2 * pairC r s < t + s ∧ t + 2 ≤ 2 * pairC r s then t - r
      else if 2 * pairC r s < t + s + r ∧ t + r + 2 ≤ 2 * pairC r s then
        2 * pairC r s - 2 - (2 * pairC r s - 2 - t) % r
      else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, pairTop]
  rw [stPerm_orbStair (2 * pairC r s - 1 - r - 1) (2 * pairC r s - 1 - 1) r _ _ (by omega)
    (by omega) (by omega)]
  rw [show 2 * pairC r s - 1 - 1 = 2 * pairC r s - 2 by omega]
  split_ifs <;> omega

/-- Stage `5` (the first Hopf letter) of the strand map. -/
theorem stPerm_pairOrbStage_five {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 5) t = if t + 1 = 2 * pairC r s then 2 * pairC r s
      else if t = 2 * pairC r s then 2 * pairC r s - 1 else t :=
  stPerm_pairOrbStage_zero h t

/-- Stage `6` (the first round) of the strand map. -/
theorem stPerm_pairOrbStage_six {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 6) t = if t + r + 1 = 2 * pairC r s then 2 * pairC r s - 1
      else if t + 1 = 2 * pairC r s then 2 * pairC r s - 1 - r else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, stPerm, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `7` (the big climb) of the strand map. -/
theorem stPerm_pairOrbStage_seven {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 7) t = if t + s + r = 2 * pairC r s then 2 * pairC r s - r
      else if t + r = 2 * pairC r s then 2 * pairC r s - s - r else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, stPerm, pairTop, pairRunUp]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `8` (the increasing run) of the strand map. -/
theorem stPerm_pairOrbStage_eight {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 8) t = if t + s + r = 2 * pairC r s then pairC r s - s + 1
      else if pairC r s + 1 ≤ t + s ∧ t + s + r < 2 * pairC r s then t + 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, pairRunUp]
  rw [stPerm_orbRunUp _ _ _ _ (by omega)]
  split_ifs <;> omega

/-- Stage `9` (the decreasing run) of the strand map. -/
theorem stPerm_pairOrbStage_nine {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 9) t = if t + 2 = r then pairC r s - s + 1
      else if r ≤ t + 1 ∧ t + s ≤ pairC r s + 1 then t - 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage]
  rw [stPerm_orbRunDown _ _ _ _ (by omega) (by omega)]
  split_ifs <;> omega

/-- Stage `10` (the left climbs) of the strand map. -/
theorem stPerm_pairOrbStage_ten {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    stPerm (pairOrbStage r s 10) t =
      if t + 2 < r ∨ (2 * pairC r s < t + r ∧ t + 2 ≤ 2 * pairC r s)
      then 2 * pairC r s - 2 - t else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  simp only [pairOrbStage, pairTop]
  rw [stPerm_orbNested _ _ _ (by omega)]
  split_ifs <;> omega

/-! ### The strand loop of each stage -/

/-- Stage `0`: the second Hopf loop, collected by `T`. -/
theorem stLoop_pairOrbStage_zero {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 0) (runTop (pairStrands r s) (pairOrbPre r s 0) f)
        p = if p = pairTop r s then
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s) else 1 := by
  rw [stLoop_pairOrbStage_single h f (by omega) (b := SBlock.neg (pairTop r s)) rfl]
  simp only [SBlock.carries, decide_eq_true_eq]
  rfl

/-- Stage `1`: the right descents `D'_j`. -/
theorem stLoop_pairOrbStage_one {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 1) (runTop (pairStrands r s) (pairOrbPre r s 1) f)
        p = ((List.range (r - 2)).reverse.map fun j ↦
          if r - 3 < p + j ∧ p ≤ pairTop r s + 2 - s - r + j then
            loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j) else 1).prod := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  have hst : pairOrbStage r s 1 = (List.range (r - 2)).map fun j ↦
      SBlock.band (r - 3 - j) (pairTop r s + 2 - s - r + j) := rfl
  rw [hst, stLoop_orbSpread _ _ _ _ _ _ (by unfold pairTop; omega) (by omega),
    prod_loopAt_pairOrbStage h f (by omega) _ hst _
      (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j))]
  intro j hj
  simp only [pairOrbStageOff, pairIdxDp, pairIdxB]
  congr 1
  omega

/-- Stage `2`: the top-right climb `C`. -/
theorem stLoop_pairOrbStage_two {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 2) (runTop (pairStrands r s) (pairOrbPre r s 2) f)
        p = if p = pairTop r s ∨ (pairTop r s - s < p ∧ p < pairTop r s) then
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxC r s) else 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  rw [stLoop_pairOrbStage_single h f (by omega)
    (b := SBlock.band (pairTop r s - s) (pairTop r s)) rfl]
  simp only [SBlock.carries, decide_eq_true_eq, pairOrbStageOff, pairIdxC, pairIdxB]
  rw [show 2 * pairC r s - r + 2 = 2 * pairC r s - s - r + s + 2 by omega]

/-- Stage `3`: the last round `R_(s-1)`. -/
theorem stLoop_pairOrbStage_three {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 3) (runTop (pairStrands r s) (pairOrbPre r s 3) f)
        p = if p = pairTop r s + 1 - s ∨ (r - 2 < p ∧ p < pairTop r s + 1 - s) then
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1)) else 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  rw [stLoop_pairOrbStage_single h f (by omega)
    (b := SBlock.band (r - 2) (pairTop r s + 1 - s)) rfl]
  simp only [SBlock.carries, decide_eq_true_eq, pairOrbStageOff, pairIdxR, pairIdxB,
    show s - 1 ≠ 0 by omega, ite_false]
  rw [show 2 * pairC r s - r + 1 = 2 * pairC r s - s - r + 2 + (s - 1) by omega]

/-- Stage `4`: the staircase rounds `R_(j+1)`, `j < s - 2`. -/
theorem stLoop_pairOrbStage_four {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 4) (runTop (pairStrands r s) (pairOrbPre r s 4) f)
        p = ((List.range (s - 2)).reverse.map fun j ↦
          if (if pairTop r s - 1 < p + (s - 2) ∧ p ≤ pairTop r s - 1 then j + p = pairTop r s - 1
            else pairTop r s - r - 1 < p + (s - 2) ∧ p ≤ pairTop r s - 1 ∧
              j + p < pairTop r s - 1 ∧ (pairTop r s - 1 - p - j) % r ≠ 0) then
            loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (j + 1)) else 1).prod := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  have hst : pairOrbStage r s 4 = (List.range (s - 2)).map fun j ↦
      SBlock.band (pairTop r s - r - 1 - j) (pairTop r s - 1 - j) := rfl
  rw [hst, stLoop_orbStair _ _ _ r _ _ _ (by unfold pairTop; omega) (by omega)
      (by unfold pairTop; omega),
    prod_loopAt_pairOrbStage h f (by omega) _ hst _
      (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (j + 1)))]
  intro j hj
  simp only [pairOrbStageOff, pairIdxR, pairIdxB, Nat.add_one_ne_zero, ite_false]
  congr 1
  omega

/-- Stage `5`: the first Hopf loop, collected by `T`. -/
theorem stLoop_pairOrbStage_five {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 5) (runTop (pairStrands r s) (pairOrbPre r s 5) f)
        p = if p = pairTop r s then
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH1 r s) else 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  rw [stLoop_pairOrbStage_single h f (by omega) (b := SBlock.neg (pairTop r s)) rfl]
  simp only [SBlock.carries, decide_eq_true_eq, pairOrbStageOff, pairIdxH1, pairIdxB]

/-- Stage `6`: the first round `R_0`. -/
theorem stLoop_pairOrbStage_six {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 6) (runTop (pairStrands r s) (pairOrbPre r s 6) f)
        p = if p = pairTop r s ∨ (pairTop r s - r < p ∧ p < pairTop r s) then
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0) else 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  rw [stLoop_pairOrbStage_single h f (by omega)
    (b := SBlock.band (pairTop r s - r) (pairTop r s)) rfl]
  simp only [SBlock.carries, decide_eq_true_eq, pairOrbStageOff, pairIdxR, pairIdxB, ite_true]

/-- Stage `7`: the big climb `B`. -/
theorem stLoop_pairOrbStage_seven {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 7) (runTop (pairStrands r s) (pairOrbPre r s 7) f)
        p = if p = pairTop r s + 1 - r ∨
            (r - 2 + pairRunDown r s + pairRunUp r s < p ∧ p < pairTop r s + 1 - r) then
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxB r s) else 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  rw [stLoop_pairOrbStage_single h f (by omega)
    (b := SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r)) rfl]
  simp only [SBlock.carries, decide_eq_true_eq, pairOrbStageOff, pairIdxB]

/-- Stage `8`: the increasing run, collected only by its top strand. -/
theorem stLoop_pairOrbStage_eight {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 8) (runTop (pairStrands r s) (pairOrbPre r s 8) f)
        p = ((List.range (pairRunUp r s)).reverse.map fun j ↦
          if p = r - 2 + pairRunDown r s + pairRunUp r s then
            loopAt (pairStrands r s) (pairBlocks r s) f (r - 2 + pairRunDown r s + j)
          else 1).prod := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  have hst : pairOrbStage r s 8 = (List.range (pairRunUp r s)).map fun j ↦
      SBlock.band (r - 2 + pairRunDown r s + j) (r - 1 + pairRunDown r s + j) := rfl
  rw [hst, stLoop_orbRunUp _ (r - 2 + pairRunDown r s) _ _ _ _ (by omega),
    prod_loopAt_pairOrbStage h f (by omega) _ hst _
      (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (r - 2 + pairRunDown r s + j))]
  intro j hj
  rfl

/-- Stage `9`: the decreasing run. -/
theorem stLoop_pairOrbStage_nine {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 9) (runTop (pairStrands r s) (pairOrbPre r s 9) f)
        p = ((List.range (pairRunDown r s)).reverse.map fun j ↦
          if j + p = r + pairRunDown r s - 2 then
            loopAt (pairStrands r s) (pairBlocks r s) f (r - 2 + j) else 1).prod := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrbStage_arith h
  have hst : pairOrbStage r s 9 = (List.range (pairRunDown r s)).map fun j ↦
      SBlock.band (r + pairRunDown r s - 3 - j) (r + pairRunDown r s - 2 - j) := rfl
  rw [hst, stLoop_orbRunDown _ (r + pairRunDown r s - 3) _ _ _ _ (by omega) (by omega),
    prod_loopAt_pairOrbStage h f (by omega) _ hst _
      (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (r - 2 + j))]
  intro j hj
  rfl

/-- Stage `10`: the left climbs `A_j`. -/
theorem stLoop_pairOrbStage_ten {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    (p : ℕ) :
    stLoop (pairStrands r s) (pairOrbStage r s 10)
        (runTop (pairStrands r s) (pairOrbPre r s 10) f) p =
      ((List.range (r - 2)).reverse.map fun j ↦
        if j < p ∧ j + p ≤ pairTop r s - 1 then
          loopAt (pairStrands r s) (pairBlocks r s) f j else 1).prod := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  have hst : pairOrbStage r s 10 = (List.range (r - 2)).map fun i ↦
      SBlock.band i (pairTop r s - 1 - i) := rfl
  rw [hst, stLoop_orbNested _ _ _ _ _ (by unfold pairTop; omega),
    prod_loopAt_pairOrbStage h f (by omega) _ hst _
      (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f j)]
  intro j hj
  simp only [pairOrbStageOff, Nat.zero_add]

/-! ### Stage loops whose carried blocks form an interval -/

/-- Stage `1` when the carried descents form an interval. -/
theorem stLoop_pairOrbStage_one_eq {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p lo len : ℕ} (hle : lo + len ≤ r - 2)
    (hc : ∀ j, j < r - 2 →
      (r - 3 < p + j ∧ p ≤ pairTop r s + 2 - s - r + j ↔ lo ≤ j ∧ j < lo + len)) :
    stLoop (pairStrands r s) (pairOrbStage r s 1) (runTop (pairStrands r s) (pairOrbPre r s 1) f)
        p = descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j))
          lo len := by
  rw [stLoop_pairOrbStage_one h, prod_range_ite_eq_descProd _ _ hle hc]

/-- Stage `4` when the carried rounds form an interval. -/
theorem stLoop_pairOrbStage_four_eq {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p lo len : ℕ} (hle : lo + len ≤ s - 2)
    (hc : ∀ j, j < s - 2 →
      ((if pairTop r s - 1 < p + (s - 2) ∧ p ≤ pairTop r s - 1 then j + p = pairTop r s - 1
        else pairTop r s - r - 1 < p + (s - 2) ∧ p ≤ pairTop r s - 1 ∧
          j + p < pairTop r s - 1 ∧ (pairTop r s - 1 - p - j) % r ≠ 0) ↔
        lo ≤ j ∧ j < lo + len)) :
    stLoop (pairStrands r s) (pairOrbStage r s 4) (runTop (pairStrands r s) (pairOrbPre r s 4) f)
        p = descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (j + 1)))
          lo len := by
  rw [stLoop_pairOrbStage_four h, prod_range_ite_eq_descProd _ _ hle hc]

/-- Stage `8` when the carried run blocks form an interval. -/
theorem stLoop_pairOrbStage_eight_eq {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p lo len : ℕ} (hle : lo + len ≤ pairRunUp r s)
    (hc : ∀ j, j < pairRunUp r s →
      (p = r - 2 + pairRunDown r s + pairRunUp r s ↔ lo ≤ j ∧ j < lo + len)) :
    stLoop (pairStrands r s) (pairOrbStage r s 8) (runTop (pairStrands r s) (pairOrbPre r s 8) f)
        p = descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f
          (r - 2 + pairRunDown r s + j)) lo len := by
  rw [stLoop_pairOrbStage_eight h, prod_range_ite_eq_descProd _ _ hle hc]

/-- Stage `9` when the carried run blocks form an interval. -/
theorem stLoop_pairOrbStage_nine_eq {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p lo len : ℕ} (hle : lo + len ≤ pairRunDown r s)
    (hc : ∀ j, j < pairRunDown r s →
      (j + p = r + pairRunDown r s - 2 ↔ lo ≤ j ∧ j < lo + len)) :
    stLoop (pairStrands r s) (pairOrbStage r s 9) (runTop (pairStrands r s) (pairOrbPre r s 9) f)
        p = descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (r - 2 + j))
          lo len := by
  rw [stLoop_pairOrbStage_nine h, prod_range_ite_eq_descProd _ _ hle hc]

/-- Stage `10` when the carried left climbs form an interval. -/
theorem stLoop_pairOrbStage_ten_eq {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p lo len : ℕ} (hle : lo + len ≤ r - 2)
    (hc : ∀ j, j < r - 2 → (j < p ∧ j + p ≤ pairTop r s - 1 ↔ lo ≤ j ∧ j < lo + len)) :
    stLoop (pairStrands r s) (pairOrbStage r s 10)
        (runTop (pairStrands r s) (pairOrbPre r s 10) f) p =
      descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f j) lo len := by
  rw [stLoop_pairOrbStage_ten h, prod_range_ite_eq_descProd _ _ hle hc]

/-- The strand loop of `pairBlocks r s` as the product of the eleven stage loops. -/
theorem stLoop_pairBlocks_eleven (r s : ℕ) (f : Fin (pairStrands r s) → G) (t : ℕ) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      stLoop (pairStrands r s) (pairOrbStage r s 0)
          (runTop (pairStrands r s) (pairOrbPre r s 0) f) t *
        stLoop (pairStrands r s) (pairOrbStage r s 1)
          (runTop (pairStrands r s) (pairOrbPre r s 1) f) (pairOrbPos r s 1 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 2)
          (runTop (pairStrands r s) (pairOrbPre r s 2) f) (pairOrbPos r s 2 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 3)
          (runTop (pairStrands r s) (pairOrbPre r s 3) f) (pairOrbPos r s 3 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 4)
          (runTop (pairStrands r s) (pairOrbPre r s 4) f) (pairOrbPos r s 4 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 5)
          (runTop (pairStrands r s) (pairOrbPre r s 5) f) (pairOrbPos r s 5 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 6)
          (runTop (pairStrands r s) (pairOrbPre r s 6) f) (pairOrbPos r s 6 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 7)
          (runTop (pairStrands r s) (pairOrbPre r s 7) f) (pairOrbPos r s 7 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 8)
          (runTop (pairStrands r s) (pairOrbPre r s 8) f) (pairOrbPos r s 8 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 9)
          (runTop (pairStrands r s) (pairOrbPre r s 9) f) (pairOrbPos r s 9 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 10)
          (runTop (pairStrands r s) (pairOrbPre r s 10) f) (pairOrbPos r s 10 t) := by
  rw [stLoop_pairBlocks_stages]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, pairOrbPos_zero,
    mul_assoc]

/-! ### One-block stages, carried or not -/

/-- Stage `0` (the second Hopf letter) when its block is not carried. -/
theorem stLoop_pairOrbStage_zero_off {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : ¬ (p = pairTop r s)) :
    stLoop (pairStrands r s) (pairOrbStage r s 0) (runTop (pairStrands r s) (pairOrbPre r s 0) f)
      p = 1 := by
  rw [stLoop_pairOrbStage_zero h, ite_eq_right hp]

/-- Stage `0` (the second Hopf letter) when its block is carried. -/
theorem stLoop_pairOrbStage_zero_on {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : p = pairTop r s) :
    stLoop (pairStrands r s) (pairOrbStage r s 0) (runTop (pairStrands r s) (pairOrbPre r s 0) f)
      p = loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s) := by
  rw [stLoop_pairOrbStage_zero h, ite_eq_left hp]

/-- Stage `2` (the top-right climb) when its block is not carried. -/
theorem stLoop_pairOrbStage_two_off {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : ¬ (p = pairTop r s ∨ (pairTop r s - s < p ∧ p < pairTop r s))) :
    stLoop (pairStrands r s) (pairOrbStage r s 2) (runTop (pairStrands r s) (pairOrbPre r s 2) f)
      p = 1 := by
  rw [stLoop_pairOrbStage_two h, ite_eq_right hp]

/-- Stage `2` (the top-right climb) when its block is carried. -/
theorem stLoop_pairOrbStage_two_on {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : p = pairTop r s ∨ (pairTop r s - s < p ∧ p < pairTop r s)) :
    stLoop (pairStrands r s) (pairOrbStage r s 2) (runTop (pairStrands r s) (pairOrbPre r s 2) f)
      p = loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxC r s) := by
  rw [stLoop_pairOrbStage_two h, ite_eq_left hp]

/-- Stage `3` (the last round) when its block is not carried. -/
theorem stLoop_pairOrbStage_three_off {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : ¬ (p = pairTop r s + 1 - s ∨ (r - 2 < p ∧ p < pairTop r s + 1 - s))) :
    stLoop (pairStrands r s) (pairOrbStage r s 3) (runTop (pairStrands r s) (pairOrbPre r s 3) f)
      p = 1 := by
  rw [stLoop_pairOrbStage_three h, ite_eq_right hp]

/-- Stage `3` (the last round) when its block is carried. -/
theorem stLoop_pairOrbStage_three_on {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : p = pairTop r s + 1 - s ∨ (r - 2 < p ∧ p < pairTop r s + 1 - s)) :
    stLoop (pairStrands r s) (pairOrbStage r s 3) (runTop (pairStrands r s) (pairOrbPre r s 3) f)
      p = loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1)) := by
  rw [stLoop_pairOrbStage_three h, ite_eq_left hp]

/-- Stage `5` (the first Hopf letter) when its block is not carried. -/
theorem stLoop_pairOrbStage_five_off {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : ¬ (p = pairTop r s)) :
    stLoop (pairStrands r s) (pairOrbStage r s 5) (runTop (pairStrands r s) (pairOrbPre r s 5) f)
      p = 1 := by
  rw [stLoop_pairOrbStage_five h, ite_eq_right hp]

/-- Stage `5` (the first Hopf letter) when its block is carried. -/
theorem stLoop_pairOrbStage_five_on {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : p = pairTop r s) :
    stLoop (pairStrands r s) (pairOrbStage r s 5) (runTop (pairStrands r s) (pairOrbPre r s 5) f)
      p = loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH1 r s) := by
  rw [stLoop_pairOrbStage_five h, ite_eq_left hp]

/-- Stage `6` (the first round) when its block is not carried. -/
theorem stLoop_pairOrbStage_six_off {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : ¬ (p = pairTop r s ∨ (pairTop r s - r < p ∧ p < pairTop r s))) :
    stLoop (pairStrands r s) (pairOrbStage r s 6) (runTop (pairStrands r s) (pairOrbPre r s 6) f)
      p = 1 := by
  rw [stLoop_pairOrbStage_six h, ite_eq_right hp]

/-- Stage `6` (the first round) when its block is carried. -/
theorem stLoop_pairOrbStage_six_on {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : p = pairTop r s ∨ (pairTop r s - r < p ∧ p < pairTop r s)) :
    stLoop (pairStrands r s) (pairOrbStage r s 6) (runTop (pairStrands r s) (pairOrbPre r s 6) f)
      p = loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0) := by
  rw [stLoop_pairOrbStage_six h, ite_eq_left hp]

/-- Stage `7` (the big climb) when its block is not carried. -/
theorem stLoop_pairOrbStage_seven_off {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : ¬ (p = pairTop r s + 1 - r ∨
      (r - 2 + pairRunDown r s + pairRunUp r s < p ∧ p < pairTop r s + 1 - r))) :
    stLoop (pairStrands r s) (pairOrbStage r s 7) (runTop (pairStrands r s) (pairOrbPre r s 7) f)
      p = 1 := by
  rw [stLoop_pairOrbStage_seven h, ite_eq_right hp]

/-- Stage `7` (the big climb) when its block is carried. -/
theorem stLoop_pairOrbStage_seven_on {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p : ℕ}
    (hp : p = pairTop r s + 1 - r ∨
      (r - 2 + pairRunDown r s + pairRunUp r s < p ∧ p < pairTop r s + 1 - r)) :
    stLoop (pairStrands r s) (pairOrbStage r s 7) (runTop (pairStrands r s) (pairOrbPre r s 7) f)
      p = loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxB r s) := by
  rw [stLoop_pairOrbStage_seven h, ite_eq_left hp]

/-- Computational check of the stage decomposition: the list, the offsets, and the block
positions collected by every strand, stage by stage. -/
def pairOrbCheckStages (r s : ℕ) : Bool :=
  pairBlocks r s == pairOrbPre r s 0 ++ pairOrbStage r s 0 &&
    (List.range 11).all (fun k ↦ (pairOrbPre r s k).length == pairOrbStageOff r s k) &&
    (List.range (pairStrands r s)).all fun t ↦
      pairOrbStLoopIdx (pairBlocks r s) t ==
        ((List.range 11).map fun k ↦ (pairOrbStLoopIdx (pairOrbStage r s k)
          (pairOrbPos r s k t)).map (· + pairOrbStageOff r s k)).flatten

#guard [(2, 3), (2, 5), (3, 4), (3, 5), (4, 5), (5, 7), (4, 9)].all fun p ↦
  pairOrbCheckStages p.1 p.2

end AJConjecture
