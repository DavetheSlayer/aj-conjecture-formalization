import Mathlib
import AJTwist.Classical.TwCBlocks

/-!
# The run of the twist chain

Let `X = twChain M j₀ ℓ` (`0 < j₀ < M`) act on a tuple `g` of `M + twExtra ℓ` elements which it
restores on the new levels (`runTop X g k = g k` for `k ≥ M`; true for the tuple of a fixed
point of the whole block list, because no other block touches the new levels). Write
`L = twcChainLoop M j₀ ℓ g` for the ratio of the chamber products of level `1` above and below
the chain. Then:

* `length_twChain`, `twChain_valid`;
* `prePr_runTop_twChain`: on the old levels the chain acts on the chamber products as a band
  `b(0, j₀)` with loop `L`: the chamber products of the levels `1, …, j₀` are multiplied by `L`
  on the left and the others are unchanged. Reason: only the two long bands of the chain have
  old levels in their gaps, `[1, …]` for the one from `0` and `[j₀ + 1, …]` for the one from
  `j₀`; the levels `j₀ + 1, …, M` receive the product of the two loops, which is `1` because the
  chamber product of level `M` is the total product (unchanged by every block) divided by the
  restored new entries;
* `twChain_detour`: the strand map and the loops collected in the chain. The old positions other
  than `0`, `j₀` are fixed and collect `L` (between `0` and `j₀`) or `1`. Starting from the top
  position `j₀` and iterating the strand map of the chain one meets only new positions and then
  `0`; the loops collected on the way multiply to `L^(1-ℓ)` (untwisted: `L`). Starting from `0`
  one meets the other new positions and then `j₀`; the product is `L^ℓ` (untwisted: `1`).
  Together the two detours contain every new position once.

All chain letters between new discs and the long band from `j₀` have loops `L^(±1)`; the proof is
by induction on `|ℓ|`, separately for the two signs (the chain for `ℓ < 0` has a descending and
an ascending run of positive letters, the chain for `ℓ > 0` an ascending and a descending run of
negative letters), using the restored new entries to compute the loops as in
`prePr_runTop_twChain`.

Checked numerically (`SCR/C/py/w3_chain.py`): the strand map for `M ∈ {5, 7, 12}`,
`j₀ ∈ {1, 3, M - 1}`, `|ℓ| ≤ 4`; the loops and chamber products on `SU(2)` representations of
the groups of `twBlocks`, `(r, s) ∈ {(2,3), (3,4)}`, `ℓ ∈ {±1, ±2}` (`w2_twk_all.py`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The loop of the chain: the ratio of the chamber products of level `1` above and below
it. -/
def twcChainLoop (M j₀ : ℕ) (ℓ : ℤ) (g : Fin (M + twExtra ℓ) → G) : G :=
  prePr (runTop (M + twExtra ℓ) (twChain M j₀ ℓ) g) 1 * (prePr g 1)⁻¹

/-- The chain has `twExtra ℓ + 1` blocks. -/
theorem length_twChain (M j₀ : ℕ) (ℓ : ℤ) : (twChain M j₀ ℓ).length = twExtra ℓ + 1 := by
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne
    rw [twChain, ite_eq_right hl.ne, ite_eq_left hl, twExtra, ite_eq_left hl.le]
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega
  · rfl
  · rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt, twExtra, ite_eq_right hl.not_ge]
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega

/-- The blocks of the chain live on `M + twExtra ℓ` strands. -/
theorem twChain_valid {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ) :
    ∀ b ∈ twChain M j₀ ℓ, b.Valid (M + twExtra ℓ) := by
  intro b hb
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne
    rw [twChain, ite_eq_right hl.ne, ite_eq_left hl] at hb
    rw [twExtra, ite_eq_left hl.le]
    generalize ℓ.natAbs = n at hb hn ⊢
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hb
    rcases hb with (((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | rfl <;>
      simp only [SBlock.Valid] <;> omega
  · rw [twChain, ite_eq_left rfl, List.mem_singleton] at hb
    subst hb
    simp only [SBlock.Valid]
    omega
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne'
    rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt] at hb
    rw [twExtra, ite_eq_right hl.not_ge]
    generalize ℓ.natAbs = n at hb hn ⊢
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hb
    rcases hb with (((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | rfl <;>
      simp only [SBlock.Valid] <;> omega

/-- Decide the conditions of `if … then … else` by `omega`. -/
local macro "twc_ite" : tactic =>
  `(tactic| simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte])

/-- Decide the conditions of `if … then … else` by `omega` and remove the factors `1`. -/
local macro "twc_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, mul_one,
    one_mul] $[$loc]?)

/-- A block on two adjacent levels: the positive letter `band i (i + 1)` (`e = true`) or the
negative letter `neg i`. -/
private def twcAdj (e : Bool) (i : ℕ) : SBlock :=
  match e with
  | true => SBlock.band i (i + 1)
  | false => SBlock.neg i

/-- The strand map of a letter is the transposition of its two levels. -/
private theorem twcAdj_perm_twCChain (e : Bool) (i t : ℕ) :
    (twcAdj e i).perm t = if t = i then i + 1 else if t = i + 1 then i else t := by
  cases e <;> rfl

/-- The gap of a letter is the level between its two strands. -/
private theorem twcAdj_gapLoop_twCChain {m : ℕ} (e : Bool) (i : ℕ) (f : Fin m → G) (n : ℕ) :
    (twcAdj e i).gapLoop f n = if n = i + 1 then (twcAdj e i).loop f else 1 := by
  have h : (i + 1 ≤ n ∧ n ≤ i + 1) = (n = i + 1) := propext (by omega)
  cases e <;> simp only [twcAdj, SBlock.gapLoop, SBlock.lo, SBlock.hi, h]

/-- A positive letter is carried by the strand at its upper level. -/
private theorem twcAdj_true_strandLoop_twCChain {m : ℕ} (i : ℕ) (f : Fin m → G) (t : ℕ) :
    (twcAdj true i).strandLoop f t = if t = i + 1 then (twcAdj true i).loop f else 1 := by
  have h : (t = i + 1 ∨ i < t ∧ t < i + 1) = (t = i + 1) := propext (by omega)
  simp only [twcAdj, SBlock.strandLoop, SBlock.carries, decide_eq_true_eq, h]

/-- A negative letter is carried by the strand at its lower level. -/
private theorem twcAdj_false_strandLoop_twCChain {m : ℕ} (i : ℕ) (f : Fin m → G) (t : ℕ) :
    (twcAdj false i).strandLoop f t = if t = i then (twcAdj false i).loop f else 1 := by
  simp only [twcAdj, SBlock.strandLoop, SBlock.carries, decide_eq_true_eq]

/-- The gap factor of a band. -/
private theorem gapLoop_band_twCChain {m : ℕ} (f : Fin m → G) (i j n : ℕ) :
    (SBlock.band i j).gapLoop f n = if i + 1 ≤ n ∧ n ≤ j then (SBlock.band i j).loop f else 1 :=
  rfl

/-- The loop collected by a strand in a band. -/
private theorem strandLoop_band_twCChain {m : ℕ} (f : Fin m → G) (i j t : ℕ) :
    (SBlock.band i j).strandLoop f t =
      if t = j ∨ (i < t ∧ t < j) then (SBlock.band i j).loop f else 1 := by
  simp only [SBlock.strandLoop, SBlock.carries, decide_eq_true_eq]

/-- The strand map of a band. -/
private theorem perm_band_twCChain (i j t : ℕ) :
    (SBlock.band i j).perm t = if t = i then j else if t = j then i else t :=
  rfl

/-- The gap factor of one block. -/
private theorem gapProd_singleton_twCChain {m : ℕ} (b : SBlock) (f : Fin m → G) (n : ℕ) :
    gapProd m [b] f n = b.gapLoop f n := by
  rw [gapProd, gapProd, one_mul]

/-- The strand loop of one block. -/
private theorem stLoop_singleton_twCChain {m : ℕ} (b : SBlock) (f : Fin m → G) (t : ℕ) :
    stLoop m [b] f t = b.strandLoop f t := by
  rw [stLoop, stLoop, one_mul, stPerm]

/-- The letters on the levels `a, a + 1, …, a + k - 1`, in this order. -/
private def twcAsc (e : Bool) (a : ℕ) : ℕ → List SBlock
  | 0 => []
  | k + 1 => twcAsc e a k ++ [twcAdj e (a + k)]

/-- The letters on the levels `a + k - 1, …, a + 1, a`, in this order. -/
private def twcDesc (e : Bool) (a : ℕ) : ℕ → List SBlock
  | 0 => []
  | k + 1 => twcAdj e (a + k) :: twcDesc e a k

/-- A mapped range of letters on increasing levels is an ascending run. -/
private theorem map_range_eq_twcAsc_twCChain (e : Bool) (a k : ℕ) (F : ℕ → SBlock)
    (hF : ∀ i, i < k → F i = twcAdj e (a + i)) : (List.range k).map F = twcAsc e a k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, ih fun i hi ↦ hF i (by omega),
      hF k (by omega), twcAsc]

/-- A mapped range of letters on decreasing levels is a descending run. -/
private theorem map_range_eq_twcDesc_twCChain (e : Bool) (a k : ℕ) (F : ℕ → SBlock)
    (hF : ∀ i, i < k → F i = twcAdj e (a + k - 1 - i)) :
    (List.range k).map F = twcDesc e a k := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    have h1 : (List.range k).map (F ∘ Nat.succ) = twcDesc e a k := ih _ fun i hi ↦ by
      rw [Function.comp_apply, hF (i + 1) (by omega)]
      congr 1
      omega
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, h1, hF 0 (by omega), twcDesc]
    rfl

/-- An ascending run has no gap factor off its levels. -/
private theorem gapProd_twcAsc_one_twCChain {m : ℕ} (e : Bool) (a k : ℕ) (f : Fin m → G) (p : ℕ)
    (hp : ¬(a + 1 ≤ p ∧ p ≤ a + k)) : gapProd m (twcAsc e a k) f p = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [twcAsc, gapProd_append, ih (by omega), gapProd_singleton_twCChain, twcAdj_gapLoop_twCChain,
      ite_eq_right (by omega), mul_one]

/-- A descending run has no gap factor off its levels. -/
private theorem gapProd_twcDesc_one_twCChain {m : ℕ} (e : Bool) (a k : ℕ) (f : Fin m → G) (p : ℕ)
    (hp : ¬(a + 1 ≤ p ∧ p ≤ a + k)) : gapProd m (twcDesc e a k) f p = 1 := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [twcDesc, gapProd, ih _ (by omega), twcAdj_gapLoop_twCChain, ite_eq_right (by omega),
      mul_one]

/-- The strand map of an ascending run: the top strand goes to the bottom, the others move
up by one level. -/
private theorem stPerm_twcAsc_twCChain (e : Bool) (a k t : ℕ) :
    stPerm (twcAsc e a k) t =
      if t = a + k then a else if a ≤ t ∧ t < a + k then t + 1 else t := by
  induction k generalizing t with
  | zero =>
    simp only [twcAsc, stPerm]
    split_ifs <;> omega
  | succ k ih =>
    rw [twcAsc, stPerm_append, ih, stPerm, stPerm, twcAdj_perm_twCChain]
    split_ifs <;> omega

/-- The strand map of a descending run: the bottom strand goes to the top, the others move
down by one level. -/
private theorem stPerm_twcDesc_twCChain (e : Bool) (a k t : ℕ) :
    stPerm (twcDesc e a k) t =
      if t = a then a + k else if a < t ∧ t ≤ a + k then t - 1 else t := by
  induction k generalizing t with
  | zero =>
    simp only [twcDesc, stPerm]
    split_ifs <;> omega
  | succ k ih =>
    rw [twcDesc, stPerm, ih, twcAdj_perm_twCChain]
    split_ifs <;> omega

/-- In an ascending run of positive letters with loops `x` only the top strand collects loops:
all of them. -/
private theorem stLoop_twcAsc_band_twCChain {m : ℕ} (a k : ℕ) (f : Fin m → G) (x : G)
    (hx : ∀ p, a + 1 ≤ p → p ≤ a + k → gapProd m (twcAsc true a k) f p = x) (t : ℕ) :
    stLoop m (twcAsc true a k) f t = if t = a + k then x ^ k else 1 := by
  induction k generalizing t with
  | zero => simp [twcAsc, stLoop]
  | succ k ih =>
    have hb : (twcAdj true (a + k)).loop (runTop m (twcAsc true a k) f) = x := by
      have := hx (a + k + 1) (by omega) (by omega)
      rwa [twcAsc, gapProd_append, gapProd_singleton_twCChain, twcAdj_gapLoop_twCChain,
        ite_eq_left rfl, gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega), mul_one] at this
    have hx' : ∀ p, a + 1 ≤ p → p ≤ a + k → gapProd m (twcAsc true a k) f p = x := by
      intro p h1 h2
      have := hx p h1 (by omega)
      rwa [twcAsc, gapProd_append, gapProd_singleton_twCChain, twcAdj_gapLoop_twCChain,
        ite_eq_right (by omega), one_mul] at this
    rw [twcAsc, stLoop_append, stLoop_singleton_twCChain, stPerm, stPerm,
      twcAdj_true_strandLoop_twCChain, hb, ih hx', twcAdj_perm_twCChain]
    by_cases h1 : t = a + k + 1
    · subst h1
      twc_ite
      rw [pow_succ']
    · twc_ite
      rw [one_mul]
      split_ifs <;> first | omega | rfl

/-- In an ascending run of negative letters with loops `x` every strand but the top one
collects one loop. -/
private theorem stLoop_twcAsc_neg_twCChain {m : ℕ} (a k : ℕ) (f : Fin m → G) (x : G)
    (hx : ∀ p, a + 1 ≤ p → p ≤ a + k → gapProd m (twcAsc false a k) f p = x) (t : ℕ) :
    stLoop m (twcAsc false a k) f t = if a ≤ t ∧ t < a + k then x else 1 := by
  induction k generalizing t with
  | zero =>
    simp only [twcAsc, stLoop]
    twc_ite
  | succ k ih =>
    have hb : (twcAdj false (a + k)).loop (runTop m (twcAsc false a k) f) = x := by
      have := hx (a + k + 1) (by omega) (by omega)
      rwa [twcAsc, gapProd_append, gapProd_singleton_twCChain, twcAdj_gapLoop_twCChain,
        ite_eq_left rfl, gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega), mul_one] at this
    have hx' : ∀ p, a + 1 ≤ p → p ≤ a + k → gapProd m (twcAsc false a k) f p = x := by
      intro p h1 h2
      have := hx p h1 (by omega)
      rwa [twcAsc, gapProd_append, gapProd_singleton_twCChain, twcAdj_gapLoop_twCChain,
        ite_eq_right (by omega), one_mul] at this
    rw [twcAsc, stLoop_append, stLoop_singleton_twCChain, stPerm, stPerm,
      twcAdj_false_strandLoop_twCChain, hb, ih hx', twcAdj_perm_twCChain]
    by_cases h1 : t = a + k
    · subst h1
      twc_ite
      rw [mul_one]
    · by_cases h2 : t = a + k + 1
      · subst h2
        twc_ite
        rw [mul_one]
      · twc_ite
        rw [one_mul]
        split_ifs <;> first | omega | rfl

/-- In a descending run of positive letters with loops `x` every strand but the bottom one
collects one loop. -/
private theorem stLoop_twcDesc_band_twCChain {m : ℕ} (a k : ℕ) (f : Fin m → G) (x : G)
    (hx : ∀ p, a + 1 ≤ p → p ≤ a + k → gapProd m (twcDesc true a k) f p = x) (t : ℕ) :
    stLoop m (twcDesc true a k) f t = if a < t ∧ t ≤ a + k then x else 1 := by
  induction k generalizing f with
  | zero =>
    simp only [twcDesc, stLoop]
    twc_ite
  | succ k ih =>
    have hb : (twcAdj true (a + k)).loop f = x := by
      have := hx (a + k + 1) (by omega) (by omega)
      rwa [twcDesc, gapProd, twcAdj_gapLoop_twCChain, ite_eq_left rfl,
        gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega), one_mul] at this
    have hx' : ∀ p, a + 1 ≤ p → p ≤ a + k →
        gapProd m (twcDesc true a k) ((twcAdj true (a + k)).step m f) p = x := by
      intro p h1 h2
      have := hx p h1 (by omega)
      rwa [twcDesc, gapProd, twcAdj_gapLoop_twCChain, ite_eq_right (by omega), mul_one] at this
    rw [twcDesc, stLoop, ih _ hx', twcAdj_true_strandLoop_twCChain, hb, stPerm_twcDesc_twCChain]
    by_cases h1 : t = a + k + 1
    · subst h1
      twc_ite
      rw [one_mul]
    · by_cases h2 : t = a
      · subst h2
        twc_ite
        rw [mul_one]
      · twc_ite
        split_ifs <;> first | omega | rw [mul_one]

/-- In a descending run of negative letters with loops `x` only the bottom strand collects
loops: all of them. -/
private theorem stLoop_twcDesc_neg_twCChain {m : ℕ} (a k : ℕ) (f : Fin m → G) (x : G)
    (hx : ∀ p, a + 1 ≤ p → p ≤ a + k → gapProd m (twcDesc false a k) f p = x) (t : ℕ) :
    stLoop m (twcDesc false a k) f t = if t = a then x ^ k else 1 := by
  induction k generalizing f with
  | zero => simp [twcDesc, stLoop]
  | succ k ih =>
    have hb : (twcAdj false (a + k)).loop f = x := by
      have := hx (a + k + 1) (by omega) (by omega)
      rwa [twcDesc, gapProd, twcAdj_gapLoop_twCChain, ite_eq_left rfl,
        gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega), one_mul] at this
    have hx' : ∀ p, a + 1 ≤ p → p ≤ a + k →
        gapProd m (twcDesc false a k) ((twcAdj false (a + k)).step m f) p = x := by
      intro p h1 h2
      have := hx p h1 (by omega)
      rwa [twcDesc, gapProd, twcAdj_gapLoop_twCChain, ite_eq_right (by omega), mul_one] at this
    rw [twcDesc, stLoop, ih _ hx', twcAdj_false_strandLoop_twCChain, hb, stPerm_twcDesc_twCChain]
    by_cases h1 : t = a
    · subst h1
      twc_ite
      rw [pow_succ]
    · twc_ite
      split_ifs <;> first | omega | rw [mul_one]

/-- A block without the level `n` in its gap does not contribute to the gap factor. -/
private theorem gapProd_eq_one_twCChain {m : ℕ} (bs : List SBlock) (f : Fin m → G) (n : ℕ)
    (h : ∀ b ∈ bs, ¬(b.lo ≤ n ∧ n ≤ b.hi)) : gapProd m bs f n = 1 := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rw [gapProd, ih _ h.2, SBlock.gapLoop, ite_eq_right h.1, one_mul]

/-- The upper end of the gap of a block living on `m` strands is below `m`. -/
private theorem hi_lt_twCChain {m : ℕ} (b : SBlock) (hb : b.Valid m) : b.hi < m := by
  cases b <;> simp only [SBlock.Valid, SBlock.hi] at hb ⊢ <;> omega

/-- Tuples with the same total product and the same entries from `M` on have the same chamber
products from the level `M` on. -/
private theorem prePr_eq_of_tail_twCChain {m M : ℕ} (f f' : Fin m → G)
    (hk : ∀ k : Fin m, M ≤ (k : ℕ) → f' k = f k) (hm : prePr f' m = prePr f m) (d p : ℕ)
    (hp : M ≤ p) (hd : p + d = m) : prePr f' p = prePr f p := by
  induction d generalizing p with
  | zero =>
    rw [show p = m by omega]
    exact hm
  | succ d ih =>
    have h1 := ih (p + 1) (by omega) (by omega)
    rw [prePr_succ f' p (by omega), prePr_succ f p (by omega), hk ⟨p, by omega⟩ hp] at h1
    exact mul_right_cancel h1

/-- A run that restores the entries from `M` on has trivial gap factors from the level `M`
on. -/
private theorem gapProd_eq_one_of_fix_twCChain {m M : ℕ} (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (g : Fin m → G)
    (hfix : ∀ k : Fin m, M ≤ (k : ℕ) → runTop m bs g k = g k) {p : ℕ} (hp : M ≤ p) :
    gapProd m bs g p = 1 := by
  have hbig : ∀ q, m ≤ q → gapProd m bs g q = 1 := fun q hq ↦
    gapProd_eq_one_twCChain bs g q fun b hb h ↦ by
      have := hi_lt_twCChain b (hv b hb)
      omega
  by_cases hpm : p ≤ m
  · have htot : prePr (runTop m bs g) m = prePr g m := by
      rw [prePr_runTop bs hv, hbig m le_rfl, one_mul]
    have h := prePr_eq_of_tail_twCChain g (runTop m bs g) hfix htot (m - p) p hp (by omega)
    rw [prePr_runTop bs hv] at h
    exact mul_right_cancel (h.trans (one_mul _).symm)
  · exact hbig p (by omega)

/-- Evaluate the strand map of a band or a run of letters at a position. -/
local macro "twc_perm" : tactic =>
  `(tactic| (simp (disch := omega) only [perm_band_twCChain, stPerm_twcAsc_twCChain,
    stPerm_twcDesc_twCChain, ite_eq_left, ite_eq_right, ↓reduceIte, true_or, or_true, true_and,
    and_true, false_or, or_false, false_and, and_false]) <;> omega)

/-- Decide the conditions of `if … then … else` by `omega`, then use `group`. -/
local macro "twc_group" : tactic =>
  `(tactic| (simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, mul_one,
    one_mul, zpow_zero, zpow_one, zpow_neg_one, true_or, or_true, true_and, and_true, false_or,
    or_false, false_and, and_false]) <;> group)

/-- A long band, a run of letters, a long band, a run of letters and a long band. -/
private def twcFive (b0 : SBlock) (R1 : List SBlock) (J : SBlock) (R2 : List SBlock)
    (Z : SBlock) : List SBlock :=
  b0 :: (R1 ++ J :: (R2 ++ [Z]))

/-- The gap factor of five blocks. -/
private theorem gapProd_twcFive_twCChain {m : ℕ} (b0 J Z : SBlock) (R1 R2 : List SBlock)
    (g : Fin m → G) (p : ℕ) :
    gapProd m (twcFive b0 R1 J R2 Z) g p =
      Z.gapLoop (runTop m R2 (J.step m (runTop m R1 (b0.step m g)))) p *
        gapProd m R2 (J.step m (runTop m R1 (b0.step m g))) p *
        J.gapLoop (runTop m R1 (b0.step m g)) p * gapProd m R1 (b0.step m g) p *
        b0.gapLoop g p := by
  rw [twcFive, gapProd, gapProd_append, gapProd, gapProd_append, gapProd_singleton_twCChain]

/-- The strand map of five blocks. -/
private theorem stPerm_twcFive_twCChain (b0 J Z : SBlock) (R1 R2 : List SBlock) (t : ℕ) :
    stPerm (twcFive b0 R1 J R2 Z) t =
      b0.perm (stPerm R1 (J.perm (stPerm R2 (Z.perm t)))) := by
  simp only [twcFive, stPerm, stPerm_append]

/-- The strand loop of five blocks. -/
private theorem stLoop_twcFive_twCChain {m : ℕ} (b0 J Z : SBlock) (R1 R2 : List SBlock)
    (g : Fin m → G) (t : ℕ) :
    stLoop m (twcFive b0 R1 J R2 Z) g t =
      Z.strandLoop (runTop m R2 (J.step m (runTop m R1 (b0.step m g)))) t *
        stLoop m R2 (J.step m (runTop m R1 (b0.step m g))) (Z.perm t) *
        J.strandLoop (runTop m R1 (b0.step m g)) (stPerm R2 (Z.perm t)) *
        stLoop m R1 (b0.step m g) (J.perm (stPerm R2 (Z.perm t))) *
        b0.strandLoop g (stPerm R1 (J.perm (stPerm R2 (Z.perm t)))) := by
  rw [twcFive, stLoop, stLoop_append, stLoop, stLoop_append, stLoop_singleton_twCChain]
  simp only [stPerm, stPerm_append, mul_assoc]

/-- The loops of the chain for a negative twist, from the gap relations of the new levels. -/
private theorem twc_neg_loops_twCChain {m M j₀ d : ℕ} (hjM : j₀ < M) (g g1 g2 g3 g4 : Fin m → G)
    (hgap : ∀ p, M ≤ p → (SBlock.band j₀ (M + 2 * d + 1)).gapLoop g4 p *
      gapProd m (twcAsc true (M + d + 1) d) g3 p * (SBlock.band M (M + d + 1)).gapLoop g2 p *
      gapProd m (twcDesc true M d) g1 p * (SBlock.band 0 (M + d)).gapLoop g p = 1) :
    (SBlock.band j₀ (M + 2 * d + 1)).loop g4 = ((SBlock.band 0 (M + d)).loop g)⁻¹ ∧
      (SBlock.band M (M + d + 1)).loop g2 = (SBlock.band 0 (M + d)).loop g ∧
      (∀ p, M + d + 1 + 1 ≤ p → p ≤ M + d + 1 + d →
        gapProd m (twcAsc true (M + d + 1) d) g3 p = (SBlock.band 0 (M + d)).loop g) ∧
      ∀ p, M + 1 ≤ p → p ≤ M + d →
        gapProd m (twcDesc true M d) g1 p = ((SBlock.band 0 (M + d)).loop g)⁻¹ := by
  simp only [gapLoop_band_twCChain] at hgap
  have hZ : (SBlock.band j₀ (M + 2 * d + 1)).loop g4 = ((SBlock.band 0 (M + d)).loop g)⁻¹ := by
    have h := hgap M le_rfl
    rw [gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega),
      gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    exact eq_inv_of_mul_eq_one_left h
  have hJ : (SBlock.band M (M + d + 1)).loop g2 = (SBlock.band 0 (M + d)).loop g := by
    have h := hgap (M + d + 1) (by omega)
    rw [gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega),
      gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    rw [hZ] at h
    exact (inv_mul_eq_one.1 h).symm
  refine ⟨hZ, hJ, fun p h1 h2 ↦ ?_, fun p h1 h2 ↦ ?_⟩
  · have h := hgap p (by omega)
    rw [gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    rw [hZ] at h
    exact (inv_mul_eq_one.1 h).symm
  · have h := hgap p (by omega)
    rw [gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    rw [hZ, hJ, inv_mul_cancel, one_mul] at h
    exact eq_inv_of_mul_eq_one_left h

/-- The chain for the twist `-(d + 1)`. -/
private def twcNegX (M j₀ d : ℕ) : List SBlock :=
  twcFive (SBlock.band 0 (M + d)) (twcDesc true M d) (SBlock.band M (M + d + 1))
    (twcAsc true (M + d + 1) d) (SBlock.band j₀ (M + 2 * d + 1))

/-- The strand map of the chain for the twist `-(d + 1)`. -/
private def twcNegP (M j₀ d t : ℕ) : ℕ :=
  if t = 0 then M + d else if t = j₀ then 0 else if t < M then t else if t = M then M + d + 1
  else if t ≤ M + d then t - 1 else if t < M + 2 * d + 1 then t + 1 else j₀

/-- The strand loops of the chain for the twist `-(d + 1)`, `x` the loop of the chain. -/
private def twcNegS (M j₀ d : ℕ) (x : G) (t : ℕ) : G :=
  if t = 0 then 1 else if t = j₀ then x ^ (d + 2) else if t < M then (if t < j₀ then x else 1)
  else if t = M then x⁻¹ else if t ≤ M + d then 1 else if t < M + 2 * d + 1 then x⁻¹ else 1

/-- The strand map and the strand loops of five blocks, from the positions of the strand
between them. -/
private theorem twcFive_eval_twCChain {m : ℕ} (b0 J Z : SBlock) (R1 R2 : List SBlock)
    (g : Fin m → G) (t t1 t2 t3 t4 : ℕ) (h1 : Z.perm t = t1) (h2 : stPerm R2 t1 = t2)
    (h3 : J.perm t2 = t3) (h4 : stPerm R1 t3 = t4) :
    stPerm (twcFive b0 R1 J R2 Z) t = b0.perm t4 ∧
      stLoop m (twcFive b0 R1 J R2 Z) g t =
        Z.strandLoop (runTop m R2 (J.step m (runTop m R1 (b0.step m g)))) t *
          stLoop m R2 (J.step m (runTop m R1 (b0.step m g))) t1 *
          J.strandLoop (runTop m R1 (b0.step m g)) t2 * stLoop m R1 (b0.step m g) t3 *
          b0.strandLoop g t4 := by
  subst h1 h2 h3 h4
  exact ⟨stPerm_twcFive_twCChain _ _ _ _ _ _, stLoop_twcFive_twCChain _ _ _ _ _ _ _⟩

/-- The strand map and the strand loops of the chain for a negative twist. -/
private theorem twc_neg_strand_twCChain {m M j₀ d : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (g : Fin m → G)
    (hgap : ∀ p, M ≤ p → gapProd m (twcNegX M j₀ d) g p = 1) (t : ℕ)
    (ht : t < M + 2 * d + 2) :
    stPerm (twcNegX M j₀ d) t = twcNegP M j₀ d t ∧
      stLoop m (twcNegX M j₀ d) g t =
        twcNegS M j₀ d ((SBlock.band 0 (M + d)).loop g) t := by
  simp only [twcNegX, gapProd_twcFive_twCChain] at hgap
  obtain ⟨hZ, hJ, hA, hD⟩ := twc_neg_loops_twCChain hjM _ _ _ _ _ hgap
  have E := twcFive_eval_twCChain (SBlock.band 0 (M + d)) (SBlock.band M (M + d + 1))
    (SBlock.band j₀ (M + 2 * d + 1)) (twcDesc true M d) (twcAsc true (M + d + 1) d) g t
  simp only [strandLoop_band_twCChain, stLoop_twcAsc_band_twCChain _ _ _ _ hA,
    stLoop_twcDesc_band_twCChain _ _ _ _ hD, hZ, hJ] at E
  rw [twcNegX, twcNegP, twcNegS]
  generalize (SBlock.band 0 (M + d)).loop g = x at E ⊢
  clear hgap hZ hJ hA hD
  by_cases c1 : t = 0
  · obtain ⟨hp, hs⟩ := E t t t t (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c2 : t = j₀
  · obtain ⟨hp, hs⟩ := E (M + 2 * d + 1) (M + d + 1) M (M + d) (by twc_perm) (by twc_perm)
      (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c3 : t < M
  · obtain ⟨hp, hs⟩ := E t t t t (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    by_cases c3' : t < j₀
    · exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
    · exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c4 : t = M
  · obtain ⟨hp, hs⟩ := E t t (M + d + 1) (M + d + 1) (by twc_perm) (by twc_perm)
      (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c5 : t ≤ M + d
  · obtain ⟨hp, hs⟩ := E t t t (t - 1) (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c6 : t < M + 2 * d + 1
  · obtain ⟨hp, hs⟩ := E t (t + 1) (t + 1) (t + 1) (by twc_perm) (by twc_perm) (by twc_perm)
      (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  · obtain ⟨hp, hs⟩ := E j₀ j₀ j₀ j₀ (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩

/-- The gap factors of the old levels for a negative twist. -/
private theorem twc_neg_oldgap_twCChain {m M j₀ d : ℕ} (hjM : j₀ < M) (g : Fin m → G)
    (hgap : ∀ p, M ≤ p → gapProd m (twcNegX M j₀ d) g p = 1) (n : ℕ) (hn : n ≤ M) :
    gapProd m (twcNegX M j₀ d) g n =
      if 1 ≤ n ∧ n ≤ j₀ then (SBlock.band 0 (M + d)).loop g else 1 := by
  simp only [twcNegX, gapProd_twcFive_twCChain] at hgap
  obtain ⟨hZ, -, -, -⟩ := twc_neg_loops_twCChain hjM _ _ _ _ _ hgap
  rw [twcNegX, gapProd_twcFive_twCChain, gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega),
    gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)]
  simp only [gapLoop_band_twCChain, hZ]
  generalize (SBlock.band 0 (M + d)).loop g = x
  by_cases h1 : n = 0
  · twc_group
  by_cases h2 : n ≤ j₀
  · twc_group
  · twc_group

/-- The statement of `twChain_detour` for a block list `X` with `e` new levels and loop `L`. -/
private def TwcDetour {m : ℕ} (M j₀ e : ℕ) (X : List SBlock) (g : Fin m → G) (L : G)
    (ℓ : ℤ) : Prop :=
  (∀ t, t < M → t ≠ 0 → t ≠ j₀ →
      stPerm X t = t ∧ stLoop m X g t = if t < j₀ then L else 1) ∧
    ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 0 < k₂ ∧ k₁ + k₂ = e + 2 ∧
      (stPerm X)^[k₁] j₀ = 0 ∧
      (∀ i, 0 < i → i < k₁ → M ≤ (stPerm X)^[i] j₀) ∧
      ((List.range k₁).map fun i ↦ stLoop m X g ((stPerm X)^[i] j₀)).prod = L ^ (1 - ℓ) ∧
      (stPerm X)^[k₂] 0 = j₀ ∧
      (∀ i, 0 < i → i < k₂ → M ≤ (stPerm X)^[i] 0) ∧
      ((List.range k₂).map fun i ↦ stLoop m X g ((stPerm X)^[i] 0)).prod = L ^ ℓ ∧
      ∀ p, M ≤ p → p < M + e →
        (∃ i, 0 < i ∧ i < k₁ ∧ (stPerm X)^[i] j₀ = p) ∨
          ∃ i, 0 < i ∧ i < k₂ ∧ (stPerm X)^[i] 0 = p

/-- The detour statement from a description of the orbit of `0`: `path i` is its `i`-th
position, `L ^ ex i` the loop collected there and `c` the partial sums of `ex`. -/
private theorem twcDetour_of_path_twCChain {m M j₀ e : ℕ} {X : List SBlock} {g : Fin m → G} {L : G}
    {ℓ : ℤ}
    (hold : ∀ t, t < M → t ≠ 0 → t ≠ j₀ →
      stPerm X t = t ∧ stLoop m X g t = if t < j₀ then L else 1)
    (hj₀ : stPerm X j₀ = 0 ∧ stLoop m X g j₀ = L ^ (1 - ℓ))
    (path : ℕ → ℕ) (ex c : ℕ → ℤ) (hp0 : path 0 = 0) (hpe : path (e + 1) = j₀)
    (hstep : ∀ i, i ≤ e → stPerm X (path i) = path (i + 1) ∧ stLoop m X g (path i) = L ^ ex i)
    (hnew : ∀ i, 0 < i → i ≤ e → M ≤ path i)
    (hc0 : c 0 = 0) (hcs : ∀ i, i ≤ e → c (i + 1) = c i + ex i) (hce : c (e + 1) = ℓ)
    (hsurj : ∀ p, M ≤ p → p < M + e → ∃ i, 0 < i ∧ i ≤ e ∧ path i = p) :
    TwcDetour M j₀ e X g L ℓ := by
  have hit : ∀ i, i ≤ e + 1 → (stPerm X)^[i] 0 = path i := by
    intro i
    induction i with
    | zero => exact fun _ ↦ hp0.symm
    | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply', ih (by omega), (hstep i (by omega)).1]
  have hprod : ∀ k, k ≤ e + 1 →
      ((List.range k).map fun i ↦ stLoop m X g ((stPerm X)^[i] 0)).prod = L ^ c k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hc0, zpow_zero]
      rfl
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.map_singleton,
        List.prod_singleton, hit k (by omega), (hstep k (by omega)).2, ← zpow_add,
        hcs k (by omega)]
  refine ⟨hold, 1, e + 1, Nat.one_pos, Nat.succ_pos e, by omega, hj₀.1,
    fun i h1 h2 ↦ by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.range_one, List.map_singleton, List.prod_singleton]
    exact hj₀.2
  · rw [hit _ le_rfl, hpe]
  · intro i h1 h2
    rw [hit i (by omega)]
    exact hnew i h1 (by omega)
  · rw [hprod _ le_rfl, hce]
  · intro p h1 h2
    obtain ⟨i, hi0, hie, hip⟩ := hsurj p h1 h2
    exact Or.inr ⟨i, hi0, by omega, by rw [hit i (by omega), hip]⟩

/-- The detour statement for a negative twist. -/
private theorem twc_neg_detour_twCChain {m M j₀ d e : ℕ} {ℓ : ℤ} (hj : 0 < j₀) (hjM : j₀ < M)
    (he : e = 2 * d + 2) (hℓ : ℓ = -((d : ℤ) + 1)) (g : Fin m → G)
    (hgap : ∀ p, M ≤ p → gapProd m (twcNegX M j₀ d) g p = 1) :
    TwcDetour M j₀ e (twcNegX M j₀ d) g ((SBlock.band 0 (M + d)).loop g) ℓ := by
  subst he hℓ
  have hs := twc_neg_strand_twCChain hj hjM g hgap
  simp only [twcNegP, twcNegS] at hs
  generalize (SBlock.band 0 (M + d)).loop g = x at hs ⊢
  refine twcDetour_of_path_twCChain ?_ ?_
    (fun i ↦ if i = 0 then 0 else if i ≤ d + 1 then M + d + 1 - i
      else if i ≤ 2 * d + 2 then M + i - 1 else j₀)
    (fun i ↦ if d + 1 ≤ i ∧ i ≤ 2 * d + 1 then -1 else 0)
    (fun k ↦ if k ≤ d + 1 then 0 else if k ≤ 2 * d + 2 then -((k : ℤ) - (d + 1))
      else -((d : ℤ) + 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht h0 hj'
    obtain ⟨hp, hl⟩ := hs t (by omega)
    exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
  · obtain ⟨hp, hl⟩ := hs j₀ (by omega)
    refine ⟨hp.trans (by twc_perm), hl.trans ?_⟩
    rw [show (1 : ℤ) - -((d : ℤ) + 1) = ((d + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    twc_group
  · twc_perm
  · twc_perm
  · intro i hi
    by_cases c1 : i = 0
    · obtain ⟨hp, hl⟩ := hs 0 (by omega)
      subst c1
      exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
    by_cases c2 : i ≤ d
    · obtain ⟨hp, hl⟩ := hs (M + d + 1 - i) (by omega)
      rw [ite_eq_right c1, ite_eq_left (by omega)]
      exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
    by_cases c3 : i = d + 1
    · obtain ⟨hp, hl⟩ := hs M (by omega)
      rw [ite_eq_right c1, ite_eq_left (by omega), show M + d + 1 - i = M by omega]
      exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
    · obtain ⟨hp, hl⟩ := hs (M + i - 1) (by omega)
      rw [ite_eq_right c1, ite_eq_right (by omega), ite_eq_left (by omega)]
      by_cases c4 : i = 2 * d + 2
      · exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
      · exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
  · intro i h0 hi
    split_ifs <;> omega
  · twc_perm
  · intro i hi
    push_cast
    split_ifs <;> omega
  · twc_perm
  · intro p h1 h2
    by_cases hp : p ≤ M + d
    · exact ⟨M + d + 1 - p, by omega, by omega, by twc_perm⟩
    · exact ⟨p + 1 - M, by omega, by omega, by twc_perm⟩

/-- The chain for the twist `n > 0`. -/
private def twcPosX (M j₀ n : ℕ) : List SBlock :=
  twcFive (SBlock.band 0 (M + n + 1)) (twcAsc false (M + n + 1) (n + 2))
    (SBlock.band (M + n) (M + 2 * n + 3)) (twcDesc false M n) (SBlock.band j₀ M)

/-- The strand map of the chain for the twist `n > 0`. -/
private def twcPosP (M j₀ n t : ℕ) : ℕ :=
  if t = 0 then M + n + 1 else if t = j₀ then 0 else if t < M then t else if t = M then j₀
  else if t ≤ M + n then t - 1 else if t < M + 2 * n + 3 then t + 1 else M + n

/-- The strand loops of the chain for the twist `n > 0`, `x` the loop of the chain. -/
private def twcPosS (M j₀ n : ℕ) (x : G) (t : ℕ) : G :=
  if t = 0 then 1 else if t = j₀ then x⁻¹ ^ n * x
  else if t < M then (if t < j₀ then x else 1)
  else if t = M then 1 else if t ≤ M + n then x else 1

/-- The loops of the chain for a positive twist, from the gap relations of the new levels. -/
private theorem twc_pos_loops_twCChain {m M j₀ n : ℕ} (hjM : j₀ < M) (g g1 g2 g3 g4 : Fin m → G)
    (hgap : ∀ p, M ≤ p → (SBlock.band j₀ M).gapLoop g4 p *
      gapProd m (twcDesc false M n) g3 p * (SBlock.band (M + n) (M + 2 * n + 3)).gapLoop g2 p *
      gapProd m (twcAsc false (M + n + 1) (n + 2)) g1 p *
      (SBlock.band 0 (M + n + 1)).gapLoop g p = 1) :
    (SBlock.band j₀ M).loop g4 = ((SBlock.band 0 (M + n + 1)).loop g)⁻¹ ∧
      (SBlock.band (M + n) (M + 2 * n + 3)).loop g2 =
        ((SBlock.band 0 (M + n + 1)).loop g)⁻¹ ∧
      (∀ p, M + 1 ≤ p → p ≤ M + n →
        gapProd m (twcDesc false M n) g3 p = ((SBlock.band 0 (M + n + 1)).loop g)⁻¹) ∧
      ∀ p, M + n + 1 + 1 ≤ p → p ≤ M + n + 1 + (n + 2) →
        gapProd m (twcAsc false (M + n + 1) (n + 2)) g1 p =
          (SBlock.band 0 (M + n + 1)).loop g := by
  simp only [gapLoop_band_twCChain] at hgap
  have hZ : (SBlock.band j₀ M).loop g4 = ((SBlock.band 0 (M + n + 1)).loop g)⁻¹ := by
    have h := hgap M le_rfl
    rw [gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega),
      gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    exact eq_inv_of_mul_eq_one_left h
  have hJ : (SBlock.band (M + n) (M + 2 * n + 3)).loop g2 =
      ((SBlock.band 0 (M + n + 1)).loop g)⁻¹ := by
    have h := hgap (M + n + 1) (by omega)
    rw [gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega),
      gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    exact eq_inv_of_mul_eq_one_left h
  refine ⟨hZ, hJ, fun p h1 h2 ↦ ?_, fun p h1 h2 ↦ ?_⟩
  · have h := hgap p (by omega)
    rw [gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    exact eq_inv_of_mul_eq_one_left h
  · have h := hgap p (by omega)
    rw [gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)] at h
    twc_simp at h
    rw [hJ] at h
    exact (inv_mul_eq_one.1 h).symm

/-- The strand map and the strand loops of the chain for a positive twist. -/
private theorem twc_pos_strand_twCChain {m M j₀ n : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (g : Fin m → G)
    (hgap : ∀ p, M ≤ p → gapProd m (twcPosX M j₀ n) g p = 1) (t : ℕ)
    (ht : t < M + 2 * n + 4) :
    stPerm (twcPosX M j₀ n) t = twcPosP M j₀ n t ∧
      stLoop m (twcPosX M j₀ n) g t =
        twcPosS M j₀ n ((SBlock.band 0 (M + n + 1)).loop g) t := by
  simp only [twcPosX, gapProd_twcFive_twCChain] at hgap
  obtain ⟨hZ, hJ, hV, hU⟩ := twc_pos_loops_twCChain hjM _ _ _ _ _ hgap
  have E := twcFive_eval_twCChain (SBlock.band 0 (M + n + 1)) (SBlock.band (M + n) (M + 2 * n + 3))
    (SBlock.band j₀ M) (twcAsc false (M + n + 1) (n + 2)) (twcDesc false M n) g t
  simp only [strandLoop_band_twCChain, stLoop_twcAsc_neg_twCChain _ _ _ _ hU,
    stLoop_twcDesc_neg_twCChain _ _ _ _ hV, hZ, hJ] at E
  rw [twcPosX, twcPosP, twcPosS]
  generalize (SBlock.band 0 (M + n + 1)).loop g = x at E ⊢
  clear hgap hZ hJ hV hU
  by_cases c1 : t = 0
  · obtain ⟨hp, hs⟩ := E t t t t (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c2 : t = j₀
  · obtain ⟨hp, hs⟩ := E M (M + n) (M + 2 * n + 3) (M + n + 1) (by twc_perm) (by twc_perm)
      (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c3 : t < M
  · obtain ⟨hp, hs⟩ := E t t t t (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    by_cases c3' : t < j₀
    · exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
    · exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c4 : t = M
  · obtain ⟨hp, hs⟩ := E j₀ j₀ j₀ j₀ (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c5 : t ≤ M + n
  · obtain ⟨hp, hs⟩ := E t (t - 1) (t - 1) (t - 1) (by twc_perm) (by twc_perm) (by twc_perm)
      (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  by_cases c6 : t < M + 2 * n + 3
  · obtain ⟨hp, hs⟩ := E t t t (t + 1) (by twc_perm) (by twc_perm) (by twc_perm) (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩
  · obtain ⟨hp, hs⟩ := E t t (M + n) (M + n) (by twc_perm) (by twc_perm) (by twc_perm)
      (by twc_perm)
    exact ⟨hp.trans (by twc_perm), hs.trans (by twc_group)⟩

/-- The gap factors of the old levels for a positive twist. -/
private theorem twc_pos_oldgap_twCChain {m M j₀ n : ℕ} (hjM : j₀ < M) (g : Fin m → G)
    (hgap : ∀ p, M ≤ p → gapProd m (twcPosX M j₀ n) g p = 1) (k : ℕ) (hk : k ≤ M) :
    gapProd m (twcPosX M j₀ n) g k =
      if 1 ≤ k ∧ k ≤ j₀ then (SBlock.band 0 (M + n + 1)).loop g else 1 := by
  simp only [twcPosX, gapProd_twcFive_twCChain] at hgap
  obtain ⟨hZ, -, -, -⟩ := twc_pos_loops_twCChain hjM _ _ _ _ _ hgap
  rw [twcPosX, gapProd_twcFive_twCChain, gapProd_twcAsc_one_twCChain _ _ _ _ _ (by omega),
    gapProd_twcDesc_one_twCChain _ _ _ _ _ (by omega)]
  simp only [gapLoop_band_twCChain, hZ]
  generalize (SBlock.band 0 (M + n + 1)).loop g = x
  by_cases h1 : k = 0
  · twc_group
  by_cases h2 : k ≤ j₀
  · twc_group
  · twc_group

/-- The detour statement for a positive twist. -/
private theorem twc_pos_detour_twCChain {m M j₀ n e : ℕ} {ℓ : ℤ} (hj : 0 < j₀) (hjM : j₀ < M)
    (he : e = 2 * n + 4) (hℓ : ℓ = (n : ℤ)) (g : Fin m → G)
    (hgap : ∀ p, M ≤ p → gapProd m (twcPosX M j₀ n) g p = 1) :
    TwcDetour M j₀ e (twcPosX M j₀ n) g ((SBlock.band 0 (M + n + 1)).loop g) ℓ := by
  subst he hℓ
  have hs := twc_pos_strand_twCChain hj hjM g hgap
  simp only [twcPosP, twcPosS] at hs
  generalize (SBlock.band 0 (M + n + 1)).loop g = x at hs ⊢
  refine twcDetour_of_path_twCChain ?_ ?_
    (fun i ↦ if i = 0 then 0 else if i ≤ n + 3 then M + n + i
      else if i ≤ 2 * n + 4 then M + 2 * n + 4 - i else j₀)
    (fun i ↦ if n + 4 ≤ i ∧ i ≤ 2 * n + 3 then 1 else 0)
    (fun k ↦ if k ≤ n + 4 then 0 else if k ≤ 2 * n + 4 then (k : ℤ) - (n + 4) else (n : ℤ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht h0 hj'
    obtain ⟨hp, hl⟩ := hs t (by omega)
    exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
  · obtain ⟨hp, hl⟩ := hs j₀ (by omega)
    exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
  · twc_perm
  · twc_perm
  · intro i hi
    by_cases c1 : i = 0
    · obtain ⟨hp, hl⟩ := hs 0 (by omega)
      subst c1
      exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
    by_cases c2 : i ≤ n + 3
    · obtain ⟨hp, hl⟩ := hs (M + n + i) (by omega)
      rw [ite_eq_right c1, ite_eq_left c2]
      by_cases c2' : i = n + 3
      · exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
      · exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
    · obtain ⟨hp, hl⟩ := hs (M + 2 * n + 4 - i) (by omega)
      rw [ite_eq_right c1, ite_eq_right c2, ite_eq_left (by omega)]
      by_cases c3 : i = 2 * n + 4
      · exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
      · exact ⟨hp.trans (by twc_perm), hl.trans (by twc_group)⟩
  · intro i h0 hi
    split_ifs <;> omega
  · twc_perm
  · intro i hi
    push_cast
    split_ifs <;> omega
  · twc_perm
  · intro p h1 h2
    by_cases hp : p ≤ M + n
    · exact ⟨M + 2 * n + 4 - p, by omega, by omega, by twc_perm⟩
    · exact ⟨p - M - n, by omega, by omega, by twc_perm⟩

/-- The detour statement without twist. -/
private theorem twc_zero_detour_twCChain {m M j₀ e : ℕ} (hj : 0 < j₀) (he : e = 0) (g : Fin m → G) :
    TwcDetour M j₀ e [SBlock.band 0 j₀] g ((SBlock.band 0 j₀).loop g) 0 := by
  subst he
  have hP : ∀ t, stPerm [SBlock.band 0 j₀] t = if t = 0 then j₀ else if t = j₀ then 0 else t :=
    fun t ↦ rfl
  have hS : ∀ t, stLoop m [SBlock.band 0 j₀] g t =
      if t = j₀ ∨ (0 < t ∧ t < j₀) then (SBlock.band 0 j₀).loop g else 1 := fun t ↦ by
    rw [stLoop_singleton_twCChain, strandLoop_band_twCChain]
  generalize (SBlock.band 0 j₀).loop g = x at hS ⊢
  refine twcDetour_of_path_twCChain ?_ ?_ (fun i ↦ if i = 0 then 0 else j₀) (fun _ ↦ 0) (fun _ ↦ 0)
    rfl rfl ?_ ?_ rfl ?_ rfl ?_
  · intro t ht h0 hj'
    rw [hP, hS]
    by_cases c : t < j₀
    · exact ⟨by twc_perm, by twc_group⟩
    · exact ⟨by twc_perm, by twc_group⟩
  · rw [hP, hS]
    exact ⟨by twc_perm, by twc_group⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    rw [hP, hS]
    exact ⟨by twc_perm, by twc_group⟩
  · intro i h0 hi
    omega
  · intro i hi
    rfl
  · intro p h1 h2
    omega

/-- The chain for the twist `-(d + 1)` in the five-block form. -/
private theorem twChain_eq_twcNegX_twCChain (M j₀ : ℕ) {ℓ : ℤ} {d : ℕ} (hd : ℓ = -((d : ℤ) + 1)) :
    twChain M j₀ ℓ = twcNegX M j₀ d ∧ twExtra ℓ = 2 * d + 2 := by
  have hn : ℓ.natAbs = d + 1 := by omega
  have hl : ℓ < 0 := by omega
  have hD : (List.range (d + 1 - 1)).map
      (fun i ↦ SBlock.band (M + (d + 1) - 2 - i) (M + (d + 1) - 1 - i)) = twcDesc true M d := by
    rw [Nat.add_sub_cancel]
    refine map_range_eq_twcDesc_twCChain true M d _ fun i hi ↦ ?_
    show SBlock.band _ _ = SBlock.band _ _
    congr 1
    omega
  have hA : (List.range (d + 1 - 1)).map
      (fun i ↦ SBlock.band (M + (d + 1) + i) (M + (d + 1) + 1 + i)) =
        twcAsc true (M + d + 1) d := by
    rw [Nat.add_sub_cancel]
    refine map_range_eq_twcAsc_twCChain true (M + d + 1) d _ fun i hi ↦ ?_
    show SBlock.band _ _ = SBlock.band _ _
    congr 1
    omega
  constructor
  · rw [twChain, ite_eq_right hl.ne, ite_eq_left hl, hn, hD, hA,
      show M + (d + 1) - 1 = M + d by omega, show M + 2 * (d + 1) - 1 = M + 2 * d + 1 by omega]
    simp only [twcNegX, twcFive, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  · rw [twExtra, ite_eq_left hl.le, hn]
    omega

/-- The chain for the twist `n > 0` in the five-block form. -/
private theorem twChain_eq_twcPosX_twCChain (M j₀ : ℕ) {ℓ : ℤ} {n : ℕ} (hl : 0 < ℓ)
    (hn : ℓ = (n : ℤ)) :
    twChain M j₀ ℓ = twcPosX M j₀ n ∧ twExtra ℓ = 2 * n + 4 := by
  have hn' : ℓ.natAbs = n := by omega
  have hU : (List.range (n + 2)).map (fun i ↦ SBlock.neg (M + n + 1 + i)) =
      twcAsc false (M + n + 1) (n + 2) :=
    map_range_eq_twcAsc_twCChain false (M + n + 1) (n + 2) _ fun i hi ↦ rfl
  have hV : (List.range n).map (fun i ↦ SBlock.neg (M + n - 1 - i)) = twcDesc false M n :=
    map_range_eq_twcDesc_twCChain false M n _ fun i hi ↦ rfl
  constructor
  · rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt, hn', hU, hV]
    simp only [twcPosX, twcFive, List.append_assoc, List.cons_append, List.nil_append]
  · rw [twExtra, ite_eq_right hl.not_ge, hn']

/-- The gap factors of the old levels and the detour statement of the chain. -/
private theorem twChain_facts_twCChain {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ)
    (g : Fin (M + twExtra ℓ) → G)
    (hfix : ∀ k : Fin (M + twExtra ℓ), M ≤ (k : ℕ) →
      runTop (M + twExtra ℓ) (twChain M j₀ ℓ) g k = g k) :
    (∀ n, n ≤ M → gapProd (M + twExtra ℓ) (twChain M j₀ ℓ) g n =
      if 1 ≤ n ∧ n ≤ j₀ then twcChainLoop M j₀ ℓ g else 1) ∧
      TwcDetour M j₀ (twExtra ℓ) (twChain M j₀ ℓ) g (twcChainLoop M j₀ ℓ g) ℓ := by
  have hv := twChain_valid hj hjM ℓ
  have hgap : ∀ p, M ≤ p → gapProd (M + twExtra ℓ) (twChain M j₀ ℓ) g p = 1 := fun p hp ↦
    gapProd_eq_one_of_fix_twCChain _ hv g hfix hp
  have hL : twcChainLoop M j₀ ℓ g = gapProd (M + twExtra ℓ) (twChain M j₀ ℓ) g 1 := by
    rw [twcChainLoop, prePr_runTop _ hv, mul_inv_cancel_right]
  rw [hL]
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, ℓ = -((d : ℤ) + 1) := ⟨(-ℓ - 1).toNat, by omega⟩
    obtain ⟨hX, he⟩ := twChain_eq_twcNegX_twCChain M j₀ hd
    rw [hX] at hgap ⊢
    have hold := twc_neg_oldgap_twCChain hjM g hgap
    rw [hold 1 (by omega), ite_eq_left ⟨le_rfl, hj⟩]
    exact ⟨hold, twc_neg_detour_twCChain hj hjM he hd g hgap⟩
  · have hX : twChain M j₀ 0 = [SBlock.band 0 j₀] := by rw [twChain, ite_eq_left rfl]
    have he : twExtra 0 = 0 := rfl
    have hold : ∀ n, gapProd (M + twExtra 0) [SBlock.band 0 j₀] g n =
        if 1 ≤ n ∧ n ≤ j₀ then (SBlock.band 0 j₀).loop g else 1 := fun n ↦ by
      rw [gapProd_singleton_twCChain, gapLoop_band_twCChain]
    rw [hX, hold 1, ite_eq_left ⟨le_rfl, hj⟩]
    exact ⟨fun n _ ↦ hold n, twc_zero_detour_twCChain hj he g⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ℓ = (n : ℤ) := ⟨ℓ.toNat, by omega⟩
    obtain ⟨hX, he⟩ := twChain_eq_twcPosX_twCChain M j₀ hl hn
    rw [hX] at hgap ⊢
    have hold := twc_pos_oldgap_twCChain hjM g hgap
    rw [hold 1 (by omega), ite_eq_left ⟨le_rfl, hj⟩]
    exact ⟨hold, twc_pos_detour_twCChain hj hjM he hn g hgap⟩

/-- A chain that restores the new entries acts on the chamber products of the old levels as a
band `b(0, j₀)` with loop `twcChainLoop`. -/
theorem prePr_runTop_twChain {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ)
    (g : Fin (M + twExtra ℓ) → G)
    (hfix : ∀ k : Fin (M + twExtra ℓ), M ≤ (k : ℕ) →
      runTop (M + twExtra ℓ) (twChain M j₀ ℓ) g k = g k)
    {n : ℕ} (hn : n ≤ M) :
    prePr (runTop (M + twExtra ℓ) (twChain M j₀ ℓ) g) n =
      if 1 ≤ n ∧ n ≤ j₀ then twcChainLoop M j₀ ℓ g * prePr g n else prePr g n := by
  rw [prePr_runTop _ (twChain_valid hj hjM ℓ), (twChain_facts_twCChain hj hjM ℓ g hfix).1 n hn]
  by_cases h : 1 ≤ n ∧ n ≤ j₀
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, one_mul]

/-- The strand map of the chain and the loops collected in it, for a chain that restores the new
entries: the old positions off `0`, `j₀` are fixed; the detour from the top position `j₀` ends
at `0` with total loop `L^(1-ℓ)`, the detour from `0` ends at `j₀` with total loop `L^ℓ`, and
the two detours pass through all new positions. -/
theorem twChain_detour {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ)
    (g : Fin (M + twExtra ℓ) → G)
    (hfix : ∀ k : Fin (M + twExtra ℓ), M ≤ (k : ℕ) →
      runTop (M + twExtra ℓ) (twChain M j₀ ℓ) g k = g k) :
    (∀ t, t < M → t ≠ 0 → t ≠ j₀ →
      stPerm (twChain M j₀ ℓ) t = t ∧
        stLoop (M + twExtra ℓ) (twChain M j₀ ℓ) g t =
          if t < j₀ then twcChainLoop M j₀ ℓ g else 1) ∧
    ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 0 < k₂ ∧ k₁ + k₂ = twExtra ℓ + 2 ∧
      (stPerm (twChain M j₀ ℓ))^[k₁] j₀ = 0 ∧
      (∀ i, 0 < i → i < k₁ → M ≤ (stPerm (twChain M j₀ ℓ))^[i] j₀) ∧
      ((List.range k₁).map fun i ↦ stLoop (M + twExtra ℓ) (twChain M j₀ ℓ) g
        ((stPerm (twChain M j₀ ℓ))^[i] j₀)).prod = twcChainLoop M j₀ ℓ g ^ (1 - ℓ) ∧
      (stPerm (twChain M j₀ ℓ))^[k₂] 0 = j₀ ∧
      (∀ i, 0 < i → i < k₂ → M ≤ (stPerm (twChain M j₀ ℓ))^[i] 0) ∧
      ((List.range k₂).map fun i ↦ stLoop (M + twExtra ℓ) (twChain M j₀ ℓ) g
        ((stPerm (twChain M j₀ ℓ))^[i] 0)).prod = twcChainLoop M j₀ ℓ g ^ ℓ ∧
      ∀ p, M ≤ p → p < M + twExtra ℓ →
        (∃ i, 0 < i ∧ i < k₁ ∧ (stPerm (twChain M j₀ ℓ))^[i] j₀ = p) ∨
          ∃ i, 0 < i ∧ i < k₂ ∧ (stPerm (twChain M j₀ ℓ))^[i] 0 = p :=
  (twChain_facts_twCChain hj hjM ℓ g hfix).2

end AJConjecture
