import Mathlib
import AJHandoff.TorusKnot.PairKKnot
import AJHandoff.TorusKnot.PairKPeriGeneric

/-!
# The gap relations of `pairBlocks r s`

Positions in `pairBlocks r s` (with `b₀ = 2c - s - r`, `c = (r - 1)s`): the left climbs `A_i` at
`i < r - 2`, the decreasing and increasing runs at `r - 2, …, b₀ - 1`, the big climb `B` at `b₀`,
the round `R_0` at `b₀ + 1`, the first Hopf letter `H₁` at `b₀ + 2`, the rounds `R_t` at
`b₀ + 2 + t` for `1 ≤ t ≤ s - 1` (the last round `R_(s-1) = b(r - 2, T + 1 - s)`), the top-right
climb `C` at `b₀ + s + 2`, the right descents `D'_j` at `b₀ + s + 3 + j` and the second Hopf
letter `H₂` at `2c + 1`.

`PairGapRels r s L` lists the relations `gapProd = 1` of a tuple fixed by the run of
`pairBlocks r s`, written with the loops `L q` of the blocks, level by level (the bottom levels
`1, …, r - 2`, the run levels, the climb levels `2c - 1 - t` for `s ≤ t ≤ s + r - 2`, the
staircase levels `2c - 1 - t` for `t ≤ s - 1`, and the Hopf level `2c`). Checked by computer
against the block list for `2 ≤ r ≤ 6`, `s ≤ 15`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Position of the big climb `B` in `pairBlocks r s`. -/
def pairIdxB (r s : ℕ) : ℕ := 2 * pairC r s - s - r

/-- Position of the round `R_t` (`t ≤ s - 1`) in `pairBlocks r s`. -/
def pairIdxR (r s t : ℕ) : ℕ := if t = 0 then pairIdxB r s + 1 else pairIdxB r s + 2 + t

/-- Position of the first Hopf letter in `pairBlocks r s`. -/
def pairIdxH1 (r s : ℕ) : ℕ := pairIdxB r s + 2

/-- Position of the top-right climb `C` in `pairBlocks r s`. -/
def pairIdxC (r s : ℕ) : ℕ := pairIdxB r s + s + 2

/-- Position of the right descent `D'_j` (`j < r - 2`) in `pairBlocks r s`. -/
def pairIdxDp (r s j : ℕ) : ℕ := pairIdxB r s + s + 3 + j

/-- Position of the second Hopf letter in `pairBlocks r s`. -/
def pairIdxH2 (r s : ℕ) : ℕ := 2 * pairC r s + 1

/-- Position of the run block whose gap is the level `n` (`r - 1 ≤ n ≤ 2c - s - r`). -/
def pairIdxRun (r s n : ℕ) : ℕ :=
  if n ≤ r + pairRunDown r s - 2 then 2 * r + pairRunDown r s - 4 - n else n - 1

/-- The descending product `g (a + n - 1) * ⋯ * g (a + 1) * g a`. -/
def descProd (g : ℕ → G) (a n : ℕ) : G :=
  ((List.range n).reverse.map fun i ↦ g (a + i)).prod

/-- The gap relations of a tuple fixed by the run of `pairBlocks r s`, in terms of the block
loops `L q`. -/
structure PairGapRels (r s : ℕ) (L : ℕ → G) : Prop where
  /-- The bottom levels `1 ≤ n ≤ r - 2`: `D'_(r-3) ⋯ D'_(r-2-n) A_(n-1) ⋯ A_0 = 1`. -/
  bot : ∀ n, 1 ≤ n → n ≤ r - 2 →
    descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - n) n * descProd L 0 n = 1
  /-- The run levels: `D' R_(s-1) X_n A = 1`. -/
  run : ∀ n, r - 1 ≤ n → n ≤ 2 * pairC r s - s - r →
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s n) * descProd L 0 (r - 2) = 1
  /-- The climb levels `2c - 1 - t`, `s ≤ t ≤ s + r - 2`. -/
  climb : ∀ t, s ≤ t → t ≤ s + r - 2 →
    descProd (fun j ↦ L (pairIdxDp r s j)) (s + r - 2 - t) (t - s) *
      descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) (s + r - 1 - t) * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1
  /-- The lower staircase levels `2c - 1 - t`, `t ≤ r - 2`. -/
  stairLow : ∀ t, t ≤ r - 2 →
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) 0 (t + 1) * descProd L 0 t = 1
  /-- The upper staircase levels `2c - 1 - t`, `r - 1 ≤ t ≤ s - 1`. -/
  stairHigh : ∀ t, r - 1 ≤ t → t ≤ s - 1 →
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1
  /-- The Hopf level `2c`. -/
  top : L (pairIdxH2 r s) * L (pairIdxH1 r s) = 1

/-! ### The blocks of `pairBlocks r s` by position -/

/-- The arithmetic of an admissible pair: `s ≤ c`, `r + 1 ≤ s` and `E + s + r = c + 3`. -/
private theorem pairGap_arith {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
  simp only [pairC, pairRunDown, Nat.add_sub_cancel]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [show a + 2 - 1 = a + 1 by omega]
    nlinarith
  · rw [show a + 2 - 1 = a + 1 by omega]
    ring

/-- The arithmetic facts used to place the blocks, with `c = (r - 1)s` and
`E = (r - 2)(s - 1) + 1`. -/
private def PairArith (r s c E : ℕ) : Prop := 2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ c ∧ E + s + r = c + 3

/-- The block at position `q` of `pairBlocks r s`, by regime, with `c = (r - 1)s` and
`E = (r - 2)(s - 1) + 1` as parameters. -/
private def pairBlkAt (r s c E q : ℕ) : SBlock :=
  if q < r - 2 then SBlock.band q (2 * c - 2 - q)
  else if q < r - 2 + E then SBlock.band (2 * r + E - 5 - q) (2 * r + E - 4 - q)
  else if q < 2 * c - s - r then SBlock.band q (q + 1)
  else if q = 2 * c - s - r then SBlock.band (2 * c - s - r) (2 * c - r)
  else if q = 2 * c - s - r + 1 then SBlock.band (2 * c - 1 - r) (2 * c - 1)
  else if q = 2 * c - s - r + 2 then SBlock.neg (2 * c - 1)
  else if q < 2 * c - r + 1 then SBlock.band (4 * c - s - 2 * r + 1 - q) (4 * c - s - r + 1 - q)
  else if q = 2 * c - r + 1 then SBlock.band (r - 2) (2 * c - s)
  else if q = 2 * c - r + 2 then SBlock.band (2 * c - 1 - s) (2 * c - 1)
  else if q < 2 * c + 1 then SBlock.band (2 * c - q) (q - s - 2)
  else SBlock.neg (2 * c - 1)

/-- The block at position `q` of `pairBlocks r s`, by regime. -/
private def pairBlk (r s q : ℕ) : SBlock := pairBlkAt r s (pairC r s) (pairRunDown r s) q

/-- Splitting a mapped range. -/
private theorem map_range_add_pairGap {α : Type*} (f : ℕ → α) (a l : ℕ) :
    (List.range (a + l)).map f = (List.range a).map f ++ (List.range l).map fun j ↦ f (a + j) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- The left climbs `A_q`. -/
private theorem pairBlkAt_reg1 {r s c E q : ℕ} (hq : q < r - 2) :
    pairBlkAt r s c E q = SBlock.band q (2 * c - 2 - q) := by
  unfold pairBlkAt
  exact ite_eq_left hq

/-- The decreasing run. -/
private theorem pairBlkAt_reg2 {r s c E q : ℕ} (h1 : r - 2 ≤ q) (h2 : q < r - 2 + E) :
    pairBlkAt r s c E q = SBlock.band (2 * r + E - 5 - q) (2 * r + E - 4 - q) := by
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The increasing run. -/
private theorem pairBlkAt_reg3 {r s c E q : ℕ} (h1 : r - 2 + E ≤ q) (h2 : q < 2 * c - s - r) :
    pairBlkAt r s c E q = SBlock.band q (q + 1) := by
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The big climb `B`. -/
private theorem pairBlkAt_reg4 {r s c E q : ℕ} (hA : PairArith r s c E) (hq : q = 2 * c - s - r) :
    pairBlkAt r s c E q = SBlock.band (2 * c - s - r) (2 * c - r) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

/-- The round `R_0`. -/
private theorem pairBlkAt_reg5 {r s c E q : ℕ} (hA : PairArith r s c E)
    (hq : q = 2 * c - s - r + 1) :
    pairBlkAt r s c E q = SBlock.band (2 * c - 1 - r) (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The first Hopf letter. -/
private theorem pairBlkAt_reg6 {r s c E q : ℕ} (hA : PairArith r s c E)
    (hq : q = 2 * c - s - r + 2) :
    pairBlkAt r s c E q = SBlock.neg (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The rounds `R_t`, `1 ≤ t ≤ s - 2`. -/
private theorem pairBlkAt_reg7 {r s c E q : ℕ} (hA : PairArith r s c E)
    (h1 : 2 * c - s - r + 3 ≤ q) (h2 : q < 2 * c - r + 1) :
    pairBlkAt r s c E q = SBlock.band (4 * c - s - 2 * r + 1 - q)
      (4 * c - s - r + 1 - q) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

/-- The last round `R_(s-1)`. -/
private theorem pairBlkAt_reg8 {r s c E q : ℕ} (hA : PairArith r s c E) (hq : q = 2 * c - r + 1) :
    pairBlkAt r s c E q = SBlock.band (r - 2) (2 * c - s) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The top-right climb `C`. -/
private theorem pairBlkAt_reg9 {r s c E q : ℕ} (hA : PairArith r s c E) (hq : q = 2 * c - r + 2) :
    pairBlkAt r s c E q = SBlock.band (2 * c - 1 - s) (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The right descents `D'_j`. -/
private theorem pairBlkAt_reg10 {r s c E q : ℕ} (hA : PairArith r s c E)
    (h1 : 2 * c - r + 3 ≤ q) (h2 : q < 2 * c + 1) :
    pairBlkAt r s c E q = SBlock.band (2 * c - q) (q - s - 2) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

/-- The second Hopf letter. -/
private theorem pairBlkAt_reg11 {r s c E q : ℕ} (hA : PairArith r s c E) (hq : 2 * c + 1 ≤ q) :
    pairBlkAt r s c E q = SBlock.neg (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-- The left climbs of `pairBlocks r s` by position. -/
private theorem pairBlocks_piece_climbs {r s c E : ℕ} :
    (List.range (r - 2)).map (fun i ↦ SBlock.band i (2 * c - 1 - 1 - i)) =
      (List.range (r - 2)).map (pairBlkAt r s c E) := by
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg1 (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The decreasing run of `pairBlocks r s` by position. -/
private theorem pairBlocks_piece_down {r s c E : ℕ} (hA : PairArith r s c E) :
    (List.range E).map (fun j ↦ SBlock.band (r + E - 3 - j) (r + E - 2 - j)) =
      (List.range E).map (fun j ↦ pairBlkAt r s c E (r - 2 + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg2 (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The increasing run of `pairBlocks r s` by position. -/
private theorem pairBlocks_piece_up {r s c E : ℕ} (hA : PairArith r s c E) :
    (List.range (c - r - 1)).map
        (fun j ↦ SBlock.band (r - 2 + E + j) (r - 1 + E + j)) =
      (List.range (c - r - 1)).map (fun j ↦ pairBlkAt r s c E (r - 2 + E + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg3 (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The big climb, the round `R_0` and the first Hopf letter by position. -/
private theorem pairBlocks_piece_mid {r s c E : ℕ} (hA : PairArith r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1)) :
    [SBlock.band o (2 * c - 1 + 1 - r), SBlock.band (2 * c - 1 - r) (2 * c - 1),
        SBlock.neg (2 * c - 1)] =
      [pairBlkAt r s c E (o + 0), pairBlkAt r s c E (o + 1), pairBlkAt r s c E (o + 2)] := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  rw [pairBlkAt_reg4 (q := o + 0) hA (by omega), pairBlkAt_reg5 (q := o + 1) hA (by omega),
    pairBlkAt_reg6 (q := o + 2) hA (by omega)]
  exact congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega))
    (congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega))
      (congrArg₂ List.cons (congrArg SBlock.neg (by omega)) rfl))

/-- The rounds `R_1, …, R_(s-2)` by position. -/
private theorem pairBlocks_piece_rounds {r s c E : ℕ} (hA : PairArith r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1)) :
    (List.range (s - 2)).map
        (fun j ↦ SBlock.band (2 * c - 1 - r - 1 - j) (2 * c - 1 - 1 - j)) =
      (List.range (s - 2)).map (fun j ↦ pairBlkAt r s c E (o + 3 + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg7 hA (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The last round and the top-right climb by position. -/
private theorem pairBlocks_piece_last {r s c E : ℕ} (hA : PairArith r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1) + 3 + (s - 2)) :
    [SBlock.band (r - 2) (2 * c - 1 + 1 - s), SBlock.band (2 * c - 1 - s) (2 * c - 1)] =
      [pairBlkAt r s c E (o + 0), pairBlkAt r s c E (o + 1)] := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  rw [pairBlkAt_reg8 (q := o + 0) hA (by omega), pairBlkAt_reg9 (q := o + 1) hA (by omega)]
  exact congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega))
    (congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega)) rfl)

/-- The right descents by position. -/
private theorem pairBlocks_piece_desc {r s c E : ℕ} (hA : PairArith r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1) + 3 + (s - 2)) :
    (List.range (r - 2)).map
        (fun j ↦ SBlock.band (r - 3 - j) (2 * c - 1 + 2 - s - r + j)) =
      (List.range (r - 2)).map (fun j ↦ pairBlkAt r s c E (o + 2 + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg10 hA (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The second Hopf letter by position. -/
private theorem pairBlocks_piece_hopf {r s c E : ℕ} (hA : PairArith r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1) + 3 + (s - 2)) :
    [SBlock.neg (2 * c - 1)] = [pairBlkAt r s c E (o + 2 + (r - 2) + 0)] := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  rw [pairBlkAt_reg11 hA (by omega)]

/-- `pairBlocks r s` read position by position. -/
private theorem pairBlocks_eq_map {r s : ℕ} (h : IsTorusPair r s) :
    pairBlocks r s = (List.range (2 * pairC r s + 2)).map (pairBlk r s) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  rw [show 2 * pairC r s + 2 = r - 2 + pairRunDown r s + (pairC r s - r - 1) + 3 + (s - 2) + 2 +
    (r - 2) + 1 by omega]
  simp only [map_range_add_pairGap]
  simp only [pairBlocks, pairTop, pairRunUp, pairBlk]
  rw [show pairBlk r s = pairBlkAt r s (pairC r s) (pairRunDown r s) from rfl]
  rw [show List.range 3 = [0, 1, 2] from rfl, show List.range 2 = [0, 1] from rfl,
    show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  generalize pairC r s = c at hc hE ⊢
  generalize pairRunDown r s = E at hE ⊢
  have hA : PairArith r s c E := ⟨hr, hrs, hc, hE⟩
  rw [pairBlocks_piece_climbs, pairBlocks_piece_down hA, pairBlocks_piece_up hA,
    pairBlocks_piece_mid hA _ rfl, pairBlocks_piece_rounds hA _ rfl, pairBlocks_piece_last hA _ rfl,
    pairBlocks_piece_desc hA _ rfl, pairBlocks_piece_hopf hA _ rfl]

/-- The block at position `q` of `pairBlocks r s`. -/
private theorem pairBlocks_getD {r s : ℕ} (h : IsTorusPair r s) (q : ℕ)
    (hq : q < 2 * pairC r s + 2) (d : SBlock) : (pairBlocks r s).getD q d = pairBlk r s q := by
  rw [pairBlocks_eq_map h, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq]
  rfl

/-- The gap interval of the block at position `q` of `pairBlocks r s`, by regime. -/
private theorem pairBlk_lohi {r s : ℕ} (h : IsTorusPair r s) (q : ℕ) :
    (q < r - 2 ∧
      (pairBlk r s q).lo = q + 1 ∧
      (pairBlk r s q).hi = 2 * pairC r s - 2 - q) ∨
    (r - 2 ≤ q ∧ q < r - 2 + pairRunDown r s ∧
      (pairBlk r s q).lo = 2 * r + pairRunDown r s - 5 - q + 1 ∧
      (pairBlk r s q).hi = 2 * r + pairRunDown r s - 4 - q) ∨
    (r - 2 + pairRunDown r s ≤ q ∧ q < 2 * pairC r s - s - r ∧
      (pairBlk r s q).lo = q + 1 ∧
      (pairBlk r s q).hi = q + 1) ∨
    (q = 2 * pairC r s - s - r ∧
      (pairBlk r s q).lo = 2 * pairC r s - s - r + 1 ∧
      (pairBlk r s q).hi = 2 * pairC r s - r) ∨
    (q = 2 * pairC r s - s - r + 1 ∧
      (pairBlk r s q).lo = 2 * pairC r s - 1 - r + 1 ∧
      (pairBlk r s q).hi = 2 * pairC r s - 1) ∨
    (q = 2 * pairC r s - s - r + 2 ∧
      (pairBlk r s q).lo = 2 * pairC r s - 1 + 1 ∧
      (pairBlk r s q).hi = 2 * pairC r s - 1 + 1) ∨
    (2 * pairC r s - s - r + 3 ≤ q ∧ q < 2 * pairC r s - r + 1 ∧
      (pairBlk r s q).lo = 4 * pairC r s - s - 2 * r + 1 - q + 1 ∧
      (pairBlk r s q).hi = 4 * pairC r s - s - r + 1 - q) ∨
    (q = 2 * pairC r s - r + 1 ∧
      (pairBlk r s q).lo = r - 2 + 1 ∧
      (pairBlk r s q).hi = 2 * pairC r s - s) ∨
    (q = 2 * pairC r s - r + 2 ∧
      (pairBlk r s q).lo = 2 * pairC r s - 1 - s + 1 ∧
      (pairBlk r s q).hi = 2 * pairC r s - 1) ∨
    (2 * pairC r s - r + 3 ≤ q ∧ q < 2 * pairC r s + 1 ∧
      (pairBlk r s q).lo = 2 * pairC r s - q + 1 ∧
      (pairBlk r s q).hi = q - s - 2) ∨
    (2 * pairC r s + 1 ≤ q ∧
      (pairBlk r s q).lo = 2 * pairC r s - 1 + 1 ∧
      (pairBlk r s q).hi = 2 * pairC r s - 1 + 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hA : PairArith r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  unfold pairBlk
  by_cases h1 : q < r - 2
  · rw [pairBlkAt_reg1 h1]
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h2 : q < r - 2 + pairRunDown r s
  · rw [pairBlkAt_reg2 (by omega) h2]
    iterate 1 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  by_cases h3 : q < 2 * pairC r s - s - r
  · rw [pairBlkAt_reg3 (by omega) (by omega)]
    iterate 2 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  by_cases h4 : q = 2 * pairC r s - s - r
  · rw [pairBlkAt_reg4 hA (by omega)]
    iterate 3 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h5 : q = 2 * pairC r s - s - r + 1
  · rw [pairBlkAt_reg5 hA (by omega)]
    iterate 4 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h6 : q = 2 * pairC r s - s - r + 2
  · rw [pairBlkAt_reg6 hA (by omega)]
    iterate 5 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h7 : q < 2 * pairC r s - r + 1
  · rw [pairBlkAt_reg7 hA (by omega) (by omega)]
    iterate 6 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  by_cases h8 : q = 2 * pairC r s - r + 1
  · rw [pairBlkAt_reg8 hA (by omega)]
    iterate 7 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h9 : q = 2 * pairC r s - r + 2
  · rw [pairBlkAt_reg9 hA (by omega)]
    iterate 8 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h10 : q < 2 * pairC r s + 1
  · rw [pairBlkAt_reg10 hA (by omega) (by omega)]
    iterate 9 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  rw [pairBlkAt_reg11 hA (by omega)]
  iterate 10 right
  exact ⟨by omega, rfl, rfl⟩

/-! ### Descending products -/

/-- The empty descending product. -/
private theorem descProd_zero_gap (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

/-- Splitting off the top factor of a descending product. -/
private theorem descProd_succ_top_gap (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- A descending product of one factor. -/
private theorem descProd_one_gap (g : ℕ → G) (a : ℕ) : descProd g a 1 = g a := by
  simp [descProd]

/-- Splitting off the bottom factor of a descending product. -/
private theorem descProd_succ_bot_gap (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_gap, ih, descProd_succ_top_gap, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_gap (g h : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = h (b + i)) : descProd g a n = descProd h b n := by
  induction n with
  | zero => simp [descProd_zero_gap]
  | succ n ih =>
    rw [descProd_succ_top_gap, descProd_succ_top_gap, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-- The right descents as consecutive block loops. -/
private theorem descProd_dp_shift (r s : ℕ) (L : ℕ → G) (a n : ℕ) :
    descProd (fun j ↦ L (pairIdxDp r s j)) a n = descProd L (pairIdxDp r s a) n :=
  descProd_congr_gap _ _ _ _ _ fun i _ ↦ by simp only [pairIdxDp, Nat.add_assoc]

/-- The rounds `R_a, R_(a+1), …` (`1 ≤ a`) as consecutive block loops. -/
private theorem descProd_round_shift (r s : ℕ) (L : ℕ → G) (a n : ℕ) (ha : 1 ≤ a) :
    descProd (fun u ↦ L (pairIdxR r s u)) a n = descProd L (pairIdxR r s a) n :=
  descProd_congr_gap _ _ _ _ _ fun i _ ↦ by
    simp only [pairIdxR, show a + i ≠ 0 by omega, show a ≠ 0 by omega, ↓reduceIte,
      Nat.add_assoc]

/-! ### The gap products of `pairBlocks r s` -/

/-- The product of `F (m - 1), …, F 0`. -/
private def gapRevProd (F : ℕ → G) (m : ℕ) : G := ((List.range m).reverse.map F).prod

/-- The empty product. -/
private theorem gapRevProd_zero (F : ℕ → G) : gapRevProd F 0 = 1 := by
  simp [gapRevProd]

/-- Splitting off the top factor. -/
private theorem gapRevProd_succ (F : ℕ → G) (m : ℕ) :
    gapRevProd F (m + 1) = F m * gapRevProd F m := by
  simp [gapRevProd, List.range_succ]

/-- Factors equal to `1` at the top can be dropped. -/
private theorem gapRevProd_skip (F : ℕ → G) (a m : ℕ) (ha : a ≤ m)
    (hf : ∀ q, a ≤ q → q < m → F q = 1) : gapRevProd F m = gapRevProd F a := by
  induction m, ha using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [gapRevProd_succ, hf m hm (by omega), one_mul, ih fun q h1 h2 ↦ hf q h1 (by omega)]

/-- Consecutive factors at the top form a descending product. -/
private theorem gapRevProd_take (F L : ℕ → G) (a k : ℕ)
    (ht : ∀ q, a ≤ q → q < a + k → F q = L q) :
    gapRevProd F (a + k) = descProd L a k * gapRevProd F a := by
  induction k with
  | zero => simp [descProd_zero_gap]
  | succ k ih =>
    rw [← Nat.add_assoc, gapRevProd_succ, ht (a + k) (by omega) (by omega),
      ih fun q h1 h2 ↦ ht q h1 (by omega), descProd_succ_top_gap, mul_assoc]

/-- The factor of the block at position `q` in the gap product of level `n`. -/
private def pairGapF (r s : ℕ) (L : ℕ → G) (n q : ℕ) : G :=
  if (pairBlk r s q).lo ≤ n ∧ n ≤ (pairBlk r s q).hi then L q else 1

/-- Peeling off a run of consecutive blocks whose gap contains `n`, above which no gap contains
`n`. -/
private theorem gapRevProd_pair_peel (r s : ℕ) (L : ℕ → G) (n a k m : ℕ) (hm : a + k ≤ m)
    (ht : ∀ q, a ≤ q → q < a + k → (pairBlk r s q).lo ≤ n ∧ n ≤ (pairBlk r s q).hi)
    (hf : ∀ q, a + k ≤ q → q < m → ¬((pairBlk r s q).lo ≤ n ∧ n ≤ (pairBlk r s q).hi)) :
    gapRevProd (pairGapF r s L n) m = descProd L a k * gapRevProd (pairGapF r s L n) a := by
  rw [gapRevProd_skip (pairGapF r s L n) (a + k) m hm fun q h1 h2 ↦ ite_eq_right (hf q h1 h2),
    gapRevProd_take (pairGapF r s L n) L a k fun q h1 h2 ↦ ite_eq_left (ht q h1 h2)]

/-- The number `2c + 2` of blocks. -/
private theorem length_pairBlocks {r s : ℕ} (h : IsTorusPair r s) :
    (pairBlocks r s).length = 2 * pairC r s + 2 := by
  rw [pairBlocks_eq_map h, List.length_map, List.length_range]

/-- The gap relations of a fixed tuple, block by block. -/
private theorem gapRevProd_pair_eq_one {r s : ℕ} (h : IsTorusPair r s)
    (ρ : KnotGroup (pairWhiteheadKnot r s h) →* G) (n : ℕ) :
    gapRevProd (pairGapF r s (loopAt (pairStrands r s) (pairBlocks r s)
      (fun t ↦ ρ (PresentedGroup.of t))) n) (2 * pairC r s + 2) = 1 := by
  have h0 := gapProd_fixed (pairWhiteheadKnot r s h) (pairBlocks r s) rfl
    (pairBlocks_valid h) ρ n
  rw [gapProd_eq_prod_range, length_pairBlocks h] at h0
  rw [← h0, gapRevProd]
  refine congrArg List.prod (List.map_congr_left fun q hq ↦ ?_)
  have hq' := List.mem_range.1 (List.mem_reverse.1 hq)
  simp only [pairGapF, pairBlocks_getD h q hq']
  rfl

/-- The bottom levels. -/
private theorem pairGap_bot {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn1 : 1 ≤ n) (hn2 : n ≤ r - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - n) n * descProd L 0 n = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key n
  rw [
    gapRevProd_pair_peel r s L n (b + s + 3 + (r - 2 - n)) (n) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L n (0) (n) (b + s + 3 + (r - 2 - n))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one] at k
  subst hb
  rw [descProd_dp_shift]
  exact k

/-- The run levels of the decreasing run. -/
private theorem pairGap_run_down {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn1 : r - 1 ≤ n) (hn2 : n ≤ 2 * pairC r s - s - r) (hn : n ≤ r + pairRunDown r s - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s n) * descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have hri : pairIdxRun r s n = 2 * r + pairRunDown r s - 4 - n := ite_eq_left hn
  have k := key n
  rw [
    gapRevProd_pair_peel r s L n (b + s + 3) (r - 2) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L n (b + s + 1) (1) (b + s + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L n (pairIdxRun r s n) (1) (b + s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L n (0) (r - 2) (pairIdxRun r s n)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one, descProd_one_gap, descProd_one_gap] at k
  subst hb
  have hR : pairIdxR r s (s - 1) = 2 * pairC r s - s - r + s + 1 := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    unfold pairIdxB
    omega
  rw [descProd_dp_shift, hR]
  simp only [mul_assoc] at k ⊢
  exact k

/-- The run levels of the increasing run. -/
private theorem pairGap_run_up {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn2 : n ≤ 2 * pairC r s - s - r) (hn : ¬n ≤ r + pairRunDown r s - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s n) * descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have hri : pairIdxRun r s n = n - 1 := ite_eq_right hn
  have k := key n
  rw [
    gapRevProd_pair_peel r s L n (b + s + 3) (r - 2) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L n (b + s + 1) (1) (b + s + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L n (pairIdxRun r s n) (1) (b + s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L n (0) (r - 2) (pairIdxRun r s n)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one, descProd_one_gap, descProd_one_gap] at k
  subst hb
  have hR : pairIdxR r s (s - 1) = 2 * pairC r s - s - r + s + 1 := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    unfold pairIdxB
    omega
  rw [descProd_dp_shift, hR]
  simp only [mul_assoc] at k ⊢
  exact k

/-- The run levels. -/
private theorem pairGap_run {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (n : ℕ)
    (hn1 : r - 1 ≤ n) (hn2 : n ≤ 2 * pairC r s - s - r) :
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s n) * descProd L 0 (r - 2) = 1 := by
  by_cases hn : n ≤ r + pairRunDown r s - 2
  · exact pairGap_run_down h L key n hn1 hn2 hn
  · exact pairGap_run_up h L key n hn2 hn

/-- The climb levels. -/
private theorem pairGap_climb {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht1 : s ≤ t) (ht2 : t ≤ s + r - 2) :
    descProd (fun j ↦ L (pairIdxDp r s j)) (s + r - 2 - t) (t - s) *
      descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) (s + r - 1 - t) * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + s + 3 + (s + r - 2 - t)) (t - s)
      (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + 2 + (t + 1 - r)) (s + r - 1 - t)
      (b + s + 3 + (s + r - 2 - t))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b) (1) (b + 2 + (t + 1 - r))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (0) (r - 2) (b)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one, descProd_one_gap] at k
  subst hb
  have hR : pairIdxR r s (t + 1 - r) = 2 * pairC r s - s - r + 2 + (t + 1 - r) := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    rfl
  rw [descProd_dp_shift, descProd_round_shift r s L _ _ (by omega), hR]
  simp only [mul_assoc] at k ⊢
  exact k

/-- The lower staircase levels. -/
private theorem pairGap_stairLow {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht : t ≤ r - 2) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) 0 (t + 1) * descProd L 0 t = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + s + 2) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + 3) (t) (b + s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + 1) (1) (b + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (0) (t) (b + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one, descProd_one_gap, descProd_one_gap] at k
  subst hb
  rw [descProd_succ_bot_gap, Nat.zero_add, descProd_round_shift r s L 1 t le_rfl]
  simp only [pairIdxR, pairIdxC, pairIdxB, one_ne_zero, ↓reduceIte, mul_assoc] at k ⊢
  exact k

/-- The first upper staircase level `t = r - 1`. -/
private theorem pairGap_stairHigh_first {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht1 : r - 1 ≤ t) (htr : t < r) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + s + 2) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + 3) (r - 1) (b + s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + 1) (1) (b + 3)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b) (1) (b + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (0) (r - 2) (b)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one, descProd_one_gap, descProd_one_gap, descProd_one_gap] at k
  subst hb
  rw [show descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r =
      descProd (fun u ↦ L (pairIdxR r s u)) 0 (r - 1 + 1) by congr 1 <;> omega,
    descProd_succ_bot_gap, Nat.zero_add, descProd_round_shift r s L 1 _ le_rfl]
  simp only [pairIdxR, pairIdxC, pairIdxB, one_ne_zero, ↓reduceIte, mul_assoc] at k ⊢
  exact k

/-- The upper staircase levels `r ≤ t ≤ s - 1`. -/
private theorem pairGap_stairHigh_rest {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (htr : r ≤ t) (ht2 : t ≤ s - 1) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s - 1 - t)
  rw [
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + s + 2) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b + 2 + (t + 1 - r)) (r) (b + s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (b) (1) (b + 2 + (t + 1 - r))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s - 1 - t) (0) (r - 2) (b)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one, descProd_one_gap, descProd_one_gap] at k
  subst hb
  have hR : pairIdxR r s (t + 1 - r) = 2 * pairC r s - s - r + 2 + (t + 1 - r) := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    rfl
  rw [descProd_round_shift r s L _ _ (by omega), hR]
  simp only [pairIdxC, pairIdxB, mul_assoc] at k ⊢
  exact k

/-- The upper staircase levels. -/
private theorem pairGap_stairHigh {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) (t : ℕ)
    (ht1 : r - 1 ≤ t) (ht2 : t ≤ s - 1) :
    L (pairIdxC r s) * descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r * L (pairIdxB r s) *
      descProd L 0 (r - 2) = 1 := by
  rcases Nat.lt_or_ge t r with htr | htr
  · exact pairGap_stairHigh_first h L key t ht1 htr
  · exact pairGap_stairHigh_rest h L key t htr ht2

/-- The Hopf level. -/
private theorem pairGap_top {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (key : ∀ n, gapRevProd (pairGapF r s L n) (2 * pairC r s + 2) = 1) :
    L (pairIdxH2 r s) * L (pairIdxH1 r s) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arith h
  have hl := pairBlk_lohi h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have k := key (2 * pairC r s)
  rw [
    gapRevProd_pair_peel r s L (2 * pairC r s) (2 * pairC r s + 1) (1) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s) (b + 2) (1) (2 * pairC r s + 1)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peel r s L (2 * pairC r s) (0) (0) (b + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zero, mul_one, descProd_zero_gap, mul_one, descProd_one_gap, descProd_one_gap] at k
  subst hb
  exact k

/-- The block loops of a tuple fixed by the run of `pairBlocks r s` (the images of the
generators under a representation) satisfy the gap relations. -/
theorem pairGapRels_of_hom {r s : ℕ} (h : IsTorusPair r s)
    (ρ : KnotGroup (pairWhiteheadKnot r s h) →* G) :
    PairGapRels r s (loopAt (pairStrands r s) (pairBlocks r s)
      (fun t ↦ ρ (PresentedGroup.of t))) := by
  have key := gapRevProd_pair_eq_one h ρ
  exact ⟨pairGap_bot h _ key, pairGap_run h _ key, pairGap_climb h _ key,
    pairGap_stairLow h _ key, pairGap_stairHigh h _ key, pairGap_top h _ key⟩

end AJConjecture
