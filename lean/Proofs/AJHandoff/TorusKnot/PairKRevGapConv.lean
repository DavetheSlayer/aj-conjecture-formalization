import Mathlib
import AJHandoff.TorusKnot.PairKPeriGapRel
import AJHandoff.TorusKnot.PairKRevGeneric

/-!
# The gap relations give trivial gap products

`gapPrefix_pairBlocks_eq_one`: for loops `ℓ` satisfying the gap relations `PairGapRels r s ℓ`,
the product `gapPrefix (pairBlocks r s) ℓ n` of the loops of the blocks whose gap contains the
level `n` is `1` at every level. This is `pairGapRels_of_hom`
(`AJHandoff.TorusKnot.PairKPeriGapRel`) read backwards: the levels `0` and `n ≥ 2c + 1` lie in
no gap, and every other level is a bottom, run, climb, staircase or Hopf level, whose gap product
regroups to the corresponding relation. The block-by-position machinery is a copy of the private
part of `PairKPeriGapRel` (suffix `Rv`), made public here for the loop equations of the reverse
construction, together with `gapPrefix_take_pairBlocks` (the corrected chamber products as
products over positions) and the loop equations in edge-meridian form (`loopPr_band_edge`,
`loopPr_neg_edge`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### The blocks of `pairBlocks r s` by position -/

/-- The arithmetic of an admissible pair: `s ≤ c`, `r + 1 ≤ s` and `E + s + r = c + 3`. -/
theorem pairGap_arithRv {r s : ℕ} (h : IsTorusPair r s) :
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
def PairArithRv (r s c E : ℕ) : Prop := 2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ c ∧ E + s + r = c + 3

/-- The block at position `q` of `pairBlocks r s`, by regime, with `c = (r - 1)s` and
`E = (r - 2)(s - 1) + 1` as parameters. -/
def pairBlkAtRv (r s c E q : ℕ) : SBlock :=
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
def pairBlkRv (r s q : ℕ) : SBlock := pairBlkAtRv r s (pairC r s) (pairRunDown r s) q

/-- Splitting a mapped range. -/
theorem map_range_add_pairGapRv {α : Type*} (f : ℕ → α) (a l : ℕ) :
    (List.range (a + l)).map f = (List.range a).map f ++ (List.range l).map fun j ↦ f (a + j) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- The left climbs `A_q`. -/
theorem pairBlkAt_reg1Rv {r s c E q : ℕ} (hq : q < r - 2) :
    pairBlkAtRv r s c E q = SBlock.band q (2 * c - 2 - q) := by
  unfold pairBlkAtRv
  exact ite_eq_left hq

/-- The decreasing run. -/
theorem pairBlkAt_reg2Rv {r s c E q : ℕ} (h1 : r - 2 ≤ q) (h2 : q < r - 2 + E) :
    pairBlkAtRv r s c E q = SBlock.band (2 * r + E - 5 - q) (2 * r + E - 4 - q) := by
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The increasing run. -/
theorem pairBlkAt_reg3Rv {r s c E q : ℕ} (h1 : r - 2 + E ≤ q) (h2 : q < 2 * c - s - r) :
    pairBlkAtRv r s c E q = SBlock.band q (q + 1) := by
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The big climb `B`. -/
theorem pairBlkAt_reg4Rv {r s c E q : ℕ} (hA : PairArithRv r s c E) (hq : q = 2 * c - s - r) :
    pairBlkAtRv r s c E q = SBlock.band (2 * c - s - r) (2 * c - r) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

/-- The round `R_0`. -/
theorem pairBlkAt_reg5Rv {r s c E q : ℕ} (hA : PairArithRv r s c E)
    (hq : q = 2 * c - s - r + 1) :
    pairBlkAtRv r s c E q = SBlock.band (2 * c - 1 - r) (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The first Hopf letter. -/
theorem pairBlkAt_reg6Rv {r s c E q : ℕ} (hA : PairArithRv r s c E)
    (hq : q = 2 * c - s - r + 2) :
    pairBlkAtRv r s c E q = SBlock.neg (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The rounds `R_t`, `1 ≤ t ≤ s - 2`. -/
theorem pairBlkAt_reg7Rv {r s c E q : ℕ} (hA : PairArithRv r s c E)
    (h1 : 2 * c - s - r + 3 ≤ q) (h2 : q < 2 * c - r + 1) :
    pairBlkAtRv r s c E q = SBlock.band (4 * c - s - 2 * r + 1 - q)
      (4 * c - s - r + 1 - q) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

/-- The last round `R_(s-1)`. -/
theorem pairBlkAt_reg8Rv {r s c E q : ℕ} (hA : PairArithRv r s c E) (hq : q = 2 * c - r + 1) :
    pairBlkAtRv r s c E q = SBlock.band (r - 2) (2 * c - s) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The top-right climb `C`. -/
theorem pairBlkAt_reg9Rv {r s c E q : ℕ} (hA : PairArithRv r s c E) (hq : q = 2 * c - r + 2) :
    pairBlkAtRv r s c E q = SBlock.band (2 * c - 1 - s) (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The right descents `D'_j`. -/
theorem pairBlkAt_reg10Rv {r s c E q : ℕ} (hA : PairArithRv r s c E)
    (h1 : 2 * c - r + 3 ≤ q) (h2 : q < 2 * c + 1) :
    pairBlkAtRv r s c E q = SBlock.band (2 * c - q) (q - s - 2) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

/-- The second Hopf letter. -/
theorem pairBlkAt_reg11Rv {r s c E q : ℕ} (hA : PairArithRv r s c E) (hq : 2 * c + 1 ≤ q) :
    pairBlkAtRv r s c E q = SBlock.neg (2 * c - 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  unfold pairBlkAtRv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-- The left climbs of `pairBlocks r s` by position. -/
theorem pairBlocks_piece_climbsRv {r s c E : ℕ} :
    (List.range (r - 2)).map (fun i ↦ SBlock.band i (2 * c - 1 - 1 - i)) =
      (List.range (r - 2)).map (pairBlkAtRv r s c E) := by
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg1Rv (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The decreasing run of `pairBlocks r s` by position. -/
theorem pairBlocks_piece_downRv {r s c E : ℕ} (hA : PairArithRv r s c E) :
    (List.range E).map (fun j ↦ SBlock.band (r + E - 3 - j) (r + E - 2 - j)) =
      (List.range E).map (fun j ↦ pairBlkAtRv r s c E (r - 2 + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg2Rv (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The increasing run of `pairBlocks r s` by position. -/
theorem pairBlocks_piece_upRv {r s c E : ℕ} (hA : PairArithRv r s c E) :
    (List.range (c - r - 1)).map
        (fun j ↦ SBlock.band (r - 2 + E + j) (r - 1 + E + j)) =
      (List.range (c - r - 1)).map (fun j ↦ pairBlkAtRv r s c E (r - 2 + E + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg3Rv (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The big climb, the round `R_0` and the first Hopf letter by position. -/
theorem pairBlocks_piece_midRv {r s c E : ℕ} (hA : PairArithRv r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1)) :
    [SBlock.band o (2 * c - 1 + 1 - r), SBlock.band (2 * c - 1 - r) (2 * c - 1),
        SBlock.neg (2 * c - 1)] =
      [pairBlkAtRv r s c E (o + 0), pairBlkAtRv r s c E (o + 1), pairBlkAtRv r s c E (o + 2)] := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  rw [pairBlkAt_reg4Rv (q := o + 0) hA (by omega), pairBlkAt_reg5Rv (q := o + 1) hA (by omega),
    pairBlkAt_reg6Rv (q := o + 2) hA (by omega)]
  exact congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega))
    (congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega))
      (congrArg₂ List.cons (congrArg SBlock.neg (by omega)) rfl))

/-- The rounds `R_1, …, R_(s-2)` by position. -/
theorem pairBlocks_piece_roundsRv {r s c E : ℕ} (hA : PairArithRv r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1)) :
    (List.range (s - 2)).map
        (fun j ↦ SBlock.band (2 * c - 1 - r - 1 - j) (2 * c - 1 - 1 - j)) =
      (List.range (s - 2)).map (fun j ↦ pairBlkAtRv r s c E (o + 3 + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg7Rv hA (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The last round and the top-right climb by position. -/
theorem pairBlocks_piece_lastRv {r s c E : ℕ} (hA : PairArithRv r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1) + 3 + (s - 2)) :
    [SBlock.band (r - 2) (2 * c - 1 + 1 - s), SBlock.band (2 * c - 1 - s) (2 * c - 1)] =
      [pairBlkAtRv r s c E (o + 0), pairBlkAtRv r s c E (o + 1)] := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  rw [pairBlkAt_reg8Rv (q := o + 0) hA (by omega), pairBlkAt_reg9Rv (q := o + 1) hA (by omega)]
  exact congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega))
    (congrArg₂ List.cons (congrArg₂ SBlock.band (by omega) (by omega)) rfl)

/-- The right descents by position. -/
theorem pairBlocks_piece_descRv {r s c E : ℕ} (hA : PairArithRv r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1) + 3 + (s - 2)) :
    (List.range (r - 2)).map
        (fun j ↦ SBlock.band (r - 3 - j) (2 * c - 1 + 2 - s - r + j)) =
      (List.range (r - 2)).map (fun j ↦ pairBlkAtRv r s c E (o + 2 + j)) := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  refine List.map_congr_left fun j hj ↦ ?_
  have := List.mem_range.1 hj
  rw [pairBlkAt_reg10Rv hA (by omega) (by omega)]
  exact congrArg₂ SBlock.band (by omega) (by omega)

/-- The second Hopf letter by position. -/
theorem pairBlocks_piece_hopfRv {r s c E : ℕ} (hA : PairArithRv r s c E) (o : ℕ)
    (ho : o = r - 2 + E + (c - r - 1) + 3 + (s - 2)) :
    [SBlock.neg (2 * c - 1)] = [pairBlkAtRv r s c E (o + 2 + (r - 2) + 0)] := by
  obtain ⟨hr, hrs, hc, hE⟩ := id hA
  rw [pairBlkAt_reg11Rv hA (by omega)]

/-- `pairBlocks r s` read position by position. -/
theorem pairBlocks_eq_mapRv {r s : ℕ} (h : IsTorusPair r s) :
    pairBlocks r s = (List.range (2 * pairC r s + 2)).map (pairBlkRv r s) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  rw [show 2 * pairC r s + 2 = r - 2 + pairRunDown r s + (pairC r s - r - 1) + 3 + (s - 2) + 2 +
    (r - 2) + 1 by omega]
  simp only [map_range_add_pairGapRv]
  simp only [pairBlocks, pairTop, pairRunUp, pairBlkRv]
  rw [show pairBlkRv r s = pairBlkAtRv r s (pairC r s) (pairRunDown r s) from rfl]
  rw [show List.range 3 = [0, 1, 2] from rfl, show List.range 2 = [0, 1] from rfl,
    show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  generalize pairC r s = c at hc hE ⊢
  generalize pairRunDown r s = E at hE ⊢
  have hA : PairArithRv r s c E := ⟨hr, hrs, hc, hE⟩
  rw [pairBlocks_piece_climbsRv, pairBlocks_piece_downRv hA, pairBlocks_piece_upRv hA,
    pairBlocks_piece_midRv hA _ rfl, pairBlocks_piece_roundsRv hA _ rfl, pairBlocks_piece_lastRv hA _ rfl,
    pairBlocks_piece_descRv hA _ rfl, pairBlocks_piece_hopfRv hA _ rfl]

/-- The block at position `q` of `pairBlocks r s`. -/
theorem pairBlocks_getDRv {r s : ℕ} (h : IsTorusPair r s) (q : ℕ)
    (hq : q < 2 * pairC r s + 2) (d : SBlock) : (pairBlocks r s).getD q d = pairBlkRv r s q := by
  rw [pairBlocks_eq_mapRv h, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq]
  rfl

/-- The gap interval of the block at position `q` of `pairBlocks r s`, by regime. -/
theorem pairBlk_lohiRv {r s : ℕ} (h : IsTorusPair r s) (q : ℕ) :
    (q < r - 2 ∧
      (pairBlkRv r s q).lo = q + 1 ∧
      (pairBlkRv r s q).hi = 2 * pairC r s - 2 - q) ∨
    (r - 2 ≤ q ∧ q < r - 2 + pairRunDown r s ∧
      (pairBlkRv r s q).lo = 2 * r + pairRunDown r s - 5 - q + 1 ∧
      (pairBlkRv r s q).hi = 2 * r + pairRunDown r s - 4 - q) ∨
    (r - 2 + pairRunDown r s ≤ q ∧ q < 2 * pairC r s - s - r ∧
      (pairBlkRv r s q).lo = q + 1 ∧
      (pairBlkRv r s q).hi = q + 1) ∨
    (q = 2 * pairC r s - s - r ∧
      (pairBlkRv r s q).lo = 2 * pairC r s - s - r + 1 ∧
      (pairBlkRv r s q).hi = 2 * pairC r s - r) ∨
    (q = 2 * pairC r s - s - r + 1 ∧
      (pairBlkRv r s q).lo = 2 * pairC r s - 1 - r + 1 ∧
      (pairBlkRv r s q).hi = 2 * pairC r s - 1) ∨
    (q = 2 * pairC r s - s - r + 2 ∧
      (pairBlkRv r s q).lo = 2 * pairC r s - 1 + 1 ∧
      (pairBlkRv r s q).hi = 2 * pairC r s - 1 + 1) ∨
    (2 * pairC r s - s - r + 3 ≤ q ∧ q < 2 * pairC r s - r + 1 ∧
      (pairBlkRv r s q).lo = 4 * pairC r s - s - 2 * r + 1 - q + 1 ∧
      (pairBlkRv r s q).hi = 4 * pairC r s - s - r + 1 - q) ∨
    (q = 2 * pairC r s - r + 1 ∧
      (pairBlkRv r s q).lo = r - 2 + 1 ∧
      (pairBlkRv r s q).hi = 2 * pairC r s - s) ∨
    (q = 2 * pairC r s - r + 2 ∧
      (pairBlkRv r s q).lo = 2 * pairC r s - 1 - s + 1 ∧
      (pairBlkRv r s q).hi = 2 * pairC r s - 1) ∨
    (2 * pairC r s - r + 3 ≤ q ∧ q < 2 * pairC r s + 1 ∧
      (pairBlkRv r s q).lo = 2 * pairC r s - q + 1 ∧
      (pairBlkRv r s q).hi = q - s - 2) ∨
    (2 * pairC r s + 1 ≤ q ∧
      (pairBlkRv r s q).lo = 2 * pairC r s - 1 + 1 ∧
      (pairBlkRv r s q).hi = 2 * pairC r s - 1 + 1) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hA : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  unfold pairBlkRv
  by_cases h1 : q < r - 2
  · rw [pairBlkAt_reg1Rv h1]
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h2 : q < r - 2 + pairRunDown r s
  · rw [pairBlkAt_reg2Rv (by omega) h2]
    iterate 1 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  by_cases h3 : q < 2 * pairC r s - s - r
  · rw [pairBlkAt_reg3Rv (by omega) (by omega)]
    iterate 2 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  by_cases h4 : q = 2 * pairC r s - s - r
  · rw [pairBlkAt_reg4Rv hA (by omega)]
    iterate 3 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h5 : q = 2 * pairC r s - s - r + 1
  · rw [pairBlkAt_reg5Rv hA (by omega)]
    iterate 4 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h6 : q = 2 * pairC r s - s - r + 2
  · rw [pairBlkAt_reg6Rv hA (by omega)]
    iterate 5 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h7 : q < 2 * pairC r s - r + 1
  · rw [pairBlkAt_reg7Rv hA (by omega) (by omega)]
    iterate 6 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  by_cases h8 : q = 2 * pairC r s - r + 1
  · rw [pairBlkAt_reg8Rv hA (by omega)]
    iterate 7 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h9 : q = 2 * pairC r s - r + 2
  · rw [pairBlkAt_reg9Rv hA (by omega)]
    iterate 8 right
    exact Or.inl ⟨by omega, rfl, rfl⟩
  by_cases h10 : q < 2 * pairC r s + 1
  · rw [pairBlkAt_reg10Rv hA (by omega) (by omega)]
    iterate 9 right
    exact Or.inl ⟨by omega, by omega, rfl, rfl⟩
  rw [pairBlkAt_reg11Rv hA (by omega)]
  iterate 10 right
  exact ⟨by omega, rfl, rfl⟩

/-! ### Descending products -/

/-- The empty descending product. -/
theorem descProd_zero_gapRv (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

/-- Splitting off the top factor of a descending product. -/
theorem descProd_succ_top_gapRv (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- A descending product of one factor. -/
theorem descProd_one_gapRv (g : ℕ → G) (a : ℕ) : descProd g a 1 = g a := by
  simp [descProd]

/-- Splitting off the bottom factor of a descending product. -/
theorem descProd_succ_bot_gapRv (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_gapRv, ih, descProd_succ_top_gapRv, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- Descending products with the same factors agree. -/
theorem descProd_congr_gapRv (g h : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = h (b + i)) : descProd g a n = descProd h b n := by
  induction n with
  | zero => simp [descProd_zero_gapRv]
  | succ n ih =>
    rw [descProd_succ_top_gapRv, descProd_succ_top_gapRv, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-- The right descents as consecutive block loops. -/
theorem descProd_dp_shiftRv (r s : ℕ) (L : ℕ → G) (a n : ℕ) :
    descProd (fun j ↦ L (pairIdxDp r s j)) a n = descProd L (pairIdxDp r s a) n :=
  descProd_congr_gapRv _ _ _ _ _ fun i _ ↦ by simp only [pairIdxDp, Nat.add_assoc]

/-- The rounds `R_a, R_(a+1), …` (`1 ≤ a`) as consecutive block loops. -/
theorem descProd_round_shiftRv (r s : ℕ) (L : ℕ → G) (a n : ℕ) (ha : 1 ≤ a) :
    descProd (fun u ↦ L (pairIdxR r s u)) a n = descProd L (pairIdxR r s a) n :=
  descProd_congr_gapRv _ _ _ _ _ fun i _ ↦ by
    simp only [pairIdxR, show a + i ≠ 0 by omega, show a ≠ 0 by omega, ↓reduceIte,
      Nat.add_assoc]

/-! ### The gap products of `pairBlocks r s` -/

/-- The product of `F (m - 1), …, F 0`. -/
def gapRevProdRv (F : ℕ → G) (m : ℕ) : G := ((List.range m).reverse.map F).prod

/-- The empty product. -/
theorem gapRevProd_zeroRv (F : ℕ → G) : gapRevProdRv F 0 = 1 := by
  simp [gapRevProdRv]

/-- Splitting off the top factor. -/
theorem gapRevProd_succRv (F : ℕ → G) (m : ℕ) :
    gapRevProdRv F (m + 1) = F m * gapRevProdRv F m := by
  simp [gapRevProdRv, List.range_succ]

/-- Factors equal to `1` at the top can be dropped. -/
theorem gapRevProd_skipRv (F : ℕ → G) (a m : ℕ) (ha : a ≤ m)
    (hf : ∀ q, a ≤ q → q < m → F q = 1) : gapRevProdRv F m = gapRevProdRv F a := by
  induction m, ha using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [gapRevProd_succRv, hf m hm (by omega), one_mul, ih fun q h1 h2 ↦ hf q h1 (by omega)]

/-- Consecutive factors at the top form a descending product. -/
theorem gapRevProd_takeRv (F L : ℕ → G) (a k : ℕ)
    (ht : ∀ q, a ≤ q → q < a + k → F q = L q) :
    gapRevProdRv F (a + k) = descProd L a k * gapRevProdRv F a := by
  induction k with
  | zero => simp [descProd_zero_gapRv]
  | succ k ih =>
    rw [← Nat.add_assoc, gapRevProd_succRv, ht (a + k) (by omega) (by omega),
      ih fun q h1 h2 ↦ ht q h1 (by omega), descProd_succ_top_gapRv, mul_assoc]

/-- The factor of the block at position `q` in the gap product of level `n`. -/
def pairGapFRv (r s : ℕ) (L : ℕ → G) (n q : ℕ) : G :=
  if (pairBlkRv r s q).lo ≤ n ∧ n ≤ (pairBlkRv r s q).hi then L q else 1

/-- Peeling off a run of consecutive blocks whose gap contains `n`, above which no gap contains
`n`. -/
theorem gapRevProd_pair_peelRv (r s : ℕ) (L : ℕ → G) (n a k m : ℕ) (hm : a + k ≤ m)
    (ht : ∀ q, a ≤ q → q < a + k → (pairBlkRv r s q).lo ≤ n ∧ n ≤ (pairBlkRv r s q).hi)
    (hf : ∀ q, a + k ≤ q → q < m → ¬((pairBlkRv r s q).lo ≤ n ∧ n ≤ (pairBlkRv r s q).hi)) :
    gapRevProdRv (pairGapFRv r s L n) m = descProd L a k * gapRevProdRv (pairGapFRv r s L n) a := by
  rw [gapRevProd_skipRv (pairGapFRv r s L n) (a + k) m hm fun q h1 h2 ↦ ite_eq_right (hf q h1 h2),
    gapRevProd_takeRv (pairGapFRv r s L n) L a k fun q h1 h2 ↦ ite_eq_left (ht q h1 h2)]

/-- The number `2c + 2` of blocks. -/
theorem length_pairBlocksRv {r s : ℕ} (h : IsTorusPair r s) :
    (pairBlocks r s).length = 2 * pairC r s + 2 := by
  rw [pairBlocks_eq_mapRv h, List.length_map, List.length_range]

/-- The number `2c + 2` of blocks of `pairBlocks r s`. -/
theorem length_pairBlocks_rev {r s : ℕ} (h : IsTorusPair r s) :
    (pairBlocks r s).length = 2 * pairC r s + 2 :=
  length_pairBlocksRv h

/-! ### `gapPrefix` as a product over positions -/

/-- `gapPrefix` as the product, over the positions in decreasing order, of the prescribed loops
of the blocks whose gap contains `n`. -/
theorem gapPrefix_eq_prod_range (bs : List SBlock) (ℓ : ℕ → G) (n : ℕ) :
    gapPrefix bs ℓ n = ((List.range bs.length).reverse.map fun q ↦
      if (bs.getD q (SBlock.neg 0)).lo ≤ n ∧ n ≤ (bs.getD q (SBlock.neg 0)).hi then ℓ q else 1).prod := by
  induction bs generalizing ℓ with
  | nil => simp [gapPrefix]
  | cons b bs ih =>
    rw [gapPrefix, ih, List.length_cons, List.range_succ_eq_map, List.reverse_cons,
      List.map_append, List.prod_append, List.map_reverse, List.map_reverse, List.map_map]
    congr 1
    simp

/-- `gapPrefix` of `pairBlocks r s` as a product over the `2c + 2` positions. -/
private theorem gapPrefix_pairBlocks_eq_rv {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) (n : ℕ) :
    gapPrefix (pairBlocks r s) L n = gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) := by
  rw [gapPrefix_eq_prod_range, length_pairBlocksRv h, gapRevProdRv]
  refine congrArg List.prod (List.map_congr_left fun q hq ↦ ?_)
  have hq' := List.mem_range.1 (List.mem_reverse.1 hq)
  simp only [pairGapFRv, pairBlocks_getDRv h q hq']

/-- The prefix `gapPrefix (take q)` of `pairBlocks r s` as a product over the first `q`
positions (the corrected chamber products of `loopAt_eq_of_prescribed`). -/
theorem gapPrefix_take_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) (q n : ℕ)
    (hq : q ≤ 2 * pairC r s + 2) :
    gapPrefix ((pairBlocks r s).take q) L n = gapRevProdRv (pairGapFRv r s L n) q := by
  rw [gapPrefix_eq_prod_range, List.length_take, length_pairBlocksRv h,
    Nat.min_eq_left hq, gapRevProdRv]
  refine congrArg List.prod (List.map_congr_left fun q' hq' ↦ ?_)
  have hq'' := List.mem_range.1 (List.mem_reverse.1 hq')
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq'', ← List.getD_eq_getElem?_getD]
  simp only [pairGapFRv, pairBlocks_getDRv h q' (by omega)]

/-- The loop equation of a band read on corrected chamber products of edge meridians
`P(n) = e_(n-1) ⋯ e_0`: `G(j+1) e_j G(j)⁻¹ · G(i) e_i⁻¹ G(i+1)⁻¹`. -/
theorem loopPr_band_edge (i j : ℕ) (Gf e : ℕ → G) :
    loopPr (SBlock.band i j) (fun n ↦ Gf n * descProd e 0 n) =
      Gf (j + 1) * e j * (Gf j)⁻¹ * (Gf i * (e i)⁻¹ * (Gf (i + 1))⁻¹) := by
  simp only [loopPr, descProd, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, List.prod_cons, Nat.zero_add]
  group

/-- The loop equation of a negative letter on corrected chamber products of edge meridians:
`G(i) e_i⁻¹ G(i+1)⁻¹ · G(i+2) e_(i+1) G(i+1)⁻¹`. -/
theorem loopPr_neg_edge (i : ℕ) (Gf e : ℕ → G) :
    loopPr (SBlock.neg i) (fun n ↦ Gf n * descProd e 0 n) =
      Gf i * (e i)⁻¹ * (Gf (i + 1))⁻¹ * (Gf (i + 2) * e (i + 1) * (Gf (i + 1))⁻¹) := by
  simp only [loopPr, descProd, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, List.prod_cons, Nat.zero_add]
  group

/-! ### The levels, one regime at a time -/

/-- The levels in no gap: `0` and `n ≥ 2c + 1`. -/
private theorem rvGap_none {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) (n : ℕ)
    (hn : n = 0 ∨ 2 * pairC r s + 1 ≤ n) :
    gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  rw [gapRevProd_skipRv (pairGapFRv r s L n) 0 _ (Nat.zero_le _) fun q _ _ ↦
    ite_eq_right (by have := hl q; omega), gapRevProd_zeroRv]

/-- The bottom levels. -/
private theorem rvGap_bot {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L)
    (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ r - 2) :
    gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  rw [
    gapRevProd_pair_peelRv r s L n (b + s + 3 + (r - 2 - n)) (n) (2 * pairC r s + 2)
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_pair_peelRv r s L n (0) (n) (b + s + 3 + (r - 2 - n))
      (by omega) (fun q h1 h2 ↦ by have := hl q; omega)
      (fun q h1 h2 ↦ by have := hl q; omega),
    gapRevProd_zeroRv, mul_one]
  subst hb
  have k := hL.bot n hn1 hn2
  rw [descProd_dp_shiftRv] at k
  exact k

/-- The run levels of the decreasing run. -/
private theorem rvGap_run_down {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (n : ℕ) (hn1 : r - 1 ≤ n) (hn2 : n ≤ 2 * pairC r s - s - r)
    (hn : n ≤ r + pairRunDown r s - 2) :
    gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have hri : pairIdxRun r s n = 2 * r + pairRunDown r s - 4 - n := ite_eq_left hn
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
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv]
  subst hb
  have hR : pairIdxR r s (s - 1) = 2 * pairC r s - s - r + s + 1 := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    unfold pairIdxB
    omega
  have k := hL.run n hn1 hn2
  rw [descProd_dp_shiftRv, hR] at k
  simp only [mul_assoc] at k ⊢
  exact k

/-- The run levels of the increasing run. -/
private theorem rvGap_run_up {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (n : ℕ) (hn1 : r - 1 ≤ n) (hn2 : n ≤ 2 * pairC r s - s - r)
    (hn : ¬n ≤ r + pairRunDown r s - 2) :
    gapRevProdRv (pairGapFRv r s L n) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
  have hri : pairIdxRun r s n = n - 1 := ite_eq_right hn
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
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv]
  subst hb
  have hR : pairIdxR r s (s - 1) = 2 * pairC r s - s - r + s + 1 := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    unfold pairIdxB
    omega
  have k := hL.run n hn1 hn2
  rw [descProd_dp_shiftRv, hR] at k
  simp only [mul_assoc] at k ⊢
  exact k

/-- The climb levels. -/
private theorem rvGap_climb {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L)
    (t : ℕ) (ht1 : s ≤ t) (ht2 : t ≤ s + r - 2) :
    gapRevProdRv (pairGapFRv r s L (2 * pairC r s - 1 - t)) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
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
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv]
  subst hb
  have hR : pairIdxR r s (t + 1 - r) = 2 * pairC r s - s - r + 2 + (t + 1 - r) := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    rfl
  have k := hL.climb t ht1 ht2
  rw [descProd_dp_shiftRv, descProd_round_shiftRv r s L _ _ (by omega), hR] at k
  simp only [mul_assoc] at k ⊢
  exact k

/-- The lower staircase levels. -/
private theorem rvGap_stairLow {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (t : ℕ) (ht : t ≤ r - 2) :
    gapRevProdRv (pairGapFRv r s L (2 * pairC r s - 1 - t)) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
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
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv]
  subst hb
  have k := hL.stairLow t ht
  rw [descProd_succ_bot_gapRv, Nat.zero_add, descProd_round_shiftRv r s L 1 t le_rfl] at k
  simp only [pairIdxR, pairIdxC, pairIdxB, one_ne_zero, ↓reduceIte, mul_assoc] at k ⊢
  exact k

/-- The first upper staircase level `t = r - 1`. -/
private theorem rvGap_stairHigh_first {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (t : ℕ) (ht1 : r - 1 ≤ t) (htr : t < r) :
    gapRevProdRv (pairGapFRv r s L (2 * pairC r s - 1 - t)) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
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
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv, descProd_one_gapRv]
  subst hb
  have k := hL.stairHigh t ht1 (by omega)
  rw [show descProd (fun u ↦ L (pairIdxR r s u)) (t + 1 - r) r =
      descProd (fun u ↦ L (pairIdxR r s u)) 0 (r - 1 + 1) by congr 1 <;> omega,
    descProd_succ_bot_gapRv, Nat.zero_add, descProd_round_shiftRv r s L 1 _ le_rfl] at k
  simp only [pairIdxR, pairIdxC, pairIdxB, one_ne_zero, ↓reduceIte, mul_assoc] at k ⊢
  exact k

/-- The upper staircase levels `r ≤ t ≤ s - 1`. -/
private theorem rvGap_stairHigh_rest {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (t : ℕ) (htr : r ≤ t) (ht2 : t ≤ s - 1) :
    gapRevProdRv (pairGapFRv r s L (2 * pairC r s - 1 - t)) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
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
    gapRevProd_zeroRv, mul_one, descProd_one_gapRv, descProd_one_gapRv]
  subst hb
  have hR : pairIdxR r s (t + 1 - r) = 2 * pairC r s - s - r + 2 + (t + 1 - r) := by
    unfold pairIdxR
    rw [ite_eq_right (by omega)]
    rfl
  have k := hL.stairHigh t (by omega) ht2
  rw [descProd_round_shiftRv r s L _ _ (by omega), hR] at k
  simp only [pairIdxC, pairIdxB, mul_assoc] at k ⊢
  exact k

/-- The Hopf level. -/
private theorem rvGap_top {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) (hL : PairGapRels r s L) :
    gapRevProdRv (pairGapFRv r s L (2 * pairC r s)) (2 * pairC r s + 2) = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hl := pairBlk_lohiRv h
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * pairC r s - s - r := ⟨_, rfl⟩
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
    descProd_one_gapRv]
  subst hb
  exact hL.top

/-- Loops satisfying the gap relations of `pairBlocks r s` have trivial gap products at every
level. -/
theorem gapPrefix_pairBlocks_eq_one {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℕ → G)
    (hℓ : PairGapRels r s ℓ) (n : ℕ) : gapPrefix (pairBlocks r s) ℓ n = 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  rw [gapPrefix_pairBlocks_eq_rv h]
  by_cases h0 : n = 0 ∨ 2 * pairC r s + 1 ≤ n
  · exact rvGap_none h ℓ n h0
  by_cases h1 : n ≤ r - 2
  · exact rvGap_bot h ℓ hℓ n (by omega) h1
  by_cases h2 : n ≤ 2 * pairC r s - s - r
  · by_cases hn : n ≤ r + pairRunDown r s - 2
    · exact rvGap_run_down h ℓ hℓ n (by omega) h2 hn
    · exact rvGap_run_up h ℓ hℓ n (by omega) h2 hn
  by_cases h3 : n = 2 * pairC r s
  · subst h3
    exact rvGap_top h ℓ hℓ
  obtain ⟨t, rfl⟩ : ∃ t, n = 2 * pairC r s - 1 - t := ⟨2 * pairC r s - 1 - n, by omega⟩
  by_cases h4 : s ≤ t
  · exact rvGap_climb h ℓ hℓ t h4 (by omega)
  by_cases h5 : t ≤ r - 2
  · exact rvGap_stairLow h ℓ hℓ t h5
  by_cases h6 : t < r
  · exact rvGap_stairHigh_first h ℓ hℓ t (by omega) h6
  · exact rvGap_stairHigh_rest h ℓ hℓ t (by omega) (by omega)

end AJConjecture
