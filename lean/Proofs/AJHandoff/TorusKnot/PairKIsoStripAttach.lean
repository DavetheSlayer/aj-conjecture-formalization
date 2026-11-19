import Mathlib
import AJHandoff.TorusKnot.PairKIsoDeadEnd
import AJHandoff.TorusKnot.PairKIsoStripDefs

/-!
# The blocks of `Wh⁻₀(T(r, s))` satisfy the retraction hypotheses

Every disc `1, …, 2c` of `pairBlocks r s` carries two blocks (four for the disc `T`, which also
carries the two Hopf letters), and the blocks are valid (`pairBlocks_valid`). The first and last
blocks of each disc, by regime, are read off the table of `PairKIsoStripDefs`.
-/

namespace AJConjecture

/-- A block attached to the disc `m` bounds its first block from above. -/
private theorem isoFirst_le_of_getElem?_attach {B : List SBlock} {m i : ℕ} {b : SBlock}
    (hb : B[i]? = some b) (ha : isoAttached m b = true) : isoFirst B m ≤ i := by
  by_contra hlt
  push Not at hlt
  have h := List.not_of_lt_findIdx (p := isoAttached m) (xs := B) hlt
  obtain ⟨hi, hb⟩ := List.getElem?_eq_some_iff.mp hb
  rw [hb] at h
  rw [h] at ha
  exact Bool.false_ne_true ha

/-- A block attached to the disc `m` bounds its last block from below. -/
private theorem le_isoLast_of_getElem?_attach {B : List SBlock} {m j : ℕ} {b : SBlock}
    (hb : B[j]? = some b) (ha : isoAttached m b = true) :
    j ≤ isoLast B m ∧ isoLast B m < B.length := by
  have hj : j < B.length := (List.getElem?_eq_some_iff.mp hb).1
  have h2 : B.reverse[B.length - 1 - j]? = some b := by
    rw [List.getElem?_reverse (by omega), show B.length - 1 - (B.length - 1 - j) = j by omega]
    exact hb
  have := isoFirst_le_of_getElem?_attach h2 ha
  unfold isoFirst at this
  unfold isoLast
  omega

/-- Two blocks attached to the disc `m`. -/
private theorem isoFirst_lt_isoLast_of_two {B : List SBlock} {m i j : ℕ} {b b' : SBlock}
    (hb : B[i]? = some b) (hb' : B[j]? = some b') (hij : i < j)
    (ha : isoAttached m b = true) (ha' : isoAttached m b' = true) :
    isoFirst B m < isoLast B m ∧ isoLast B m < B.length := by
  have h1 := isoFirst_le_of_getElem?_attach hb ha
  have h2 := le_isoLast_of_getElem?_attach hb' ha'
  omega

/-- The arithmetic of an admissible pair. -/
private theorem pairBlocks_arith_attach {r s : ℕ} (h : IsTorusPair r s) :
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

/-- Look up a block of `pairBlocks`. -/
local macro "pair_lookup" : tactic => `(tactic| (
  simp only [pairBlocks, List.getElem?_append, List.length_append, List.length_map,
    List.length_range, List.length_cons, List.length_nil, List.getElem?_map]
  split_ifs <;> first | omega | simp_all))

/-- A left climb. -/
private theorem pairBlocksAt_climb {r s i : ℕ} (hi : i < r - 2) :
    (pairBlocks r s)[i]? = some (SBlock.band i (pairTop r s - 1 - i)) := by pair_lookup

/-- A block of the decreasing run. -/
private theorem pairBlocksAt_runDown {r s j : ℕ} (hj : j < pairRunDown r s) :
    (pairBlocks r s)[r - 2 + j]? =
      some (SBlock.band (r + pairRunDown r s - 3 - j) (r + pairRunDown r s - 2 - j)) := by
  pair_lookup

/-- A block of the increasing run. -/
private theorem pairBlocksAt_runUp {r s j : ℕ} (hj : j < pairRunUp r s) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + j]? =
      some (SBlock.band (r - 2 + pairRunDown r s + j) (r - 1 + pairRunDown r s + j)) := by
  pair_lookup

/-- The big climb. -/
private theorem pairBlocksAt_bigClimb {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s]? =
      some (SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r)) := by
  pair_lookup

/-- Round `0`. -/
private theorem pairBlocksAt_roundZero {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 1]? =
      some (SBlock.band (pairTop r s - r) (pairTop r s)) := by
  pair_lookup

/-- The first Hopf letter. -/
private theorem pairBlocksAt_hopfFirst {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 2]? =
      some (SBlock.neg (pairTop r s)) := by
  pair_lookup

/-- A middle round. -/
private theorem pairBlocksAt_round {r s j : ℕ} (hj : j < s - 2) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + j]? =
      some (SBlock.band (pairTop r s - r - 1 - j) (pairTop r s - 1 - j)) := by
  pair_lookup

/-- The last round. -/
private theorem pairBlocksAt_lastRound {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2)]? =
      some (SBlock.band (r - 2) (pairTop r s + 1 - s)) := by
  pair_lookup

/-- The top-right climb. -/
private theorem pairBlocksAt_topRight {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1]? =
      some (SBlock.band (pairTop r s - s) (pairTop r s)) := by
  pair_lookup

/-- A right descent. -/
private theorem pairBlocksAt_descent {r s j : ℕ} (hj : j < r - 2) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + j]? =
      some (SBlock.band (r - 3 - j) (pairTop r s + 2 - s - r + j)) := by
  pair_lookup

/-- The second Hopf letter. -/
private theorem pairBlocksAt_hopfSecond {r s : ℕ} (hr : 2 ≤ r) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + (r - 2)]? =
      some (SBlock.neg (pairTop r s)) := by
  pair_lookup

/-- Attachment of a block to a disc, by arithmetic. -/
local macro "pair_att" : tactic =>
  `(tactic| (rw [isoAttached, decide_eq_true_eq]; simp only [isoEnds, true_or, or_true] <;> omega))

/-- The blocks of `Wh⁻₀(T(r, s))` can be thinned and retracted. -/
theorem isoFenceable_pairBlocks {r s : ℕ} (h : IsTorusPair r s) :
    IsoFenceable (pairStrands r s - 1) (pairBlocks r s) := by
  obtain ⟨hr, hrs, hcs, hE⟩ := pairBlocks_arith_attach h
  have hN : pairStrands r s = 2 * pairC r s + 1 := rfl
  refine ⟨fun b hb ↦ ?_, ?_⟩
  · rw [show pairStrands r s - 1 + 1 = pairStrands r s by omega]
    exact pairBlocks_valid h b hb
  intro m hm1 hm
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have hE1 : 1 ≤ pairRunDown r s := by simp [pairRunDown]
  set E := pairRunDown r s with hEdef
  set z := pairRunUp r s with hzdef
  set T := pairTop r s with hTdef
  set K := r - 2 + E + z + 3 with hK
  -- (a) the left climbs and the right descents
  rcases Nat.lt_or_ge m (r - 2) with ha | ha
  · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_climb (s := s) (i := m) ha)
      (pairBlocksAt_descent (j := r - 3 - m) (by omega)) (by omega) (by pair_att) (by pair_att)
  -- (b) the disc `r - 2`
  rcases Nat.lt_or_ge m (r - 1) with hb | hb
  · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_runDown (j := E - 1) (by omega))
      pairBlocksAt_lastRound (by omega) (by pair_att) (by pair_att)
  -- (c) inside the decreasing run
  rcases Nat.lt_or_ge m (r + E - 2) with hc | hc
  · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_runDown (j := r + E - 3 - m) (by omega))
      (pairBlocksAt_runDown (j := r + E - 2 - m) (by omega)) (by omega) (by pair_att) (by pair_att)
  -- (d, e) the end of the decreasing run and the increasing run
  rcases Nat.lt_or_ge m (r + E - 1 + z) with hd | hd
  · have first : ∃ i b, (pairBlocks r s)[i]? = some b ∧ isoAttached m b = true ∧
        i + 1 ≤ r - 2 + E + (m + 2 - r - E) := by
      rcases Nat.lt_or_ge m (r + E - 1) with hd' | hd'
      · exact ⟨_, _, pairBlocksAt_runDown (j := 0) (by omega), by pair_att, by omega⟩
      · exact ⟨_, _, pairBlocksAt_runUp (j := m + 1 - r - E) (by omega), by pair_att, by omega⟩
    obtain ⟨i, b, hb1, hb2, hi⟩ := first
    rcases Nat.lt_or_ge m (r + E - 2 + z) with he | he
    · exact isoFirst_lt_isoLast_of_two hb1 (pairBlocksAt_runUp (j := m + 2 - r - E) (by omega))
        (by omega) hb2 (by pair_att)
    · exact isoFirst_lt_isoLast_of_two hb1 pairBlocksAt_bigClimb (by omega) hb2 (by pair_att)
  -- (f) the left edges of the rounds and the right descents
  rcases Nat.lt_or_ge m (T - s) with hf | hf
  · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_round (j := T - r - 1 - m) (by omega))
      (pairBlocksAt_descent (j := m - (T + 2 - s - r)) (by omega)) (by omega) (by pair_att)
      (by pair_att)
  -- (g) the disc `T - s`
  rcases Nat.lt_or_ge m (T - s + 1) with hg | hg
  · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_round (j := s - r - 1) (by omega))
      pairBlocksAt_topRight (by omega) (by pair_att) (by pair_att)
  -- (h) the discs between `T - s + 1` and `T - r - 1`
  rcases Nat.lt_or_ge m (T - r) with hh | hh
  · rcases Nat.lt_or_ge m (T - s + 2) with hh' | hh'
    · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_round (j := s - r - 2) (by omega))
        pairBlocksAt_lastRound (by omega) (by pair_att) (by pair_att)
    · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_round (j := T - r - 1 - m) (by omega))
        (pairBlocksAt_round (j := T - 1 - m) (by omega)) (by omega) (by pair_att) (by pair_att)
  -- (i) the disc `T - r`
  rcases Nat.lt_or_ge m (T - r + 1) with hi | hi
  · rcases Nat.lt_or_ge (r + 1) s with hi' | hi'
    · exact isoFirst_lt_isoLast_of_two pairBlocksAt_roundZero
        (pairBlocksAt_round (j := r - 1) (by omega))
        (by omega) (by pair_att) (by pair_att)
    · exact isoFirst_lt_isoLast_of_two pairBlocksAt_roundZero pairBlocksAt_lastRound
        (by omega) (by pair_att) (by pair_att)
  -- (j) the disc `T + 1 - r`
  rcases Nat.lt_or_ge m (T - r + 2) with hj | hj
  · exact isoFirst_lt_isoLast_of_two pairBlocksAt_bigClimb
      (pairBlocksAt_round (j := r - 2) (by omega))
      (by omega) (by pair_att) (by pair_att)
  -- (k) the right ends of the left climbs
  rcases Nat.lt_or_ge m T with hk | hk
  · exact isoFirst_lt_isoLast_of_two (pairBlocksAt_climb (s := s) (i := T - 1 - m) (by omega))
      (pairBlocksAt_round (j := T - 1 - m) (by omega)) (by omega) (by pair_att) (by pair_att)
  -- (l, m) the discs `T` and `T + 1`
  rcases Nat.lt_or_ge m (T + 1) with hl | hl
  · exact isoFirst_lt_isoLast_of_two pairBlocksAt_roundZero (pairBlocksAt_hopfSecond hr) (by omega)
      (by pair_att) (by pair_att)
  · exact isoFirst_lt_isoLast_of_two pairBlocksAt_hopfFirst (pairBlocksAt_hopfSecond hr) (by omega)
      (by pair_att) (by pair_att)

/-- The arithmetic of an admissible pair: `r + 1 ≤ s ≤ c` and `E + s + r = c + 3`. -/
theorem pairBlocks_arith_iso {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 :=
  pairBlocks_arith_attach h

/-- The left climbs of `pairBlocks`. -/
theorem pairBlocks_getElem?_climb {r s i : ℕ} (hi : i < r - 2) :
    (pairBlocks r s)[i]? = some (SBlock.band i (pairTop r s - 1 - i)) :=
  pairBlocksAt_climb hi

/-- The decreasing run of `pairBlocks`. -/
theorem pairBlocks_getElem?_runDown {r s j : ℕ} (hj : j < pairRunDown r s) :
    (pairBlocks r s)[r - 2 + j]? =
      some (SBlock.band (r + pairRunDown r s - 3 - j) (r + pairRunDown r s - 2 - j)) :=
  pairBlocksAt_runDown hj

/-- The increasing run of `pairBlocks`. -/
theorem pairBlocks_getElem?_runUp {r s j : ℕ} (hj : j < pairRunUp r s) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + j]? =
      some (SBlock.band (r - 2 + pairRunDown r s + j) (r - 1 + pairRunDown r s + j)) :=
  pairBlocksAt_runUp hj

/-- The big climb of `pairBlocks`. -/
theorem pairBlocks_getElem?_bigClimb {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s]? =
      some (SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r)) :=
  pairBlocksAt_bigClimb

/-- Round `0` of `pairBlocks`. -/
theorem pairBlocks_getElem?_roundZero {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 1]? =
      some (SBlock.band (pairTop r s - r) (pairTop r s)) :=
  pairBlocksAt_roundZero

/-- The first Hopf letter of `pairBlocks`. -/
theorem pairBlocks_getElem?_hopfFirst {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 2]? =
      some (SBlock.neg (pairTop r s)) :=
  pairBlocksAt_hopfFirst

/-- The middle rounds of `pairBlocks`. -/
theorem pairBlocks_getElem?_round {r s j : ℕ} (hj : j < s - 2) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + j]? =
      some (SBlock.band (pairTop r s - r - 1 - j) (pairTop r s - 1 - j)) :=
  pairBlocksAt_round hj

/-- The last round of `pairBlocks`. -/
theorem pairBlocks_getElem?_lastRound {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2)]? =
      some (SBlock.band (r - 2) (pairTop r s + 1 - s)) :=
  pairBlocksAt_lastRound

/-- The top-right climb of `pairBlocks`. -/
theorem pairBlocks_getElem?_topRight {r s : ℕ} :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1]? =
      some (SBlock.band (pairTop r s - s) (pairTop r s)) :=
  pairBlocksAt_topRight

/-- The right descents of `pairBlocks`. -/
theorem pairBlocks_getElem?_descent {r s j : ℕ} (hj : j < r - 2) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + j]? =
      some (SBlock.band (r - 3 - j) (pairTop r s + 2 - s - r + j)) :=
  pairBlocksAt_descent hj

/-- The second Hopf letter of `pairBlocks`. -/
theorem pairBlocks_getElem?_hopfSecond {r s : ℕ} (hr : 2 ≤ r) :
    (pairBlocks r s)[r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + (r - 2)]? =
      some (SBlock.neg (pairTop r s)) :=
  pairBlocksAt_hopfSecond hr

/-- The number of blocks of `pairBlocks`. -/
theorem pairBlocks_length (r s : ℕ) :
    (pairBlocks r s).length =
      r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + (r - 2) + 1 := by
  simp only [pairBlocks, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]

/-- A block attached to the disc `m` bounds its first block from above. -/
theorem isoFirst_le_of_attached {B : List SBlock} {m i : ℕ} {b : SBlock}
    (hb : B[i]? = some b) (ha : isoAttached m b = true) : isoFirst B m ≤ i :=
  isoFirst_le_of_getElem?_attach hb ha

/-- A block attached to the disc `m` bounds its last block from below. -/
theorem le_isoLast_of_attached {B : List SBlock} {m j : ℕ} {b : SBlock}
    (hb : B[j]? = some b) (ha : isoAttached m b = true) :
    j ≤ isoLast B m ∧ isoLast B m < B.length :=
  le_isoLast_of_getElem?_attach hb ha

end AJConjecture
