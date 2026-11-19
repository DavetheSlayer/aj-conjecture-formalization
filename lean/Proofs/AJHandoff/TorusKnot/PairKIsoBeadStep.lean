import Mathlib
import AJHandoff.TorusKnot.PairKIsoBeadDefs

/-!
# Local moves of beads

The letter steps of a bead journey along `morseDouble G`, generic in the bead:

* `morseReach_isoBead_D`: a band bead passes a doubled crossing at any shift (from
  `morseReach_beadD_left` of the library with `morseReach_frame`, and its mirror);
* `morseReach_isoBead_cap`: a band bead turns around a doubled cap and is rotated
  (induction on the bead, one letter around the cap at a time; for `−0 −0` this is the library macro
  `TWCAP`);
* `morseReach_isoBead_cup`: the same around a doubled cup (for `−0` the library macro `HCUPM`);

and two fixed macros of the twist transfer (checked at thickness one and two with equal arcs,
`SCR/ISO/tools`): a doubled curl passes the conjugated clasp, and a negative full twist of the band
is two positive edge curls followed by a negative doubled curl. A full twist does **not** pass the
clasp (`−0 −0 · claspWord` and `claspWord · −0 −0` have different operators at thickness `2`), so
twists that lie between the clasp and the top end along the knot are moved as doubled curls.
-/

namespace AJConjecture

/-! ### Nested cups and caps, rotation of a tangle around them -/

/-- `k` nested caps closing the strands `m, …, m + k - 1` against the next `k` strands. -/
private def isoCapNestW (m k : ℕ) : MorseWord :=
  (List.range k).reverse.map fun j ↦ (MorseKind.cap, m + j)

/-- `k` nested cups opening the strands `m, …, m + 2k - 1`. -/
private def isoCupNestW (m k : ℕ) : MorseWord :=
  (List.range k).map fun j ↦ (MorseKind.cup, m + j)

private theorem isoCapNestW_succ (m k : ℕ) :
    isoCapNestW m (k + 1) = (MorseKind.cap, m + k) :: isoCapNestW m k := by
  simp [isoCapNestW, List.range_succ]

private theorem isoCapNestW_add (m i j : ℕ) :
    isoCapNestW m (i + j) = isoCapNestW (m + i) j ++ isoCapNestW m i := by
  induction j with
  | zero => simp [isoCapNestW]
  | succ j ih =>
    rw [← Nat.add_assoc, isoCapNestW_succ, ih, isoCapNestW_succ, Nat.add_assoc]
    rfl

private theorem isoCupNestW_succ (m k : ℕ) :
    isoCupNestW m (k + 1) = isoCupNestW m k ++ [(MorseKind.cup, m + k)] := by
  simp [isoCupNestW, List.range_succ]

private theorem isoCupNestW_add (m i j : ℕ) :
    isoCupNestW m (i + j) = isoCupNestW m i ++ isoCupNestW (m + i) j := by
  induction j with
  | zero => simp [isoCupNestW]
  | succ j ih =>
    rw [← Nat.add_assoc, isoCupNestW_succ, ih, isoCupNestW_succ, List.append_assoc, Nat.add_assoc]

private theorem isoCapNestW_shift (d m k : ℕ) :
    morseShiftWord d (isoCapNestW m k) = isoCapNestW (m + d) k := by
  simp only [isoCapNestW, morseShiftWord, List.map_map]
  exact List.map_congr_left fun j _ ↦ by simp [shiftLetter]; omega

private theorem isoCupNestW_shift (d m k : ℕ) :
    morseShiftWord d (isoCupNestW m k) = isoCupNestW (m + d) k := by
  simp only [isoCupNestW, morseShiftWord, List.map_map]
  exact List.map_congr_left fun j _ ↦ by simp [shiftLetter]; omega

private theorem isoCapNestW_fits (m k n : ℕ) (h : m + 2 * k ≤ n) :
    morseFits n (isoCapNestW m k) = true ∧ morseOut n (isoCapNestW m k) = n - 2 * k := by
  induction k generalizing n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [isoCapNestW_succ, morseFits_cons]
    obtain ⟨h1, h2⟩ := ih (n - 2) (by omega)
    simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · rw [show n + 0 - 2 = n - 2 by omega]; exact h1
    · rw [show n + 0 - 2 = n - 2 by omega, h2]; omega

private theorem isoCupNestW_fits (m k n : ℕ) (h : m ≤ n) :
    morseFits n (isoCupNestW m k) = true ∧ morseOut n (isoCupNestW m k) = n + 2 * k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [isoCupNestW_succ, morseFits_append, morseOut_append, ih.1, ih.2]
    simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, Bool.true_and, and_true]
    omega

/-- A crossing turns around two nested caps. -/
private theorem morseReach_isoCrossCapBase (s : Bool) :
    MorseReach 4 [(MorseKind.cross s, 0), (MorseKind.cap, 1), (MorseKind.cap, 0)]
      [(MorseKind.cross s, 2), (MorseKind.cap, 1), (MorseKind.cap, 0)] := by
  cases s
  · exact ⟨[(1, .capSlide 1 false false, true), (3, .exch (.cap, 0) (.cap, 2), true),
      (0, .exch (.cross false, 0) (.cross false, 2), false), (1, .capSlide 0 false true, false)],
      by decide⟩
  · exact ⟨[(1, .capSlide 1 true false, true), (3, .exch (.cap, 0) (.cap, 2), true),
      (0, .exch (.cross true, 0) (.cross true, 2), false), (1, .capSlide 0 true true, false)],
      by decide⟩

/-- A crossing turns around two nested cups. -/
private theorem morseReach_isoCrossCupBase (s : Bool) :
    MorseReach 0 [(MorseKind.cup, 0), (MorseKind.cup, 1), (MorseKind.cross s, 0)]
      [(MorseKind.cup, 0), (MorseKind.cup, 1), (MorseKind.cross s, 2)] := by
  cases s
  · exact ⟨[(1, .cupSlide 1 false true, true), (0, .exch (.cup, 0) (.cup, 0), false),
      (3, .exch (.cross false, 0) (.cross false, 2), true), (1, .cupSlide 0 false false, false)],
      by decide⟩
  · exact ⟨[(1, .cupSlide 1 true true, true), (0, .exch (.cup, 0) (.cup, 0), false),
      (3, .exch (.cross true, 0) (.cross true, 2), true), (1, .cupSlide 0 true false, false)],
      by decide⟩


/-- The base turn of a crossing around two nested caps, at any position. -/
private theorem morseReach_isoCrossCapAt (n₀ d e : ℕ) (s : Bool) (u v : MorseWord)
    (hu : morseOut n₀ u = d + 4 + e) :
    MorseReach n₀ (u ++ [(MorseKind.cross s, d), (MorseKind.cap, d + 1), (MorseKind.cap, d)] ++ v)
      (u ++ [(MorseKind.cross s, d + 2), (MorseKind.cap, d + 1), (MorseKind.cap, d)] ++ v) := by
  have h := morseReach_frame 4 n₀ d e u v _ _ (morseReach_isoCrossCapBase s)
    (by cases s <;> rfl) hu
  simpa [morseShiftWord, shiftLetter, Nat.add_comm] using h

/-- The base turn of a crossing around two nested cups, at any position. -/
private theorem morseReach_isoCrossCupAt (n₀ d e : ℕ) (s : Bool) (u v : MorseWord)
    (hu : morseOut n₀ u = d + e) :
    MorseReach n₀ (u ++ [(MorseKind.cup, d), (MorseKind.cup, d + 1), (MorseKind.cross s, d)] ++ v)
      (u ++ [(MorseKind.cup, d), (MorseKind.cup, d + 1), (MorseKind.cross s, d + 2)] ++ v) := by
  have h := morseReach_frame 0 n₀ d e u v _ _ (morseReach_isoCrossCupBase s) (by cases s <;> rfl)
    (by omega)
  simpa [morseShiftWord, shiftLetter, Nat.add_comm] using h

/-- A one-letter word shifted. -/
private theorem morseShiftWord_single_iso (M : ℕ) (k : MorseKind) (i : ℕ) :
    morseShiftWord M [(k, i)] = [(k, i + M)] := rfl

/-- A zig `u_i n_{i+1}` at any junction. -/
private theorem morseReach_isoZigT (n₀ i : ℕ) (u v : MorseWord)
    (hu : i + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ [(MorseKind.cup, i), (MorseKind.cap, i + 1)] ++ v) (u ++ v) := by
  have h := morseReach_isoRule n₀ u v (.zig i true) rfl (by
    simp only [morseRuleLhs, ite_true, morseFits_cons, morseFits_nil, morseLetterOut, morseKindIn,
      morseKindOut, and_true]; omega) rfl
  simpa [morseRuleLhs, morseRuleRhs] using h

/-- A zig `u_{i+1} n_i` at any junction. -/
private theorem morseReach_isoZigF (n₀ i : ℕ) (u v : MorseWord)
    (hu : i + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ [(MorseKind.cup, i + 1), (MorseKind.cap, i)] ++ v) (u ++ v) := by
  have h := morseReach_isoRule n₀ u v (.zig i false) rfl (by
    simp only [morseRuleLhs, Bool.false_eq_true, ite_false, morseFits_cons, morseFits_nil,
      morseLetterOut, morseKindIn, morseKindOut, and_true]; omega) rfl
  simpa [morseRuleLhs, morseRuleRhs] using h

/-- A crossing on the left block turns around `a` nested caps. -/
private theorem morseReach_isoCapX (n₀ m a i e : ℕ) (s : Bool) (u v : MorseWord)
    (hi : i + 2 ≤ a) (hu : morseOut n₀ u = m + 2 * a + e) :
    MorseReach n₀ (u ++ [(MorseKind.cross s, m + i)] ++ isoCapNestW m a ++ v)
      (u ++ [(MorseKind.cross s, m + 2 * a - 2 - i)] ++ isoCapNestW m a ++ v) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = i + 2 + c := ⟨a - i - 2, by omega⟩
  have hN : isoCapNestW m (i + 2 + c) = isoCapNestW (m + i + 2) c ++
      [(MorseKind.cap, m + i + 1), (MorseKind.cap, m + i)] ++ isoCapNestW m i := by
    rw [Nat.add_comm (i + 2) c, ← Nat.add_comm _ c, isoCapNestW_add m (i + 2) c,
      isoCapNestW_succ, isoCapNestW_succ, ← Nat.add_assoc]
    simp [Nat.add_assoc]
  have hC := isoCapNestW_shift (m + i + 2) 0 c
  rw [Nat.zero_add] at hC
  have hY := (isoCapNestW_fits 0 c (2 * c) (by omega)).1
  have hA := morseReach_symm (morseReach_isoShiftComm n₀ (m + i + 2) (2 * c) (e + i + 2) u
    [(MorseKind.cross s, m + i)] (isoCapNestW 0 c)
    ([(MorseKind.cap, m + i + 1), (MorseKind.cap, m + i)] ++ isoCapNestW m i ++ v)
    (by rw [morseFits_cons]; exact ⟨by simp [morseKindIn], rfl⟩) hY (by rw [hu]; ring))
  rw [hC, show morseOut (m + i + 2) [(MorseKind.cross s, m + i)] = m + i + 2 from rfl, hC] at hA
  have hCf := isoCapNestW_fits (m + i + 2) c (m + 2 * (i + 2 + c) + e) (by omega)
  have hB := morseReach_isoCrossCapAt n₀ (m + i) (e + i) s (u ++ isoCapNestW (m + i + 2) c)
    (isoCapNestW m i ++ v) (by rw [morseOut_append, hu, hCf.2]; omega)
  have hCf' := isoCapNestW_fits (m + i + 2) c (m + 2 * (i + 2 + c) - 2 - i) (by omega)
  have hD := morseReach_isoShiftComm n₀ (m + 2 * (i + 2 + c) - 2 - i) 2 (e + i) u
    (isoCapNestW (m + i + 2) c) [(MorseKind.cross s, 0)]
    ([(MorseKind.cap, m + i + 1), (MorseKind.cap, m + i)] ++ isoCapNestW m i ++ v) hCf'.1
    (by cases s <;> rfl) (by rw [hu]; omega)
  rw [morseShiftWord_single_iso, morseShiftWord_single_iso, hCf'.2,
    show m + 2 * (i + 2 + c) - 2 - i - 2 * c = m + i + 2 by omega] at hD
  rw [hN]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add] at hA hB hD ⊢
  exact morseReach_trans hA (morseReach_trans (by simpa [Nat.add_assoc] using hB)
    (morseReach_symm hD))


/-- A cup on the left block turns around nested caps into a cap on the right block. -/
private theorem morseReach_isoCapU (n₀ m a i e : ℕ) (u v : MorseWord) (hi : i ≤ a)
    (hu : morseOut n₀ u = m + 2 * a + 2 + e) :
    MorseReach n₀ (u ++ [(MorseKind.cup, m + i)] ++ isoCapNestW m (a + 2) ++ v)
      (u ++ [(MorseKind.cap, m + 2 * a - i)] ++ isoCapNestW m a ++ v) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = i + c := ⟨a - i, by omega⟩
  have hN1 : isoCapNestW m (i + c + 2) = isoCapNestW (m + i + 2) c ++
      [(MorseKind.cap, m + i + 1), (MorseKind.cap, m + i)] ++ isoCapNestW m i := by
    rw [show i + c + 2 = (i + 2) + c by omega, isoCapNestW_add m (i + 2) c,
      isoCapNestW_succ, isoCapNestW_succ]
    simp [Nat.add_assoc]
  have hN2 : isoCapNestW m (i + c) = isoCapNestW (m + i) c ++ isoCapNestW m i :=
    isoCapNestW_add m i c
  have hS1 := isoCapNestW_shift (m + i) 0 c
  have hS2 := isoCapNestW_shift (m + i + 2) 0 c
  rw [Nat.zero_add] at hS1 hS2
  have hY := (isoCapNestW_fits 0 c (2 * c) (by omega)).1
  have hA := morseReach_isoShiftComm n₀ (m + i) (2 * c) (e + i + 2) u
    [(MorseKind.cup, m + i)] (isoCapNestW 0 c)
    ([(MorseKind.cap, m + i + 1), (MorseKind.cap, m + i)] ++ isoCapNestW m i ++ v)
    (by rw [morseFits_cons]; exact ⟨by simp [morseKindIn], rfl⟩) hY (by rw [hu]; ring)
  rw [hS1, show morseOut (m + i) [(MorseKind.cup, m + i)] = m + i + 2 from rfl, hS2] at hA
  have hCf := isoCapNestW_fits (m + i) c (m + 2 * (i + c) + 2 + e) (by omega)
  have hB := morseReach_isoZigT n₀ (m + i) (u ++ isoCapNestW (m + i) c)
    ([(MorseKind.cap, m + i)] ++ isoCapNestW m i ++ v) (by rw [morseOut_append, hu, hCf.2]; omega)
  have hCf' := isoCapNestW_fits (m + i) c (m + 2 * (i + c) - i) (by omega)
  have hC := morseReach_isoShiftComm n₀ (m + 2 * (i + c) - i) 2 (e + i) u
    (isoCapNestW (m + i) c) [(MorseKind.cap, 0)] (isoCapNestW m i ++ v) hCf'.1
    rfl (by rw [hu]; omega)
  rw [morseShiftWord_single_iso, morseShiftWord_single_iso, hCf'.2,
    show m + 2 * (i + c) - i - 2 * c = m + i by omega] at hC
  rw [hN1, hN2]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add] at hA hB hC ⊢
  exact morseReach_trans (morseReach_symm hA) (morseReach_trans hB (morseReach_symm hC))

/-- A cap on the left block turns around nested caps into a cup on the right block. -/
private theorem morseReach_isoCapN (n₀ m a i e : ℕ) (u v : MorseWord) (hi : i + 2 ≤ a)
    (hu : morseOut n₀ u = m + 2 * a - 2 + e) :
    MorseReach n₀ (u ++ [(MorseKind.cap, m + i)] ++ isoCapNestW m (a - 2) ++ v)
      (u ++ [(MorseKind.cup, m + 2 * a - 2 - i)] ++ isoCapNestW m a ++ v) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = i + 2 + c := ⟨a - i - 2, by omega⟩
  have hN1 : isoCapNestW m (i + 2 + c) = isoCapNestW (m + i + 2) c ++
      [(MorseKind.cap, m + i + 1), (MorseKind.cap, m + i)] ++ isoCapNestW m i := by
    rw [isoCapNestW_add m (i + 2) c, isoCapNestW_succ, isoCapNestW_succ]
    simp [Nat.add_assoc]
  have hN2 : isoCapNestW m (i + 2 + c - 2) = isoCapNestW (m + i) c ++ isoCapNestW m i := by
    rw [show i + 2 + c - 2 = i + c by omega]; exact isoCapNestW_add m i c
  have hS1 := isoCapNestW_shift (m + i) 0 c
  have hS2 := isoCapNestW_shift (m + i + 2) 0 c
  rw [Nat.zero_add] at hS1 hS2
  have hY := (isoCapNestW_fits 0 c (2 * c) (by omega)).1
  have hL := morseReach_isoShiftComm n₀ (m + i + 2) (2 * c) (e + i) u
    [(MorseKind.cap, m + i)] (isoCapNestW 0 c) (isoCapNestW m i ++ v)
    (by rw [morseFits_cons]; exact ⟨by simp [morseKindIn], rfl⟩) hY (by rw [hu]; omega)
  rw [hS2, show morseOut (m + i + 2) [(MorseKind.cap, m + i)] = m + i from rfl, hS1] at hL
  have hCf' := isoCapNestW_fits (m + i + 2) c (m + 2 * (i + 2 + c) - 2 - i) (by omega)
  have hR1 := morseReach_isoShiftComm n₀ (m + 2 * (i + 2 + c) - 2 - i) 0 (e + i) u
    (isoCapNestW (m + i + 2) c) [(MorseKind.cup, 0)]
    ([(MorseKind.cap, m + i + 1), (MorseKind.cap, m + i)] ++ isoCapNestW m i ++ v) hCf'.1
    rfl (by rw [hu]; omega)
  rw [morseShiftWord_single_iso, morseShiftWord_single_iso, hCf'.2,
    show m + 2 * (i + 2 + c) - 2 - i - 2 * c = m + i + 2 by omega] at hR1
  have hCf := isoCapNestW_fits (m + i + 2) c (m + 2 * (i + 2 + c) - 2 + e) (by omega)
  have hR2 := morseReach_isoZigF n₀ (m + i + 1) (u ++ isoCapNestW (m + i + 2) c)
    ([(MorseKind.cap, m + i)] ++ isoCapNestW m i ++ v)
    (by rw [morseOut_append, hu, hCf.2]; omega)
  rw [hN1, hN2]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add,
    show m + i + 1 + 1 = m + i + 2 by omega] at hL hR1 hR2 ⊢
  exact morseReach_trans (morseReach_symm hL) (morseReach_symm (morseReach_trans hR1 hR2))

/-- A crossing on the left block turns around nested cups. -/
private theorem morseReach_isoCupX (n₀ m k i e : ℕ) (s : Bool) (u v : MorseWord)
    (hi : i + 2 ≤ k) (hu : morseOut n₀ u = m + e) :
    MorseReach n₀ (u ++ isoCupNestW m k ++ [(MorseKind.cross s, m + i)] ++ v)
      (u ++ isoCupNestW m k ++ [(MorseKind.cross s, m + 2 * k - 2 - i)] ++ v) := by
  obtain ⟨c, rfl⟩ : ∃ c, k = i + 2 + c := ⟨k - i - 2, by omega⟩
  have hN : isoCupNestW m (i + 2 + c) = isoCupNestW m i ++
      [(MorseKind.cup, m + i), (MorseKind.cup, m + i + 1)] ++ isoCupNestW (m + i + 2) c := by
    rw [isoCupNestW_add m (i + 2) c, isoCupNestW_succ, isoCupNestW_succ]
    simp [Nat.add_assoc]
  have hS := isoCupNestW_shift (m + i + 2) 0 c
  rw [Nat.zero_add] at hS
  have hI := isoCupNestW_fits m i (m + e) (by omega)
  have hu1 : morseOut n₀ (u ++ isoCupNestW m i ++ [(MorseKind.cup, m + i),
      (MorseKind.cup, m + i + 1)]) = m + 2 * i + 4 + e := by
    rw [morseOut_append, morseOut_append, hu, hI.2]
    simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]; omega
  have hA := morseReach_isoShiftComm n₀ (m + i + 2) 0 (e + i + 2) (u ++ isoCupNestW m i ++
    [(MorseKind.cup, m + i), (MorseKind.cup, m + i + 1)]) [(MorseKind.cross s, m + i)]
    (isoCupNestW 0 c) v (by rw [morseFits_cons]; exact ⟨by simp [morseKindIn], rfl⟩)
    (isoCupNestW_fits 0 c 0 le_rfl).1 (by rw [hu1]; omega)
  rw [hS, show morseOut (m + i + 2) [(MorseKind.cross s, m + i)] = m + i + 2 from rfl, hS] at hA
  have hB := morseReach_isoCrossCupAt n₀ (m + i) (e + i) s (u ++ isoCupNestW m i)
    (isoCupNestW (m + i + 2) c ++ v) (by rw [morseOut_append, hu, hI.2]; omega)
  have hCf := isoCupNestW_fits (m + i + 2) c (m + i + 2) le_rfl
  have hC := morseReach_isoShiftComm n₀ (m + i + 2) 2 (e + i) (u ++ isoCupNestW m i ++
    [(MorseKind.cup, m + i), (MorseKind.cup, m + i + 1)]) (isoCupNestW (m + i + 2) c)
    [(MorseKind.cross s, 0)] v hCf.1 (by cases s <;> rfl) (by rw [hu1]; omega)
  rw [morseShiftWord_single_iso, morseShiftWord_single_iso, hCf.2,
    show m + i + 2 + 2 * c = m + 2 * (i + 2 + c) - 2 - i by omega] at hC
  rw [hN]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add] at hA hB hC ⊢
  exact morseReach_trans hA (morseReach_trans hB hC)

/-- A cup on the left block turns around nested cups into a cap on the right block. -/
private theorem morseReach_isoCupU (n₀ m k i e : ℕ) (u v : MorseWord) (hi : i ≤ k)
    (hu : morseOut n₀ u = m + e) :
    MorseReach n₀ (u ++ isoCupNestW m k ++ [(MorseKind.cup, m + i)] ++ v)
      (u ++ isoCupNestW m (k + 2) ++ [(MorseKind.cap, m + 2 * k + 2 - i)] ++ v) := by
  obtain ⟨c, rfl⟩ : ∃ c, k = i + c := ⟨k - i, by omega⟩
  have hN1 : isoCupNestW m (i + c) = isoCupNestW m i ++ isoCupNestW (m + i) c :=
    isoCupNestW_add m i c
  have hN2 : isoCupNestW m (i + c + 2) = isoCupNestW m i ++
      [(MorseKind.cup, m + i), (MorseKind.cup, m + i + 1)] ++ isoCupNestW (m + i + 2) c := by
    rw [show i + c + 2 = (i + 2) + c by omega, isoCupNestW_add m (i + 2) c, isoCupNestW_succ,
      isoCupNestW_succ]
    simp [Nat.add_assoc]
  have hS1 := isoCupNestW_shift (m + i) 0 c
  have hS2 := isoCupNestW_shift (m + i + 2) 0 c
  rw [Nat.zero_add] at hS1 hS2
  have hI := isoCupNestW_fits m i (m + e) (by omega)
  have hu0 : morseOut n₀ (u ++ isoCupNestW m i) = m + 2 * i + e := by
    rw [morseOut_append, hu, hI.2]; omega
  have hA := morseReach_isoShiftComm n₀ (m + i) 0 (e + i) (u ++ isoCupNestW m i)
    [(MorseKind.cup, m + i)] (isoCupNestW 0 c) v
    (by rw [morseFits_cons]; exact ⟨by simp [morseKindIn], rfl⟩)
    (isoCupNestW_fits 0 c 0 le_rfl).1 (by rw [hu0]; omega)
  rw [hS1, show morseOut (m + i) [(MorseKind.cup, m + i)] = m + i + 2 from rfl, hS2] at hA
  have hu1 : morseOut n₀ (u ++ isoCupNestW m i ++ [(MorseKind.cup, m + i),
      (MorseKind.cup, m + i + 1)]) = m + 2 * i + 4 + e := by
    rw [morseOut_append, hu0]
    simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]; omega
  have hCf := isoCupNestW_fits (m + i + 2) c (m + i + 2) le_rfl
  have hB := morseReach_isoShiftComm n₀ (m + i + 2) 2 (e + i) (u ++ isoCupNestW m i ++
    [(MorseKind.cup, m + i), (MorseKind.cup, m + i + 1)]) (isoCupNestW (m + i + 2) c)
    [(MorseKind.cap, 0)] v hCf.1 rfl (by rw [hu1]; omega)
  rw [morseShiftWord_single_iso, morseShiftWord_single_iso, hCf.2,
    show m + i + 2 + 2 * c = m + 2 * (i + c) + 2 - i by omega] at hB
  have hZ := morseReach_isoZigT n₀ (m + i + 1) (u ++ isoCupNestW m i ++ [(MorseKind.cup, m + i)])
    (isoCupNestW (m + i + 2) c ++ v) (by
      rw [morseOut_append, hu0]
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]; omega)
  rw [hN1, hN2]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add,
    show m + i + 1 + 1 = m + i + 2 by omega] at hA hB hZ ⊢
  exact morseReach_trans hA (morseReach_trans (morseReach_symm hZ) hB)

/-- A cap on the left block turns around nested cups into a cup on the right block. -/
private theorem morseReach_isoCupN (n₀ m k i e : ℕ) (u v : MorseWord) (hi : i + 2 ≤ k)
    (hu : morseOut n₀ u = m + e) :
    MorseReach n₀ (u ++ isoCupNestW m k ++ [(MorseKind.cap, m + i)] ++ v)
      (u ++ isoCupNestW m (k - 2) ++ [(MorseKind.cup, m + 2 * k - 4 - i)] ++ v) := by
  obtain ⟨c, rfl⟩ : ∃ c, k = i + 2 + c := ⟨k - i - 2, by omega⟩
  have hN1 : isoCupNestW m (i + 2 + c) = isoCupNestW m i ++
      [(MorseKind.cup, m + i), (MorseKind.cup, m + i + 1)] ++ isoCupNestW (m + i + 2) c := by
    rw [isoCupNestW_add m (i + 2) c, isoCupNestW_succ, isoCupNestW_succ]
    simp [Nat.add_assoc]
  have hN2 : isoCupNestW m (i + 2 + c - 2) = isoCupNestW m i ++ isoCupNestW (m + i) c := by
    rw [show i + 2 + c - 2 = i + c by omega]; exact isoCupNestW_add m i c
  have hS1 := isoCupNestW_shift (m + i) 0 c
  have hS2 := isoCupNestW_shift (m + i + 2) 0 c
  rw [Nat.zero_add] at hS1 hS2
  have hI := isoCupNestW_fits m i (m + e) (by omega)
  have hu0 : morseOut n₀ (u ++ isoCupNestW m i) = m + 2 * i + e := by
    rw [morseOut_append, hu, hI.2]; omega
  have hu1 : morseOut n₀ (u ++ isoCupNestW m i ++ [(MorseKind.cup, m + i),
      (MorseKind.cup, m + i + 1)]) = m + 2 * i + 4 + e := by
    rw [morseOut_append, hu0]
    simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]; omega
  have hA := morseReach_isoShiftComm n₀ (m + i + 2) 0 (e + i + 2) (u ++ isoCupNestW m i ++
    [(MorseKind.cup, m + i), (MorseKind.cup, m + i + 1)]) [(MorseKind.cap, m + i)]
    (isoCupNestW 0 c) v (by rw [morseFits_cons]; exact ⟨by simp [morseKindIn], rfl⟩)
    (isoCupNestW_fits 0 c 0 le_rfl).1 (by rw [hu1]; omega)
  rw [hS2, show morseOut (m + i + 2) [(MorseKind.cap, m + i)] = m + i from rfl, hS1] at hA
  have hZ := morseReach_isoZigF n₀ (m + i) (u ++ isoCupNestW m i ++ [(MorseKind.cup, m + i)])
    (isoCupNestW (m + i) c ++ v) (by
      rw [morseOut_append, hu0]
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]; omega)
  have hCf := isoCupNestW_fits (m + i) c (m + i) le_rfl
  have hB := morseReach_isoShiftComm n₀ (m + i) 0 (e + i) (u ++ isoCupNestW m i)
    (isoCupNestW (m + i) c) [(MorseKind.cup, 0)] v hCf.1 rfl (by rw [hu0]; omega)
  rw [morseShiftWord_single_iso, morseShiftWord_single_iso, hCf.2,
    show m + i + 2 * c = m + 2 * (i + 2 + c) - 4 - i by omega] at hB
  rw [hN1, hN2]
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add] at hA hB hZ ⊢
  exact morseReach_trans hA (morseReach_trans hZ hB)


/-- One letter turns around nested caps. -/
private theorem morseReach_isoCapLetter (n₀ m a e : ℕ) (l : MorseLetter) (u v : MorseWord)
    (hl : l.2 + morseKindIn l.1 ≤ a) (hu : morseOut n₀ u = m + a + morseLetterOut a l + e) :
    MorseReach n₀ (u ++ [shiftLetter m l] ++ isoCapNestW m (morseLetterOut a l) ++ v)
      (u ++ [shiftLetter (m + a) (isoRotLetter a l)] ++ isoCapNestW m a ++ v) := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [shiftLetter, isoRotLetter, morseLetterOut, morseKindIn, morseKindOut] at hl hu ⊢
    rw [show i + m = m + i by omega, show a - i + (m + a) = m + 2 * a - i by omega,
      show a + 2 - 0 = a + 2 by omega]
    exact morseReach_isoCapU n₀ m a i e u v hl (by omega)
  | cap =>
    simp only [shiftLetter, isoRotLetter, morseLetterOut, morseKindIn, morseKindOut] at hl hu ⊢
    rw [show i + m = m + i by omega, show a - 2 - i + (m + a) = m + 2 * a - 2 - i by omega,
      show a + 0 - 2 = a - 2 by omega]
    exact morseReach_isoCapN n₀ m a i e u v hl (by omega)
  | cross s =>
    simp only [shiftLetter, isoRotLetter, morseLetterOut, morseKindIn, morseKindOut] at hl hu ⊢
    rw [show i + m = m + i by omega, show a - 2 - i + (m + a) = m + 2 * a - 2 - i by omega,
      show a + 2 - 2 = a by omega]
    exact morseReach_isoCapX n₀ m a i e s u v hl (by omega)

/-- One letter turns around nested cups. -/
private theorem morseReach_isoCupLetter (n₀ m k e : ℕ) (l : MorseLetter) (u v : MorseWord)
    (hl : l.2 + morseKindIn l.1 ≤ k) (hu : morseOut n₀ u = m + e) :
    MorseReach n₀ (u ++ isoCupNestW m k ++ [shiftLetter m l] ++ v)
      (u ++ isoCupNestW m (morseLetterOut k l) ++
        [shiftLetter (m + morseLetterOut k l) (isoRotLetter k l)] ++ v) := by
  obtain ⟨c, i⟩ := l
  cases c with
  | cup =>
    simp only [shiftLetter, isoRotLetter, morseLetterOut, morseKindIn, morseKindOut] at hl ⊢
    rw [show i + m = m + i by omega, show k - i + (m + (k + 2 - 0)) = m + 2 * k + 2 - i by omega,
      show k + 2 - 0 = k + 2 by omega]
    exact morseReach_isoCupU n₀ m k i e u v hl hu
  | cap =>
    simp only [shiftLetter, isoRotLetter, morseLetterOut, morseKindIn, morseKindOut] at hl ⊢
    rw [show i + m = m + i by omega,
      show k - 2 - i + (m + (k + 0 - 2)) = m + 2 * k - 4 - i by omega,
      show k + 0 - 2 = k - 2 by omega]
    exact morseReach_isoCupN n₀ m k i e u v hl hu
  | cross s =>
    simp only [shiftLetter, isoRotLetter, morseLetterOut, morseKindIn, morseKindOut] at hl ⊢
    rw [show i + m = m + i by omega,
      show k - 2 - i + (m + (k + 2 - 2)) = m + 2 * k - 2 - i by omega]
    exact morseReach_isoCupX n₀ m k i e s u v hl hu

/-- A tangle turns around nested caps and is rotated. -/
private theorem morseReach_isoCapRot (n₀ m e : ℕ) :
    ∀ (T : MorseWord) (a : ℕ) (u v : MorseWord),
    morseFits a T = true → morseOut n₀ u = m + a + morseOut a T + e →
    MorseReach n₀ (u ++ morseShiftWord m T ++ isoCapNestW m (morseOut a T) ++ v)
      (u ++ morseShiftWord (m + a) (isoRot a T) ++ isoCapNestW m a ++ v)
  | [], a, u, v, _, _ => morseReach_refl n₀ _
  | l :: T, a, u, v, hT, hu => by
    rw [morseFits_cons] at hT
    have hR := isoRot_fits T (morseLetterOut a l) hT.2
    have hl1 := hT.1
    have hb : morseOut a (l :: T) = morseOut (morseLetterOut a l) T := rfl
    rw [hb] at hu ⊢
    have h1 := morseReach_isoCapRot n₀ m e T (morseLetterOut a l) (u ++ [shiftLetter m l]) v hT.2
      (by rw [morseOut_append, hu]; simp only [morseOut, morseLetterOut, shiftLetter]; omega)
    have h2 := morseReach_isoShiftComm n₀ (m + a) (morseOut (morseLetterOut a l) T) e u
      [shiftLetter m l] (isoRot (morseLetterOut a l) T)
      (isoCapNestW m (morseLetterOut a l) ++ v)
      (by rw [morseFits_cons]; exact ⟨by simp only [shiftLetter]; omega, rfl⟩) hR.1
      (by rw [hu])
    rw [show morseOut (m + a) [shiftLetter m l] = m + morseLetterOut a l by
      simp only [morseOut, morseLetterOut, shiftLetter]; omega] at h2
    have hs := morseOut_shift_iso (m + a) (morseOut (morseLetterOut a l) T) e
      (isoRot (morseLetterOut a l) T) hR.1
    have h3 := morseReach_isoCapLetter n₀ m a e l
      (u ++ morseShiftWord (m + a) (isoRot (morseLetterOut a l) T)) v hl1
      (by rw [morseOut_append, hu, hs.1, hR.2])
    simp only [isoRot, morseShiftWord, List.map_cons, List.map_append, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans (morseReach_symm h2) h3)

/-- A tangle turns around nested cups and is rotated. -/
private theorem morseReach_isoCupRot (n₀ m e : ℕ) :
    ∀ (T : MorseWord) (k : ℕ) (u v : MorseWord),
    morseFits k T = true → morseOut n₀ u = m + e →
    MorseReach n₀ (u ++ isoCupNestW m k ++ morseShiftWord m T ++ v)
      (u ++ isoCupNestW m (morseOut k T) ++ morseShiftWord (m + morseOut k T) (isoRot k T) ++ v)
  | [], k, u, v, _, _ => by simpa [morseShiftWord, isoRot, morseOut] using morseReach_refl n₀ _
  | l :: T, k, u, v, hT, hu => by
    rw [morseFits_cons] at hT
    have hl := isoRotLetter_fits k l hT.1
    have hb : morseOut k (l :: T) = morseOut (morseLetterOut k l) T := rfl
    rw [hb]
    have h1 := morseReach_isoCupLetter n₀ m k e l u (morseShiftWord m T ++ v) hT.1 hu
    have hC := isoCupNestW_fits m (morseLetterOut k l) (m + e) (by omega)
    have hX : morseFits (m + morseLetterOut k l) (morseShiftWord m T) = true := by
      have := morseFits_morseShiftWord (morseLetterOut k l) m 0 T hT.2
      rwa [Nat.add_zero, Nat.add_comm] at this
    have h2 := morseReach_isoShiftComm n₀ (m + morseLetterOut k l) (morseLetterOut k l) e
      (u ++ isoCupNestW m (morseLetterOut k l)) (morseShiftWord m T) [isoRotLetter k l] v hX
      (by rw [morseFits_cons]; exact ⟨hl.1, rfl⟩) (by rw [morseOut_append, hu, hC.2]; omega)
    rw [show morseOut (m + morseLetterOut k l) (morseShiftWord m T) =
      m + morseOut (morseLetterOut k l) T by
        rw [Nat.add_comm m, morseOut_morseShiftWord _ _ _ hT.2, Nat.add_comm]] at h2
    have h3 := morseReach_isoCupRot n₀ m e T (morseLetterOut k l) u
      ([shiftLetter (m + morseOut (morseLetterOut k l) T) (isoRotLetter k l)] ++ v) hT.2 hu
    simp only [isoRot, morseShiftWord, List.map_cons, List.map_append, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- A band bead passes a doubled crossing (`p` the position of the left band). -/
theorem morseReach_isoBead_D (n₀ p : ℕ) (T u v : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 2 * p + 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p) T ++ morseShiftWord (2 * p) phaseTwoD ++ v)
      (u ++ morseShiftWord (2 * p) phaseTwoD ++ morseShiftWord (2 * p + 2) T ++ v) := by
  have h := morseReach_beadD_left 4 [] T [] hT hTo le_rfl
  have hf : morseFits 4 (T ++ phaseTwoD) = true := by
    rw [morseFits_append, morseFits_add_right_iso 2 2 T hT, morseOut_add_right 2 2 T hT, hTo]
    rfl
  have h2 := morseReach_frame 4 n₀ (2 * p) (morseOut n₀ u - 2 * p - 4) u v _ _
    (by simpa using h) hf (by omega)
  rw [morseShiftWord_append, morseShiftWord_append, morseShiftWord_shift_iso,
    Nat.add_comm 2 (2 * p)] at h2
  simpa only [List.append_assoc] using h2

/-- A band bead turns around a doubled cap and is rotated. -/
theorem morseReach_isoBead_cap (n₀ p : ℕ) (T u v : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 2 * p + 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p) T ++ morseDouble [isoN p] ++ v)
      (u ++ morseShiftWord (2 * p + 2) (isoRot 2 T) ++ morseDouble [isoN p] ++ v) := by
  have hD : morseDouble [isoN p] = isoCapNestW (2 * p) 2 := by
    simp [morseDouble, morseDoubleLetter, isoN, isoCapNestW, List.range_succ]
  have h := morseReach_isoCapRot n₀ (2 * p) (morseOut n₀ u - 2 * p - 4) T 2 u v hT
    (by rw [hTo]; omega)
  rw [hTo] at h
  rw [hD]
  exact h

/-- A band bead turns around a doubled cup and is rotated. -/
theorem morseReach_isoBead_cup (n₀ p : ℕ) (T u v : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (hu : 2 * p ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseDouble [isoU p] ++ morseShiftWord (2 * p) T ++ v)
      (u ++ morseDouble [isoU p] ++ morseShiftWord (2 * p + 2) (isoRot 2 T) ++ v) := by
  have hD : morseDouble [isoU p] = isoCupNestW (2 * p) 2 := by
    simp [morseDouble, morseDoubleLetter, isoU, isoCupNestW, List.range_succ]
  have h := morseReach_isoCupRot n₀ (2 * p) (morseOut n₀ u - 2 * p) T 2 u v hT (by omega)
  rw [hTo] at h
  rw [hD]
  exact h

/-- A negative full twist of the band is two positive edge curls and a negative doubled curl. -/
theorem morseReach_isoTwist_dcurl :
    MorseReach 2 [isoX false 0, isoX false 0]
      (isoCurlL true 1 ++ isoCurlL true 0 ++ morseDouble (isoCurlR false 0)) :=
    ⟨[(0, .zig 1 true, true), (1, .zig 2 true, true), (2, .capSlide 3 true false, true),
      (4, .exch (.cap, 2) (.cap, 4), true), (5, .r2 1 true, true),
      (1, .cupSlide 2 true true, true), (3, .r3 3 true, false),
      (5, .exch (.cap, 2) (.cross true, 4), true),
      (2, .exch (.cross true, 2) (.cross true, 4), false), (3, .capSlide 2 true true, false),
      (0, .exch (.cup, 1) (.cup, 1), false), (1, .exch (.cup, 1) (.cross true, 2), false),
      (2, .exch (.cup, 1) (.cap, 1), false), (3, .cupSlide 1 true false, false),
      (3, .zig 0 true, true), (4, .zig 1 true, true), (5, .capSlide 2 true false, true),
      (7, .exch (.cap, 1) (.cap, 3), true), (8, .r2 0 true, true),
      (4, .cupSlide 1 true true, true), (6, .r3 2 true, false),
      (8, .exch (.cap, 1) (.cross true, 3), true),
      (5, .exch (.cross true, 1) (.cross true, 3), false), (6, .capSlide 1 true true, false),
      (3, .exch (.cup, 0) (.cup, 0), false), (4, .exch (.cup, 0) (.cross true, 1), false),
      (5, .exch (.cup, 0) (.cap, 0), false), (6, .cupSlide 0 true false, false),
      (8, .exch (.cap, 1) (.cup, 4), false), (7, .exch (.cross false, 0) (.cup, 4), false),
      (9, .exch (.cap, 1) (.cross false, 3), false), (10, .exch (.cap, 1) (.cap, 4), false),
      (8, .exch (.cross false, 0) (.cross false, 3), false),
      (9, .exch (.cross false, 0) (.cap, 4), false), (6, .exch (.cup, 1) (.cup, 2), false),
      (7, .exch (.cup, 1) (.cross false, 1), false), (8, .exch (.cup, 1) (.cap, 2), false),
      (11, .capSlide 1 false false, true), (10, .exch (.cross false, 0) (.cross false, 2), false),
      (13, .exch (.cross false, 0) (.cap, 2), true), (11, .r3 0 false, false),
      (9, .cupSlide 1 false false, false), (9, .exch (.cross false, 0) (.cup, 2), true),
      (9, .exch (.cross false, 0) (.cup, 2), false),
      (12, .exch (.cross false, 0) (.cap, 2), true), (10, .r3 0 false, false),
      (8, .exch (.cap, 2) (.cup, 4), false), (7, .exch (.cross false, 1) (.cup, 4), false),
      (6, .exch (.cup, 2) (.cup, 2), false), (9, .capSlide 2 false false, true),
      (8, .exch (.cross false, 1) (.cross false, 3), false),
      (11, .exch (.cross false, 1) (.cap, 3), true), (9, .r3 1 false, false),
      (7, .cupSlide 2 false false, false), (7, .exch (.cross false, 1) (.cup, 3), true),
      (10, .exch (.cross false, 0) (.cap, 3), true),
      (11, .exch (.cross false, 1) (.cap, 3), true),
      (9, .exch (.cross false, 0) (.cross false, 2), true),
      (7, .exch (.cross false, 1) (.cup, 3), false)],
    by decide⟩

end AJConjecture
