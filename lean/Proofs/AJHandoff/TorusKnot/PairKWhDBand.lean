import Mathlib
import AJHandoff.TorusKnot.PairKWhDOrientBasic

/-!
# The band of the Whitehead double is untwisted

**Untwisted.** `zero_mem_bandLinkings_whBand`: for every long-knot diagram `D`, the band
`whBand D = morseDouble D ++ bandUntwist (morseWrithe D)`, viewed as a two-string tangle whose two
strings (the two edges of the band) both run upward, carries the labelling induced from the
orientation of `D`, and in it the linking number of the two edges, computed from crossing signs,
is `0`. (The blackboard double contributes the writhe `w` of `D`: each crossing of `D` gives two
crossings between different edges, of the oriented sign of the original crossing; the correction
contributes `-w`.) For the cut-open torus knots the labelling is the only one
(`bandLinkings_whBand_braidLongDiagram`, `PairKWhDBandTorus`).

The clasp sign is in `PairKWhDClasp`.

Route: `lkStates_frame` (as `orientStates_frame`); each doubled letter acts on the window of the
doubled labels (`lkDouble`) of its strands (a cup on `(d, !d)` gives the four labels
`lkDouble [d, !d]`, a crossing of oriented sign `ε` gives `2ε`, a cap needs opposite directions),
a finite computation; `lkStates_morseDouble_of_mem` by induction on `D`; `lkStates_bandUntwist` by
induction on the number of twists.
-/

namespace AJConjecture

/-- The doubled labels of an orientation: each strand of direction `d` becomes its two parallel
copies, both of direction `d`; the copy on the left in the direction of travel is the component
`false` (so an upward strand gives `[(true, false), (true, true)]`). -/
def lkDouble (a : List Bool) : List (Bool × Bool) :=
  a.flatMap fun d ↦ [(d, !d), (d, d)]

/-- A concatenation acts as its first part followed by its second part. -/
theorem lkStates_append (u v : MorseWord) (S : List (List (Bool × Bool) × ℤ)) :
    lkStates (u ++ v) S = lkStates v (lkStates u S) := by
  induction u generalizing S with
  | nil => rfl
  | cons l u ih => exact ih _

/-- A word acts on a concatenation of state lists part by part. -/
theorem lkStates_append_states (w : MorseWord) (S T : List (List (Bool × Bool) × ℤ)) :
    lkStates w (S ++ T) = lkStates w S ++ lkStates w T := by
  induction w generalizing S T with
  | nil => rfl
  | cons l w ih =>
    simp only [lkStates, List.flatMap_append]
    exact ih _ _

/-- A word acts state by state. -/
theorem lkStates_eq_flatMap (w : MorseWord) (S : List (List (Bool × Bool) × ℤ)) :
    lkStates w S = S.flatMap fun st ↦ lkStates w [st] := by
  induction S with
  | nil =>
    induction w with
    | nil => rfl
    | cons l w ih => simpa [lkStates] using ih
  | cons st S ih =>
    rw [List.flatMap_cons, ← ih, ← lkStates_append_states]
    rfl

/-- A fitting letter maps `n` directions to `morseLetterOut n l` directions. -/
private theorem lkLetter_length (n : ℕ) (l : MorseLetter) (hl : l.2 + morseKindIn l.1 ≤ n)
    (st : List (Bool × Bool) × ℤ) (hst : st.1.length = n) :
    ∀ st' ∈ lkLetter l st, st'.1.length = morseLetterOut n l := by
  obtain ⟨a, x⟩ := st
  obtain ⟨k, i⟩ := l
  simp only at hst
  cases k with
  | cup =>
    simp only [morseKindIn] at hl
    intro st' h
    simp only [lkLetter] at h
    rw [ite_eq_left (by omega)] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;>
      simp [morseLetterOut, morseKindOut, morseKindIn, hst] <;> omega
  | cap =>
    simp only [morseKindIn] at hl
    obtain ⟨p, q, b, hb⟩ : ∃ p q b, a.drop i = p :: q :: b := by
      rcases h : a.drop i with _ | ⟨p, _ | ⟨q, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨p, q, b, rfl⟩
    have hlen : b.length + 2 + i = n := by
      have := congrArg List.length hb; simp at this; omega
    intro st' h
    simp only [lkLetter, hb] at h
    split_ifs at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp [morseLetterOut, morseKindOut, morseKindIn]
      omega
    · simp at h
  | cross s =>
    simp only [morseKindIn] at hl
    obtain ⟨p, q, b, hb⟩ : ∃ p q b, a.drop i = p :: q :: b := by
      rcases h : a.drop i with _ | ⟨p, _ | ⟨q, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨p, q, b, rfl⟩
    have hlen : b.length + 2 + i = n := by
      have := congrArg List.length hb; simp at this; omega
    intro st' h
    simp only [lkLetter, hb, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp [morseLetterOut, morseKindOut, morseKindIn]
    omega

/-- On a fitting word, every output state has `morseOut n w` directions. -/
private theorem lkStates_length (n : ℕ) (w : MorseWord) (hw : morseFits n w = true)
    (S : List (List (Bool × Bool) × ℤ)) (hS : ∀ st ∈ S, st.1.length = n) :
    ∀ st ∈ lkStates w S, st.1.length = morseOut n w := by
  induction w generalizing n S with
  | nil => exact hS
  | cons l w ih =>
    rw [morseFits_cons] at hw
    refine ih _ hw.2 _ fun st' h ↦ ?_
    obtain ⟨st, hst, h⟩ := List.mem_flatMap.1 h
    exact lkLetter_length n l hw.1 st (hS st hst) st' h

/-- The frame of a letter. -/
private theorem lkLetter_frame (m : ℕ) (l : MorseLetter) (hl : l.2 + morseKindIn l.1 ≤ m)
    (p a q : List (Bool × Bool)) (ha : a.length = m) (x : ℤ) :
    lkLetter (shiftLetter p.length l) (p ++ a ++ q, x) =
      (lkLetter l (a, x)).map fun st ↦ (p ++ st.1 ++ q, st.2) := by
  obtain ⟨k, i⟩ := l
  have htake : ∀ j ≤ a.length, (p ++ a ++ q).take (j + p.length) = p ++ a.take j := by
    intro j hj
    rw [List.append_assoc, Nat.add_comm, List.take_length_add_append,
      List.take_append_of_le_length hj]
  have hdrop : ∀ j ≤ a.length, (p ++ a ++ q).drop (j + p.length) = a.drop j ++ q := by
    intro j hj
    rw [List.append_assoc, Nat.add_comm, List.drop_length_add_append,
      List.drop_append_of_le_length hj]
  simp only [shiftLetter]
  cases k with
  | cup =>
    simp only [morseKindIn] at hl
    simp only [lkLetter, List.length_append]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), htake i (by omega), hdrop i (by omega)]
    simp
  | cap =>
    simp only [morseKindIn] at hl
    obtain ⟨u, v, b, hb⟩ : ∃ u v b, a.drop i = u :: v :: b := by
      rcases h : a.drop i with _ | ⟨u, _ | ⟨v, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨u, v, b, rfl⟩
    simp only [lkLetter, hdrop i (by omega), hb, htake i (by omega), List.cons_append]
    split_ifs <;> simp
  | cross s =>
    simp only [morseKindIn] at hl
    obtain ⟨u, v, b, hb⟩ : ∃ u v b, a.drop i = u :: v :: b := by
      rcases h : a.drop i with _ | ⟨u, _ | ⟨v, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨u, v, b, rfl⟩
    simp only [lkLetter, hdrop i (by omega), hb, htake i (by omega), List.cons_append]
    simp

/-- The frame of a word, on a list of states. -/
private theorem lkStates_frame_list (m : ℕ) (w : MorseWord) (hw : morseFits m w = true)
    (p q : List (Bool × Bool)) (S : List (List (Bool × Bool) × ℤ))
    (hS : ∀ st ∈ S, st.1.length = m) :
    lkStates (morseShiftWord p.length w) (S.map fun st ↦ (p ++ st.1 ++ q, st.2)) =
      (lkStates w S).map fun st ↦ (p ++ st.1 ++ q, st.2) := by
  induction w generalizing m S with
  | nil => rfl
  | cons l w ih =>
    rw [morseFits_cons] at hw
    simp only [morseShiftWord, List.map_cons, lkStates] at ih ⊢
    rw [List.flatMap_map]
    rw [List.flatMap_congr (g := fun st ↦ (lkLetter l st).map
      fun st ↦ (p ++ st.1 ++ q, st.2)) fun st hst ↦
        lkLetter_frame m l hw.1 p st.1 q (hS st hst) st.2]
    rw [← List.map_flatMap]
    refine ih _ hw.2 _ fun st' h ↦ ?_
    obtain ⟨st, hst, h⟩ := List.mem_flatMap.1 h
    exact lkLetter_length m l hw.1 st (hS st hst) st' h

/-- The frame of a word for labelled states (as `orientStates_frame`). -/
theorem lkStates_frame (m d : ℕ) (w : MorseWord) (hw : morseFits m w = true)
    (p a q : List (Bool × Bool)) (hp : p.length = d) (ha : a.length = m) (x : ℤ) :
    lkStates (morseShiftWord d w) [(p ++ a ++ q, x)] =
      (lkStates w [(a, x)]).map fun st ↦ (p ++ st.1 ++ q, st.2) := by
  subst hp
  have := lkStates_frame_list m w hw p q [(a, x)] (by simp [ha])
  simpa using this

/-- The doubled labels of a concatenation. -/
theorem lkDouble_append (u v : List Bool) : lkDouble (u ++ v) = lkDouble u ++ lkDouble v :=
  List.flatMap_append

/-- Each direction gives two labels. -/
theorem length_lkDouble (u : List Bool) : (lkDouble u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons d u ih => simp [lkDouble] at ih ⊢; omega

/-- The double of a letter at `i` is the double of the letter at `0`, shifted by `2i`. -/
private theorem morseDoubleLetter_shift (k : MorseKind) (i : ℕ) :
    morseDoubleLetter (k, i) = morseShiftWord (2 * i) (morseDoubleLetter (k, 0)) := by
  cases k with
  | cup => simp [morseDoubleLetter, morseShiftWord, shiftLetter]; omega
  | cap => simp [morseDoubleLetter, morseShiftWord, shiftLetter]; omega
  | cross s =>
    cases s <;> simp [morseDoubleLetter, cable, cableGen, morseOfBraid, morseShiftWord,
      shiftLetter, List.range_succ] <;> omega

/-- One letter: the double of an oriented state is a labelled state of the doubled letter. -/
private theorem lkDoubleLetter_of_mem {l : MorseLetter} {a : List Bool} {x : ℤ}
    {st : List Bool × ℤ} (h : st ∈ orientLetter l (a, x)) :
    (lkDouble st.1, 2 * st.2) ∈ lkStates (morseDoubleLetter l) [(lkDouble a, 2 * x)] := by
  obtain ⟨k, i⟩ := l
  rw [morseDoubleLetter_shift]
  -- the window of a letter that fits
  have hwin : ∀ (p q : Bool) (b : List Bool), a.drop i = p :: q :: b →
      (lkDouble (a.take i)).length = 2 * i ∧
        lkDouble a = lkDouble (a.take i) ++ lkDouble [p, q] ++ lkDouble b := by
    intro p q b hb
    have hi : i < a.length := by
      by_contra hc
      rw [List.drop_of_length_le (by omega)] at hb
      simp at hb
    refine ⟨by rw [length_lkDouble, List.length_take]; omega, ?_⟩
    rw [← lkDouble_append, ← lkDouble_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop i a, hb]
    simp
  cases k with
  | cup =>
    simp only [orientLetter] at h
    split_ifs at h with hi
    swap
    · simp at h
    have hP : (lkDouble (a.take i)).length = 2 * i := by
      rw [length_lkDouble, List.length_take]; omega
    have ha : lkDouble a = lkDouble (a.take i) ++ [] ++ lkDouble (a.drop i) := by
      rw [List.append_nil, ← lkDouble_append, List.take_append_drop]
    rw [ha, lkStates_frame 0 (2 * i) _ rfl _ _ _ hP rfl]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine List.mem_map.2 ⟨(lkDouble [true, false], 2 * x), ?_, ?_⟩
      · simp [morseDoubleLetter, lkStates, lkLetter, lkDouble]
      · simp [lkDouble]
    · refine List.mem_map.2 ⟨(lkDouble [false, true], 2 * x), ?_, ?_⟩
      · simp [morseDoubleLetter, lkStates, lkLetter, lkDouble]
      · simp [lkDouble]
  | cap =>
    obtain ⟨p, q, b, hb⟩ : ∃ p q b, a.drop i = p :: q :: b := by
      rcases hd : a.drop i with _ | ⟨p, _ | ⟨q, b⟩⟩
      · simp [orientLetter, hd] at h
      · simp [orientLetter, hd] at h
      · exact ⟨p, q, b, rfl⟩
    obtain ⟨hP, ha⟩ := hwin p q b hb
    simp only [orientLetter, hb] at h
    split_ifs at h with hpq
    · simp at h
    simp only [List.mem_singleton] at h
    subst h
    rw [ha, lkStates_frame 4 (2 * i) _ rfl _ _ _ hP rfl]
    refine List.mem_map.2 ⟨([], 2 * x), ?_, by simp [lkDouble_append]⟩
    cases p <;> cases q <;> simp_all [morseDoubleLetter, lkStates, lkLetter, lkDouble]
  | cross s =>
    obtain ⟨p, q, b, hb⟩ : ∃ p q b, a.drop i = p :: q :: b := by
      rcases hd : a.drop i with _ | ⟨p, _ | ⟨q, b⟩⟩
      · simp [orientLetter, hd] at h
      · simp [orientLetter, hd] at h
      · exact ⟨p, q, b, rfl⟩
    obtain ⟨hP, ha⟩ := hwin p q b hb
    simp only [orientLetter, hb, List.mem_singleton] at h
    subst h
    rw [ha, lkStates_frame 4 (2 * i) _ (by cases s <;> rfl) _ _ _ hP rfl]
    refine List.mem_map.2 ⟨(lkDouble [q, p], 2 * x + 2 * orientSign s p q), ?_, ?_⟩
    · cases p <;> cases q <;> cases s <;>
        simp [morseDoubleLetter, cable, cableGen, morseOfBraid, lkStates, lkLetter, lkDouble,
          orientSign, List.range_succ] <;> ring
    · simp [lkDouble]
      ring

/-- **The double of an orientation is a labelling of the double**: every oriented state of `w`
gives a labelled state of `morseDouble w`, with twice the oriented writhe as the sum of the
signs of the crossings between different components. -/
theorem lkStates_morseDouble_of_mem {w : MorseWord} {a b : List Bool} {x y : ℤ}
    (h : (b, y) ∈ orientStates w [(a, x)]) :
    (lkDouble b, 2 * y) ∈ lkStates (morseDouble w) [(lkDouble a, 2 * x)] := by
  induction w generalizing a x with
  | nil =>
    simp only [orientStates, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact List.mem_singleton_self _
  | cons l w ih =>
    rw [orientStates, orientStates_eq_flatMap, List.mem_flatMap] at h
    obtain ⟨st, hst, h⟩ := h
    rw [List.flatMap_singleton] at hst
    have h1 := lkDoubleLetter_of_mem hst
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from List.flatMap_cons,
      lkStates_append, lkStates_eq_flatMap (morseDouble w), List.mem_flatMap]
    exact ⟨_, h1, ih h⟩

/-- The correction twists, on the band end: `2|w|` crossings between the two edges, of total
sign `-2w`. -/
theorem lkStates_bandUntwist (w x : ℤ) :
    lkStates (bandUntwist w) [(bandEnd, x)] = [(bandEnd, x - 2 * w)] := by
  have hrep : ∀ (s : Bool) (n : ℕ) (y : ℤ),
      lkStates (List.replicate (2 * n) (.cross s, 0)) [(bandEnd, y)] =
        [(bandEnd, y + 2 * n * (if s then 1 else -1))] := by
    intro s n
    induction n with
    | zero => intro y; simp [lkStates]
    | succ n ih =>
      intro y
      rw [show 2 * (n + 1) = 2 + 2 * n by ring, List.replicate_add, lkStates_append]
      have h2 : lkStates (List.replicate 2 (.cross s, 0)) [(bandEnd, y)] =
          [(bandEnd, y + 2 * (if s then 1 else -1))] := by
        cases s <;> simp [lkStates, lkLetter, bandEnd, orientSign] <;> ring_nf
      rw [h2, ih]
      push_cast
      ring_nf
  unfold bandUntwist
  split_ifs with hw
  · rw [hrep]
    simp only [Bool.false_eq_true, ↓reduceIte, Int.toNat_of_nonneg hw]
    ring_nf
  · rw [hrep]
    simp only [↓reduceIte, Int.toNat_of_nonneg (by omega : 0 ≤ -w)]
    ring_nf

/-- **The band of the Whitehead double is untwisted**: with the labelling induced from the
orientation of `D`, the two edges of `whBand D` have linking number `0`. -/
theorem zero_mem_bandLinkings_whBand {D : MorseWord} (hD : IsLongKnotDiagram D) :
    0 ∈ bandLinkings (whBand D) := by
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.1 hD.2
  have hwr : morseWrithe D = v := by rw [morseWrithe, hv, List.sum_singleton]
  have hmem : ([true], v) ∈ orientStates D [([true], 0)] := by
    have : v ∈ orientWrithes D := by rw [hv]; exact List.mem_singleton_self v
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 this
    obtain ⟨hst, h1⟩ := List.mem_filter.1 hst
    rw [decide_eq_true_eq] at h1
    obtain ⟨a, y⟩ := st
    simp only at h1 ⊢
    rw [← h1]
    exact h1 ▸ hst
  have hdbl := lkStates_morseDouble_of_mem hmem
  rw [mul_zero, show lkDouble [true] = bandEnd from rfl] at hdbl
  have htw : (bandEnd, 2 * v - 2 * v) ∈ lkStates (whBand D) [(bandEnd, 0)] := by
    rw [whBand, hwr, lkStates_append, lkStates_eq_flatMap (bandUntwist v)]
    exact List.mem_flatMap.2 ⟨_, hdbl, by rw [lkStates_bandUntwist]; simp⟩
  rw [sub_self] at htw
  exact List.mem_map.2 ⟨(bandEnd, 0), List.mem_filter.2 ⟨htw, by simp⟩, rfl⟩

end AJConjecture
