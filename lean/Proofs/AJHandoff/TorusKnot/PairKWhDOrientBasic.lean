import Mathlib
import AJHandoff.TorusKnot.PairKWhDDefs
import AJFamily.Skein.MorsePhaseTools

/-!
# Oriented states: composition, order, offsets and frames

Structural facts about `orientStates` used by the invariance proof:

* `orientStates_append`, `orientStates_append_states`, `orientStates_eq_flatMap`: a word acts
  letter by letter and state by state;
* `orientStates_perm`: it respects reordering of the input states;
* `orientStates_add`: the writhe already accumulated is carried along;
* `orientStates_length`: on a fitting word, the output directions have `morseOut` entries;
* `orientStates_frame`: a fitting word shifted by `d` acts on the middle part of a longer label
  list and leaves `d` labels on the left and any labels on the right untouched.
-/

namespace AJConjecture

/-- A concatenation acts as its first part followed by its second part. -/
theorem orientStates_append (u v : MorseWord) (S : List (List Bool × ℤ)) :
    orientStates (u ++ v) S = orientStates v (orientStates u S) := by
  induction u generalizing S with
  | nil => rfl
  | cons l u ih => exact ih _

/-- A word acts on a concatenation of state lists part by part. -/
theorem orientStates_append_states (w : MorseWord) (S T : List (List Bool × ℤ)) :
    orientStates w (S ++ T) = orientStates w S ++ orientStates w T := by
  induction w generalizing S T with
  | nil => rfl
  | cons l w ih =>
    simp only [orientStates, List.flatMap_append]
    exact ih _ _

/-- A word acts state by state. -/
theorem orientStates_eq_flatMap (w : MorseWord) (S : List (List Bool × ℤ)) :
    orientStates w S = S.flatMap fun st ↦ orientStates w [st] := by
  induction S with
  | nil =>
    induction w with
    | nil => rfl
    | cons l w ih => simpa [orientStates] using ih
  | cons st S ih =>
    rw [List.flatMap_cons, ← ih, ← orientStates_append_states]
    rfl

/-- Reordering the input states reorders the output states. -/
theorem orientStates_perm (w : MorseWord) {S T : List (List Bool × ℤ)} (h : S.Perm T) :
    (orientStates w S).Perm (orientStates w T) := by
  rw [orientStates_eq_flatMap w S, orientStates_eq_flatMap w T]
  exact h.flatMap_right _

/-- One letter carries the accumulated writhe. -/
theorem orientLetter_add (l : MorseLetter) (a : List Bool) (y x : ℤ) :
    orientLetter l (a, y + x) = (orientLetter l (a, y)).map fun st ↦ (st.1, st.2 + x) := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup => simp only [orientLetter]; split_ifs <;> simp
  | cap =>
    simp only [orientLetter]
    rcases a.drop i with _ | ⟨p, _ | ⟨q, b⟩⟩ <;> simp only [List.map_nil]
    split_ifs <;> simp
  | cross s =>
    simp only [orientLetter]
    rcases a.drop i with _ | ⟨p, _ | ⟨q, b⟩⟩ <;> simp only [List.map_nil]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    ring

/-- A word carries an accumulated writhe through all its states. -/
private theorem orientStates_map_add (w : MorseWord) (S : List (List Bool × ℤ)) (x : ℤ) :
    orientStates w (S.map fun st ↦ (st.1, st.2 + x)) =
      (orientStates w S).map fun st ↦ (st.1, st.2 + x) := by
  induction w generalizing S with
  | nil => rfl
  | cons l w ih =>
    simp only [orientStates]
    rw [← ih]
    congr 1
    rw [List.flatMap_map, List.map_flatMap]
    exact List.flatMap_congr fun st _ ↦ orientLetter_add l st.1 st.2 x

/-- The writhe accumulated before a word is carried through it. -/
theorem orientStates_add (w : MorseWord) (a : List Bool) (x : ℤ) :
    orientStates w [(a, x)] = (orientStates w [(a, 0)]).map fun st ↦ (st.1, st.2 + x) := by
  rw [← orientStates_map_add]
  simp

/-- A fitting letter maps `n` directions to `morseLetterOut n l` directions. -/
theorem orientLetter_length (n : ℕ) (l : MorseLetter) (hl : l.2 + morseKindIn l.1 ≤ n)
    (st : List Bool × ℤ) (hst : st.1.length = n) :
    ∀ st' ∈ orientLetter l st, st'.1.length = morseLetterOut n l := by
  obtain ⟨a, x⟩ := st
  obtain ⟨k, i⟩ := l
  simp only at hst
  cases k with
  | cup =>
    simp only [morseKindIn] at hl
    intro st' h
    simp only [orientLetter] at h
    rw [ite_eq_left (by omega)] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;>
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
    simp only [orientLetter, hb] at h
    split_ifs at h
    · simp at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp [morseLetterOut, morseKindOut, morseKindIn]
      omega
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
    simp only [orientLetter, hb, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp [morseLetterOut, morseKindOut, morseKindIn]
    omega

/-- On a fitting word, every output state has `morseOut n w` directions. -/
theorem orientStates_length (n : ℕ) (w : MorseWord) (hw : morseFits n w = true)
    (S : List (List Bool × ℤ)) (hS : ∀ st ∈ S, st.1.length = n) :
    ∀ st ∈ orientStates w S, st.1.length = morseOut n w := by
  induction w generalizing n S with
  | nil => exact hS
  | cons l w ih =>
    rw [morseFits_cons] at hw
    refine ih _ hw.2 _ fun st' h ↦ ?_
    obtain ⟨st, hst, h⟩ := List.mem_flatMap.1 h
    exact orientLetter_length n l hw.1 st (hS st hst) st' h

/-- The frame of a letter. -/
theorem orientLetter_frame (m : ℕ) (l : MorseLetter) (hl : l.2 + morseKindIn l.1 ≤ m)
    (p a q : List Bool) (ha : a.length = m) (x : ℤ) :
    orientLetter (shiftLetter p.length l) (p ++ a ++ q, x) =
      (orientLetter l (a, x)).map fun st ↦ (p ++ st.1 ++ q, st.2) := by
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
    simp only [orientLetter, List.length_append]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), htake i (by omega), hdrop i (by omega)]
    simp
  | cap =>
    simp only [morseKindIn] at hl
    obtain ⟨u, v, b, hb⟩ : ∃ u v b, a.drop i = u :: v :: b := by
      rcases h : a.drop i with _ | ⟨u, _ | ⟨v, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨u, v, b, rfl⟩
    simp only [orientLetter, hdrop i (by omega), hb, htake i (by omega), List.cons_append]
    split_ifs <;> simp
  | cross s =>
    simp only [morseKindIn] at hl
    obtain ⟨u, v, b, hb⟩ : ∃ u v b, a.drop i = u :: v :: b := by
      rcases h : a.drop i with _ | ⟨u, _ | ⟨v, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨u, v, b, rfl⟩
    simp only [orientLetter, hdrop i (by omega), hb, htake i (by omega), List.cons_append]
    simp

/-- The frame of a word, on a list of states. -/
private theorem orientStates_frame_list (m : ℕ) (w : MorseWord) (hw : morseFits m w = true)
    (p q : List Bool) (S : List (List Bool × ℤ)) (hS : ∀ st ∈ S, st.1.length = m) :
    orientStates (morseShiftWord p.length w) (S.map fun st ↦ (p ++ st.1 ++ q, st.2)) =
      (orientStates w S).map fun st ↦ (p ++ st.1 ++ q, st.2) := by
  induction w generalizing m S with
  | nil => rfl
  | cons l w ih =>
    rw [morseFits_cons] at hw
    simp only [morseShiftWord, List.map_cons, orientStates] at ih ⊢
    rw [List.flatMap_map]
    rw [List.flatMap_congr (g := fun st ↦ (orientLetter l st).map
      fun st ↦ (p ++ st.1 ++ q, st.2)) fun st hst ↦
        orientLetter_frame m l hw.1 p st.1 q (hS st hst) st.2]
    rw [← List.map_flatMap]
    refine ih _ hw.2 _ fun st' h ↦ ?_
    obtain ⟨st, hst, h⟩ := List.mem_flatMap.1 h
    exact orientLetter_length m l hw.1 st (hS st hst) st' h

/-- The frame of a word: shifted by `d`, a word fitting on `m` strands acts on the `m` labels
after the first `d` and leaves the others untouched. -/
theorem orientStates_frame (m d : ℕ) (w : MorseWord) (hw : morseFits m w = true)
    (p a q : List Bool) (hp : p.length = d) (ha : a.length = m) (x : ℤ) :
    orientStates (morseShiftWord d w) [(p ++ a ++ q, x)] =
      (orientStates w [(a, x)]).map fun st ↦ (p ++ st.1 ++ q, st.2) := by
  subst hp
  have := orientStates_frame_list m w hw p q [(a, x)] (by simp [ha])
  simpa using this

end AJConjecture
