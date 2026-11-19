import Mathlib
import AJHandoff.TorusKnot.PairKWhDBand
import AJHandoff.TorusKnot.PairKWhDClosure

/-!
# The band over a closed braid has a unique labelling (crux)

`bandLinkings_whBand_braidLongDiagram`: for a closed braid `K` with one component, cut open, the
band `whBand (braidLongDiagram K)` has exactly one labelling with both edges running upward from
the bottom to the top (no closed components, the left edge ends on the left), and in it the
linking number of the two edges is `0`. With `zero_mem_bandLinkings_whBand` this is the
statement "the band is untwisted" without any choice of labelling.

Route (as `orientWrithes_braidLongDiagram`, with pairs of labels): `morseDouble` of the long
closure is the doubled cups, `morseOfBraid (cable 2 K.word)` (`morseDouble_morseOfBraid`) and the
doubled caps. From `bandEnd` the doubled cups give the states whose labels are, pair by pair, a
free label `π_j ∈ (Bool × Bool)²` on the left half and its mirror (reversed pair, directions
flipped) on the right half; the cable braid permutes the pairs by the strand permutation of
`K.word` (keeping the order inside a pair) and adds the inter-component signs; the doubled caps
keep a state iff the pair labels are invariant under the permutation; by `K.connected` every pair
equals the first pair `bandEnd`, a single state, whose sum is `2 · writhe K.word` (two
inter-component crossings of the sign of the letter per letter); `lkStates_bandUntwist` removes it.
-/

namespace AJConjecture

/-- The labels of the strands in a list of pairs of strands, pair by pair. -/
private def bandFlat (P : List ((Bool × Bool) × (Bool × Bool))) : List (Bool × Bool) :=
  P.flatMap fun p ↦ [p.1, p.2]

/-- The label of the other leg of a cup or cap: opposite direction, same component. -/
private def bandFlip (a : Bool × Bool) : Bool × Bool := (!a.1, a.2)

/-- The pair of labels of the band ends. -/
private def bandPair : (Bool × Bool) × (Bool × Bool) := ((true, false), (true, true))

/-- The pairs of labels inserted by a doubled cup, in the order of `lkLetter`. -/
private def bandCupPairs : List ((Bool × Bool) × (Bool × Bool)) :=
  let l : List (Bool × Bool) := [true, false].flatMap fun d ↦ [false, true].map fun c ↦ (d, c)
  l.flatMap fun p ↦ l.map fun q ↦ (p, q)

/-- The lists of pair labels produced by the doubled cups of a long closure, in their order. -/
private def bandCupSeqs : ℕ → List (List ((Bool × Bool) × (Bool × Bool)))
  | 0 => [[]]
  | k + 1 => (bandCupSeqs k).flatMap fun P ↦ bandCupPairs.map fun pq ↦ P ++ [pq]

/-- Exchange the entries at `i`, `i + 1` of a list. -/
private def bandSwapAt {β : Type} (i : ℕ) (a : List β) : List β :=
  match a.drop i with
  | p :: q :: b => a.take i ++ q :: p :: b
  | _ => a

/-- The entries of a list after a braid word. -/
private def bandBraidLabels {β : Type} : BraidWord → List β → List β
  | [], a => a
  | g :: w, a => bandBraidLabels w (bandSwapAt g.1 a)

/-- The sign contributed by a crossing of sign `s` of two labelled strands. -/
private def bandSign (s : Bool) (a b : Bool × Bool) : ℤ :=
  if a.2 = b.2 then 0 else orientSign s a.1 b.1

/-- The signs contributed by a doubled crossing of the pairs `p`, `q`. -/
private def bandCrossSum (s : Bool) (p q : (Bool × Bool) × (Bool × Bool)) : ℤ :=
  bandSign s p.2 q.1 + bandSign s p.2 q.2 + bandSign s p.1 q.1 + bandSign s p.1 q.2

/-- The signs collected by the double of a braid word on pairs of labels. -/
private def bandBraidSum : BraidWord → List ((Bool × Bool) × (Bool × Bool)) → ℤ
  | [], _ => 0
  | g :: w, a =>
    (match a.drop g.1 with
      | p :: q :: _ => bandCrossSum g.2 p q
      | _ => 0) + bandBraidSum w (bandSwapAt g.1 a)

/-- Each pair gives two labels. -/
private theorem length_bandFlat (P : List ((Bool × Bool) × (Bool × Bool))) :
    (bandFlat P).length = 2 * P.length := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [bandFlat] at ih ⊢; omega

/-- The double of a concatenation. -/
private theorem morseDouble_append_band (u v : MorseWord) :
    morseDouble (u ++ v) = morseDouble u ++ morseDouble v :=
  List.flatMap_append

/-- A doubled cup at the end of a left part of `2n` labels: one state for every pair of
labels of its two left legs, the right legs carrying the flipped labels in mirror order. -/
private theorem lkStates_doubleCup_band (n : ℕ) (L M : List (Bool × Bool))
    (hL : L.length = 2 * n) (x : ℤ) :
    lkStates (morseDoubleLetter (.cup, n)) [(L ++ M, x)] =
      bandCupPairs.map fun pq ↦
        (L ++ pq.1 :: pq.2 :: bandFlip pq.2 :: bandFlip pq.1 :: M, x) := by
  have e : morseDoubleLetter (.cup, n) = morseShiftWord (2 * n) [(.cup, 0), (.cup, 1)] := by
    simp [morseDoubleLetter, morseShiftWord, shiftLetter]
    omega
  rw [e, show L ++ M = L ++ [] ++ M by simp, lkStates_frame 0 (2 * n) _ rfl L [] M hL rfl x]
  simp [lkStates, lkLetter, bandCupPairs, bandFlip]

/-- The produced lists of pairs have length `k`. -/
private theorem length_of_mem_bandCupSeqs :
    ∀ {k : ℕ} {P : List ((Bool × Bool) × (Bool × Bool))},
      P ∈ bandCupSeqs k → P.length = k
  | 0, P, h => by simp [bandCupSeqs] at h; simp [h]
  | k + 1, P, h => by
    simp only [bandCupSeqs, List.mem_flatMap, List.mem_map] at h
    obtain ⟨P', hP', pq, -, rfl⟩ := h
    simp [length_of_mem_bandCupSeqs hP']

/-- No list of pairs is produced twice. -/
private theorem nodup_bandCupSeqs : ∀ k : ℕ, (bandCupSeqs k).Nodup
  | 0 => by simp [bandCupSeqs]
  | k + 1 => by
    rw [bandCupSeqs, List.nodup_flatMap]
    refine ⟨fun P _ ↦ ?_, (nodup_bandCupSeqs k).imp fun {a b} hab ↦ ?_⟩
    · refine List.Nodup.map (fun x y h ↦ ?_) (by decide)
      simpa using h
    · intro x hxa hxb
      simp only [List.mem_map] at hxa hxb
      obtain ⟨p, -, rfl⟩ := hxa
      obtain ⟨q, -, h⟩ := hxb
      exact hab (List.append_inj' h rfl).1.symm

/-- The list of band-end pairs is produced. -/
private theorem replicate_mem_bandCupSeqs : ∀ k : ℕ, List.replicate k bandPair ∈ bandCupSeqs k
  | 0 => by simp [bandCupSeqs]
  | k + 1 => by
    rw [bandCupSeqs, List.mem_flatMap]
    exact ⟨_, replicate_mem_bandCupSeqs k, List.mem_map.2 ⟨bandPair, by decide,
      by simp [List.replicate_succ']⟩⟩

/-- The doubled cups of a long closure from the band end: one state for every list `P` of
pair labels of the left legs, the right legs carrying the flipped labels in mirror order. -/
private theorem lkStates_closureCups_band (k : ℕ) :
    lkStates (morseDouble ((List.range k).map fun j ↦ (MorseKind.cup, j + 1))) [(bandEnd, 0)] =
      (bandCupSeqs k).map fun P ↦
        (bandFlat (bandPair :: P) ++ ((bandFlat P).map bandFlip).reverse, 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, morseDouble_append_band, lkStates_append, ih,
      List.map_singleton, lkStates_eq_flatMap, List.flatMap_map, bandCupSeqs, List.map_flatMap]
    refine List.flatMap_congr fun P hP ↦ ?_
    have hl := length_of_mem_bandCupSeqs hP
    rw [show morseDouble [(MorseKind.cup, k + 1)] = morseDoubleLetter (.cup, k + 1) by
      simp [morseDouble], lkStates_doubleCup_band (k + 1) _ _ (by simp [length_bandFlat, hl])]
    simp [bandFlat]

/-- A cap joins `a` to the flip of `b` iff `a = b`. -/
private theorem bandFlip_cap_iff (a b : Bool × Bool) :
    (a.1 ≠ (bandFlip b).1 ∧ a.2 = (bandFlip b).2) ↔ a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  cases a1 <;> cases b1 <;> simp [bandFlip]

/-- A doubled cap on the pair `y` and the flipped mirror of the pair `z` closes iff `y = z`. -/
private theorem lkStates_doubleCapWindow_band (y z : (Bool × Bool) × (Bool × Bool)) (x : ℤ) :
    lkStates [(.cap, 1), (.cap, 0)] [([y.1, y.2, bandFlip z.2, bandFlip z.1], x)] =
      if y = z then [([], x)] else [] := by
  have h2 := bandFlip_cap_iff y.2 z.2
  have h1 := bandFlip_cap_iff y.1 z.1
  by_cases e : y = z
  · simp only [lkStates, lkLetter, List.drop, List.take, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ite_eq_left (h2.2 (e ▸ rfl)), List.cons_append, List.nil_append,
      ite_eq_left (h1.2 (e ▸ rfl)), ite_eq_left e]
  · simp only [lkStates, lkLetter, List.drop, List.take, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ite_eq_right e]
    by_cases e2 : y.2 = z.2
    · have e1 : y.1 ≠ z.1 := fun h ↦ e (Prod.ext h e2)
      simp only [ite_eq_left (h2.2 e2), lkLetter, List.drop, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.cons_append, List.nil_append, ite_eq_right (mt h1.1 e1)]
    · simp only [ite_eq_right (mt h2.1 e2), List.flatMap_nil]

/-- The double of a word beginning with a letter. -/
private theorem morseDouble_cons_band (l : MorseLetter) (w : MorseWord) :
    morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w :=
  List.flatMap_cons

/-- No input state, no output state. -/
private theorem lkStates_nil_band (w : MorseWord) : lkStates w [] = [] := by
  rw [lkStates_eq_flatMap, List.flatMap_nil]

/-- The doubled caps of a long closure keep a state iff the left pairs equal the pairs of the
left legs, and leave the first pair. -/
private theorem lkStates_closureCaps_band : ∀ (k : ℕ) (c : (Bool × Bool) × (Bool × Bool))
    (T O : List ((Bool × Bool) × (Bool × Bool))), T.length = k → O.length = k → ∀ x : ℤ,
    lkStates (morseDouble ((List.range k).reverse.map fun j ↦ (MorseKind.cap, j + 1)))
      [(bandFlat (c :: T) ++ ((bandFlat O).map bandFlip).reverse, x)] =
      if T = O then [(bandFlat [c], x)] else []
  | 0, c, T, O, hT, hO, x => by
    rw [List.length_eq_zero_iff] at hT hO
    subst hT hO
    simp [bandFlat, morseDouble, lkStates]
  | k + 1, c, T, O, hT, hO, x => by
    have hsnoc : ∀ u : List ((Bool × Bool) × (Bool × Bool)), u.length = k + 1 →
        ∃ u' y, u = u' ++ [y] ∧ u'.length = k := by
      intro u hu
      have hne : u ≠ [] := by rintro rfl; simp at hu
      refine ⟨u.dropLast, u.getLast hne, (List.dropLast_append_getLast hne).symm, ?_⟩
      simp [hu]
    obtain ⟨T', y, rfl, hT'⟩ := hsnoc T hT
    obtain ⟨O', z, rfl, hO'⟩ := hsnoc O hO
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, morseDouble_cons_band, lkStates_append]
    have hL : bandFlat (c :: (T' ++ [y])) ++ ((bandFlat (O' ++ [z])).map bandFlip).reverse =
        bandFlat (c :: T') ++ [y.1, y.2, bandFlip z.2, bandFlip z.1] ++
          ((bandFlat O').map bandFlip).reverse := by
      simp [bandFlat]
    have e : morseDoubleLetter (.cap, k + 1) =
        morseShiftWord (2 * (k + 1)) [(.cap, 1), (.cap, 0)] := by
      simp [morseDoubleLetter, morseShiftWord, shiftLetter]
      omega
    rw [hL, e, lkStates_frame 4 (2 * (k + 1)) _ rfl _ _ _
      (by simp [length_bandFlat, hT']) rfl x, lkStates_doubleCapWindow_band]
    by_cases hyz : y = z
    · subst hyz
      simp only [ite_true, List.map_singleton, List.append_nil]
      rw [lkStates_closureCaps_band k c T' O' hT' hO' x]
      simp
    · simp only [hyz, ite_false, List.map_nil, lkStates_nil_band]
      split_ifs with h
      · exact absurd (List.append_inj' h rfl).2 (by simpa using hyz)
      · rfl

/-- A doubled crossing at `0` exchanges two pairs of labels and adds their signs. -/
private theorem lkStates_doubleCrossWindow_band (s : Bool) (p q : (Bool × Bool) × (Bool × Bool))
    (x : ℤ) :
    lkStates (morseDoubleLetter (.cross s, 0)) [([p.1, p.2, q.1, q.2], x)] =
      [([q.1, q.2, p.1, p.2], x + bandCrossSum s p q)] := by
  cases s <;>
    simp [morseDoubleLetter, cable, cableGen, morseOfBraid, lkStates, lkLetter, bandCrossSum,
      bandSign, List.range_succ] <;> ring

/-- A doubled crossing at `i` is the doubled crossing at `0`, shifted by `2i`. -/
private theorem morseDoubleLetter_cross_shift_band (s : Bool) (i : ℕ) :
    morseDoubleLetter (.cross s, i) =
      morseShiftWord (2 * i) (morseDoubleLetter (.cross s, 0)) := by
  cases s <;> simp [morseDoubleLetter, cable, cableGen, morseOfBraid, morseShiftWord,
    shiftLetter, List.range_succ] <;> omega

/-- Exchanging two entries keeps the length. -/
private theorem length_bandSwapAt {β : Type} (i : ℕ) (a : List β) :
    (bandSwapAt i a).length = a.length := by
  unfold bandSwapAt
  split
  · next p q b h =>
    have := congrArg List.length h
    simp at this ⊢
    omega
  · rfl

/-- A braid word keeps the number of entries. -/
private theorem length_bandBraidLabels {β : Type} (w : BraidWord) (a : List β) :
    (bandBraidLabels w a).length = a.length := by
  induction w generalizing a with
  | nil => rfl
  | cons g w ih => rw [bandBraidLabels, ih, length_bandSwapAt]

/-- The double of a braid word on `m` strands acts deterministically on the first `m` pairs of
labels. -/
private theorem lkStates_morseDoubleBraid_band (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w)
    (A : List ((Bool × Bool) × (Bool × Bool))) (R : List (Bool × Bool)) (hA : A.length = m)
    (x : ℤ) :
    lkStates (morseDouble (morseOfBraid w)) [(bandFlat A ++ R, x)] =
      [(bandFlat (bandBraidLabels w A) ++ R, x + bandBraidSum w A)] := by
  induction w generalizing A x with
  | nil => simp [morseOfBraid, morseDouble, lkStates, bandBraidLabels, bandBraidSum]
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    obtain ⟨p, q, b, hb⟩ : ∃ p q b, A.drop g.1 = p :: q :: b := by
      rcases h : A.drop g.1 with _ | ⟨p, _ | ⟨q, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨p, q, b, rfl⟩
    have hs : bandSwapAt g.1 A = A.take g.1 ++ q :: p :: b := by simp [bandSwapAt, hb]
    have hA' : bandFlat A ++ R =
        bandFlat (A.take g.1) ++ [p.1, p.2, q.1, q.2] ++ (bandFlat b ++ R) := by
      conv_lhs => rw [← List.take_append_drop g.1 A, hb]
      simp [bandFlat]
    have hS : bandFlat (A.take g.1) ++ [q.1, q.2, p.1, p.2] ++ (bandFlat b ++ R) =
        bandFlat (bandSwapAt g.1 A) ++ R := by
      rw [hs]
      simp [bandFlat]
    rw [show morseOfBraid (g :: w) = (.cross g.2, g.1) :: morseOfBraid w from rfl,
      morseDouble_cons_band, lkStates_append, hA', morseDoubleLetter_cross_shift_band,
      lkStates_frame 4 (2 * g.1) _ (by cases g.2 <;> rfl) _ _ _
        (by simp [length_bandFlat]; omega) rfl x,
      lkStates_doubleCrossWindow_band, List.map_singleton]
    dsimp only
    rw [hS, ih (fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg')) _
      (by rw [length_bandSwapAt, hA])]
    simp only [bandBraidLabels, bandBraidSum, hb]
    ring_nf

/-- Exchanging two entries commutes with a map to directions. -/
private theorem swapAt_map_band {β : Type} (i : ℕ) (L : List β) (φ : β → Bool) :
    swapAt i (L.map φ) = (bandSwapAt i L).map φ := by
  unfold swapAt bandSwapAt
  rw [← List.map_drop]
  rcases h : L.drop i with _ | ⟨p, _ | ⟨q, b⟩⟩ <;> simp [List.map_take]

/-- A braid word commutes with a map to directions. -/
private theorem braidLabels_map_band {β : Type} (w : BraidWord) (L : List β) (φ : β → Bool) :
    braidLabels w (L.map φ) = (bandBraidLabels w L).map φ := by
  induction w generalizing L with
  | nil => rfl
  | cons g w ih => rw [braidLabels, bandBraidLabels, swapAt_map_band, ih]

/-- Exchanging two equal entries does nothing. -/
private theorem bandSwapAt_replicate {β : Type} (i m : ℕ) (x : β) :
    bandSwapAt i (List.replicate m x) = List.replicate m x := by
  unfold bandSwapAt
  rw [List.drop_replicate]
  rcases h : m - i with _ | _ | t
  · rfl
  · rfl
  · obtain rfl : m = i + (t + 2) := by omega
    simp [List.replicate_add, List.replicate_succ]

/-- A braid word fixes a constant list. -/
private theorem bandBraidLabels_replicate {β : Type} (w : BraidWord) (m : ℕ) (x : β) :
    bandBraidLabels w (List.replicate m x) = List.replicate m x := by
  induction w with
  | nil => rfl
  | cons g w ih => rw [bandBraidLabels, bandSwapAt_replicate, ih]

/-- On band-end pairs everywhere, the double of a braid word collects twice its writhe. -/
private theorem bandBraidSum_replicate (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) :
    bandBraidSum w (List.replicate m bandPair) = 2 * writhe w := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    have hd : (List.replicate m bandPair).drop g.1 =
        bandPair :: bandPair :: List.replicate (m - g.1 - 2) bandPair := by
      rw [List.drop_replicate]
      obtain ⟨t, ht⟩ : ∃ t, m - g.1 = t + 2 := ⟨m - g.1 - 2, by omega⟩
      rw [ht]
      simp [List.replicate_succ]
    rw [bandBraidSum, bandSwapAt_replicate, hd,
      ih (fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg'))]
    cases h : g.2 <;> simp [h, writhe, bandCrossSum, bandSign, bandPair, orientSign] <;> ring

/-- For a closed braid with one component, the braid fixes the pairs `bandPair :: P` only if
they are all `bandPair`. -/
private theorem bandBraidLabels_fixed (K : BraidKnot) (k : ℕ) (hk : K.strands = k + 1)
    (P : List ((Bool × Bool) × (Bool × Bool))) (hP : P.length = k)
    (h : bandBraidLabels K.word (bandPair :: P) = bandPair :: P) :
    P = List.replicate k bandPair := by
  set φ : (Bool × Bool) × (Bool × Bool) → Bool := fun x ↦ decide (x = bandPair) with hφ
  have h1 : braidLabels K.word (true :: P.map φ) = true :: P.map φ := by
    have := braidLabels_map_band K.word (bandPair :: P) φ
    rw [h] at this
    simpa [φ] using this
  have h2 := (braidLabels_fixed_iff K k hk (P.map φ) (by simp [hP])).1 h1
  rw [List.eq_replicate_iff]
  refine ⟨hP, fun x hx ↦ ?_⟩
  have : φ x ∈ P.map φ := List.mem_map_of_mem hx
  rw [h2] at this
  simpa [φ] using List.eq_of_mem_replicate this

/-- The correction twists keep the labels of two strands. -/
private theorem lkStates_bandUntwist_labels (w : ℤ) (u v : Bool × Bool) (y : ℤ) :
    ∃ y', lkStates (bandUntwist w) [([u, v], y)] = [([u, v], y')] := by
  have hrep : ∀ (s : Bool) (n : ℕ) (y : ℤ),
      ∃ y', lkStates (List.replicate (2 * n) (.cross s, 0)) [([u, v], y)] = [([u, v], y')] := by
    intro s n
    induction n with
    | zero => intro y; exact ⟨y, rfl⟩
    | succ n ih =>
      intro y
      rw [show 2 * (n + 1) = 2 + 2 * n by ring, List.replicate_add, lkStates_append]
      simp only [List.replicate, lkStates, lkLetter, List.drop, List.take, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append]
      exact ih _
  unfold bandUntwist
  split_ifs
  · exact hrep _ _ y
  · exact hrep _ _ y

/-- A `flatMap` selecting one list of pairs. -/
private theorem flatMap_ite_eq_filter_band (x : List ((Bool × Bool) × (Bool × Bool))) (v : ℤ)
    (l : List (List ((Bool × Bool) × (Bool × Bool)))) :
    (l.flatMap fun o ↦ if o = x then [v] else []) = (l.filter (· = x)).map fun _ ↦ v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = x
    · simp [h, ih]
    · simp [h, ih]

/-- A `flatMap` selecting one list of pairs that occurs exactly once. -/
private theorem flatMap_ite_singleton_band {l : List (List ((Bool × Bool) × (Bool × Bool)))}
    {x : List ((Bool × Bool) × (Bool × Bool))} (v : ℤ) (hl : l.Nodup) (hx : x ∈ l) :
    (l.flatMap fun o ↦ if o = x then [v] else []) = [v] := by
  rw [flatMap_ite_eq_filter_band, List.filter_eq, List.count_eq_one_of_mem hl hx]
  rfl

/-- **The band over a closed braid is untwisted, with its unique labelling.** -/
theorem bandLinkings_whBand_braidLongDiagram (K : BraidKnot) :
    bandLinkings (whBand (braidLongDiagram K)) = [0] := by
  obtain ⟨k, hk⟩ : ∃ k, K.strands = k + 1 :=
    ⟨K.strands - 1, by have := K.strands_pos; omega⟩
  have hk1 : K.strands - 1 = k := by omega
  rw [bandLinkings, whBand, morseWrithe_braidLongDiagram, lkStates_append]
  simp only [braidLongDiagram, morseLongClosure, hk1]
  rw [morseDouble_append_band, morseDouble_append_band, lkStates_append, lkStates_append,
    lkStates_closureCups_band, lkStates_eq_flatMap (morseDouble (morseOfBraid _)),
    List.flatMap_map, lkStates_eq_flatMap (morseDouble _), List.flatMap_assoc,
    lkStates_eq_flatMap (bandUntwist _), List.flatMap_assoc, List.filter_flatMap,
    List.map_flatMap]
  rw [List.flatMap_congr (g := fun P ↦ if P = List.replicate k bandPair then [0] else [])]
  · exact flatMap_ite_singleton_band _ (nodup_bandCupSeqs k) (replicate_mem_bandCupSeqs k)
  intro P hP
  have hPl := length_of_mem_bandCupSeqs hP
  have hlen : (bandPair :: P).length = K.strands := by simp [hPl, hk]
  rw [lkStates_morseDoubleBraid_band K.strands K.word K.isOnStrands _ _ hlen,
    List.flatMap_singleton]
  have hbl : (bandBraidLabels K.word (bandPair :: P)).length = k + 1 := by
    rw [length_bandBraidLabels, hlen, hk]
  obtain ⟨c, T, hct⟩ : ∃ c T, bandBraidLabels K.word (bandPair :: P) = c :: T := by
    rcases h : bandBraidLabels K.word (bandPair :: P) with _ | ⟨c, T⟩
    · rw [h] at hbl; simp at hbl
    · exact ⟨c, T, rfl⟩
  have hT : T.length = k := by rw [hct] at hbl; simpa using hbl
  rw [hct, lkStates_closureCaps_band k c T P hT hPl]
  by_cases hfix : bandBraidLabels K.word (bandPair :: P) = bandPair :: P
  · have hrep := bandBraidLabels_fixed K k hk P hPl hfix
    have hsum : bandBraidSum K.word (bandPair :: P) = 2 * writhe K.word := by
      rw [hrep, ← List.replicate_succ, ← hk]
      exact bandBraidSum_replicate K.strands K.word K.isOnStrands
    rw [hct] at hfix
    obtain ⟨rfl, rfl⟩ := List.cons.inj hfix
    rw [ite_eq_left rfl, hsum, List.flatMap_singleton, show bandFlat [bandPair] = bandEnd from rfl,
      lkStates_bandUntwist]
    simp [hrep]
  · have hne : P ≠ List.replicate k bandPair := by
      rintro rfl
      exact hfix (by rw [← List.replicate_succ, bandBraidLabels_replicate])
    rw [ite_eq_right hne]
    split_ifs with hTP
    · have hc : c ≠ bandPair := by
        rintro rfl
        exact hfix (by rw [hct, hTP])
      obtain ⟨y', hy'⟩ := lkStates_bandUntwist_labels (writhe K.word) c.1 c.2
        (0 + bandBraidSum K.word (bandPair :: P))
      rw [List.flatMap_singleton, show bandFlat [c] = [c.1, c.2] from rfl, hy']
      have : [c.1, c.2] ≠ bandEnd := fun h ↦ hc (by
        simp only [bandEnd, List.cons.injEq, and_true] at h
        exact Prod.ext h.1 h.2)
      simp [this]
    · simp

end AJConjecture
