import Mathlib
import AJHandoff.TorusKnot.PairKWhDOrientBasic

/-!
# The orientation of a closed braid cut open (crux)

`orientWrithes_braidLongDiagram`: the long-knot diagram of a closed braid with one component has
exactly one orientation with both ends upward, all its braid strands point upward, and its
oriented writhe is the braid writhe `writhe K.word`. Consequences: `braidLongDiagram K` is a
long-knot diagram and its blackboard framing is `writhe K.word`.

Route (state by state, no global tracing):
1. the `m - 1` cups from `[true]` give exactly the states `(true :: o ++ (o.map not).reverse, 0)`,
   one for every `o : List Bool` of length `m - 1` (cup `j + 1` inserts `(b, !b)` after
   `true :: o`), in a fixed enumeration order;
2. the braid word acts on a state with `m` labels on the left deterministically: it permutes the
   `m` labels by the strand permutation (`strandPerm m w`, label at `j` after the braid = label at
   `(strandPerm m w)⁻¹ j` before, or the inverse convention — fix by `strandSwap`) and adds
   `Σ orientSign`, which is `writhe w` when all labels are `true`;
3. the caps at `m - 1, …, 1` keep a state iff the label at `j ≥ 1` after the braid equals the
   label `o_j` before it, and the output is `[label 0]`;
4. so a surviving state with output `[true]` has labels invariant under the strand permutation and
   `true` at `0`; by `K.connected` they are all `true`, i.e. `o` is all `true`; this `o` occurs
   once in the enumeration, and its writhe is `writhe K.word`.
-/

namespace AJConjecture

/-- The number of strands after a concatenation. -/
private theorem morseOut_append_cl (n : ℕ) (u v : MorseWord) :
    morseOut n (u ++ v) = morseOut (morseOut n u) v := by
  induction u generalizing n with
  | nil => rfl
  | cons l u ih => exact ih _

/-- A concatenation fits if both pieces fit in turn. -/
private theorem morseFits_append_cl {n : ℕ} {u v : MorseWord} (hu : morseFits n u = true)
    (hv : morseFits (morseOut n u) v = true) : morseFits n (u ++ v) = true := by
  induction u generalizing n with
  | nil => exact hv
  | cons l u ih =>
    simp only [morseFits, Bool.and_eq_true] at hu
    simp only [List.cons_append, morseFits, Bool.and_eq_true]
    exact ⟨hu.1, ih hu.2 hv⟩

/-- The cups of a long closure fit on `n ≥ 1` strands and add `2p` strands. -/
private theorem morseFits_cups_cl (p n : ℕ) (hn : 1 ≤ n) :
    morseFits n ((List.range p).map fun j ↦ (MorseKind.cup, j + 1)) = true ∧
      morseOut n ((List.range p).map fun j ↦ (MorseKind.cup, j + 1)) = n + 2 * p := by
  induction p with
  | zero => exact ⟨rfl, rfl⟩
  | succ p ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine ⟨morseFits_append_cl ih.1 ?_, ?_⟩
    · rw [ih.2]
      simp only [morseFits, morseKindIn, Bool.and_true]
      exact decide_eq_true (by omega)
    · rw [morseOut_append_cl, ih.2]
      simp only [morseOut, morseLetterOut, morseKindOut, morseKindIn]
      omega

/-- The caps of a long closure fit on `1 + 2p` strands and leave one strand. -/
private theorem morseFits_caps_cl (p : ℕ) :
    morseFits (1 + 2 * p) ((List.range p).reverse.map fun j ↦ (MorseKind.cap, j + 1)) = true ∧
      morseOut (1 + 2 * p) ((List.range p).reverse.map fun j ↦ (MorseKind.cap, j + 1)) = 1 := by
  induction p with
  | zero => exact ⟨rfl, rfl⟩
  | succ p ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons]
    have e : morseLetterOut (1 + 2 * (p + 1)) (MorseKind.cap, p + 1) = 1 + 2 * p := by
      simp only [morseLetterOut, morseKindOut, morseKindIn]
      omega
    refine ⟨?_, ?_⟩
    · simp only [morseFits, Bool.and_eq_true, e, ih.1, and_true, morseKindIn]
      exact decide_eq_true (by omega)
    · simp only [morseOut, e, ih.2]

/-- A braid word on `m ≤ n` strands fits on `n` strands and keeps their number. -/
private theorem morseFits_morseOfBraid_cl (n m : ℕ) (w : BraidWord) (hw : IsOnStrands m w)
    (hmn : m ≤ n) : morseFits n (morseOfBraid w) = true ∧ morseOut n (morseOfBraid w) = n := by
  induction w with
  | nil => exact ⟨rfl, rfl⟩
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg')
    have e : morseLetterOut n (MorseKind.cross g.2, g.1) = n := by
      simp only [morseLetterOut, morseKindOut, morseKindIn]
      omega
    refine ⟨?_, ?_⟩
    · change (decide (g.1 + morseKindIn (MorseKind.cross g.2) ≤ n) &&
        morseFits (morseLetterOut n (MorseKind.cross g.2, g.1)) (morseOfBraid w)) = true
      simp only [e, h1, Bool.and_true, morseKindIn]
      exact decide_eq_true (by omega)
    · change morseOut (morseLetterOut n (MorseKind.cross g.2, g.1)) (morseOfBraid w) = n
      rw [e, h2]

/-- The diagram of a closed braid cut open fits on one strand and ends on one strand. -/
theorem morseFits_braidLongDiagram (K : BraidKnot) :
    morseFits 1 (braidLongDiagram K) = true ∧ morseOut 1 (braidLongDiagram K) = 1 := by
  obtain ⟨hc1, hc2⟩ := morseFits_cups_cl (K.strands - 1) 1 le_rfl
  obtain ⟨hb1, hb2⟩ := morseFits_morseOfBraid_cl (1 + 2 * (K.strands - 1)) K.strands K.word
    K.isOnStrands (by have := K.strands_pos; omega)
  obtain ⟨hp1, hp2⟩ := morseFits_caps_cl (K.strands - 1)
  refine ⟨?_, ?_⟩
  · refine morseFits_append_cl (morseFits_append_cl hc1 ?_) ?_
    · rw [hc2]; exact hb1
    · rw [morseOut_append_cl, hc2, hb2]; exact hp1
  · rw [braidLongDiagram, morseLongClosure, morseOut_append_cl, morseOut_append_cl, hc2, hb2, hp2]

/-- The direction lists produced by the cups of a long closure, in their order. -/
def closureSeqs : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (closureSeqs k).flatMap fun o ↦ [o ++ [true], o ++ [false]]

/-- The produced lists have length `k`. -/
theorem length_of_mem_closureSeqs :
    ∀ {k : ℕ} {o : List Bool}, o ∈ closureSeqs k → o.length = k
  | 0, o, h => by simp [closureSeqs] at h; simp [h]
  | k + 1, o, h => by
    simp only [closureSeqs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨o', ho', rfl | rfl⟩ := h <;> simp [length_of_mem_closureSeqs ho']

/-- No list is produced twice. -/
theorem nodup_closureSeqs : ∀ k : ℕ, (closureSeqs k).Nodup
  | 0 => by simp [closureSeqs]
  | k + 1 => by
    rw [closureSeqs, List.nodup_flatMap]
    refine ⟨fun o _ ↦ by simp, (nodup_closureSeqs k).imp fun {a b} hab ↦ ?_⟩
    intro x hxa hxb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxa hxb
    rcases hxa with rfl | rfl <;> rcases hxb with h | h <;> exact hab (List.append_inj' h rfl).1

/-- The all-upward list is produced. -/
theorem replicate_mem_closureSeqs : ∀ k : ℕ, List.replicate k true ∈ closureSeqs k
  | 0 => by simp [closureSeqs]
  | k + 1 => by
    rw [closureSeqs, List.mem_flatMap]
    exact ⟨_, replicate_mem_closureSeqs k, by simp [List.replicate_succ']⟩

/-- No input state, no output state. -/
theorem orientStates_nil_states (w : MorseWord) : orientStates w [] = [] := by
  induction w with
  | nil => rfl
  | cons l w ih => simpa [orientStates] using ih

/-- The cups of a long closure from one upward strand: one state for every list `o` of
directions of the left legs, the right legs carrying the opposite directions in mirror order. -/
theorem orientStates_closureCups (k : ℕ) :
    orientStates ((List.range k).map fun j ↦ (MorseKind.cup, j + 1)) [([true], 0)] =
      (closureSeqs k).map fun o ↦ (true :: o ++ (o.map not).reverse, 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, orientStates_append, ih, List.map_singleton]
    simp only [orientStates, closureSeqs, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun o ho ↦ ?_
    have hl := length_of_mem_closureSeqs ho
    simp only [orientLetter, List.length_cons, List.length_append, List.length_reverse,
      List.length_map, hl]
    rw [ite_eq_left (by omega)]
    have ht : (true :: (o ++ (o.map not).reverse)).take (k + 1) = true :: o := by
      rw [List.take_succ_cons, List.take_append_of_le_length (by omega), List.take_of_length_le
        (by omega)]
    have hd : (true :: (o ++ (o.map not).reverse)).drop (k + 1) = (o.map not).reverse := by
      rw [List.drop_succ_cons, List.drop_append_of_le_length (by omega),
        List.drop_of_length_le (by omega), List.nil_append]
    rw [List.cons_append] at *
    rw [ht, hd]
    simp

/-- Exchange the labels at `i`, `i + 1`. -/
def swapAt (i : ℕ) (a : List Bool) : List Bool :=
  match a.drop i with
  | p :: q :: b => a.take i ++ q :: p :: b
  | _ => a

/-- The labels after a braid word. -/
def braidLabels : BraidWord → List Bool → List Bool
  | [], a => a
  | g :: w, a => braidLabels w (swapAt g.1 a)

/-- The oriented writhe collected by a braid word. -/
def braidWr : BraidWord → List Bool → ℤ
  | [], _ => 0
  | g :: w, a =>
    (match a.drop g.1 with
      | p :: q :: _ => orientSign g.2 p q
      | _ => 0) + braidWr w (swapAt g.1 a)

/-- Exchanging two labels keeps the length. -/
theorem length_swapAt (i : ℕ) (a : List Bool) : (swapAt i a).length = a.length := by
  unfold swapAt
  split
  · next p q b h =>
    have := congrArg List.length h
    simp at this ⊢
    omega
  · rfl

/-- A braid word acts deterministically on the first `m` labels. -/
theorem orientStates_morseOfBraid (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w)
    (a R : List Bool) (ha : a.length = m) (x : ℤ) :
    orientStates (morseOfBraid w) [(a ++ R, x)] = [(braidLabels w a ++ R, x + braidWr w a)] := by
  induction w generalizing a x with
  | nil => simp [morseOfBraid, orientStates, braidLabels, braidWr]
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    obtain ⟨p, q, b, hb⟩ : ∃ p q b, a.drop g.1 = p :: q :: b := by
      rcases h : a.drop g.1 with _ | ⟨p, _ | ⟨q, b⟩⟩
      · have := congrArg List.length h; simp at this; omega
      · have := congrArg List.length h; simp at this; omega
      · exact ⟨p, q, b, rfl⟩
    have hs : swapAt g.1 a = a.take g.1 ++ q :: p :: b := by simp [swapAt, hb]
    have hdrop : (a ++ R).drop g.1 = p :: q :: (b ++ R) := by
      rw [List.drop_append_of_le_length (by omega), hb]; rfl
    have htake : (a ++ R).take g.1 = a.take g.1 := List.take_append_of_le_length (by omega)
    change orientStates (morseOfBraid w) (orientLetter (.cross g.2, g.1) (a ++ R, x) ++ []) = _
    simp only [orientLetter, hdrop, htake, List.append_nil]
    have := ih (fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg')) (swapAt g.1 a)
      (by rw [length_swapAt, ha]) (x + orientSign g.2 p q)
    rw [hs] at this
    simp only [List.append_assoc, List.cons_append] at this
    rw [this]
    simp [braidLabels, braidWr, hb, hs]
    ring

/-- The caps of a long closure keep a state iff each left label equals the direction of the
corresponding left leg, and leave the first label. -/
theorem orientStates_closureCaps : ∀ (k : ℕ) (c : Bool) (t o : List Bool),
    t.length = k → o.length = k → ∀ x : ℤ,
    orientStates ((List.range k).reverse.map fun j ↦ (MorseKind.cap, j + 1))
      [(c :: t ++ (o.map not).reverse, x)] = if t = o then [([c], x)] else []
  | 0, c, t, o, ht, ho, x => by
    rw [List.length_eq_zero_iff] at ht ho
    subst ht ho
    rfl
  | k + 1, c, t, o, ht, ho, x => by
    have hsnoc : ∀ u : List Bool, u.length = k + 1 →
        ∃ u' y, u = u' ++ [y] ∧ u'.length = k := by
      intro u hu
      have hne : u ≠ [] := by rintro rfl; simp at hu
      refine ⟨u.dropLast, u.getLast hne, (List.dropLast_append_getLast hne).symm, ?_⟩
      simp [hu]
    obtain ⟨t', y, rfl, ht'⟩ := hsnoc t ht
    obtain ⟨o', z, rfl, ho'⟩ := hsnoc o ho
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons]
    have hL : c :: (t' ++ [y]) ++ ((o' ++ [z]).map not).reverse =
        (c :: t') ++ (y :: (!z) :: (o'.map not).reverse) := by simp
    have hd : ((c :: t') ++ (y :: (!z) :: (o'.map not).reverse)).drop (k + 1) =
        y :: (!z) :: (o'.map not).reverse := by
      rw [List.drop_append_of_le_length (by simp [ht']), List.drop_of_length_le (by simp [ht']),
        List.nil_append]
    have htk : ((c :: t') ++ (y :: (!z) :: (o'.map not).reverse)).take (k + 1) = c :: t' := by
      rw [List.take_append_of_le_length (by simp [ht']), List.take_of_length_le (by simp [ht'])]
    change orientStates _ (orientLetter (.cap, k + 1) _ ++ []) = _
    rw [hL]
    simp only [orientLetter, hd, htk, List.append_nil]
    by_cases hyz : y = z
    · subst hyz
      simp only [Bool.eq_not_self, ↓reduceIte]
      rw [orientStates_closureCaps k c t' o' ht' ho' x]
      simp
    · have hy : y = !z := by cases y <;> cases z <;> simp_all
      simp only [hy, ↓reduceIte, orientStates_nil_states]
      split_ifs with h
      · exact absurd (List.append_inj' h rfl).2 (by simp)
      · rfl

/-- Exchanging two labels is precomposing with the transposition. -/
theorem swapAt_ofFn (m i : ℕ) (hi : i + 1 < m) (f : Fin m → Bool) :
    swapAt i (List.ofFn f) = List.ofFn (f ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩) := by
  have hd : (List.ofFn f).drop i =
      f ⟨i, by omega⟩ :: f ⟨i + 1, hi⟩ :: (List.ofFn f).drop (i + 2) := by
    apply List.ext_getElem
    · simp; omega
    · intro j h1 h2
      rcases j with _ | _ | j <;> simp [List.getElem_drop]
      congr 1
      simp only [Fin.mk.injEq]
      omega
  apply List.ext_getElem
  · rw [length_swapAt]; simp
  · intro j h1 h2
    simp only [List.length_ofFn] at h2
    simp only [swapAt, hd, List.getElem_ofFn, Function.comp_apply]
    have hmin : min i m = i := by omega
    rcases lt_trichotomy j i with hj | rfl | hj
    · rw [List.getElem_append_left (by simp; omega)]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega)]
      simp
    · rw [List.getElem_append_right (by simp)]
      simp [Equiv.swap_apply_left, hmin]
    · rw [List.getElem_append_right (by simp; omega)]
      rcases Nat.lt_or_ge j (i + 2) with hj2 | hj2
      · obtain rfl : j = i + 1 := by omega
        simp [Equiv.swap_apply_right, hmin]
      · rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega)
          (by simp [Fin.ext_iff]; omega)]
        obtain ⟨t, rfl⟩ : ∃ t, j = i + 2 + t := ⟨j - (i + 2), by omega⟩
        have : i + 2 + t - i = t + 2 := by omega
        simp [List.getElem_drop, hmin, this]

/-- A braid word permutes the labels by its strand permutation. -/
theorem braidLabels_ofFn (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) (f : Fin m → Bool) :
    braidLabels w (List.ofFn f) = List.ofFn (f ∘ strandPerm m w) := by
  induction w generalizing f with
  | nil => simp [braidLabels, strandPerm]
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    rw [braidLabels, swapAt_ofFn m g.1 hg, ih (fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg'))]
    congr 1
    funext j
    simp [strandPerm, strandSwap, hg]

/-- On all-upward labels a braid word collects its writhe. -/
theorem braidWr_replicate (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) :
    braidWr w (List.replicate m true) = writhe w := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    have hs : swapAt g.1 (List.replicate m true) = List.replicate m true := by
      have := swapAt_ofFn m g.1 hg (fun _ ↦ true)
      simpa using this
    have hd : (List.replicate m true).drop g.1 =
        true :: true :: List.replicate (m - g.1 - 2) true := by
      rw [List.drop_replicate]
      obtain ⟨t, ht⟩ : ∃ t, m - g.1 = t + 2 := ⟨m - g.1 - 2, by omega⟩
      rw [ht]
      simp [List.replicate_succ]
    rw [braidWr, hs, hd, ih (fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg'))]
    simp [writhe, orientSign]

/-- For a closed braid with one component, the braid fixes the labels `true :: o` iff they
are all upward. -/
theorem braidLabels_fixed_iff (K : BraidKnot) (k : ℕ) (hk : K.strands = k + 1) (o : List Bool)
    (ho : o.length = k) :
    braidLabels K.word (true :: o) = true :: o ↔ o = List.replicate k true := by
  have hlen : (true :: o).length = K.strands := by simp [ho, hk]
  set f : Fin K.strands → Bool := fun j ↦ (true :: o)[(j : ℕ)]'(by rw [hlen]; exact j.isLt)
    with hf
  have ha : true :: o = List.ofFn f := by
    apply List.ext_getElem (by simp [hlen]) fun j h1 h2 ↦ by simp [hf]
  constructor
  · intro h
    rw [ha, braidLabels_ofFn _ _ K.isOnStrands] at h
    have hfix : f ∘ strandPerm K.strands K.word = f := List.ofFn_injective h
    have hpow : ∀ n : ℕ, ∀ j, f ((strandPerm K.strands K.word ^ n) j) = f j := by
      intro n
      induction n with
      | zero => intro j; simp
      | succ n ih =>
        intro j
        rw [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply, ih]
        exact congrFun hfix j
    have h0 : (0 : ℕ) < K.strands := K.strands_pos
    have hall : ∀ j, f j = true := by
      intro j
      obtain ⟨n, hn⟩ := K.connected ⟨0, h0⟩ j
      rw [← hn, hpow]
      simp [hf]
    have : true :: o = List.replicate (k + 1) true := by
      rw [ha, List.eq_replicate_iff]
      refine ⟨by simp [hk], fun b hb ↦ ?_⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      exact hall j
    rw [List.replicate_succ] at this
    exact List.cons_injective this
  · rintro rfl
    have := braidLabels_ofFn K.strands K.word K.isOnStrands (fun _ ↦ true)
    simp only [List.ofFn_const, Function.comp_def] at this
    rw [hk, List.replicate_succ] at this
    exact this

/-- A `flatMap` selecting one list. -/
private theorem flatMap_ite_eq_filter (x : List Bool) (v : ℤ) (l : List (List Bool)) :
    (l.flatMap fun o ↦ if o = x then [v] else []) = (l.filter (· = x)).map fun _ ↦ v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = x
    · simp [h, ih]
    · simp [h, ih]

/-- A `flatMap` selecting one list that occurs exactly once. -/
private theorem flatMap_ite_singleton {l : List (List Bool)} {x : List Bool} (v : ℤ)
    (hl : l.Nodup) (hx : x ∈ l) : (l.flatMap fun o ↦ if o = x then [v] else []) = [v] := by
  rw [flatMap_ite_eq_filter, List.filter_eq, List.count_eq_one_of_mem hl hx]
  rfl

/-- A braid word keeps the number of labels. -/
theorem length_braidLabels (w : BraidWord) (a : List Bool) :
    (braidLabels w a).length = a.length := by
  induction w generalizing a with
  | nil => rfl
  | cons g w ih => rw [braidLabels, ih, length_swapAt]

/-- **The orientation of a closed braid cut open**: exactly one orientation with both ends
upward, of oriented writhe the braid writhe. -/
theorem orientWrithes_braidLongDiagram (K : BraidKnot) :
    orientWrithes (braidLongDiagram K) = [writhe K.word] := by
  obtain ⟨k, hk⟩ : ∃ k, K.strands = k + 1 :=
    ⟨K.strands - 1, by have := K.strands_pos; omega⟩
  have hk1 : K.strands - 1 = k := by omega
  simp only [orientWrithes, braidLongDiagram, morseLongClosure, hk1]
  rw [orientStates_append, orientStates_append, orientStates_closureCups,
    orientStates_eq_flatMap (morseOfBraid K.word), List.flatMap_map,
    orientStates_eq_flatMap, List.flatMap_assoc, List.filter_flatMap, List.map_flatMap]
  rw [List.flatMap_congr (g := fun o ↦ if o = List.replicate k true then [writhe K.word] else [])]
  · exact flatMap_ite_singleton _ (nodup_closureSeqs k) (replicate_mem_closureSeqs k)
  intro o ho
  have hol := length_of_mem_closureSeqs ho
  have hlen : (true :: o).length = K.strands := by simp [hol, hk]
  rw [show (true :: o ++ (o.map not).reverse, (0 : ℤ)) = ((true :: o) ++ (o.map not).reverse, 0)
    from rfl, orientStates_morseOfBraid K.strands K.word K.isOnStrands _ _ hlen,
    List.flatMap_singleton]
  have hbl : (braidLabels K.word (true :: o)).length = k + 1 := by
    rw [length_braidLabels, hlen, hk]
  obtain ⟨c, t, hct⟩ : ∃ c t, braidLabels K.word (true :: o) = c :: t := by
    rcases h : braidLabels K.word (true :: o) with _ | ⟨c, t⟩
    · rw [h] at hbl; simp at hbl
    · exact ⟨c, t, rfl⟩
  have ht : t.length = k := by rw [hct] at hbl; simpa using hbl
  rw [hct, orientStates_closureCaps k c t o ht hol]
  by_cases hfix : braidLabels K.word (true :: o) = true :: o
  · have hrep := (braidLabels_fixed_iff K k hk o hol).1 hfix
    rw [hct] at hfix
    obtain ⟨rfl, rfl⟩ := List.cons.inj hfix
    have hw := braidWr_replicate K.strands K.word K.isOnStrands
    rw [hk, List.replicate_succ, ← hrep] at hw
    simp [hrep] at hw ⊢
    exact hw
  · have hne : o ≠ List.replicate k true :=
      fun h ↦ hfix ((braidLabels_fixed_iff K k hk o hol).2 h)
    rw [ite_eq_right hne]
    split_ifs with hto
    · have hc : c ≠ true := by
        rintro rfl
        exact hfix (by rw [hct, hto])
      simp [hc]
    · rfl

/-- The diagram of a closed braid cut open is a long-knot diagram. -/
theorem isLongKnotDiagram_braidLongDiagram (K : BraidKnot) :
    IsLongKnotDiagram (braidLongDiagram K) :=
  ⟨(morseFits_braidLongDiagram K).1, by rw [orientWrithes_braidLongDiagram]; rfl⟩

/-- Its blackboard framing is the braid writhe. -/
theorem morseWrithe_braidLongDiagram (K : BraidKnot) :
    morseWrithe (braidLongDiagram K) = writhe K.word := by
  rw [morseWrithe, orientWrithes_braidLongDiagram, List.sum_singleton]

end AJConjecture
