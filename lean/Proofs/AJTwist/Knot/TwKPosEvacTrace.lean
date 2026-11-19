import Mathlib
import AJTwist.Knot.TwKPosEvacStep

/-!
# Evacuation in slot form: the snowball follows the whole knot

`morseReach_isoSlotWord_evac`: for a connected long knot `G`, the doubled word with beads
`isoSlotWord 1 G β` reaches `morseDouble G ++ L.flatten`, where `L` lists the contents of the
slots in some order, each one as it is or rotated by `π`.

Route: follow the trace of `G` from the bottom end (`isoTrace G fuel (0, 0, true)`), applying
`morseReach_isoSnowStep` at every step (induction over the trace as in `isoJ_trace` of
`PairKIsoBeadSlide`, with the beading as part of the state). Facts about the trace:

* it visits every segment (`IsoConnected`), and it ends at the top end `(G.length, 0, true)`,
  where the step function is undefined;
* it visits no segment twice: `isoTraceStep` is injective where it is defined (every case of
  its definition can be inverted), and a repeated segment would make the trace periodic, so it
  could not reach the top end.

So when the trace ends, every slot but the top one has been emptied and not refilled, and the top
slot holds the snowball: the contents of all slots, each as it was or rotated (the rotation of a
concatenation is the concatenation of the rotations in the opposite order, `isoRot_append`; the
empty slots contribute `[]`). The final word is `isoSlotWord 1 G β'` with only the top slot
non-empty, which is `morseDouble G ++ β' G.length 0` (as `isoSlotWord_nil`).

Simulated outside Lean (`SCR/KP/tools/evac_test.py`) and, for the definitions of this package,
evaluated in Lean (`SCR/KP/leancheck/EvalEvac.lean`): for `twkCore2 3` the fourteen slot words
along the trace agree letter for letter with the simulation.
-/

namespace AJConjecture

/-! ### The segments of the trace -/

/-- A segment of the knot: a level, a strand at that level, downward segments below the top. -/
private def IsoSegEvacTrace (G : MorseWord) (x : ℕ × ℕ × Bool) : Prop :=
  x.1 ≤ G.length ∧ x.2.1 < morseOut 1 (G.take x.1) ∧ (x.2.2 = false → x.1 < G.length)

/-- The word around the letter of index `k`. -/
private theorem split_evacTrace (G : MorseWord) (k : ℕ) (l : MorseLetter) (hk : G[k]? = some l)
    (hG : morseFits 1 G = true) :
    k < G.length ∧ l.2 + morseKindIn l.1 ≤ morseOut 1 (G.take k) ∧
      morseOut 1 (G.take (k + 1)) = morseLetterOut (morseOut 1 (G.take k)) l := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hk
  have hd : G.drop k = l :: G.drop (k + 1) := by rw [List.drop_eq_getElem_cons hlt, hget]
  have ht : G.take (k + 1) = G.take k ++ [l] := by rw [List.take_add_one, hk]; rfl
  have hf := hG
  rw [← List.take_append_drop k G, morseFits_append, hd, Bool.and_eq_true, morseFits_cons] at hf
  refine ⟨hlt, hf.2.1, ?_⟩
  rw [ht, morseOut_append]
  rfl

/-- The step along the knot leads from a segment to a segment. -/
private theorem isoSeg_step_evacTrace (G : MorseWord) (hG : morseFits 1 G = true)
    (x y : ℕ × ℕ × Bool) (hx : IsoSegEvacTrace G x) (hy : isoTraceStep G x = some y) :
    IsoSegEvacTrace G y := by
  obtain ⟨k, p, d⟩ := x
  obtain ⟨-, hp, -⟩ := hx
  simp only at hp
  cases d with
  | true =>
    cases hl : G[k]? with
    | none => simp [isoTraceStep, hl] at hy
    | some l =>
      obtain ⟨hlt, hfit, hout⟩ := split_evacTrace G k l hl hG
      obtain ⟨kd, i⟩ := l
      simp only [morseLetterOut] at hout
      cases kd <;> simp only [isoTraceStep, hl] at hy <;>
        simp only [morseKindIn, morseKindOut] at hfit hout <;> split_ifs at hy <;>
        obtain rfl := Option.some.inj hy <;>
        refine ⟨by dsimp only; omega, by dsimp only; omega, fun h ↦ ?_⟩ <;>
        first | exact hlt | exact absurd h (by simp)
  | false =>
    cases k with
    | zero => simp [isoTraceStep] at hy
    | succ k =>
      cases hl : G[k]? with
      | none => simp [isoTraceStep, hl] at hy
      | some l =>
        obtain ⟨hlt, hfit, hout⟩ := split_evacTrace G k l hl hG
        obtain ⟨kd, i⟩ := l
        simp only [morseLetterOut] at hout
        rw [hout] at hp
        cases kd <;> simp only [isoTraceStep, hl] at hy <;>
          simp only [morseKindIn, morseKindOut] at hfit hout hp <;> split_ifs at hy <;>
          obtain rfl := Option.some.inj hy <;>
          refine ⟨by dsimp only; omega, by dsimp only; omega, fun h ↦ ?_⟩ <;>
          first | exact hlt | exact absurd h (by simp)

/-- Every element of the trace is a segment. -/
private theorem isoSeg_trace_evacTrace (G : MorseWord) (hG : morseFits 1 G = true) :
    ∀ (fuel : ℕ) (x : ℕ × ℕ × Bool), IsoSegEvacTrace G x →
      ∀ y ∈ isoTrace G fuel x, IsoSegEvacTrace G y
  | 0, x, hx, y, hy => by
    simp only [isoTrace, List.mem_singleton] at hy
    exact hy ▸ hx
  | fuel + 1, x, hx, y, hy => by
    cases hs : isoTraceStep G x with
    | none =>
      simp only [isoTrace, hs, List.mem_singleton] at hy
      exact hy ▸ hx
    | some z =>
      simp only [isoTrace, hs, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact isoSeg_trace_evacTrace G hG fuel z (isoSeg_step_evacTrace G hG x z hx hs) y hy

/-! ### Functions on the slots -/

/-- The values of a function on the slots of a word read from `n` strands, level by level. -/
private def slotListEvacTrace {α : Type} (n : ℕ) : MorseWord → (ℕ → ℕ → α) → List α
  | [], f => (List.range n).map (f 0)
  | l :: G, f =>
    (List.range n).map (f 0) ++ slotListEvacTrace (morseLetterOut n l) G (fun k ↦ f (k + 1))

/-- A function on the slots with a new value in one slot. -/
private def slotUpdEvacTrace {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) (a : α) : ℕ → ℕ → α :=
  Function.update f k (Function.update (f k) p a)

/-- The values of a function with a new value in one slot. -/
private theorem slotUpd_apply_evacTrace {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) (a : α)
    (j q : ℕ) : slotUpdEvacTrace f k p a j q = if j = k ∧ q = p then a else f j q := by
  unfold slotUpdEvacTrace
  by_cases hj : j = k
  · subst hj
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [hj]

/-- The beads of a slot word are the values of the beading on the slots. -/
private theorem isoSlotBeads_eq_evacTrace (n : ℕ) (G : MorseWord) (β : ℕ → ℕ → MorseWord) :
    isoSlotBeads n G β = slotListEvacTrace n G β := by
  induction G generalizing n β with
  | nil => rfl
  | cons l G ih => simp only [isoSlotBeads, slotListEvacTrace, ih]

/-- The list of the values of a composed function. -/
private theorem slotList_map_evacTrace {α γ : Type} (g : α → γ) (n : ℕ) (G : MorseWord)
    (f : ℕ → ℕ → α) :
    (slotListEvacTrace n G f).map g = slotListEvacTrace n G (fun k p ↦ g (f k p)) := by
  induction G generalizing n f with
  | nil => simp [slotListEvacTrace]
  | cons l G ih => simp [slotListEvacTrace, ih]

/-- Every entry of the list is a value of the function. -/
private theorem mem_slotList_evacTrace {α : Type} (n : ℕ) (G : MorseWord) (f : ℕ → ℕ → α)
    (a : α) (h : a ∈ slotListEvacTrace n G f) : ∃ k p, a = f k p := by
  induction G generalizing n f with
  | nil =>
    simp only [slotListEvacTrace, List.mem_map] at h
    obtain ⟨p, -, rfl⟩ := h
    exact ⟨0, p, rfl⟩
  | cons l G ih =>
    simp only [slotListEvacTrace, List.mem_append, List.mem_map] at h
    rcases h with ⟨p, -, rfl⟩ | h
    · exact ⟨0, p, rfl⟩
    · obtain ⟨k, p, rfl⟩ := ih _ _ h
      exact ⟨k + 1, p, rfl⟩

/-- A layer of lists with a new value on one band. -/
private theorem layer_update_perm_evacTrace {α : Type} (f : ℕ → List α) (p : ℕ) (a : List α) :
    ∀ n, p < n → (((List.range n).map (Function.update f p a)).flatten).Perm
      (a ++ ((List.range n).map (Function.update f p [])).flatten)
  | 0, hp => absurd hp (Nat.not_lt_zero p)
  | n + 1, hp => by
    simp only [List.range_succ, List.map_append, List.flatten_append, List.map_cons,
      List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    by_cases hpn : p = n
    · subst hpn
      have h : ∀ b : List α, (List.range p).map (Function.update f p b) = (List.range p).map f :=
        fun b ↦ List.map_congr_left fun q hq ↦
          Function.update_of_ne (by have := List.mem_range.1 hq; omega) _ _
      rw [h a, h [], Function.update_self, Function.update_self, List.append_nil]
      exact List.perm_append_comm
    · rw [Function.update_of_ne (Ne.symm hpn), Function.update_of_ne (Ne.symm hpn),
        ← List.append_assoc]
      exact (layer_update_perm_evacTrace f p a n (by omega)).append_right _

/-- The list of the values of a function of lists with a new value in one slot. -/
private theorem slotList_update_perm_evacTrace (a : List MorseWord) :
    ∀ (G : MorseWord) (n : ℕ) (Λ : ℕ → ℕ → List MorseWord) (k p : ℕ),
      p < morseOut n (G.take k) → k ≤ G.length →
      ((slotListEvacTrace n G (slotUpdEvacTrace Λ k p a)).flatten).Perm
        (a ++ (slotListEvacTrace n G (slotUpdEvacTrace Λ k p [])).flatten)
  | [], n, Λ, 0, p, hp, _ => by
    simp only [slotListEvacTrace, slotUpdEvacTrace, Function.update_self]
    exact layer_update_perm_evacTrace (Λ 0) p a n hp
  | l :: G, n, Λ, 0, p, hp, _ => by
    have h : ∀ b : List MorseWord, (fun j ↦ slotUpdEvacTrace Λ 0 p b (j + 1)) =
        fun j ↦ Λ (j + 1) := fun b ↦ by
      funext j
      simp [slotUpdEvacTrace]
    simp only [slotListEvacTrace, h, List.flatten_append]
    simp only [slotUpdEvacTrace, Function.update_self]
    rw [← List.append_assoc]
    exact (layer_update_perm_evacTrace (Λ 0) p a n hp).append_right _
  | l :: G, n, Λ, k + 1, p, hp, hk => by
    have h : ∀ b : List MorseWord, (fun j ↦ slotUpdEvacTrace Λ (k + 1) p b (j + 1)) =
        slotUpdEvacTrace (fun j ↦ Λ (j + 1)) k p b := fun b ↦ by
      funext j q
      simp [slotUpd_apply_evacTrace]
    have h0 : ∀ b : List MorseWord, slotUpdEvacTrace Λ (k + 1) p b 0 = Λ 0 := fun b ↦ by
      simp [slotUpdEvacTrace]
    simp only [slotListEvacTrace, h, h0, List.flatten_append]
    exact ((slotList_update_perm_evacTrace a G (morseLetterOut n l)
      (fun j ↦ Λ (j + 1)) k p hp (by simpa using hk)).append_left _).trans
        (List.perm_append_comm_assoc _ _ _)

/-- The value in the changed slot. -/
private theorem slotUpd_self_evacTrace {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) (a : α) :
    slotUpdEvacTrace f k p a k p = a := by
  simp [slotUpd_apply_evacTrace]

/-- The values in the other slots. -/
private theorem slotUpd_of_ne_evacTrace {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) (a : α) (j q : ℕ)
    (h : ¬(j = k ∧ q = p)) : slotUpdEvacTrace f k p a j q = f j q := by
  simp [slotUpd_apply_evacTrace, h]

/-- Writing its own value into a slot changes nothing. -/
private theorem slotUpd_eq_self_evacTrace {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) :
    slotUpdEvacTrace f k p (f k p) = f := by
  funext j q
  rw [slotUpd_apply_evacTrace]
  split_ifs with h
  · rw [h.1, h.2]
  · rfl

/-! ### Rotated permutations -/

/-- A rotated permutation followed by a permutation. -/
private theorem isoRotPerm_perm_right_evacTrace {Bs L L₂ : List MorseWord}
    (h : IsoRotPerm Bs L) (hp : L.Perm L₂) : IsoRotPerm Bs L₂ := by
  obtain ⟨L', hL', hf⟩ := h
  have h1 : Relation.Comp (List.Forall₂ (fun a b : MorseWord ↦ b = a ∨ b = isoRot 2 a))
      List.Perm L' L₂ := ⟨L, hf, hp⟩
  rw [List.forall₂_comp_perm_eq_perm_comp_forall₂] at h1
  obtain ⟨M, hM, hf'⟩ := h1
  exact ⟨M, hM.symm.trans hL', hf'⟩

/-- Rotating the first entries of a list of beads, each as it is or rotated. -/
private theorem forall₂_rot_prefix_evacTrace (C : List MorseWord) :
    ∀ (A L' : List MorseWord), (∀ a ∈ L', morseFits 2 a = true ∧ morseOut 2 a = 2) →
      List.Forall₂ (fun a b : MorseWord ↦ b = a ∨ b = isoRot 2 a) L' (A ++ C) →
      List.Forall₂ (fun a b : MorseWord ↦ b = a ∨ b = isoRot 2 a) L' (A.map (isoRot 2) ++ C)
  | [], _, _, h => h
  | a :: A, L', hv, h => by
    cases h with
    | @cons a' _ L'' _ hab htl =>
      refine List.Forall₂.cons ?_ (forall₂_rot_prefix_evacTrace C A L''
        (fun b hb ↦ hv b (List.mem_cons_of_mem _ hb)) htl)
      rcases hab with rfl | rfl
      · exact Or.inr rfl
      · have ha := hv a' List.mem_cons_self
        have h := isoRot_isoRot 2 a' ha.1
        rw [ha.2] at h
        exact Or.inl h

/-- Rotating the first entries of a rotated permutation. -/
private theorem isoRotPerm_rot_prefix_evacTrace {Bs A C : List MorseWord}
    (hB : ∀ b ∈ Bs, morseFits 2 b = true ∧ morseOut 2 b = 2) (h : IsoRotPerm Bs (A ++ C)) :
    IsoRotPerm Bs (A.map (isoRot 2) ++ C) := by
  obtain ⟨L', hL', hf⟩ := h
  exact ⟨L', hL', forall₂_rot_prefix_evacTrace C A L' (fun a ha ↦ hB a (hL'.subset ha)) hf⟩

/-- A concatenation of tangles on the band is a tangle on the band. -/
private theorem flatten_valid_evacTrace : ∀ L : List MorseWord,
    (∀ w ∈ L, morseFits 2 w = true ∧ morseOut 2 w = 2) →
    morseFits 2 L.flatten = true ∧ morseOut 2 L.flatten = 2
  | [], _ => ⟨rfl, rfl⟩
  | a :: L, h => by
    have ha := h a List.mem_cons_self
    have ih := flatten_valid_evacTrace L fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
    rw [List.flatten_cons, morseFits_append, morseOut_append, ha.1, ha.2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- The rotation of a concatenation of tangles on the band. -/
private theorem flatten_rot_evacTrace : ∀ L : List MorseWord,
    (∀ w ∈ L, morseFits 2 w = true ∧ morseOut 2 w = 2) →
    (L.reverse.map (isoRot 2)).flatten = isoRot 2 L.flatten
  | [], _ => rfl
  | a :: L, h => by
    have ha := h a List.mem_cons_self
    rw [List.reverse_cons, List.map_append, List.flatten_append,
      flatten_rot_evacTrace L fun w hw ↦ h w (List.mem_cons_of_mem _ hw), List.flatten_cons,
      isoRot_append, ha.2]
    simp

/-! ### The pieces of the snowball -/

/-- The snowball step in terms of slot updates. -/
private theorem isoSnowStep_eq_evacTrace (β : ℕ → ℕ → MorseWord) (k p k' p' : ℕ) (d d' : Bool) :
    isoSnowStep β (k, p, d) (k', p', d') =
      slotUpdEvacTrace (slotUpdEvacTrace β k p []) k' p' (match d, d' with
        | true, true => β k p ++ slotUpdEvacTrace β k p [] k' p'
        | true, false => slotUpdEvacTrace β k p [] k' p' ++ isoRot 2 (β k p)
        | false, false => slotUpdEvacTrace β k p [] k' p' ++ β k p
        | false, true => isoRot 2 (β k p) ++ slotUpdEvacTrace β k p [] k' p') := rfl

/-- The snowball step on the lists of pieces of the slots. -/
private def snowListEvacTrace (Λ : ℕ → ℕ → List MorseWord) (x y : ℕ × ℕ × Bool) :
    ℕ → ℕ → List MorseWord :=
  slotUpdEvacTrace (slotUpdEvacTrace Λ x.1 x.2.1 []) y.1 y.2.1 (match x.2.2, y.2.2 with
    | true, true => Λ x.1 x.2.1 ++ slotUpdEvacTrace Λ x.1 x.2.1 [] y.1 y.2.1
    | true, false =>
      slotUpdEvacTrace Λ x.1 x.2.1 [] y.1 y.2.1 ++ (Λ x.1 x.2.1).reverse.map (isoRot 2)
    | false, false => slotUpdEvacTrace Λ x.1 x.2.1 [] y.1 y.2.1 ++ Λ x.1 x.2.1
    | false, true =>
      (Λ x.1 x.2.1).reverse.map (isoRot 2) ++ slotUpdEvacTrace Λ x.1 x.2.1 [] y.1 y.2.1)

/-- The pieces of the slots after a step concatenate to the contents of the slots. -/
private theorem snowList_flatten_evacTrace (Λ : ℕ → ℕ → List MorseWord) (x y : ℕ × ℕ × Bool)
    (hv : ∀ w ∈ Λ x.1 x.2.1, morseFits 2 w = true ∧ morseOut 2 w = 2) :
    (fun k p ↦ (snowListEvacTrace Λ x y k p).flatten) =
      isoSnowStep (fun k p ↦ (Λ k p).flatten) x y := by
  obtain ⟨k, p, d⟩ := x
  obtain ⟨k', p', d'⟩ := y
  have h0 : ∀ j q, (slotUpdEvacTrace Λ k p [] j q).flatten =
      slotUpdEvacTrace (fun k p ↦ (Λ k p).flatten) k p [] j q := by
    intro j q
    simp only [slotUpd_apply_evacTrace]
    split_ifs <;> rfl
  funext j q
  rw [isoSnowStep_eq_evacTrace, snowListEvacTrace]
  by_cases hjq : j = k' ∧ q = p'
  · obtain ⟨rfl, rfl⟩ := hjq
    rw [slotUpd_self_evacTrace, slotUpd_self_evacTrace]
    cases d <;> cases d' <;>
      simp only [List.flatten_append, h0, flatten_rot_evacTrace _ hv]
  · rw [slotUpd_of_ne_evacTrace _ _ _ _ _ _ hjq, slotUpd_of_ne_evacTrace _ _ _ _ _ _ hjq, h0]

/-- The pieces of the slots after a step are tangles on the band. -/
private theorem snowList_valid_evacTrace (Λ : ℕ → ℕ → List MorseWord) (x y : ℕ × ℕ × Bool)
    (hv : ∀ k p, ∀ w ∈ Λ k p, morseFits 2 w = true ∧ morseOut 2 w = 2) :
    ∀ k p, ∀ w ∈ snowListEvacTrace Λ x y k p, morseFits 2 w = true ∧ morseOut 2 w = 2 := by
  obtain ⟨k, p, d⟩ := x
  obtain ⟨k', p', d'⟩ := y
  have h0 : ∀ j q, ∀ w ∈ slotUpdEvacTrace Λ k p [] j q,
      morseFits 2 w = true ∧ morseOut 2 w = 2 := by
    intro j q w hw
    rw [slotUpd_apply_evacTrace] at hw
    split_ifs at hw
    · simp at hw
    · exact hv j q w hw
  have hr : ∀ w ∈ (Λ k p).reverse.map (isoRot 2), morseFits 2 w = true ∧ morseOut 2 w = 2 := by
    intro w hw
    simp only [List.mem_map, List.mem_reverse] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have h := isoRot_fits w' 2 (hv k p w' hw').1
    rwa [(hv k p w' hw').2] at h
  intro j q w hw
  rw [snowListEvacTrace] at hw
  by_cases hjq : j = k' ∧ q = p'
  · obtain ⟨rfl, rfl⟩ := hjq
    rw [slotUpd_self_evacTrace] at hw
    cases d <;> cases d' <;> simp only [List.mem_append] at hw <;> rcases hw with hw | hw <;>
      first | exact hv k p w hw | exact h0 _ _ w hw | exact hr w hw
  · rw [slotUpd_of_ne_evacTrace _ _ _ _ _ _ hjq] at hw
    exact h0 j q w hw

/-- The pieces of all slots after a step are a rotated permutation of the pieces before. -/
private theorem snowList_perm_evacTrace (G : MorseWord) (Bs : List MorseWord)
    (hB : ∀ b ∈ Bs, morseFits 2 b = true ∧ morseOut 2 b = 2) (Λ : ℕ → ℕ → List MorseWord)
    (x y : ℕ × ℕ × Bool) (hx : x.1 ≤ G.length ∧ x.2.1 < morseOut 1 (G.take x.1))
    (hy : y.1 ≤ G.length ∧ y.2.1 < morseOut 1 (G.take y.1))
    (h : IsoRotPerm Bs (slotListEvacTrace 1 G Λ).flatten) :
    IsoRotPerm Bs (slotListEvacTrace 1 G (snowListEvacTrace Λ x y)).flatten := by
  obtain ⟨k, p, d⟩ := x
  obtain ⟨k', p', d'⟩ := y
  have hx1 := slotList_update_perm_evacTrace (Λ k p) G 1 Λ k p hx.2 hx.1
  rw [slotUpd_eq_self_evacTrace] at hx1
  have hy1 := slotList_update_perm_evacTrace (slotUpdEvacTrace Λ k p [] k' p') G 1
    (slotUpdEvacTrace Λ k p []) k' p' hy.2 hy.1
  rw [slotUpd_eq_self_evacTrace] at hy1
  have h1 := isoRotPerm_perm_right_evacTrace h (hx1.trans (hy1.append_left _))
  have h2 := fun a : List MorseWord ↦ (slotList_update_perm_evacTrace a G 1
    (slotUpdEvacTrace Λ k p []) k' p' hy.2 hy.1).symm
  rw [snowListEvacTrace]
  cases d <;> cases d'
  · refine isoRotPerm_perm_right_evacTrace h1 (List.Perm.trans ?_ (h2 _))
    rw [← List.append_assoc]
    exact List.perm_append_comm.append_right _
  · refine isoRotPerm_perm_right_evacTrace (isoRotPerm_rot_prefix_evacTrace hB h1)
      (List.Perm.trans ?_ (h2 _))
    rw [← List.append_assoc]
    exact (((List.reverse_perm _).map _).symm.append_right _).append_right _
  · refine isoRotPerm_perm_right_evacTrace (isoRotPerm_rot_prefix_evacTrace hB h1)
      (List.Perm.trans ?_ (h2 _))
    rw [← List.append_assoc]
    exact ((((List.reverse_perm _).map _).symm.append_right _).trans
      List.perm_append_comm).append_right _
  · refine isoRotPerm_perm_right_evacTrace h1 (List.Perm.trans ?_ (h2 _))
    rw [← List.append_assoc]

/-! ### The snowball along the trace -/

/-- The state of the snowball at the segment `x`: the visited slots other than the slot of `x`
are empty, and the slots are concatenations of pieces which together are a rotated permutation
of the beads. -/
private def SnowStateEvacTrace (G : MorseWord) (β : ℕ → ℕ → MorseWord) (x : ℕ × ℕ × Bool)
    (β' : ℕ → ℕ → MorseWord) (V : ℕ × ℕ → Prop) : Prop :=
  IsoSlotValid β' ∧ V (x.1, x.2.1) ∧
    (∀ k p, V (k, p) → ¬(k = x.1 ∧ p = x.2.1) → β' k p = []) ∧
    ∃ Λ : ℕ → ℕ → List MorseWord, (fun k p ↦ (Λ k p).flatten) = β' ∧
      (∀ k p, ∀ w ∈ Λ k p, morseFits 2 w = true ∧ morseOut 2 w = 2) ∧
      IsoRotPerm (isoSlotBeads 1 G β) (slotListEvacTrace 1 G Λ).flatten

/-- The beads of a valid beading are tangles on the band. -/
private theorem isoSlotBeads_valid_evacTrace (G : MorseWord) (β : ℕ → ℕ → MorseWord)
    (hβ : IsoSlotValid β) : ∀ b ∈ isoSlotBeads 1 G β, morseFits 2 b = true ∧ morseOut 2 b = 2 := by
  intro b hb
  rw [isoSlotBeads_eq_evacTrace] at hb
  obtain ⟨k, p, rfl⟩ := mem_slotList_evacTrace 1 G β b hb
  exact hβ k p

/-- The state of the snowball after one step. -/
private theorem snowState_step_evacTrace (G : MorseWord) (β : ℕ → ℕ → MorseWord)
    (hβ : IsoSlotValid β) (x y : ℕ × ℕ × Bool) (β' : ℕ → ℕ → MorseWord) (V : ℕ × ℕ → Prop)
    (hx : IsoSegEvacTrace G x) (hy : IsoSegEvacTrace G y) (h : SnowStateEvacTrace G β x β' V) :
    SnowStateEvacTrace G β y (isoSnowStep β' x y) (fun s ↦ V s ∨ s = (y.1, y.2.1)) := by
  obtain ⟨hv, -, hemp, Λ, hΛ, hpc, hperm⟩ := h
  refine ⟨isoSlotValid_isoSnowStep β' x y hv, Or.inr rfl, ?_, snowListEvacTrace Λ x y, ?_,
    snowList_valid_evacTrace Λ x y hpc, ?_⟩
  · intro k p hV hne
    obtain ⟨kx, px, d⟩ := x
    obtain ⟨ky, py, d'⟩ := y
    rw [isoSnowStep_eq_evacTrace, slotUpd_of_ne_evacTrace _ _ _ _ _ _ hne,
      slotUpd_apply_evacTrace]
    split_ifs with h1
    · rfl
    · rcases hV with hV | hV
      · exact hemp k p hV h1
      · exact absurd (by simpa using hV) hne
  · rw [snowList_flatten_evacTrace Λ x y (hpc _ _), hΛ]
  · exact snowList_perm_evacTrace G _ (isoSlotBeads_valid_evacTrace G β hβ) Λ x y
      ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩ hperm

/-- The snowball follows the trace up to a segment where the trace ends. -/
private theorem snow_trace_evacTrace (G u v : MorseWord) (β : ℕ → ℕ → MorseWord) (n₀ e : ℕ)
    (hG : morseFits 1 G = true) (hβ : IsoSlotValid β) (hu : morseOut n₀ u = 2 + e) :
    ∀ (fuel : ℕ) (x : ℕ × ℕ × Bool) (β' : ℕ → ℕ → MorseWord) (V : ℕ × ℕ → Prop),
      IsoSegEvacTrace G x → SnowStateEvacTrace G β x β' V →
      ∀ y ∈ isoTrace G fuel x, isoTraceStep G y = none →
        ∃ (β'' : ℕ → ℕ → MorseWord) (V' : ℕ × ℕ → Prop), SnowStateEvacTrace G β y β'' V' ∧
          (∀ s, V s → V' s) ∧ (∀ w ∈ isoTrace G fuel x, V' (w.1, w.2.1)) ∧
          MorseReach n₀ (u ++ isoSlotWord 1 G β' ++ v) (u ++ isoSlotWord 1 G β'' ++ v)
  | 0, x, β', V, _, hst, y, hy, _ => by
    simp only [isoTrace, List.mem_singleton] at hy
    subst hy
    refine ⟨β', V, hst, fun _ h ↦ h, fun w hw ↦ ?_, morseReach_refl _ _⟩
    simp only [isoTrace, List.mem_singleton] at hw
    exact hw ▸ hst.2.1
  | fuel + 1, x, β', V, hx, hst, y, hy, hend => by
    cases hs : isoTraceStep G x with
    | none =>
      simp only [isoTrace, hs, List.mem_singleton] at hy
      subst hy
      refine ⟨β', V, hst, fun _ h ↦ h, fun w hw ↦ ?_, morseReach_refl _ _⟩
      simp only [isoTrace, hs, List.mem_singleton] at hw
      exact hw ▸ hst.2.1
    | some z =>
      simp only [isoTrace, hs, List.mem_cons] at hy
      rcases hy with rfl | hy
      · rw [hs] at hend
        exact absurd hend (by simp)
      · have hz := isoSeg_step_evacTrace G hG x z hx hs
        obtain ⟨β'', V', hst', hV, hall, hr⟩ := snow_trace_evacTrace G u v β n₀ e hG hβ hu fuel z
          (isoSnowStep β' x z) _ hz (snowState_step_evacTrace G β hβ x z β' V hx hz hst) y hy hend
        refine ⟨β'', V', hst', fun s h ↦ hV s (Or.inl h), fun w hw ↦ ?_,
          morseReach_trans (morseReach_isoSnowStep G u v β' n₀ e x z hG hst.1 hu ⟨hx.1, hx.2.1⟩
            hs) hr⟩
        simp only [isoTrace, hs, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hV _ (Or.inl hst.2.1)
        · exact hall w hw

/-! ### The end of the trace -/

/-- A layer of empty tangles is empty. -/
private theorem isoLayer_nil_evacTrace (m : ℕ) (f : ℕ → MorseWord) (h : ∀ p < m, f p = []) :
    isoLayer m f = [] := by
  unfold isoLayer
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  rw [h p (List.mem_range.1 hp)]
  rfl

/-- A slot word whose slots below the top level are empty. -/
private theorem isoSlotWord_top_evacTrace : ∀ (G : MorseWord) (n : ℕ) (β : ℕ → ℕ → MorseWord),
    (∀ k < G.length, ∀ p < morseOut n (G.take k), β k p = []) →
    isoSlotWord n G β = morseDouble G ++ isoLayer (morseOut n G) (β G.length)
  | [], _, _, _ => rfl
  | l :: G, n, β, h => by
    have h0 : isoLayer n (β 0) = [] :=
      isoLayer_nil_evacTrace n (β 0) fun p hp ↦ h 0 (by simp) p hp
    have ih := isoSlotWord_top_evacTrace G (morseLetterOut n l) (fun k ↦ β (k + 1))
      fun k hk p hp ↦ h (k + 1) (by simpa using hk) p hp
    have h1 : isoSlotWord n (l :: G) β = isoLayer n (β 0) ++ morseDoubleLetter l ++
        isoSlotWord (morseLetterOut n l) G (fun k ↦ β (k + 1)) := rfl
    rw [h1, h0, ih]
    simp [morseDouble, morseOut]

/-- The beads of a slot word whose slots below the top level are empty. -/
private theorem slotList_top_evacTrace : ∀ (G : MorseWord) (n : ℕ) (β : ℕ → ℕ → MorseWord),
    (∀ k < G.length, ∀ p < morseOut n (G.take k), β k p = []) →
    (slotListEvacTrace n G β).flatten = ((List.range (morseOut n G)).map (β G.length)).flatten
  | [], _, _, _ => rfl
  | l :: G, n, β, h => by
    have h0 : ((List.range n).map (β 0)).flatten = [] := by
      rw [List.flatten_eq_nil_iff]
      intro w hw
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
      exact h 0 (by simp) p (List.mem_range.1 hp)
    have ih := slotList_top_evacTrace G (morseLetterOut n l) (fun k ↦ β (k + 1))
      fun k hk p hp ↦ h (k + 1) (by simpa using hk) p hp
    simp only [slotListEvacTrace, List.flatten_append, h0, ih, List.nil_append]
    rfl

/-- Evacuation in slot form. -/
theorem morseReach_isoSlotWord_evac (G u v : MorseWord) (β : ℕ → ℕ → MorseWord) (n₀ e : ℕ)
    (hG : morseFits 1 G = true ∧ morseOut 1 G = 1) (hc : IsoConnected G) (hβ : IsoSlotValid β)
    (hu : morseOut n₀ u = 2 + e) :
    ∃ L : List MorseWord, IsoRotPerm (isoSlotBeads 1 G β) L ∧
      MorseReach n₀ (u ++ isoSlotWord 1 G β ++ v) (u ++ morseDouble G ++ L.flatten ++ v) := by
  have hstart : IsoSegEvacTrace G (0, 0, true) := ⟨Nat.zero_le _, by simp [morseOut], by simp⟩
  have hst : SnowStateEvacTrace G β (0, 0, true) β (fun s ↦ s = (0, 0)) := by
    refine ⟨hβ, rfl, fun k p hV hne ↦ absurd (by simpa using hV) hne, fun k p ↦ [β k p], ?_,
      fun k p w hw ↦ ?_, ?_⟩
    · funext k p
      simp
    · rw [List.mem_singleton.1 hw]
      exact hβ k p
    · have h : (slotListEvacTrace 1 G fun k p ↦ [β k p]).flatten = isoSlotBeads 1 G β := by
        rw [isoSlotBeads_eq_evacTrace, ← slotList_map_evacTrace (fun w : MorseWord ↦ [w]),
          ← List.flatMap_def, List.flatMap_singleton']
      rw [h]
      exact ⟨_, List.Perm.refl _, List.forall₂_same.2 fun _ _ ↦ Or.inl rfl⟩
  obtain ⟨d, hd⟩ := hc G.length le_rfl 0 (by rw [List.take_length, hG.2]; omega)
  have hd' := isoSeg_trace_evacTrace G hG.1 _ _ hstart _ hd
  cases d with
  | false => exact absurd (hd'.2.2 rfl) (lt_irrefl _)
  | true =>
    obtain ⟨β'', V', ⟨-, -, hemp, Λ, hΛ, -, hperm⟩, -, hall, hr⟩ :=
      snow_trace_evacTrace G u v β n₀ e hG.1 hβ hu _ (0, 0, true) β _ hstart hst _ hd
        (by simp [isoTraceStep])
    have hempty : ∀ k < G.length, ∀ p < morseOut 1 (G.take k), β'' k p = [] := by
      intro k hk p hp
      obtain ⟨d, hd⟩ := hc k hk.le p hp
      exact hemp k p (hall _ hd) (by simp only [not_and]; omega)
    refine ⟨(slotListEvacTrace 1 G Λ).flatten, hperm, ?_⟩
    have h1 := isoSlotWord_top_evacTrace G 1 β'' hempty
    have h2 := slotList_top_evacTrace G 1 β'' hempty
    rw [hG.2] at h1 h2
    have h3 : ((slotListEvacTrace 1 G Λ).flatten).flatten = β'' G.length 0 := by
      rw [List.flatten_flatten, slotList_map_evacTrace, hΛ, h2]
      simp
    have h4 : isoLayer 1 (β'' G.length) = β'' G.length 0 := by
      simp [isoLayer, morseShiftWord_zero_iso]
    rw [h3]
    rw [h1, h4] at hr
    simpa only [List.append_assoc] using hr

end AJConjecture
