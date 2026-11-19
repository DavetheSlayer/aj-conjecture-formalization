import Mathlib
import AJTwist.Knot.TwKPosEvacTrace

/-!
# Evacuation: all beads of a doubled connected long knot move to its top end

`morseReach_isoBeaded_evac`: if `W` is the doubled word of a connected long knot `G` with band
beads `Bs` (arbitrary tangles from two strands to two strands), then `W` reaches
`morseDouble G ++ L.flatten`, where `L` lists the beads in some order, each one as it is or
rotated by `π`.

* `morseReach_isoSlotWord_evac` (`TwKPosEvacTrace`): the statement in slot form.
* `morseReach_isoBeaded_slot`: a word built by `IsoBeaded` reaches its slot form (the beads
  appended at one level are sorted by band with `morseReach_isoBead_commR`; several beads on one
  band form one slot, so a rotated permutation of the slots is a rotated permutation of the
  beads).

The order of `L` depends on `G` (for the torus core, on `s mod r`); nothing after this point
uses it (`TwKPosBeadAlg`).
-/

namespace AJConjecture

/-! ### Layers -/

/-- A layer on one more band. -/
private theorem isoLayer_succ_evac (m : ℕ) (β : ℕ → MorseWord) :
    isoLayer (m + 1) β = isoLayer m β ++ morseShiftWord (2 * m) (β m) := by
  simp [isoLayer, List.range_succ, List.flatMap_append]

/-- A layer on `m` bands depends on the tangles of these bands only. -/
private theorem isoLayer_congr_evac (m : ℕ) (β γ : ℕ → MorseWord)
    (h : ∀ p < m, β p = γ p) : isoLayer m β = isoLayer m γ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [isoLayer_succ_evac, isoLayer_succ_evac, ih fun p hp ↦ h p (by omega), h m (by omega)]

/-- A layer of empty tangles is empty. -/
private theorem isoLayer_nil_evac (m : ℕ) (f : ℕ → MorseWord) (h : ∀ p < m, f p = []) :
    isoLayer m f = [] := by
  unfold isoLayer
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  rw [h p (List.mem_range.1 hp)]
  rfl

/-- A layer of beads fits on the strands of its bands and keeps the number of strands. -/
private theorem isoLayer_fits_evac (N : ℕ) (β : ℕ → MorseWord)
    (hβ : ∀ p, morseFits 2 (β p) = true ∧ morseOut 2 (β p) = 2) :
    ∀ m, 2 * m ≤ N → morseFits N (isoLayer m β) = true ∧ morseOut N (isoLayer m β) = N
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
    have ih := isoLayer_fits_evac N β hβ m (by omega)
    have hs := morseOut_shift_iso (2 * m) 2 (N - 2 * m - 2) (β m) (hβ m).1
    rw [(hβ m).2, show 2 * m + 2 + (N - 2 * m - 2) = N by omega] at hs
    rw [isoLayer_succ_evac, morseFits_append, morseOut_append, ih.1, ih.2, hs.1, hs.2]
    exact ⟨rfl, rfl⟩

/-- A tangle above a layer joins the top of the slot of its band. -/
private theorem morseReach_isoLayer_top_evac (n₀ N : ℕ) (T : MorseWord)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) :
    ∀ (m p : ℕ) (β : ℕ → MorseWord) (u v : MorseWord),
      (∀ q, morseFits 2 (β q) = true ∧ morseOut 2 (β q) = 2) → p < m → 2 * m ≤ N →
      morseOut n₀ u = N →
      MorseReach n₀ (u ++ isoLayer m β ++ morseShiftWord (2 * p) T ++ v)
        (u ++ isoLayer m (Function.update β p (β p ++ T)) ++ v)
  | 0, p, _, _, _, _, hp, _, _ => absurd hp (Nat.not_lt_zero p)
  | m + 1, p, β, u, v, hβ, hp, hm, hu => by
    rw [isoLayer_succ_evac, isoLayer_succ_evac]
    by_cases hpm : p = m
    · subst hpm
      rw [Function.update_self, isoLayer_congr_evac p (Function.update β p (β p ++ T)) β
        (fun q hq ↦ Function.update_of_ne (by omega) _ _), morseShiftWord_append]
      simp only [List.append_assoc]
      exact morseReach_refl _ _
    · have hlay := isoLayer_fits_evac N β hβ m (by omega)
      have hs := morseOut_shift_iso (2 * m) 2 (N - 2 * m - 2) (β m) (hβ m).1
      rw [show 2 * m + 2 + (N - 2 * m - 2) = N by omega] at hs
      have h1 := morseReach_symm (morseReach_isoBead_commR n₀ (2 * p) 2 T (u ++ isoLayer m β)
        (morseShiftWord (2 * m) (β m)) v hT hTo (fun l hl ↦ by
          simp only [morseShiftWord, List.mem_map] at hl
          obtain ⟨l', -, rfl⟩ := hl
          simp only [shiftLetter]
          omega) (by rw [morseOut_append, hu, hlay.2]; exact hs.2)
        (by rw [morseOut_append, hu, hlay.2]; omega))
      have h2 := morseReach_isoLayer_top_evac n₀ N T hT hTo m p β u
        (morseShiftWord (2 * m) (β m) ++ v) hβ (by omega) (by omega) hu
      rw [Function.update_of_ne (Ne.symm hpm)]
      simp only [List.append_assoc] at h1 h2 ⊢
      exact morseReach_trans h1 h2

/-! ### Functions on the slots -/

/-- The values of a function on the slots of a word read from `n` strands, level by level. -/
private def slotListEvac {α : Type} (n : ℕ) : MorseWord → (ℕ → ℕ → α) → List α
  | [], f => (List.range n).map (f 0)
  | l :: G, f =>
    (List.range n).map (f 0) ++ slotListEvac (morseLetterOut n l) G (fun k ↦ f (k + 1))

/-- A function on the slots with a new value in one slot. -/
private def slotUpdEvac {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) (a : α) : ℕ → ℕ → α :=
  Function.update f k (Function.update (f k) p a)

/-- The values of a function with a new value in one slot. -/
private theorem slotUpd_apply_evac {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) (a : α) (j q : ℕ) :
    slotUpdEvac f k p a j q = if j = k ∧ q = p then a else f j q := by
  unfold slotUpdEvac
  by_cases hj : j = k
  · subst hj
    by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · simp [hj]

/-- Writing its own value into a slot changes nothing. -/
private theorem slotUpd_eq_self_evac {α : Type} (f : ℕ → ℕ → α) (k p : ℕ) :
    slotUpdEvac f k p (f k p) = f := by
  funext j q
  rw [slotUpd_apply_evac]
  split_ifs with h
  · rw [h.1, h.2]
  · rfl

/-- The beads of a slot word are the values of the beading on the slots. -/
private theorem isoSlotBeads_eq_evac (n : ℕ) (G : MorseWord) (β : ℕ → ℕ → MorseWord) :
    isoSlotBeads n G β = slotListEvac n G β := by
  induction G generalizing n β with
  | nil => rfl
  | cons l G ih => simp only [isoSlotBeads, slotListEvac, ih]

/-- The list of the values of a composed function. -/
private theorem slotList_map_evac {α γ : Type} (g : α → γ) (n : ℕ) (G : MorseWord)
    (f : ℕ → ℕ → α) :
    (slotListEvac n G f).map g = slotListEvac n G (fun k p ↦ g (f k p)) := by
  induction G generalizing n f with
  | nil => simp [slotListEvac]
  | cons l G ih => simp [slotListEvac, ih]

/-- A layer of lists with a new value on one band. -/
private theorem layer_update_perm_evac {α : Type} (f : ℕ → List α) (p : ℕ) (a : List α) :
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
      exact (layer_update_perm_evac f p a n (by omega)).append_right _

/-- The list of the values of a function of lists with a new value in one slot. -/
private theorem slotList_update_perm_evac (a : List MorseWord) :
    ∀ (G : MorseWord) (n : ℕ) (Λ : ℕ → ℕ → List MorseWord) (k p : ℕ),
      p < morseOut n (G.take k) → k ≤ G.length →
      ((slotListEvac n G (slotUpdEvac Λ k p a)).flatten).Perm
        (a ++ (slotListEvac n G (slotUpdEvac Λ k p [])).flatten)
  | [], n, Λ, 0, p, hp, _ => by
    simp only [slotListEvac, slotUpdEvac, Function.update_self]
    exact layer_update_perm_evac (Λ 0) p a n hp
  | l :: G, n, Λ, 0, p, hp, _ => by
    have h : ∀ b : List MorseWord, (fun j ↦ slotUpdEvac Λ 0 p b (j + 1)) =
        fun j ↦ Λ (j + 1) := fun b ↦ by
      funext j
      simp [slotUpdEvac]
    simp only [slotListEvac, h, List.flatten_append]
    simp only [slotUpdEvac, Function.update_self]
    rw [← List.append_assoc]
    exact (layer_update_perm_evac (Λ 0) p a n hp).append_right _
  | l :: G, n, Λ, k + 1, p, hp, hk => by
    have h : ∀ b : List MorseWord, (fun j ↦ slotUpdEvac Λ (k + 1) p b (j + 1)) =
        slotUpdEvac (fun j ↦ Λ (j + 1)) k p b := fun b ↦ by
      funext j q
      simp [slotUpd_apply_evac]
    have h0 : ∀ b : List MorseWord, slotUpdEvac Λ (k + 1) p b 0 = Λ 0 := fun b ↦ by
      simp [slotUpdEvac]
    simp only [slotListEvac, h, h0, List.flatten_append]
    exact ((slotList_update_perm_evac a G (morseLetterOut n l)
      (fun j ↦ Λ (j + 1)) k p hp (by simpa using hk)).append_left _).trans
        (List.perm_append_comm_assoc _ _ _)

/-- The slots of a word with one more letter. -/
private theorem slotList_concat_evac {α : Type} (l : MorseLetter) :
    ∀ (G : MorseWord) (n : ℕ) (f : ℕ → ℕ → α), slotListEvac n (G ++ [l]) f =
      slotListEvac n G f ++ (List.range (morseLetterOut (morseOut n G) l)).map (f (G.length + 1))
  | [], _, _ => rfl
  | a :: G, n, f => by
    have ih := slotList_concat_evac l G (morseLetterOut n a) (fun k ↦ f (k + 1))
    simp only [List.cons_append, slotListEvac, ih, List.append_assoc, morseOut, List.length_cons]

/-- The slot word of a word with one more letter. -/
private theorem isoSlotWord_concat_evac (l : MorseLetter) :
    ∀ (G : MorseWord) (n : ℕ) (β : ℕ → ℕ → MorseWord), isoSlotWord n (G ++ [l]) β =
      isoSlotWord n G β ++ morseDoubleLetter l ++
        isoLayer (morseLetterOut (morseOut n G) l) (β (G.length + 1))
  | [], _, _ => rfl
  | a :: G, n, β => by
    have ih := isoSlotWord_concat_evac l G (morseLetterOut n a) (fun k ↦ β (k + 1))
    simp only [List.cons_append, isoSlotWord, ih, List.append_assoc, morseOut, List.length_cons]

/-- A doubled letter fits on the doubled strands. -/
private theorem morseDoubleLetter_fits_evac (n e : ℕ) (l : MorseLetter)
    (h : l.2 + morseKindIn l.1 ≤ n) :
    morseFits (2 * n + e) (morseDoubleLetter l) = true ∧
      morseOut (2 * n + e) (morseDoubleLetter l) = 2 * morseLetterOut n l + e := by
  have h1 := morseFits_isoSlotWord n e [l] (fun _ _ ↦ [])
    (by rw [morseFits_cons]; exact ⟨h, rfl⟩) (fun _ _ ↦ ⟨rfl, rfl⟩)
  rw [isoSlotWord_nil] at h1
  simpa [morseDouble, morseOut] using h1

/-- A tangle above a slot word joins the top of the slot of its band at the top level. -/
private theorem morseReach_isoSlotWord_top_evac (n₀ e : ℕ) (T v : MorseWord)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) :
    ∀ (G : MorseWord) (n p : ℕ) (u : MorseWord) (β : ℕ → ℕ → MorseWord),
      morseFits n G = true → IsoSlotValid β → p < morseOut n G → morseOut n₀ u = 2 * n + e →
      MorseReach n₀ (u ++ isoSlotWord n G β ++ morseShiftWord (2 * p) T ++ v)
        (u ++ isoSlotWord n G (slotUpdEvac β G.length p (β G.length p ++ T)) ++ v)
  | [], n, p, u, β, _, hβ, hp, hu =>
    morseReach_isoLayer_top_evac n₀ (2 * n + e) T hT hTo n p (β 0) u v (hβ 0) hp (by omega) hu
  | l :: G, n, p, u, β, hG, hβ, hp, hu => by
    rw [morseFits_cons] at hG
    have hl₀ := isoLayer_fits_evac (2 * n + e) (β 0) (hβ 0) n (by omega)
    have hd := morseDoubleLetter_fits_evac n e l hG.1
    have ih := morseReach_isoSlotWord_top_evac n₀ e T v hT hTo G (morseLetterOut n l) p
      (u ++ isoLayer n (β 0) ++ morseDoubleLetter l) (fun k ↦ β (k + 1)) hG.2
      (fun k q ↦ hβ (k + 1) q) hp (by rw [morseOut_append, morseOut_append, hu, hl₀.2, hd.2])
    have h1 : ∀ γ : ℕ → ℕ → MorseWord, isoSlotWord n (l :: G) γ =
        isoLayer n (γ 0) ++ morseDoubleLetter l ++
          isoSlotWord (morseLetterOut n l) G (fun k ↦ γ (k + 1)) := fun _ ↦ rfl
    have h2 : ∀ a : MorseWord, (fun k ↦ slotUpdEvac β (G.length + 1) p a (k + 1)) =
        slotUpdEvac (fun k ↦ β (k + 1)) G.length p a := fun a ↦ by
      funext j q
      simp [slotUpd_apply_evac]
    have h3 : ∀ a : MorseWord, slotUpdEvac β (G.length + 1) p a 0 = β 0 := fun a ↦ by
      simp [slotUpdEvac]
    rw [h1, h1, List.length_cons, h3, h2]
    simpa only [List.append_assoc] using ih

/-- Every entry of the list is a value of the function. -/
private theorem mem_slotList_evac {α : Type} (n : ℕ) (G : MorseWord) (f : ℕ → ℕ → α)
    (a : α) (h : a ∈ slotListEvac n G f) : ∃ k p, a = f k p := by
  induction G generalizing n f with
  | nil =>
    simp only [slotListEvac, List.mem_map] at h
    obtain ⟨p, -, rfl⟩ := h
    exact ⟨0, p, rfl⟩
  | cons l G ih =>
    simp only [slotListEvac, List.mem_append, List.mem_map] at h
    rcases h with ⟨p, -, rfl⟩ | h
    · exact ⟨0, p, rfl⟩
    · obtain ⟨k, p, rfl⟩ := ih _ _ h
      exact ⟨k + 1, p, rfl⟩

/-! ### Pieces of the slots -/

/-- A concatenation of tangles on the band is a tangle on the band. -/
private theorem flatten_valid_evac : ∀ L : List MorseWord,
    (∀ w ∈ L, morseFits 2 w = true ∧ morseOut 2 w = 2) →
    morseFits 2 L.flatten = true ∧ morseOut 2 L.flatten = 2
  | [], _ => ⟨rfl, rfl⟩
  | a :: L, h => by
    have ha := h a List.mem_cons_self
    have ih := flatten_valid_evac L fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
    rw [List.flatten_cons, morseFits_append, morseOut_append, ha.1, ha.2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- The rotation of a concatenation of tangles on the band. -/
private theorem flatten_rot_evac : ∀ L : List MorseWord,
    (∀ w ∈ L, morseFits 2 w = true ∧ morseOut 2 w = 2) →
    (L.reverse.map (isoRot 2)).flatten = isoRot 2 L.flatten
  | [], _ => rfl
  | a :: L, h => by
    have ha := h a List.mem_cons_self
    rw [List.reverse_cons, List.map_append, List.flatten_append,
      flatten_rot_evac L fun w hw ↦ h w (List.mem_cons_of_mem _ hw), List.flatten_cons,
      isoRot_append, ha.2]
    simp

/-- Rotated permutations of two lists give a rotated permutation of their concatenation. -/
private theorem isoRotPerm_append_evac {A A' B B' : List MorseWord} (hA : IsoRotPerm A A')
    (hB : IsoRotPerm B B') : IsoRotPerm (A ++ B) (A' ++ B') := by
  obtain ⟨LA, hpA, hfA⟩ := hA
  obtain ⟨LB, hpB, hfB⟩ := hB
  exact ⟨LA ++ LB, hpA.append hpB, List.rel_append hfA hfB⟩

/-- A rotated permutation of the slots, each slot a concatenation of pieces, gives a rotated
permutation of the pieces with the same concatenation. -/
private theorem isoRotPerm_pieces_evac : ∀ (L₀' L₀ : List MorseWord),
    List.Forall₂ (fun a b : MorseWord ↦ b = a ∨ b = isoRot 2 a) L₀' L₀ →
    ∀ M : List (List MorseWord), L₀'.Perm (M.map List.flatten) →
      (∀ m ∈ M, ∀ w ∈ m, morseFits 2 w = true ∧ morseOut 2 w = 2) →
      ∃ L : List MorseWord, IsoRotPerm M.flatten L ∧ L.flatten = L₀.flatten
  | _, _, .nil, M, hM, _ => by
    have h : M = [] := by simpa using hM.symm.eq_nil
    subst h
    exact ⟨[], ⟨[], List.Perm.refl _, List.Forall₂.nil⟩, rfl⟩
  | _, _, @List.Forall₂.cons _ _ _ a' a L₀'' L₀t hab htl, M, hM, hv => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (hM.subset List.mem_cons_self)
    have hMp := List.perm_cons_erase hm
    have h1 : L₀''.Perm ((M.erase m).map List.flatten) :=
      (hM.trans (hMp.map List.flatten)).cons_inv
    obtain ⟨Lt, hLt, hfl⟩ := isoRotPerm_pieces_evac L₀'' L₀t htl (M.erase m) h1
      fun m' hm' ↦ hv m' (List.mem_of_mem_erase hm')
    have hMf : M.flatten.Perm (m ++ (M.erase m).flatten) := hMp.flatten
    rcases hab with rfl | rfl
    · exact ⟨m ++ Lt, isoRotPerm_of_perm hMf.symm (isoRotPerm_append_evac
        ⟨m, List.Perm.refl _, List.forall₂_same.2 fun _ _ ↦ Or.inl rfl⟩ hLt),
        by rw [List.flatten_append, hfl, List.flatten_cons]⟩
    · exact ⟨m.reverse.map (isoRot 2) ++ Lt, isoRotPerm_of_perm hMf.symm
        (isoRotPerm_append_evac ⟨m.reverse, List.reverse_perm m,
          List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun _ _ ↦ Or.inr rfl)⟩ hLt),
        by rw [List.flatten_append, hfl, flatten_rot_evac m (hv m hm), List.flatten_cons]⟩

/-- A beaded word reaches a slot word whose slots are concatenations of the beads. -/
private theorem isoBeaded_slot_gen_evac (n₀ e : ℕ) {n : ℕ} {G W : MorseWord}
    {Bs : List MorseWord} (hW : IsoBeaded n G W Bs) : morseFits n G = true →
    ∃ Λ : ℕ → ℕ → List MorseWord,
      (∀ k p, ∀ w ∈ Λ k p, morseFits 2 w = true ∧ morseOut 2 w = 2) ∧
      (∀ k, G.length < k → ∀ p, Λ k p = []) ∧
      ((slotListEvac n G Λ).flatten).Perm Bs ∧
      ∀ u v : MorseWord, morseOut n₀ u = 2 * n + e →
        MorseReach n₀ (u ++ W ++ v)
          (u ++ isoSlotWord n G (fun k p ↦ (Λ k p).flatten) ++ v) := by
  induction hW with
  | nil =>
    intro _
    refine ⟨fun _ _ ↦ [], fun _ _ w hw ↦ by simp at hw, fun _ _ _ ↦ rfl, ?_, fun u v _ ↦ ?_⟩
    · simp [slotListEvac]
    · have h : isoSlotWord n [] (fun _ _ ↦ ([] : List MorseWord).flatten) = [] :=
        isoLayer_nil_evac n _ (fun _ _ ↦ rfl)
      rw [h]
      exact morseReach_refl _ _
  | @letter G W Bs l _ ih =>
    intro hG
    rw [morseFits_append, Bool.and_eq_true] at hG
    obtain ⟨Λ, hv, hup, hperm, hr⟩ := ih hG.1
    refine ⟨Λ, hv, fun k hk p ↦ hup k (by simp at hk; omega) p, ?_, fun u v hu ↦ ?_⟩
    · have h0 : ((List.range (morseLetterOut (morseOut n G) l)).map
          (Λ (G.length + 1))).flatten = [] := by
        rw [List.flatten_eq_nil_iff]
        intro w hw
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
        exact hup _ (by omega) p
      rw [slotList_concat_evac, List.flatten_append, h0, List.append_nil]
      exact hperm
    · rw [isoSlotWord_concat_evac, isoLayer_nil_evac _ _ (fun p _ ↦ by
        simp only [hup (G.length + 1) (by omega) p, List.flatten_nil]), List.append_nil]
      have h := hr u (morseDoubleLetter l ++ v) hu
      simpa only [List.append_assoc] using h
  | @bead G W Bs p T _ hp hT hTo ih =>
    intro hG
    obtain ⟨Λ, hv, hup, hperm, hr⟩ := ih hG
    refine ⟨slotUpdEvac Λ G.length p (Λ G.length p ++ [T]), ?_, ?_, ?_, fun u v hu ↦ ?_⟩
    · intro k q w hw
      rw [slotUpd_apply_evac] at hw
      split_ifs at hw
      · rcases List.mem_append.1 hw with hw | hw
        · exact hv _ _ w hw
        · rw [List.mem_singleton.1 hw]
          exact ⟨hT, hTo⟩
      · exact hv k q w hw
    · intro k hk q
      rw [slotUpd_apply_evac]
      split_ifs with hc
      · omega
      · exact hup k hk q
    · have h1 := slotList_update_perm_evac (Λ G.length p ++ [T]) G n Λ G.length p
        (by rwa [List.take_length]) le_rfl
      have h2 := slotList_update_perm_evac (Λ G.length p) G n Λ G.length p
        (by rwa [List.take_length]) le_rfl
      rw [slotUpd_eq_self_evac] at h2
      refine h1.trans (List.Perm.trans ?_ ((h2.symm.trans hperm).append_right [T]))
      rw [List.append_assoc, List.append_assoc]
      exact List.perm_append_comm.append_left _
    · have hβ : IsoSlotValid fun k p ↦ (Λ k p).flatten :=
        fun k q ↦ flatten_valid_evac _ (hv k q)
      have ha := hr u (morseShiftWord (2 * p) T ++ v) hu
      have hb := morseReach_isoSlotWord_top_evac n₀ e T v hT hTo G n p u _ hG hβ hp hu
      have he : (fun k q ↦ (slotUpdEvac Λ G.length p (Λ G.length p ++ [T]) k q).flatten) =
          slotUpdEvac (fun k p ↦ (Λ k p).flatten) G.length p ((Λ G.length p).flatten ++ T) := by
        funext k q
        simp only [slotUpd_apply_evac]
        split_ifs <;> simp
      rw [he]
      simp only [List.append_assoc] at ha hb ⊢
      exact morseReach_trans ha hb

/-- A beaded word reaches its slot form; a rotated permutation of the slots is a rotated
permutation of the beads. -/
theorem morseReach_isoBeaded_slot (G W u v : MorseWord) (Bs : List MorseWord) (n₀ e : ℕ)
    (hG : morseFits 1 G = true) (hW : IsoBeaded 1 G W Bs) (hu : morseOut n₀ u = 2 + e) :
    ∃ β : ℕ → ℕ → MorseWord, IsoSlotValid β ∧
      MorseReach n₀ (u ++ W ++ v) (u ++ isoSlotWord 1 G β ++ v) ∧
      ∀ L₀ : List MorseWord, IsoRotPerm (isoSlotBeads 1 G β) L₀ →
        ∃ L : List MorseWord, IsoRotPerm Bs L ∧ L.flatten = L₀.flatten := by
  obtain ⟨Λ, hv, -, hperm, hr⟩ := isoBeaded_slot_gen_evac n₀ e hW hG
  refine ⟨fun k p ↦ (Λ k p).flatten, fun k p ↦ flatten_valid_evac _ (hv k p),
    hr u v (by rw [hu]), ?_⟩
  rintro L₀ ⟨L₀', hp, hf⟩
  have hb : isoSlotBeads 1 G (fun k p ↦ (Λ k p).flatten) =
      (slotListEvac 1 G Λ).map List.flatten := by
    rw [isoSlotBeads_eq_evac, slotList_map_evac]
  rw [hb] at hp
  obtain ⟨L, hL, hfl⟩ := isoRotPerm_pieces_evac L₀' L₀ hf _ hp fun m hm w hw ↦ by
    obtain ⟨k, p, rfl⟩ := mem_slotList_evac 1 G Λ m hm
    exact hv k p w hw
  exact ⟨L, isoRotPerm_of_perm hperm hL, hfl⟩

/-- Evacuation: the beads of a doubled connected long knot move to its top end. -/
theorem morseReach_isoBeaded_evac (G W u v : MorseWord) (Bs : List MorseWord) (n₀ e : ℕ)
    (hG : morseFits 1 G = true ∧ morseOut 1 G = 1) (hc : IsoConnected G)
    (hW : IsoBeaded 1 G W Bs) (hu : morseOut n₀ u = 2 + e) :
    ∃ L : List MorseWord, IsoRotPerm Bs L ∧
      MorseReach n₀ (u ++ W ++ v) (u ++ morseDouble G ++ L.flatten ++ v) := by
  obtain ⟨β, hβ, h1, h2⟩ := morseReach_isoBeaded_slot G W u v Bs n₀ e hG.1 hW hu
  obtain ⟨L₀, hL₀, h3⟩ := morseReach_isoSlotWord_evac G u v β n₀ e hG hc hβ hu
  obtain ⟨L, hL, hflat⟩ := h2 L₀ hL₀
  exact ⟨L, hL, hflat ▸ morseReach_trans h1 h3⟩

end AJConjecture
