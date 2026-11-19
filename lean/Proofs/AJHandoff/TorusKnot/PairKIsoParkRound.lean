import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkComm
import AJHandoff.TorusKnot.PairKIsoBeadStep

/-!
# Stage C by ports: a band bead rides the conveyor

One doubled round `morseDouble (walkL q (r - 1))` (`q = r - 2`) moves the band `q + a` to the band
`q + (a + 1) mod r`: for `a ≤ r - 2` the band shifts right across one doubled crossing, for
`a = r - 1` it is the moving band and walks left across all `r - 1` doubled crossings.

`morseReach_park_round`: a band bead before the round on the band `q + a` reaches the band
`q + (a + 1) mod r` after it. Proof: for `a ≤ r - 2`, exchanges past the doubled crossings at
positions `> q + a` (`morseReach_isoBead_commR`), one `morseReach_beadD_left` (shifted by
`morseReach_frame`), exchanges past the rest (`morseReach_isoBead_commL`, no shift); for
`a = r - 1`, `r - 1` times `morseReach_beadD_right`.
`morseReach_park_conv`: `t` rounds, by induction on `t`.
-/

namespace AJConjecture


/-- A doubled positive crossing is a shifted `phaseTwoD`. -/
private theorem morseDoubleLetter_cross_park (j : ℕ) :
    morseDoubleLetter (MorseKind.cross true, j) = morseShiftWord (2 * j) phaseTwoD := by
  simp [morseDoubleLetter, morseOfBraid, cable, cableGen, phaseTwoD, morseShiftWord, shiftLetter,
    List.range_succ]
  omega

/-- A leftward walk grows at the front. -/
private theorem morseWalkL_succ_park (s : Bool) (p len : ℕ) :
    morseWalkL s p (len + 1) = (MorseKind.cross s, p + len) :: morseWalkL s p len := by
  simp [morseWalkL, List.range_succ]

/-- A leftward walk splits at one of its crossings. -/
private theorem morseWalkL_split_park (s : Bool) (p a b : ℕ) :
    morseWalkL s p (a + 1 + b) =
      morseWalkL s (p + a + 1) b ++ [(MorseKind.cross s, p + a)] ++ morseWalkL s p a := by
  induction b with
  | zero =>
    rw [Nat.add_zero, morseWalkL_succ_park]
    rfl
  | succ b ih =>
    rw [← Nat.add_assoc, morseWalkL_succ_park, ih, morseWalkL_succ_park]
    simp only [List.cons_append]
    congr 2
    omega

/-- The letters of a doubled leftward walk. -/
private theorem mem_morseDouble_walkL_park {p len : ℕ} {l : MorseLetter}
    (hl : l ∈ morseDouble (morseWalkL true p len)) :
    l.1 = MorseKind.cross true ∧ 2 * p ≤ l.2 ∧ l.2 + 2 ≤ 2 * (p + len) + 2 := by
  induction len with
  | zero => simp [morseWalkL, morseDouble] at hl
  | succ len ih =>
    rw [morseWalkL_succ_park, morseDouble, List.flatMap_cons, ← morseDouble,
      morseDoubleLetter_cross_park, List.mem_append] at hl
    rcases hl with hl | hl
    · simp only [phaseTwoD, morseShiftWord, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, shiftLetter] at hl
      rcases hl with rfl | rfl | rfl | rfl <;>
        exact ⟨rfl, by simp only; omega, by simp only; omega⟩
    · obtain ⟨h1, h2, h3⟩ := ih hl
      exact ⟨h1, h2, by omega⟩

/-- A shifted doubled crossing keeps the number of strands. -/
private theorem morseOut_shift_phaseTwoD_park (n d : ℕ) :
    morseOut n (morseShiftWord d phaseTwoD) = n := by
  simp [morseShiftWord, phaseTwoD, morseOut, morseLetterOut, morseKindIn, morseKindOut,
    shiftLetter]

/-- A doubled leftward walk keeps the number of strands and fits on enough strands. -/
private theorem morseDouble_walkL_fits_park (p len n : ℕ) (hn : 2 * (p + len) + 2 ≤ n) :
    morseFits n (morseDouble (morseWalkL true p len)) = true ∧
      morseOut n (morseDouble (morseWalkL true p len)) = n := by
  have hc : ∀ b ∈ morseDouble (morseWalkL true p len), ∃ s, b.1 = MorseKind.cross s :=
    fun b hb ↦ ⟨true, (mem_morseDouble_walkL_park hb).1⟩
  exact ⟨morseFits_of_cross _ _ hc fun b hb ↦ by
    have := (mem_morseDouble_walkL_park hb).2.2; omega, morseOut_of_cross _ _ hc⟩

/-- A band bead on the right band of a doubled crossing passes it (any shift). -/
private theorem morseReach_beadD_right_park (n₀ p : ℕ) (T u v : MorseWord)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) (hu : 2 * p + 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p + 2) T ++ morseShiftWord (2 * p) phaseTwoD ++ v)
      (u ++ morseShiftWord (2 * p) phaseTwoD ++ morseShiftWord (2 * p) T ++ v) := by
  have h := morseReach_beadD_right 4 [] T [] hT hTo le_rfl
  have hf : morseFits 4 (morseShiftWord 2 T ++ phaseTwoD) = true := by
    have h1 := morseOut_shift_iso 2 2 0 T hT
    rw [morseFits_append, h1.2, h1.1, hTo]
    rfl
  have h2 := morseReach_frame 4 n₀ (2 * p) (morseOut n₀ u - 2 * p - 4) u v _ _
    (by simpa using h) hf (by omega)
  rw [morseShiftWord_append, morseShiftWord_append, morseShiftWord_shift_iso,
    Nat.add_comm 2 (2 * p)] at h2
  simpa only [List.append_assoc] using h2

/-- A band bead on the moving band rides a doubled leftward walk. -/
private theorem morseReach_walk_moving_park (n₀ : ℕ) (T v : MorseWord)
    (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) (p : ℕ) :
    ∀ (len : ℕ) (u : MorseWord), 2 * (p + len) + 2 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseShiftWord (2 * (p + len)) T ++
          morseDouble (morseWalkL true p len) ++ v)
        (u ++ morseDouble (morseWalkL true p len) ++ morseShiftWord (2 * p) T ++ v)
  | 0, u, _ => by simpa [morseWalkL, morseDouble] using morseReach_refl n₀ _
  | len + 1, u, hu => by
    rw [morseWalkL_succ_park, morseDouble, List.flatMap_cons, ← morseDouble,
      morseDoubleLetter_cross_park]
    have h1 := morseReach_beadD_right_park n₀ (p + len) T u
      (morseDouble (morseWalkL true p len) ++ v) hT hTo (by omega)
    have h2 := morseReach_walk_moving_park n₀ T v hT hTo p len
      (u ++ morseShiftWord (2 * (p + len)) phaseTwoD)
      (by rw [morseOut_append, morseOut_shift_phaseTwoD_park]; omega)
    rw [show 2 * (p + (len + 1)) = 2 * (p + len) + 2 by ring]
    simp only [List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- Doubling commutes with repetition. -/
theorem morseDouble_phaseTwoBlk (w : MorseWord) (t : ℕ) :
    morseDouble (phaseTwoBlk w t) = phaseTwoBlk (morseDouble w) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons, morseDouble,
      List.flatMap_append] at ih ⊢
    rw [ih]

/-- A band bead rides one doubled round of the conveyor. -/
theorem morseReach_park_round (n₀ r a : ℕ) (T u v : MorseWord) (hr : 3 ≤ r) (ha : a < r)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) (hu : 4 * r - 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (2 * (r - 2 + a)) T ++
        morseDouble (morseWalkL true (r - 2) (r - 1)) ++ v)
      (u ++ morseDouble (morseWalkL true (r - 2) (r - 1)) ++
        morseShiftWord (2 * (r - 2 + (a + 1) % r)) T ++ v) := by
  rcases Nat.lt_or_ge a (r - 1) with ha' | ha'
  · -- the bead is on a band crossed by the moving strand
    rw [Nat.mod_eq_of_lt (show a + 1 < r by omega)]
    have hsplit := morseWalkL_split_park true (r - 2) a (r - 2 - a)
    rw [show a + 1 + (r - 2 - a) = r - 1 by omega] at hsplit
    rw [hsplit, morseDouble, List.flatMap_append, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, ← morseDouble, ← morseDouble,
      morseDoubleLetter_cross_park]
    set W1 := morseDouble (morseWalkL true (r - 2 + a + 1) (r - 2 - a))
    set W0 := morseDouble (morseWalkL true (r - 2) a)
    have hW1 := morseDouble_walkL_fits_park (r - 2 + a + 1) (r - 2 - a) (morseOut n₀ u)
      (by omega)
    have hA := morseReach_isoBead_commR n₀ (2 * (r - 2 + a)) 2 T u W1
      (morseShiftWord (2 * (r - 2 + a)) phaseTwoD ++ W0 ++ v) hT hTo
      (fun l hl ↦ by have := (mem_morseDouble_walkL_park hl).2.1; omega) hW1.1 (by omega)
    have hB := morseReach_isoBead_D n₀ (r - 2 + a) T (u ++ W1) (W0 ++ v) hT hTo
      (by rw [morseOut_append, hW1.2]; omega)
    have hW0 := morseDouble_walkL_fits_park (r - 2) a (2 * (r - 2 + a) + 2) (by omega)
    have hC := morseReach_isoBead_commL n₀ (2 * (r - 2 + a) + 2) 2
      (morseOut n₀ u - (2 * (r - 2 + a) + 4)) T
      (u ++ W1 ++ morseShiftWord (2 * (r - 2 + a)) phaseTwoD) W0 v hT hTo hW0.1
      (by rw [morseOut_append, morseOut_append, hW1.2, morseOut_shift_phaseTwoD_park]; omega)
    rw [hW0.2, show 2 * (r - 2 + a) + 2 = 2 * (r - 2 + (a + 1)) by ring] at hC
    rw [show 2 * (r - 2 + a) + 2 = 2 * (r - 2 + (a + 1)) by ring] at hB
    simp only [List.append_assoc] at hA hB hC ⊢
    exact morseReach_trans hA (morseReach_trans hB hC)
  · -- the bead is on the moving band
    obtain rfl : a = r - 1 := by omega
    rw [show r - 1 + 1 = r by omega, Nat.mod_self, Nat.add_zero]
    have h := morseReach_walk_moving_park n₀ T v hT hTo (r - 2) (r - 1) u (by omega)
    rwa [show r - 2 + (r - 1) = r - 2 + (r - 1) from rfl] at h

/-- A band bead rides `t` doubled rounds of the conveyor. -/
theorem morseReach_park_conv (n₀ r a t : ℕ) (T u v : MorseWord) (hr : 3 ≤ r) (ha : a < r)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) (hu : 4 * r - 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (2 * (r - 2 + a)) T ++
        morseDouble (phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) t) ++ v)
      (u ++ morseDouble (phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) t) ++
        morseShiftWord (2 * (r - 2 + (a + t) % r)) T ++ v) := by
  induction t generalizing a u with
  | zero =>
    rw [Nat.add_zero, Nat.mod_eq_of_lt ha]
    simpa [phaseTwoBlk, morseDouble] using morseReach_refl n₀ _
  | succ t ih =>
    have hb : phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) (t + 1) =
        morseWalkL true (r - 2) (r - 1) ++ phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) t := by
      simp [phaseTwoBlk, List.replicate_succ]
    have hWf := morseDouble_walkL_fits_park (r - 2) (r - 1) (morseOut n₀ u) (by omega)
    rw [hb, morseDouble, List.flatMap_append, ← morseDouble, ← morseDouble]
    have h1 := morseReach_park_round n₀ r a T u
      (morseDouble (phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) t) ++ v) hr ha hT hTo hu
    have h2 := ih ((a + 1) % r) (u ++ morseDouble (morseWalkL true (r - 2) (r - 1)))
      (Nat.mod_lt _ (by omega)) (by rw [morseOut_append, hWf.2]; exact hu)
    rw [Nat.mod_add_mod, show a + 1 + t = a + (t + 1) by ring] at h2
    simp only [List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-! ### Bookkeeping for the port words -/

/-- A list of port stacks keeps the number of strands and fits when every port fits. -/
theorem morseFits_portW_park (r : ℕ) (S : ℕ → List IsoBead) : ∀ (cs : List ℕ) (n : ℕ),
    (∀ c ∈ cs, 2 * (r - 2 + c) + 2 ≤ n) →
    morseFits n (cs.flatMap fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) =
        true ∧
      morseOut n (cs.flatMap fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) = n
  | [], _, _ => ⟨rfl, rfl⟩
  | c :: cs, n, h => by
    have hc := h c List.mem_cons_self
    obtain ⟨e, rfl⟩ : ∃ e, n = 2 * (r - 2 + c) + 2 + e :=
      ⟨n - (2 * (r - 2 + c) + 2), by omega⟩
    have hB := morseOut_shift_iso (2 * (r - 2 + c)) 2 e (isoBeadsWord (S c))
      (morseFits_isoBeadsWord (S c) 0).1
    rw [(morseFits_isoBeadsWord (S c) 0).2] at hB
    have ih := morseFits_portW_park r S cs _ fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    rw [List.flatMap_cons, morseFits_append, morseOut_append, hB.1, hB.2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- The letters of a list of port stacks lie on the ports. -/
theorem mem_portW_park {r : ℕ} {S : ℕ → List IsoBead} {cs : List ℕ} {l : MorseLetter}
    (hl : l ∈ cs.flatMap fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) :
    ∃ c ∈ cs, 2 * (r - 2 + c) ≤ l.2 := by
  obtain ⟨c, hc, hl⟩ := List.mem_flatMap.1 hl
  obtain ⟨l0, -, rfl⟩ := List.mem_map.1 hl
  exact ⟨c, hc, by simp [shiftLetter]⟩

/-- A flatMap over `range r` splits at `a < r`. -/
theorem flatMap_range_split_park {β : Type} (f : ℕ → List β) (r a : ℕ) (ha : a < r) :
    (List.range r).flatMap f = (List.range a).flatMap f ++ f a ++
      ((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i)).flatMap f := by
  conv_lhs => rw [show r = (a + 1) + (r - 1 - a) by omega]
  rw [List.range_add, List.range_succ, List.flatMap_append, List.flatMap_append]
  simp

/-- Updating a stack outside the listed ports changes nothing. -/
theorem flatMap_update_park {β : Type} (g : List IsoBead → ℕ → List β)
    (S : ℕ → List IsoBead)
    (a : ℕ) (Y : List IsoBead) : ∀ (cs : List ℕ), a ∉ cs →
    cs.flatMap (fun c ↦ g (Function.update S a Y c) c) = cs.flatMap (fun c ↦ g (S c) c)
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, flatMap_update_park g S a Y cs (fun h' ↦ h
      (List.mem_cons_of_mem _ h'))]
    have hne : c ≠ a := fun e ↦ h (e ▸ List.mem_cons_self)
    rw [Function.update_of_ne hne]

/-- The stacks of a list of beads concatenate. -/
theorem isoBeadsWord_append_park (L M : List IsoBead) :
    isoBeadsWord (L ++ M) = isoBeadsWord L ++ isoBeadsWord M := List.flatMap_append

/-- Doubled nested left cups: they fit on any number of strands. -/
theorem morseDouble_cups_fits_park (j : ℕ) : ∀ (c n : ℕ), 2 * j ≤ n →
    morseFits n (morseDouble ((List.range c).map fun i ↦ isoU (j + i))) = true ∧
      morseOut n (morseDouble ((List.range c).map fun i ↦ isoU (j + i))) = n + 4 * c
  | 0, _, _ => ⟨rfl, rfl⟩
  | c + 1, n, h => by
    obtain ⟨h1, h2⟩ := morseDouble_cups_fits_park j c n h
    rw [List.range_succ, List.map_append, morseDouble, List.flatMap_append, ← morseDouble,
      morseFits_append, morseOut_append, h1, h2]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      morseDoubleLetter, isoU, morseFits_cons, morseFits_nil, morseOut, morseLetterOut,
      morseKindIn, morseKindOut, Bool.true_and]
    exact ⟨⟨by omega, by omega, trivial⟩, by omega⟩

/-- The letters of doubled cups `u_j, …, u_{j+c-1}`. -/
theorem mem_morseDouble_cups_park {j c : ℕ} {l : MorseLetter}
    (hl : l ∈ morseDouble ((List.range c).map fun i ↦ isoU (j + i))) :
    l.1 = MorseKind.cup ∧ 2 * j ≤ l.2 := by
  simp only [morseDouble, List.flatMap_map, List.mem_flatMap, List.mem_range] at hl
  obtain ⟨i, -, hl⟩ := hl
  simp only [morseDoubleLetter, isoU, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> exact ⟨rfl, by simp only; omega⟩

/-- Doubled cups `u_j, …, u_{j+c-1}` split off the first. -/
theorem morseDouble_cups_succ_park (j c : ℕ) :
    morseDouble ((List.range (c + 1)).map fun i ↦ isoU (j + i)) =
      morseDouble [isoU j] ++ morseDouble ((List.range c).map fun i ↦ isoU (j + 1 + i)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [morseDouble, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
  congr 2
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.succ_eq_add_one]
  congr 1
  omega

/-- Doubled nested caps `n_{j+c-1}, …, n_j`: fit and remove `4c` strands. -/
theorem morseDouble_caps_fits_park (j : ℕ) : ∀ (c n : ℕ), 2 * j + 4 * c ≤ n →
    morseFits n (morseDouble ((List.range c).reverse.map fun i ↦ isoN (j + i))) = true ∧
      morseOut n (morseDouble ((List.range c).reverse.map fun i ↦ isoN (j + i))) = n - 4 * c
  | 0, _, _ => ⟨rfl, rfl⟩
  | c + 1, n, h => by
    obtain ⟨h1, h2⟩ := morseDouble_caps_fits_park j c (n - 4) (by omega)
    rw [List.range_succ, List.reverse_append, List.map_append, morseDouble, List.flatMap_append,
      ← morseDouble, ← morseDouble]
    have hd : morseDouble (List.map (fun i ↦ isoN (j + i)) [c].reverse) =
        [(MorseKind.cap, 2 * (j + c) + 1), (MorseKind.cap, 2 * (j + c))] := rfl
    have ho : morseOut n [(MorseKind.cap, 2 * (j + c) + 1), (MorseKind.cap, 2 * (j + c))] =
        n - 4 := by
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]; omega
    have hf : morseFits n [(MorseKind.cap, 2 * (j + c) + 1), (MorseKind.cap, 2 * (j + c))] =
        true := by
      simp only [morseFits_cons, morseFits_nil, morseLetterOut, morseKindIn, morseKindOut,
        and_true]
      omega
    rw [hd, morseFits_append, morseOut_append, ho, hf, h1, h2]
    exact ⟨rfl, by omega⟩

/-- The letters of doubled caps `n_{j+c-1}, …, n_j`. -/
theorem mem_morseDouble_caps_park {j c : ℕ} {l : MorseLetter}
    (hl : l ∈ morseDouble ((List.range c).reverse.map fun i ↦ isoN (j + i))) :
    l.1 = MorseKind.cap ∧ 2 * j ≤ l.2 := by
  simp only [morseDouble, List.flatMap_map, List.mem_flatMap, List.mem_reverse,
    List.mem_range] at hl
  obtain ⟨i, -, hl⟩ := hl
  simp only [morseDoubleLetter, isoN, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> exact ⟨rfl, by simp only; omega⟩

/-- Nested cups split at one of them. -/
theorem cups_split_park (j c : ℕ) :
    (List.range (j + 1 + c)).map isoU = (List.range j).map isoU ++ [isoU j] ++
      (List.range c).map fun i ↦ isoU (j + 1 + i) := by
  rw [List.range_add, List.range_succ]
  simp [List.map_append]

/-- Nested caps split at one of them. -/
theorem caps_split_park (j c : ℕ) :
    (List.range (j + 1 + c)).reverse.map isoN =
      ((List.range c).reverse.map fun i ↦ isoN (j + 1 + i)) ++ [isoN j] ++
        (List.range j).reverse.map isoN := by
  rw [List.range_add, List.range_succ]
  simp [List.map_append, List.map_reverse]

/-- A run of nested cups from `0`. -/
theorem cups_zero_park (c : ℕ) :
    (List.range c).map isoU = (List.range c).map fun i ↦ isoU (0 + i) := by simp

/-- A run of nested caps down to `0`. -/
theorem caps_zero_park (c : ℕ) :
    (List.range c).reverse.map isoN = (List.range c).reverse.map fun i ↦ isoN (0 + i) := by simp

/-- The doubled conveyor fits on the strands of the port level and keeps them. -/
theorem morseDouble_pairConv_fits_park (r s n : ℕ) (hr : 3 ≤ r) (hn : 4 * r - 4 ≤ n) :
    morseFits n (morseDouble (pairConv r s)) = true ∧
      morseOut n (morseDouble (pairConv r s)) = n ∧
      ∀ l ∈ morseDouble (pairConv r s), 2 * (r - 2) ≤ l.2 ∧ l.2 + 2 ≤ 4 * r - 4 := by
  have hm : ∀ l ∈ morseDouble (pairConv r s), l.1 = MorseKind.cross true ∧
      2 * (r - 2) ≤ l.2 ∧
      l.2 + 2 ≤ 4 * r - 4 := by
    intro l hl
    rw [pairConv, morseDouble_phaseTwoBlk, phaseTwoBlk, List.mem_flatten] at hl
    obtain ⟨w, hw, hl⟩ := hl
    rw [List.eq_of_mem_replicate hw] at hl
    obtain ⟨h1, h2, h3⟩ := mem_morseDouble_walkL_park hl
    exact ⟨h1, h2, by omega⟩
  have hc : ∀ b ∈ morseDouble (pairConv r s), ∃ s, b.1 = MorseKind.cross s :=
    fun b hb ↦ ⟨true, (hm b hb).1⟩
  exact ⟨morseFits_of_cross _ _ hc fun b hb ↦ by have := (hm b hb).2.2; omega,
    morseOut_of_cross _ _ hc, fun l hl ↦ (hm l hl).2⟩

/-- The doubled cups of the core: they fit after the bottom and open the port level. -/
theorem morseDouble_pairCups_fits_park (r n : ℕ) (hr : 3 ≤ r) (hn : 2 ≤ n) :
    morseFits n (morseDouble (pairCups r)) = true ∧
      morseOut n (morseDouble (pairCups r)) = n + 4 * r - 4 := by
  have h1 := morseDouble_cups_fits_park 0 (r - 2) n (by omega)
  rw [← cups_zero_park] at h1
  rw [pairCups, morseDouble, List.flatMap_append, ← morseDouble, morseFits_append,
    morseOut_append, h1.1, h1.2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, morseDoubleLetter, isoU,
    morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn, morseKindOut,
    Bool.true_and]
  exact ⟨⟨by omega, by omega, trivial⟩, by omega⟩

/-- The number of strands at the port level of a port word. -/
theorem morseOut_park_prefix (r : ℕ) (bot : List IsoBead) (hr : 3 ≤ r) :
    morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r)) = 4 * r - 1 := by
  have hb := morseFits_isoBeadsWord bot 1
  have hc := morseDouble_pairCups_fits_park r 3 hr (by omega)
  rw [morseOut_append, morseOut_append]
  rw [show morseOut 1 [isoU 1] = 2 + 1 from rfl, hb.2, hc.2]
  omega

/-- The port stacks of a port word keep the strands of the port level. -/
theorem morseFits_portW_all_park (r : ℕ) (S : ℕ → List IsoBead) (cs : List ℕ)
    (hcs : ∀ c ∈ cs, c < r) (hr : 3 ≤ r) :
    morseFits (4 * r - 1)
        (cs.flatMap fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) = true ∧
      morseOut (4 * r - 1)
        (cs.flatMap fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) = 4 * r - 1 :=
  morseFits_portW_park r S cs _ fun c hc ↦ by have := hcs c hc; omega

/-- A stack on a port keeps the strands of the port level. -/
theorem morseFits_port_one_park (r a : ℕ) (L : List IsoBead) (ha : a < r) (hr : 3 ≤ r) :
    morseFits (4 * r - 1) (morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord L)) = true ∧
      morseOut (4 * r - 1) (morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord L)) = 4 * r - 1 := by
  have h := morseOut_shift_iso (2 * (r - 2 + a)) 2 (4 * r - 1 - 2 * (r - 2 + a) - 2)
    (isoBeadsWord L) (morseFits_isoBeadsWord L 0).1
  rw [(morseFits_isoBeadsWord L 0).2, show 2 * (r - 2 + a) + 2 +
    (4 * r - 1 - 2 * (r - 2 + a) - 2) = 4 * r - 1 by omega] at h
  exact ⟨h.2, h.1⟩

/-- The port stacks split at the port `a`, with an update there. -/
theorem portW_update_split_park (r a : ℕ) (S : ℕ → List IsoBead) (Y : List IsoBead)
    (ha : a < r) :
    (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c))
        (isoBeadsWord (Function.update S a Y c))) =
      (List.range a).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord Y) ++
        ((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i)).flatMap
          (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) := by
  rw [flatMap_range_split_park _ r a ha, Function.update_self,
    flatMap_update_park (fun L c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord L)) S a Y _
      (by simp),
    flatMap_update_park (fun L c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord L)) S a Y _
      (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; intro x _; omega)]

/-- The port stacks split at the port `a` (no update). -/
theorem portW_split_park (r a : ℕ) (S : ℕ → List IsoBead) (ha : a < r) :
    (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) =
      (List.range a).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord (S a)) ++
        ((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i)).flatMap
          (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) :=
  flatMap_range_split_park _ r a ha

end AJConjecture
