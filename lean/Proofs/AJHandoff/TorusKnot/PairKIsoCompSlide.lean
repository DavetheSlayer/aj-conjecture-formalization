import Mathlib
import AJHandoff.TorusKnot.PairKIsoCompBraid

/-!
# Conjugation by a braid off the first strand (closure slide, generic)

In a long closure, a braid `g` that does not touch the strand `0` slides around the closing arcs:
`morseLongClosure m (g · w · g⁻¹)` reaches `morseLongClosure m w`. Each letter `σ_i` (`i ≥ 1`) of
`g` at the bottom moves onto the return strands (as a crossing of two nested arcs it passes to
their right legs by `cupSlide`-type moves), commutes up past `w` (exchanges: the return strands are
right of every letter of `w`), returns onto the left legs at the caps and cancels against the
letter of `g⁻¹` by `r2`.
-/

namespace AJConjecture

/-- Closes the arity side conditions of a single move. -/
local macro "slide_fits" : tactic =>
  `(tactic| ((simp only [morseRuleLhs, morseRuleRhs, morseRuleOk, morseFits_cons, morseFits_nil,
    decide_eq_true_eq, and_true]) <;> (simp only [morseLetterOut, morseKindIn, morseKindOut]) <;>
    omega))

/-- The cups `u_a, u_{a+1}, …, u_{a+len-1}`. -/
private def slideCups (a len : ℕ) : MorseWord :=
  (List.range len).map fun j ↦ (MorseKind.cup, a + j)

/-- The caps `n_{a+len-1}, …, n_{a+1}, n_a`. -/
private def slideCaps (a len : ℕ) : MorseWord :=
  (List.range len).reverse.map fun j ↦ (MorseKind.cap, a + j)

/-- A row of cups peels at the bottom. -/
private theorem slideCups_succ (a len : ℕ) :
    slideCups a (len + 1) = (MorseKind.cup, a) :: slideCups (a + 1) len := by
  simp only [slideCups, List.range_succ_eq_map, List.map_cons, List.map_map, add_zero]
  congr 1
  exact List.map_congr_left fun j _ ↦ by simp only [Function.comp_apply]; congr 1; omega

/-- A row of cups splits. -/
private theorem slideCups_add (a k l : ℕ) :
    slideCups a (k + l) = slideCups a k ++ slideCups (a + k) l := by
  simp only [slideCups, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ ↦ by simp only [Function.comp_apply]; congr 1; omega

/-- A row of caps peels at the top. -/
private theorem slideCaps_succ (a len : ℕ) :
    slideCaps a (len + 1) = (MorseKind.cap, a + len) :: slideCaps a len := by
  simp [slideCaps, List.range_succ]

/-- A row of caps splits. -/
private theorem slideCaps_add (a k l : ℕ) :
    slideCaps a (k + l) = slideCaps (a + k) l ++ slideCaps a k := by
  simp only [slideCaps, List.range_add, List.reverse_append, List.map_append, List.map_reverse,
    List.map_map]
  congr 2
  exact List.map_congr_left fun j _ ↦ by simp only [Function.comp_apply]; congr 1; omega

/-- A row of cups adds two strands per cup. -/
private theorem morseOut_slideCups (n a len : ℕ) : morseOut n (slideCups a len) = n + 2 * len := by
  rw [morseOut_of_cups _ _ (by simp [slideCups])]
  simp [slideCups]

/-- A row of caps removes two strands per cap. -/
private theorem morseOut_slideCaps (n a len : ℕ) : morseOut n (slideCaps a len) = n - 2 * len := by
  rw [morseOut_of_caps _ _ (by simp [slideCaps])]
  simp [slideCaps]

/-- The long closure in terms of the rows. -/
private theorem morseLongClosure_eq_slide (m : ℕ) (w : BraidWord) :
    morseLongClosure m w = slideCups 1 (m - 1) ++ morseOfBraid w ++ slideCaps 1 (m - 1) := by
  simp only [morseLongClosure, slideCups, slideCaps]
  congr 1
  · congr 1
    exact List.map_congr_left fun j _ ↦ by rw [Nat.add_comm]
  · exact List.map_congr_left fun j _ ↦ by rw [Nat.add_comm]

/-- The cup macro: a crossing on the left legs of two nested cups moves to their right legs. -/
private theorem morseReach_cupMacro (ε : Bool) :
    MorseReach 0 [(MorseKind.cup, 0), (MorseKind.cup, 1), (MorseKind.cross ε, 0)]
      [(MorseKind.cup, 0), (MorseKind.cup, 1), (MorseKind.cross ε, 2)] :=
  ⟨[(1, .cupSlide 1 ε true, true), (0, .exch (.cup, 0) (.cup, 0), false),
    (3, .exch (.cross ε, 0) (.cross ε, 2), true), (1, .cupSlide 0 ε false, false)], by
    cases ε <;> decide⟩

/-- The cap macro: a crossing on the right legs of two nested caps moves to their left legs. -/
private theorem morseReach_capMacro (ε : Bool) :
    MorseReach 4 [(MorseKind.cross ε, 2), (MorseKind.cap, 1), (MorseKind.cap, 0)]
      [(MorseKind.cross ε, 0), (MorseKind.cap, 1), (MorseKind.cap, 0)] :=
  ⟨[(1, .capSlide 0 ε true, true), (0, .exch (.cross ε, 0) (.cross ε, 2), true),
    (3, .exch (.cap, 0) (.cap, 2), false), (1, .capSlide 1 ε false, false)], by
    cases ε <;> decide⟩

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_slide (w : MorseWord) : morseShiftWord 0 w = w := by
  unfold morseShiftWord
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.map_cons, ih]; rfl

/-- A crossing climbs through a row of cups to its left, two positions per cup. -/
private theorem morseReach_cross_cupsUp (n₀ : ℕ) (ε : Bool) (v : MorseWord) :
    ∀ (len a p : ℕ) (u : MorseWord), a ≤ p → p + 2 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ (MorseKind.cross ε, p) :: slideCups a len ++ v)
        (u ++ slideCups a len ++ (MorseKind.cross ε, p + 2 * len) :: v)
  | 0, a, p, u, _, _ => by simpa [slideCups] using morseReach_refl n₀ _
  | len + 1, a, p, u, hap, hp => by
    have h1 := morseReach_isoRule n₀ u ((slideCups (a + 1) len) ++ v)
      (.exch (.cup, a) (.cross ε, p)) (by slide_fits)
      (by slide_fits)
      (by slide_fits)
    have h2 := morseReach_cross_cupsUp n₀ ε v len (a + 1) (p + 2) (u ++ [(MorseKind.cup, a)])
      (by omega) (by
        simp only [morseOut_append, morseOut, morseLetterOut, morseKindIn, morseKindOut]
        omega)
    simp only [morseRuleLhs, morseRuleRhs, morseKindOut, morseKindIn,
      Nat.sub_zero, List.append_assoc, List.cons_append, List.nil_append] at h1 h2
    rw [slideCups_succ]
    simp only [List.cons_append, List.append_assoc] at h2 ⊢
    refine morseReach_trans (morseReach_symm h1) ?_
    rw [show p + 2 * (len + 1) = p + 2 + 2 * len by ring]
    exact h2

/-- A crossing climbs through a row of caps to its left, two positions down per cap. -/
private theorem morseReach_cross_capsUp (n₀ : ℕ) (ε : Bool) (v : MorseWord) :
    ∀ (len a p : ℕ) (u : MorseWord), a + 2 * len ≤ p → p + 2 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ (MorseKind.cross ε, p) :: slideCaps a len ++ v)
        (u ++ slideCaps a len ++ (MorseKind.cross ε, p - 2 * len) :: v)
  | 0, a, p, u, _, _ => by simpa [slideCaps] using morseReach_refl n₀ _
  | len + 1, a, p, u, hap, hp => by
    have h1 := morseReach_isoRule n₀ u ((slideCaps a len) ++ v)
      (.exch (.cap, a + len) (.cross ε, p)) (by slide_fits)
      (by slide_fits)
      (by slide_fits)
    have h2 := morseReach_cross_capsUp n₀ ε v len a (p - 2) (u ++ [(MorseKind.cap, a + len)])
      (by omega) (by
        simp only [morseOut_append, morseOut, morseLetterOut, morseKindIn, morseKindOut]
        omega)
    simp only [morseRuleLhs, morseRuleRhs, morseKindOut, morseKindIn, Nat.add_zero,
      List.append_assoc, List.cons_append, List.nil_append] at h1 h2
    rw [slideCaps_succ]
    simp only [List.cons_append, List.append_assoc] at h2 ⊢
    refine morseReach_trans (morseReach_symm h1) ?_
    rw [show p - 2 * (len + 1) = p - 2 - 2 * len by omega]
    exact h2

/-- A row of cups fits once its first cup does. -/
private theorem morseFits_slideCups {n a : ℕ} (len : ℕ) (h : a ≤ n) :
    morseFits n (slideCups a len) = true :=
  morseFits_isoCups n len (fun t ↦ a + t) fun t _ ↦ by omega

/-- A row of caps fits when its outermost cap does. -/
private theorem morseFits_slideCaps {n a len : ℕ} (h : a + 2 * len ≤ n) :
    morseFits n (slideCaps a len) = true :=
  morseFits_isoCaps n len (fun t ↦ a + t) fun t ht ↦ by omega

/-- A crossing passing a word to its right leaves the positions of the word unchanged. -/
private theorem map_cross_shift_slide (ε : Bool) (x : MorseWord) :
    x.map (fun b ↦ (b.1, b.2 + morseKindOut (MorseKind.cross ε) - morseKindIn (MorseKind.cross ε)))
      = x := by
  simp [morseKindOut, morseKindIn]

/-- The cups of the long closure around two nested cups. -/
private theorem slideCups_split {m i : ℕ} (hi : 1 ≤ i) (him : i + 2 ≤ m) :
    slideCups 1 (m - 1) = slideCups 1 (i - 1) ++ (MorseKind.cup, i) :: (MorseKind.cup, i + 1) ::
      slideCups (i + 2) (m - 2 - i) := by
  rw [show m - 1 = (i - 1) + (0 + 1 + 1 + (m - 2 - i)) by omega, slideCups_add,
    show 1 + (i - 1) = i by omega, slideCups_add, slideCups_succ, slideCups_succ]
  simp [slideCups, show i + 1 + 1 = i + 2 by omega]

/-- The caps of the long closure around two nested caps. -/
private theorem slideCaps_split {m i : ℕ} (hi : 1 ≤ i) (him : i + 2 ≤ m) :
    slideCaps 1 (m - 1) = slideCaps (i + 2) (m - 2 - i) ++ (MorseKind.cap, i + 1) ::
      (MorseKind.cap, i) :: slideCaps 1 (i - 1) := by
  rw [show m - 1 = (i - 1) + (0 + 1 + 1 + (m - 2 - i)) by omega, slideCaps_add,
    show 1 + (i - 1) = i by omega, slideCaps_add, slideCaps_succ, slideCaps_succ]
  simp [slideCaps]

/-- A crossing at the bottom on the left legs `i, i + 1` moves to the right legs. -/
private theorem morseReach_slide_cups {m i : ℕ} (hi : 1 ≤ i) (him : i + 2 ≤ m) (ε : Bool)
    (v : MorseWord) :
    MorseReach 1 (slideCups 1 (m - 1) ++ (MorseKind.cross ε, i) :: v)
      (slideCups 1 (m - 1) ++ (MorseKind.cross ε, 2 * m - 2 - i) :: v) := by
  rw [slideCups_split hi him]
  set C1 := slideCups 1 (i - 1)
  set C2 := slideCups (i + 2) (m - 2 - i)
  have hC1 : morseOut 1 C1 = 2 * i - 1 := by rw [morseOut_slideCups]; omega
  have h1 := morseReach_sweep 1 (C1 ++ [(MorseKind.cup, i), (MorseKind.cup, i + 1)]) C2 v
    (MorseKind.cross ε, i) (fun b hb ↦ by
      simp only [C2, slideCups, List.mem_map, List.mem_range] at hb
      obtain ⟨j, -, rfl⟩ := hb
      simp only [morseKindIn]
      omega) (by
      rw [morseFits_append, morseFits_slideCups _ (by
        simp only [morseOut_append, hC1, morseOut, morseLetterOut, morseKindIn, morseKindOut]
        omega), Bool.true_and, morseOut_slideCups]
      simp only [morseOut_append, hC1, morseOut, morseLetterOut, morseKindIn, morseKindOut,
        morseFits_cons, morseFits_nil, and_true]
      omega)
  rw [map_cross_shift_slide] at h1
  have h2 := morseReach_frame 0 1 i (i - 1) C1 (C2 ++ v) _ _ (morseReach_cupMacro ε)
    (by cases ε <;> decide) (by omega)
  have h3 := morseReach_cross_cupsUp 1 ε v (m - 2 - i) (i + 2) (i + 2)
    (C1 ++ [(MorseKind.cup, i), (MorseKind.cup, i + 1)]) le_rfl (by
      simp only [morseOut_append, hC1, morseOut, morseLetterOut, morseKindIn, morseKindOut]
      omega)
  simp only [morseShiftWord, shiftLetter, List.map_cons, List.map_nil, Nat.zero_add] at h2
  rw [show i + 2 + 2 * (m - 2 - i) = 2 * m - 2 - i by omega] at h3
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_comm 1 i,
    Nat.add_comm 2 i] at h1 h2 h3 ⊢
  exact morseReach_trans (morseReach_symm h1) (morseReach_trans h2 h3)

/-- A crossing at the top on the right legs moves to the left legs `i, i + 1`. -/
private theorem morseReach_slide_caps {m i : ℕ} (hi : 1 ≤ i) (him : i + 2 ≤ m) (ε : Bool)
    (u : MorseWord) (hu : morseOut 1 u = 2 * m - 1) :
    MorseReach 1 (u ++ (MorseKind.cross ε, 2 * m - 2 - i) :: slideCaps 1 (m - 1))
      (u ++ (MorseKind.cross ε, i) :: slideCaps 1 (m - 1)) := by
  rw [slideCaps_split hi him]
  set K1 := slideCaps 1 (i - 1)
  set K2 := slideCaps (i + 2) (m - 2 - i)
  have hK2 : morseOut 1 (u ++ K2) = 2 * i + 3 := by
    rw [morseOut_append, hu, morseOut_slideCaps]
    omega
  have h1 := morseReach_cross_capsUp 1 ε ((MorseKind.cap, i + 1) :: (MorseKind.cap, i) :: K1)
    (m - 2 - i) (i + 2) (2 * m - 2 - i) u (by omega) (by omega)
  rw [show 2 * m - 2 - i - 2 * (m - 2 - i) = i + 2 by omega] at h1
  have h2 := morseReach_frame 4 1 i (i - 1) (u ++ K2) K1 _ _ (morseReach_capMacro ε)
    (by cases ε <;> decide) (by omega)
  have h3 := morseReach_sweep 1 u K2 ((MorseKind.cap, i + 1) :: (MorseKind.cap, i) :: K1)
    (MorseKind.cross ε, i) (fun b hb ↦ by
      simp only [K2, slideCaps, List.mem_map, List.mem_reverse, List.mem_range] at hb
      obtain ⟨j, -, rfl⟩ := hb
      simp only [morseKindIn]
      omega) (by
      rw [morseFits_append, hu, morseFits_slideCaps (by omega), Bool.true_and,
        morseOut_slideCaps]
      simp only [morseFits_cons, morseFits_nil, morseKindIn, and_true]
      omega)
  rw [map_cross_shift_slide] at h3
  simp only [morseShiftWord, shiftLetter, List.map_cons, List.map_nil, Nat.zero_add] at h2
  simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_comm 1 i,
    Nat.add_comm 2 i] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_symm h3))

/-- One letter of the conjugating braid slides around the closure and cancels. -/
private theorem morseReach_slide_letter {m i : ℕ} (hi : 1 ≤ i) (him : i + 2 ≤ m) (ε : Bool)
    (B : MorseWord) (hBx : ∀ b ∈ B, ∃ s, b.1 = MorseKind.cross s) (hBp : ∀ b ∈ B, b.2 + 2 ≤ m) :
    MorseReach 1 (slideCups 1 (m - 1) ++ (MorseKind.cross ε, i) ::
        (B ++ (MorseKind.cross (!ε), i) :: slideCaps 1 (m - 1)))
      (slideCups 1 (m - 1) ++ B ++ slideCaps 1 (m - 1)) := by
  set C := slideCups 1 (m - 1)
  set K := slideCaps 1 (m - 1)
  have hC : morseOut 1 C = 2 * m - 1 := by rw [morseOut_slideCups]; omega
  have hCB : morseOut 1 (C ++ B) = 2 * m - 1 := by
    rw [morseOut_append, morseOut_of_cross _ _ hBx, hC]
  have h1 := morseReach_slide_cups hi him ε (B ++ (MorseKind.cross (!ε), i) :: K)
  have h2 := morseReach_comm 1 C (B ++ [(MorseKind.cross (!ε), i)])
    [(MorseKind.cross ε, 2 * m - 2 - i)] K (fun b hb ↦ by
      rcases List.mem_append.mp hb with hb | hb
      · exact hBx b hb
      · rw [List.mem_singleton] at hb; exact ⟨_, by rw [hb]⟩) (fun b hb a ha ↦ by
      rw [List.mem_singleton] at ha
      subst ha
      rcases List.mem_append.mp hb with hb | hb
      · have := hBp b hb; dsimp only; omega
      · rw [List.mem_singleton] at hb; subst hb; dsimp only; omega) (by
      rw [hC]
      refine morseFits_of_cross _ _ (fun b hb ↦ ?_) fun b hb ↦ ?_
      · simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with rfl | hb | rfl
        · exact ⟨_, rfl⟩
        · exact hBx b hb
        · exact ⟨_, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with rfl | hb | rfl
        · dsimp only; omega
        · have := hBp b hb; omega
        · dsimp only; omega)
  have h3 := morseReach_slide_caps hi him ε (C ++ B ++ [(MorseKind.cross (!ε), i)]) (by
    rw [morseOut_append, hCB]
    simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]
    omega)
  have h4 := morseReach_isoRule 1 (C ++ B) K (.r2 i (!ε)) rfl (by
    rw [hCB]
    simp only [morseRuleLhs, morseFits_cons, morseFits_nil, morseKindIn, morseLetterOut,
      morseKindOut, and_true]
    omega) rfl
  simp only [morseRuleLhs, morseRuleRhs, Bool.not_not, List.append_nil] at h4
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 h4))

/-- Closure slide. -/
theorem morseReach_closureSlide (m : ℕ) (g w : BraidWord) (hg : ∀ x ∈ g, 1 ≤ x.1 ∧ x.1 + 2 ≤ m)
    (hw : IsOnStrands m w) :
    MorseReach 1 (morseLongClosure m (g ++ w ++ isoBraidInv g)) (morseLongClosure m w) := by
  induction g with
  | nil => simpa [isoBraidInv] using morseReach_refl 1 (morseLongClosure m w)
  | cons x g ih =>
    obtain ⟨hx1, hx2⟩ := hg x List.mem_cons_self
    have ih' := ih fun y hy ↦ hg y (List.mem_cons_of_mem _ hy)
    rw [morseLongClosure_eq_slide, morseLongClosure_eq_slide] at ih' ⊢
    have hB : ∀ b ∈ morseOfBraid (g ++ w ++ isoBraidInv g),
        (∃ s, b.1 = MorseKind.cross s) ∧ b.2 + 2 ≤ m := by
      intro b hb
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      refine ⟨⟨_, rfl⟩, ?_⟩
      simp only [isoBraidInv, List.mem_append, List.mem_map, List.mem_reverse] at hy
      rcases hy with (hy | hy) | ⟨z, hz, rfl⟩
      · exact (hg y (List.mem_cons_of_mem _ hy)).2
      · have := hw y hy; dsimp only; omega
      · exact (hg z (List.mem_cons_of_mem _ hz)).2
    have h := morseReach_slide_letter hx1 hx2 x.2 (morseOfBraid (g ++ w ++ isoBraidInv g))
      (fun b hb ↦ (hB b hb).1) fun b hb ↦ (hB b hb).2
    have heq : morseOfBraid (x :: g ++ w ++ isoBraidInv (x :: g)) =
        (MorseKind.cross x.2, x.1) ::
          (morseOfBraid (g ++ w ++ isoBraidInv g) ++ [(MorseKind.cross (!x.2), x.1)]) := by
      simp [isoBraidInv, morseOfBraid]
    rw [heq]
    simp only [List.append_assoc, List.cons_append] at h ih' ⊢
    exact morseReach_trans h ih'

end AJConjecture
