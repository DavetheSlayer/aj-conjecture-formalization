import Mathlib
import AJFamily.Skein.MorseFrame
import AJConjecture.SkeinMorseBraid
import AJFamily.Skein.MorseReach
import AJFamily.Skein.MorseShift
import AJFamily.Skein.TorusWord

/-!
# Generic moves for the isotopy

Word families used by the closed forms of phase I (walks, cup and cap runs, the head of the small
climbs, bands, staircases) and generic moves among them, stated for arbitrary words with local
fitting hypotheses only. Moves are reversible (`morseReach_symm`); a word to the right of a word of
crossings commutes with it (`morseReach_comm`); a letter to the left of every letter of a word
passes it (`morseReach_sweep`); a walk, a strand crossing over or under `b` strands, passes any
tangle on those strands (`morseReach_pass`); and the small climbs shuffle in between the head cups
(`morseReach_headShuffle`).
-/

namespace AJConjecture

/-! ### Private helpers: arities and single moves -/

/-- The arity of a concatenation. -/
private theorem morseOut_append_phaseTools (n : ℕ) (u v : MorseWord) :
    morseOut n (u ++ v) = morseOut (morseOut n u) v := by
  induction u generalizing n with
  | nil => rfl
  | cons l u ih => exact ih _

/-- Fitting of a concatenation. -/
private theorem morseFits_append_phaseTools (n : ℕ) (u v : MorseWord) :
    morseFits n (u ++ v) = (morseFits n u && morseFits (morseOut n u) v) := by
  induction u generalizing n with
  | nil => simp [morseFits, morseOut]
  | cons l u ih => simp only [List.cons_append, morseFits, morseOut, ih, Bool.and_assoc]

/-- Arity of a cup. -/
private theorem morseKindIn_cup_phaseTools : morseKindIn .cup = 0 := rfl

/-- Arity of a cap. -/
private theorem morseKindIn_cap_phaseTools : morseKindIn .cap = 2 := rfl

/-- Arity of a crossing. -/
private theorem morseKindIn_cross_phaseTools (s : Bool) : morseKindIn (.cross s) = 2 := rfl

/-- Coarity of a cup. -/
private theorem morseKindOut_cup_phaseTools : morseKindOut .cup = 2 := rfl

/-- Coarity of a cap. -/
private theorem morseKindOut_cap_phaseTools : morseKindOut .cap = 0 := rfl

/-- Coarity of a crossing. -/
private theorem morseKindOut_cross_phaseTools (s : Bool) : morseKindOut (.cross s) = 2 := rfl

/-- The empty word fits. -/
theorem morseFits_nil (n : ℕ) : morseFits n [] = true := rfl

/-- Fitting of a concatenation, as a conjunction. -/
private theorem morseFits_append_iff_phaseTools (n : ℕ) (u v : MorseWord) :
    morseFits n (u ++ v) = true ↔ morseFits n u = true ∧ morseFits (morseOut n u) v = true := by
  rw [morseFits_append_phaseTools, Bool.and_eq_true]

/-- One move can be undone. -/
private theorem morseReach_of_morseApply_phaseTools (n₀ : ℕ) (w w' : MorseWord) (mv : MorseMove)
    (h : morseApply n₀ w mv = some w') : MorseReach n₀ w' w := by
  obtain ⟨p, r, bk⟩ := mv
  obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n₀ w w' p r bk h
  refine ⟨[(a.length, r, !bk)], ?_⟩
  have := morseApply_junction n₀ a rest r (!bk) hok (by cases bk <;> simpa using hd)
    (by cases bk <;> simpa using hs)
  cases bk <;> simpa [morseApplyAll] using this

/-- A rule applied forward at the junction of `u` and `v`. -/
private theorem morseReach_lhs_rhs_phaseTools (n₀ : ℕ) (u v : MorseWord) (r : MorseRule)
    (hok : morseRuleOk r = true)
    (hl : morseFits (morseOut n₀ u) (morseRuleLhs r) = true)
    (hr : morseFits (morseOut n₀ u) (morseRuleRhs r) = true) :
    MorseReach n₀ (u ++ morseRuleLhs r ++ v) (u ++ morseRuleRhs r ++ v) :=
  ⟨[(u.length, r, false)], by
    simpa [morseApplyAll] using morseApply_junction n₀ u v r false hok hl hr⟩

/-- A rule applied backward at the junction of `u` and `v`. -/
private theorem morseReach_rhs_lhs_phaseTools (n₀ : ℕ) (u v : MorseWord) (r : MorseRule)
    (hok : morseRuleOk r = true)
    (hl : morseFits (morseOut n₀ u) (morseRuleLhs r) = true)
    (hr : morseFits (morseOut n₀ u) (morseRuleRhs r) = true) :
    MorseReach n₀ (u ++ morseRuleRhs r ++ v) (u ++ morseRuleLhs r ++ v) :=
  ⟨[(u.length, r, true)], by
    simpa [morseApplyAll] using morseApply_junction n₀ u v r true hok hr hl⟩

/-- A word of crossings does not change the number of strands. -/
private theorem morseOut_of_cross_phaseTools (n : ℕ) (x : MorseWord)
    (hx : ∀ b ∈ x, ∃ s, b.1 = MorseKind.cross s) : morseOut n x = n := by
  induction x with
  | nil => rfl
  | cons l x ih =>
    obtain ⟨s, hs⟩ := hx l (by simp)
    simp only [morseOut, morseLetterOut, hs, morseKindOut, morseKindIn, Nat.add_sub_cancel]
    exact ih fun b hb ↦ hx b (by simp [hb])

/-- A word of crossings fits when every crossing does. -/
private theorem morseFits_of_cross_phaseTools (n : ℕ) (x : MorseWord)
    (hx : ∀ b ∈ x, ∃ s, b.1 = MorseKind.cross s) (hp : ∀ b ∈ x, b.2 + 2 ≤ n) :
    morseFits n x = true := by
  induction x with
  | nil => rfl
  | cons l x ih =>
    obtain ⟨s, hs⟩ := hx l (by simp)
    rw [morseFits_cons]
    simp only [morseLetterOut, hs, morseKindOut, morseKindIn, Nat.add_sub_cancel]
    exact ⟨hp l (by simp),
      ih (fun b hb ↦ hx b (by simp [hb])) fun b hb ↦ hp b (by simp [hb])⟩

/-- A letter `b` lying to the right of a word `x` of crossings moves to the right of `x`. -/
private theorem morseReach_letter_cross_phaseTools (n₀ : ℕ) (u x v : MorseWord)
    (b : MorseLetter) (hx : ∀ a ∈ x, ∃ s, a.1 = MorseKind.cross s)
    (hpos : ∀ a ∈ x, a.2 + 2 ≤ b.2) (hfit : morseFits (morseOut n₀ u) (b :: x) = true) :
    MorseReach n₀ (u ++ b :: x ++ v) (u ++ x ++ b :: v) := by
  induction x generalizing u with
  | nil => exact ⟨[], by simp [morseApplyAll]⟩
  | cons a x ih =>
    obtain ⟨s, hs⟩ := hx a (by simp)
    obtain ⟨ka, ia⟩ := a
    simp only at hs
    subst hs
    have hpa : ia + 2 ≤ b.2 := hpos (.cross s, ia) (by simp)
    rw [morseFits_cons, morseFits_cons] at hfit
    obtain ⟨hb, ha, hx'⟩ := hfit
    simp only [morseLetterOut, morseKindOut_cross_phaseTools, morseKindIn_cross_phaseTools]
      at ha hx'
    have h1 := morseReach_rhs_lhs_phaseTools n₀ u (x ++ v) (.exch (.cross s, ia) b)
      (by simp only [morseRuleOk, morseKindIn_cross_phaseTools]; exact decide_eq_true hpa)
      (by
        simp only [morseRuleLhs, morseFits_cons, morseLetterOut,
          morseKindOut_cross_phaseTools, morseKindIn_cross_phaseTools,
          morseFits_nil, and_true]
        omega)
      (by
        simp only [morseRuleRhs, morseFits_cons, morseLetterOut,
          morseKindOut_cross_phaseTools, morseKindIn_cross_phaseTools,
          morseFits_nil, and_true]
        omega)
    simp only [morseRuleLhs, morseRuleRhs, morseKindOut_cross_phaseTools,
      morseKindIn_cross_phaseTools, Nat.add_sub_cancel, Prod.mk.eta] at h1
    have h2 := ih (u ++ [(.cross s, ia)]) (fun a ha ↦ hx a (by simp [ha]))
      (fun a ha ↦ hpos a (by simp [ha])) (by
        rw [morseOut_append_phaseTools, morseFits_cons]
        simp only [morseOut, morseLetterOut, morseKindOut_cross_phaseTools,
          morseKindIn_cross_phaseTools, Nat.add_sub_cancel]
        rw [Nat.add_sub_cancel] at hx'
        exact ⟨hb, hx'⟩)
    simp only [List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A letter `a` lying to the left of every letter of `x` moves to the right of `x`. -/
private theorem morseReach_sweep_phaseTools (n₀ : ℕ) (u x v : MorseWord) (a : MorseLetter)
    (hleft : ∀ b ∈ x, a.2 + morseKindIn a.1 ≤ b.2)
    (hfit : morseFits (morseOut n₀ u) (x ++ [a]) = true) :
    MorseReach n₀
      (u ++ a :: x.map (fun b ↦ (b.1, b.2 + morseKindOut a.1 - morseKindIn a.1)) ++ v)
      (u ++ x ++ a :: v) := by
  induction x generalizing u with
  | nil => exact ⟨[], by simp [morseApplyAll]⟩
  | cons b x ih =>
    have hab : a.2 + morseKindIn a.1 ≤ b.2 := hleft b (by simp)
    rw [List.cons_append, morseFits_cons] at hfit
    obtain ⟨hb, hx'⟩ := hfit
    have h1 := morseReach_lhs_rhs_phaseTools n₀ u
      (x.map (fun b ↦ (b.1, b.2 + morseKindOut a.1 - morseKindIn a.1)) ++ v) (.exch a b)
      (by simpa [morseRuleOk] using hab)
      (by
        simp only [morseRuleLhs, morseFits_cons, morseLetterOut,
          morseFits_nil,
          and_true]
        omega)
      (by
        simp only [morseRuleRhs, morseFits_cons, morseLetterOut,
          morseFits_nil,
          and_true]
        omega)
    simp only [morseRuleLhs, morseRuleRhs] at h1
    have h2 := ih (u ++ [b]) (fun c hc ↦ hleft c (by simp [hc]))
      (by rw [morseOut_append_phaseTools]; exact hx')
    simp only [List.append_assoc, List.cons_append, List.map_cons]
      at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- The arity of a shifted word. -/
private theorem morseOut_morseShiftWord_phaseTools (n d : ℕ) (w : MorseWord)
    (h : morseFits n w = true) : morseOut (n + d) (morseShiftWord d w) = morseOut n w + d := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    rw [morseFits_cons] at h
    simp only [morseShiftWord, List.map_cons, morseOut] at ih ⊢
    rw [← ih _ h.2]
    congr 1
    simp only [morseLetterOut, shiftLetter]
    omega

/-- A shifted word fits on more strands. -/
private theorem morseFits_morseShiftWord_phaseTools (n d e : ℕ) (w : MorseWord)
    (h : morseFits n w = true) : morseFits (n + d + e) (morseShiftWord d w) = true := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    rw [morseFits_cons] at h
    simp only [morseShiftWord, List.map_cons] at ih ⊢
    rw [morseFits_cons]
    refine ⟨by simp only [shiftLetter]; omega, ?_⟩
    have := ih _ h.2
    convert this using 2
    simp only [morseLetterOut, shiftLetter]
    omega

/-! ### Reachability -/

theorem morseReach_refl (n : ℕ) (w : MorseWord) : MorseReach n w w := ⟨[], rfl⟩

/-- Moves are reversible. -/
theorem morseReach_symm {n : ℕ} {w w' : MorseWord} (h : MorseReach n w w') : MorseReach n w' w := by
  obtain ⟨mvs, h⟩ := h
  induction mvs generalizing w with
  | nil => exact ⟨[], by simpa [morseApplyAll] using h.symm⟩
  | cons mv mvs ih =>
    simp only [morseApplyAll] at h
    cases h₁ : morseApply n w mv with
    | none => simp [h₁] at h
    | some w₁ =>
      rw [h₁, Option.bind_some] at h
      exact morseReach_trans (ih h) (morseReach_of_morseApply_phaseTools n w w₁ mv h₁)

/-! ### Word families -/

/-- The walk: `len` crossings of sign `s` at the positions `p, p+1, …, p+len-1` (a strand moving
from the gap `p` to the gap `p + len` over or under the strands in between). -/
def morseWalk (s : Bool) (p len : ℕ) : MorseWord :=
  (List.range len).map fun i ↦ (MorseKind.cross s, p + i)

/-- The cups `u a, u (a+1), …, u b` (empty when `b < a`). -/
def morseCupRun (a b : ℕ) : MorseWord :=
  (List.range (b + 1 - a)).map fun i ↦ (MorseKind.cup, a + i)

/-- The caps `n m, n (m-1), …, n 1`. -/
def morseCapRun (m : ℕ) : MorseWord :=
  (List.range m).reverse.map fun j ↦ (MorseKind.cap, j + 1)

/-- The head of the small climbs: `u1 +0 u2 +1 ⋯ u n +(n-1)`. -/
def morseHeadRun (n : ℕ) : MorseWord :=
  (List.range n).flatMap fun i ↦ [(MorseKind.cup, i + 1), (MorseKind.cross true, i)]

/-- The small climbs `+0 +1 ⋯ +(n-1)`. -/
def morseClimbRun (n : ℕ) : MorseWord :=
  (List.range n).map fun i ↦ (MorseKind.cross true, i)

/-- The band `b(i, j)` as a Morse word. -/
def morseBand (i j : ℕ) : MorseWord :=
  morseOfBraid (surfaceBand i j)

/-- The staircase `b(b, b+2) b(b-1, b+1) ⋯ b(a, a+2)` (empty when `b < a`). -/
def morseStairRun (a b : ℕ) : MorseWord :=
  (List.range (b + 1 - a)).reverse.flatMap fun x ↦ morseBand (a + x) (a + x + 2)

/-! ### Private helpers on the word families -/

/-- A walk splits at any length. -/
private theorem morseWalk_add_phaseTools (s : Bool) (p a c : ℕ) :
    morseWalk s p (a + c) = morseWalk s p a ++ morseWalk s (p + a) c := by
  simp only [morseWalk, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp, Nat.add_assoc]

/-- A walk of length two. -/
private theorem morseWalk_two_phaseTools (s : Bool) (p : ℕ) :
    morseWalk s p 2 = [(MorseKind.cross s, p), (MorseKind.cross s, p + 1)] := rfl

/-- The letters of a walk. -/
private theorem mem_morseWalk_phaseTools {s : Bool} {p len : ℕ} {b : MorseLetter}
    (hb : b ∈ morseWalk s p len) :
    b.1 = MorseKind.cross s ∧ p ≤ b.2 ∧ b.2 + 1 ≤ p + len := by
  simp only [morseWalk, List.mem_map, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  exact ⟨rfl, by simp only; omega, by simp only; omega⟩

/-- The letters of a walk are crossings. -/
private theorem morseWalk_cross_phaseTools (s : Bool) (p len : ℕ) :
    ∀ b ∈ morseWalk s p len, ∃ t, b.1 = MorseKind.cross t :=
  fun _ hb ↦ ⟨s, (mem_morseWalk_phaseTools hb).1⟩

/-- A walk does not change the number of strands. -/
theorem morseOut_morseWalk (n : ℕ) (s : Bool) (p len : ℕ) :
    morseOut n (morseWalk s p len) = n :=
  morseOut_of_cross_phaseTools n _ (morseWalk_cross_phaseTools s p len)

/-- A walk fits on the strands to its right. -/
private theorem morseFits_morseWalk_phaseTools (n : ℕ) (s : Bool) (p len : ℕ)
    (h : p + len + 1 ≤ n) : morseFits n (morseWalk s p len) = true :=
  morseFits_of_cross_phaseTools n _ (morseWalk_cross_phaseTools s p len) fun _ hb ↦ by
    have := mem_morseWalk_phaseTools hb
    omega

/-- Shifting the letters of a walk. -/
private theorem morseWalk_map_phaseTools (s : Bool) (p len k j : ℕ) (hj : j ≤ p) :
    (morseWalk s p len).map (fun b ↦ (b.1, b.2 + k - j)) = morseWalk s (p + k - j) len := by
  simp only [morseWalk, List.map_map]
  exact List.map_congr_left fun i _ ↦ by
    simp only [Function.comp, Prod.mk.injEq, true_and]
    omega

/-- A cup run starts with its first cup. -/
private theorem morseCupRun_cons_phaseTools (a b : ℕ) (h : a ≤ b) :
    morseCupRun a b = (MorseKind.cup, a) :: morseCupRun (a + 1) b := by
  simp only [morseCupRun]
  rw [show b + 1 - a = (b + 1 - (a + 1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  exact List.map_congr_left fun i _ ↦ by
    simp only [Function.comp, Nat.succ_eq_add_one, Prod.mk.injEq, true_and]
    omega

/-- The letters of a cup run. -/
private theorem mem_morseCupRun_phaseTools {a b : ℕ} {l : MorseLetter}
    (hl : l ∈ morseCupRun a b) : l.1 = MorseKind.cup ∧ a ≤ l.2 := by
  simp only [morseCupRun, List.mem_map, List.mem_range] at hl
  obtain ⟨i, -, rfl⟩ := hl
  exact ⟨rfl, Nat.le_add_right a i⟩

/-- Cups at the consecutive positions `a, a+1, …, a+k-1`. -/
private theorem morseOut_fits_cups_phaseTools (n a k : ℕ) (ha : a ≤ n) :
    morseOut n ((List.range k).map fun i ↦ (MorseKind.cup, a + i)) = n + 2 * k ∧
      morseFits n ((List.range k).map fun i ↦ (MorseKind.cup, a + i)) = true := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, morseOut_append_phaseTools,
      morseFits_append_iff_phaseTools, ih.1]
    refine ⟨?_, ih.2, ?_⟩
    · simp only [List.map_cons, List.map_nil, morseOut, morseLetterOut,
        morseKindOut_cup_phaseTools, morseKindIn_cup_phaseTools]
      omega
    · simp only [List.map_cons, List.map_nil, morseFits_cons, morseFits_nil,
        morseKindIn_cup_phaseTools, and_true]
      omega

/-- The arity of a cup run. -/
private theorem morseOut_morseCupRun_phaseTools (n a b : ℕ) (ha : a ≤ n) :
    morseOut n (morseCupRun a b) = n + 2 * (b + 1 - a) :=
  (morseOut_fits_cups_phaseTools n a _ ha).1

/-- A cup run fits. -/
private theorem morseFits_morseCupRun_phaseTools (n a b : ℕ) (ha : a ≤ n) :
    morseFits n (morseCupRun a b) = true :=
  (morseOut_fits_cups_phaseTools n a _ ha).2

/-- The climb run grows at the end. -/
private theorem morseClimbRun_succ_phaseTools (c : ℕ) :
    morseClimbRun (c + 1) = morseClimbRun c ++ [(MorseKind.cross true, c)] := by
  simp only [morseClimbRun, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The head run grows at the end. -/
private theorem morseHeadRun_succ_phaseTools (c : ℕ) :
    morseHeadRun (c + 1) =
      morseHeadRun c ++ [(MorseKind.cup, c + 1), (MorseKind.cross true, c)] := by
  simp only [morseHeadRun, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Arity and fitting of a head run. -/
private theorem morseOut_fits_headRun_phaseTools (n c : ℕ) (hn : 1 ≤ n) :
    morseOut n (morseHeadRun c) = n + 2 * c ∧ morseFits n (morseHeadRun c) = true := by
  induction c with
  | zero => exact ⟨rfl, rfl⟩
  | succ c ih =>
    rw [morseHeadRun_succ_phaseTools, morseOut_append_phaseTools,
      morseFits_append_iff_phaseTools, ih.1]
    refine ⟨?_, ih.2, ?_⟩
    · simp only [morseOut, morseLetterOut, morseKindOut_cup_phaseTools,
        morseKindIn_cup_phaseTools, morseKindOut_cross_phaseTools, morseKindIn_cross_phaseTools]
      omega
    · simp only [morseFits_cons, morseFits_nil, morseLetterOut,
        morseKindOut_cup_phaseTools, morseKindIn_cup_phaseTools, morseKindIn_cross_phaseTools,
        and_true]
      omega

/-! ### Generic moves -/

/-- A word `y` lying to the right of a word `x` of crossings commutes with it. -/
theorem morseReach_comm (n₀ : ℕ) (u x y v : MorseWord)
    (hx : ∀ b ∈ x, ∃ s, b.1 = MorseKind.cross s)
    (hpos : ∀ b ∈ x, ∀ a ∈ y, b.2 + 2 ≤ a.2)
    (hfit : morseFits (morseOut n₀ u) (y ++ x) = true) :
    MorseReach n₀ (u ++ y ++ x ++ v) (u ++ x ++ y ++ v) := by
  induction y generalizing u with
  | nil => simpa using morseReach_refl n₀ (u ++ x ++ v)
  | cons b y ih =>
    rw [List.cons_append, morseFits_cons] at hfit
    obtain ⟨hb, hyx⟩ := hfit
    have h1 := ih (u ++ [b]) (fun c hc a ha ↦ hpos c hc a (by simp [ha]))
      (by rw [morseOut_append_phaseTools]; exact hyx)
    have h2 := morseReach_letter_cross_phaseTools n₀ u x (y ++ v) b hx
      (fun a ha ↦ hpos a ha b (by simp)) (by
        rw [morseFits_cons]
        refine ⟨hb, morseFits_of_cross_phaseTools _ x hx fun a ha ↦ ?_⟩
        have := hpos a ha b (by simp)
        simp only [morseLetterOut]
        omega)
    simp only [List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A letter lying to the left of every letter of `x` passes `x`. -/
theorem morseReach_sweep (n₀ : ℕ) (u x v : MorseWord) (a : MorseLetter)
    (hleft : ∀ b ∈ x, a.2 + morseKindIn a.1 ≤ b.2)
    (hfit : morseFits (morseOut n₀ u) (x ++ [a]) = true) :
    MorseReach n₀ (u ++ a :: x.map (fun b ↦ (b.1, b.2 + morseKindOut a.1 - morseKindIn a.1)) ++ v)
      (u ++ x ++ a :: v) :=
  morseReach_sweep_phaseTools n₀ u x v a hleft hfit

/-- Closes the arity side goals of the local moves. -/
local macro "morse_fits" : tactic =>
  `(tactic| ((simp only [morseRuleLhs, morseRuleRhs, morseRuleOk, morseOut_append_phaseTools,
    morseOut, morseLetterOut, morseFits_cons, morseFits_nil,
    morseKindIn_cross_phaseTools, morseKindOut_cross_phaseTools, morseKindIn_cup_phaseTools,
    morseKindOut_cup_phaseTools, morseKindIn_cap_phaseTools, morseKindOut_cap_phaseTools,
    and_true, ↓reduceIte]) <;> omega))

/-- Pass, first stage: the letter `(κ, p + q)` moves left past the walk letters to its right. -/
private theorem morseReach_pass_right_phaseTools (n₀ p b q : ℕ) (s : Bool) (u w : MorseWord)
    (κ : MorseKind) (hl : q + morseKindIn κ ≤ b) (hu : p + b + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk s p b ++ (κ, p + q) :: w)
      (u ++ morseWalk s p (q + morseKindIn κ) ++ (κ, p + q) ::
        (morseWalk s (p + q + morseKindOut κ) (b - q - morseKindIn κ) ++ w)) := by
  have hsplit : morseWalk s p b = morseWalk s p (q + morseKindIn κ) ++
      morseWalk s (p + (q + morseKindIn κ)) (b - q - morseKindIn κ) := by
    rw [← morseWalk_add_phaseTools]
    congr 1
    omega
  have h := morseReach_symm (morseReach_sweep_phaseTools n₀
    (u ++ morseWalk s p (q + morseKindIn κ))
    (morseWalk s (p + (q + morseKindIn κ)) (b - q - morseKindIn κ)) w (κ, p + q)
    (fun c hc ↦ by
      have := mem_morseWalk_phaseTools hc
      simp only
      omega)
    (by
      rw [morseOut_append_phaseTools, morseOut_morseWalk,
        morseFits_append_iff_phaseTools, morseOut_morseWalk]
      refine ⟨morseFits_morseWalk_phaseTools _ _ _ _ (by omega), ?_⟩
      simp only [morseFits_cons, morseFits_nil, and_true]
      omega))
  rw [morseWalk_map_phaseTools _ _ _ _ _ (by simp only; omega)] at h
  rw [show p + (q + morseKindIn κ) + morseKindOut κ - morseKindIn κ = p + q + morseKindOut κ by
    omega] at h
  rw [hsplit]
  simpa only [List.append_assoc, List.cons_append] using h

/-- Pass, last stage: the letter `(κ, p + q + 1)` moves left past the walk letters to its
left. -/
private theorem morseReach_pass_left_phaseTools (n₀ p q : ℕ) (s : Bool) (u w : MorseWord)
    (κ : MorseKind) (hu : p + q + 1 + morseKindIn κ ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk s p q ++ (κ, p + q + 1) :: w)
      (u ++ (κ, p + q + 1) :: (morseWalk s p q ++ w)) := by
  have h := morseReach_symm (morseReach_comm n₀ u (morseWalk s p q) [(κ, p + q + 1)] w
    (morseWalk_cross_phaseTools s p q)
    (fun c hc a ha ↦ by
      have := mem_morseWalk_phaseTools hc
      rw [List.mem_singleton] at ha
      subst ha
      simp only
      omega)
    (by
      rw [List.singleton_append, morseFits_cons]
      refine ⟨by simp only; omega, morseFits_morseWalk_phaseTools _ _ _ _ ?_⟩
      simp only [morseLetterOut]
      omega))
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

/-- Pass, middle stage for a crossing: `r3`, or `r2 r3 r2` for opposite signs. -/
private theorem morseReach_pass_cross_phaseTools (n₀ i : ℕ) (s t : Bool) (u w : MorseWord)
    (hu : i + 3 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ (MorseKind.cross s, i) :: (MorseKind.cross s, i + 1) ::
        (MorseKind.cross t, i) :: w)
      (u ++ (MorseKind.cross t, i + 1) :: (MorseKind.cross s, i) ::
        (MorseKind.cross s, i + 1) :: w) := by
  by_cases hts : t = s
  · subst hts
    have h := morseReach_lhs_rhs_phaseTools n₀ u w (.r3 i t) rfl (by morse_fits) (by morse_fits)
    simpa only [morseRuleLhs, morseRuleRhs, List.append_assoc, List.cons_append,
      List.nil_append] using h
  · have ht : t = !s := by cases s <;> cases t <;> simp_all
    subst ht
    have h1 := morseReach_rhs_lhs_phaseTools n₀ u
      ((MorseKind.cross s, i) :: (MorseKind.cross s, i + 1) :: (MorseKind.cross (!s), i) :: w)
      (.r2 (i + 1) (!s)) rfl (by morse_fits) (by morse_fits)
    have h2 := morseReach_rhs_lhs_phaseTools n₀ (u ++ [(MorseKind.cross (!s), i + 1)])
      ((MorseKind.cross (!s), i) :: w) (.r3 i s) rfl (by morse_fits) (by morse_fits)
    have h3 := morseReach_lhs_rhs_phaseTools n₀
      (u ++ [(MorseKind.cross (!s), i + 1), (MorseKind.cross s, i), (MorseKind.cross s, i + 1)])
      w (.r2 i s) rfl (by morse_fits) (by morse_fits)
    simp only [morseRuleLhs, morseRuleRhs, Bool.not_not, List.append_assoc, List.cons_append,
      List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- Pass, middle stage for a cup: `cupSlide` backwards. -/
private theorem morseReach_pass_cup_phaseTools (n₀ i : ℕ) (s : Bool) (u w : MorseWord)
    (hu : i + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ (MorseKind.cup, i) :: w)
      (u ++ (MorseKind.cup, i + 1) :: (MorseKind.cross s, i) :: (MorseKind.cross s, i + 1) ::
        w) := by
  have h := morseReach_rhs_lhs_phaseTools n₀ u w (.cupSlide i s true) rfl (by morse_fits)
    (by morse_fits)
  simpa only [morseRuleLhs, morseRuleRhs, ↓reduceIte, List.append_assoc, List.cons_append,
    List.nil_append] using h

/-- Pass, middle stage for a cap: `capSlide` forwards. -/
private theorem morseReach_pass_cap_phaseTools (n₀ i : ℕ) (s : Bool) (u w : MorseWord)
    (hu : i + 3 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ (MorseKind.cross s, i) :: (MorseKind.cross s, i + 1) ::
        (MorseKind.cap, i) :: w) (u ++ (MorseKind.cap, i + 1) :: w) := by
  have h := morseReach_lhs_rhs_phaseTools n₀ u w (.capSlide i s true) rfl (by morse_fits)
    (by morse_fits)
  simpa only [morseRuleLhs, morseRuleRhs, ↓reduceIte, List.append_assoc, List.cons_append,
    List.nil_append] using h

/-- The walk passes one letter. -/
private theorem morseReach_pass_letter_phaseTools (n₀ p b : ℕ) (s : Bool) (u w : MorseWord)
    (l : MorseLetter) (hl : l.2 + morseKindIn l.1 ≤ b) (hu : p + b + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk s p b ++ shiftLetter p l :: w)
      (u ++ shiftLetter (p + 1) l :: (morseWalk s p (morseLetterOut b l) ++ w)) := by
  obtain ⟨κ, q⟩ := l
  simp only [shiftLetter] at hl ⊢
  rw [show q + p = p + q by omega, show q + (p + 1) = p + q + 1 by omega]
  have h1 := morseReach_pass_right_phaseTools n₀ p b q s u w κ hl hu
  have hm : morseOut n₀ (u ++ morseWalk s p q) = morseOut n₀ u := by
    rw [morseOut_append_phaseTools, morseOut_morseWalk]
  cases κ with
  | cup =>
    simp only [morseKindIn_cup_phaseTools, morseKindOut_cup_phaseTools, Nat.add_zero,
      Nat.sub_zero] at h1 hl
    have h2 := morseReach_pass_cup_phaseTools n₀ (p + q) s (u ++ morseWalk s p q)
      (morseWalk s (p + q + 2) (b - q) ++ w) (by rw [hm]; omega)
    have h3 := morseReach_pass_left_phaseTools n₀ p q s u ((MorseKind.cross s, p + q) ::
      (MorseKind.cross s, p + q + 1) :: (morseWalk s (p + q + 2) (b - q) ++ w)) .cup
      (by rw [morseKindIn_cup_phaseTools]; omega)
    rw [show morseLetterOut b (MorseKind.cup, q) = q + (2 + (b - q)) by
      simp only [morseLetterOut, morseKindOut_cup_phaseTools, morseKindIn_cup_phaseTools]
      omega, morseWalk_add_phaseTools, morseWalk_add_phaseTools, morseWalk_two_phaseTools]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)
  | cap =>
    simp only [morseKindIn_cap_phaseTools, morseKindOut_cap_phaseTools, Nat.add_zero] at h1 hl
    rw [morseWalk_add_phaseTools, morseWalk_two_phaseTools] at h1
    have h2 := morseReach_pass_cap_phaseTools n₀ (p + q) s (u ++ morseWalk s p q)
      (morseWalk s (p + q) (b - q - 2) ++ w) (by rw [hm]; omega)
    have h3 := morseReach_pass_left_phaseTools n₀ p q s u
      (morseWalk s (p + q) (b - q - 2) ++ w) .cap (by rw [morseKindIn_cap_phaseTools]; omega)
    rw [show morseLetterOut b (MorseKind.cap, q) = q + (b - q - 2) by
      simp only [morseLetterOut, morseKindOut_cap_phaseTools, morseKindIn_cap_phaseTools]
      omega, morseWalk_add_phaseTools]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)
  | cross t =>
    simp only [morseKindIn_cross_phaseTools, morseKindOut_cross_phaseTools] at h1 hl
    rw [morseWalk_add_phaseTools, morseWalk_two_phaseTools] at h1
    have h2 := morseReach_pass_cross_phaseTools n₀ (p + q) s t (u ++ morseWalk s p q)
      (morseWalk s (p + q + 2) (b - q - 2) ++ w) (by rw [hm]; omega)
    have h3 := morseReach_pass_left_phaseTools n₀ p q s u ((MorseKind.cross s, p + q) ::
      (MorseKind.cross s, p + q + 1) :: (morseWalk s (p + q + 2) (b - q - 2) ++ w)) (.cross t)
      (by rw [morseKindIn_cross_phaseTools]; omega)
    rw [show morseLetterOut b (MorseKind.cross t, q) = q + (2 + (b - q - 2)) by
      simp only [morseLetterOut, morseKindOut_cross_phaseTools, morseKindIn_cross_phaseTools]
      omega, morseWalk_add_phaseTools, morseWalk_add_phaseTools, morseWalk_two_phaseTools]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- The walk passes an arbitrary tangle `T` on `b` strands: before, the strand of the walk ends
to the right of `T`; after, it runs to the left of `T` and crosses its outgoing strands. -/
theorem morseReach_pass (n₀ p b : ℕ) (s : Bool) (u T v : MorseWord)
    (hT : morseFits b T = true) (hu : p + b + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk s p b ++ morseShiftWord p T ++ v)
      (u ++ morseShiftWord (p + 1) T ++ morseWalk s p (morseOut b T) ++ v) := by
  induction T generalizing b u with
  | nil => exact ⟨[], by simp [morseApplyAll, morseShiftWord, morseOut]⟩
  | cons l T ih =>
    rw [morseFits_cons] at hT
    have h1 := morseReach_pass_letter_phaseTools n₀ p b s u (morseShiftWord p T ++ v) l hT.1 hu
    have h2 := ih (morseLetterOut b l) (u ++ [shiftLetter (p + 1) l]) hT.2 (by
      simp only [morseOut_append_phaseTools, morseOut, morseLetterOut, shiftLetter]
      omega)
    rw [show morseOut b (l :: T) = morseOut (morseLetterOut b l) T from rfl,
      show morseShiftWord p (l :: T) = shiftLetter p l :: morseShiftWord p T from rfl,
      show morseShiftWord (p + 1) (l :: T) = shiftLetter (p + 1) l :: morseShiftWord (p + 1) T
        from rfl]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- The head shuffle of the top step: the small climbs move in between the cups. -/
theorem morseReach_headShuffle (N c : ℕ) (hc : c ≤ N) (v : MorseWord) :
    MorseReach 1 (morseCupRun 1 N ++ morseClimbRun c ++ v)
      (morseHeadRun c ++ morseCupRun (c + 1) N ++ v) := by
  induction c generalizing v with
  | zero => exact ⟨[], by simp [morseApplyAll, morseClimbRun, morseHeadRun]⟩
  | succ c ih =>
    have h1 := ih (by omega) ((MorseKind.cross true, c) :: v)
    have hmap : (morseCupRun (c + 2) N).map (fun b ↦ (b.1, b.2 +
        morseKindOut (MorseKind.cross true, c).1 - morseKindIn (MorseKind.cross true, c).1)) =
        morseCupRun (c + 2) N :=
      List.map_id'' (fun b ↦ by simp [morseKindOut_cross_phaseTools,
        morseKindIn_cross_phaseTools]) _
    have hout : morseOut 1 (morseHeadRun c ++ [(MorseKind.cup, c + 1)]) = 2 * c + 3 := by
      rw [morseOut_append_phaseTools, (morseOut_fits_headRun_phaseTools 1 c le_rfl).1]
      simp only [morseOut, morseLetterOut, morseKindOut_cup_phaseTools,
        morseKindIn_cup_phaseTools]
      omega
    have h2 := morseReach_symm (morseReach_sweep_phaseTools 1
      (morseHeadRun c ++ [(MorseKind.cup, c + 1)]) (morseCupRun (c + 2) N) v
      (MorseKind.cross true, c)
      (fun b hb ↦ by
        have := (mem_morseCupRun_phaseTools hb).2
        simp only [morseKindIn_cross_phaseTools]
        omega)
      (by
        rw [hout, morseFits_append_iff_phaseTools,
          morseOut_morseCupRun_phaseTools _ _ _ (by omega)]
        refine ⟨morseFits_morseCupRun_phaseTools _ _ _ (by omega), ?_⟩
        simp only [morseFits_cons, morseFits_nil,
          morseKindIn_cross_phaseTools, and_true]
        omega))
    rw [hmap] at h2
    rw [morseCupRun_cons_phaseTools (c + 1) N (by omega)] at h1
    rw [morseClimbRun_succ_phaseTools, morseHeadRun_succ_phaseTools]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-! ### Arities and positions -/

theorem morseOut_append (n : ℕ) (u v : MorseWord) :
    morseOut n (u ++ v) = morseOut (morseOut n u) v :=
  morseOut_append_phaseTools n u v

theorem morseFits_append (n : ℕ) (u v : MorseWord) :
    morseFits n (u ++ v) = (morseFits n u && morseFits (morseOut n u) v) :=
  morseFits_append_phaseTools n u v

theorem morseShiftWord_append (d : ℕ) (u v : MorseWord) :
    morseShiftWord d (u ++ v) = morseShiftWord d u ++ morseShiftWord d v :=
  List.map_append

theorem morseOut_morseShiftWord (n d : ℕ) (w : MorseWord) (h : morseFits n w = true) :
    morseOut (n + d) (morseShiftWord d w) = morseOut n w + d :=
  morseOut_morseShiftWord_phaseTools n d w h

theorem morseFits_morseShiftWord (n d e : ℕ) (w : MorseWord) (h : morseFits n w = true) :
    morseFits (n + d + e) (morseShiftWord d w) = true :=
  morseFits_morseShiftWord_phaseTools n d e w h

/-- A word of crossings does not change the number of strands. -/
theorem morseOut_of_cross (n : ℕ) (x : MorseWord) (hx : ∀ b ∈ x, ∃ s, b.1 = MorseKind.cross s) :
    morseOut n x = n :=
  morseOut_of_cross_phaseTools n x hx

/-- A word of crossings fits when every crossing does. -/
theorem morseFits_of_cross (n : ℕ) (x : MorseWord) (hx : ∀ b ∈ x, ∃ s, b.1 = MorseKind.cross s)
    (hp : ∀ b ∈ x, b.2 + 2 ≤ n) : morseFits n x = true :=
  morseFits_of_cross_phaseTools n x hx hp

/-- The letters of a band `b(i, j)`, `i < j`, are crossings at the positions `i … j-1`. -/
theorem mem_morseBand {i j : ℕ} (hij : i < j) {b : MorseLetter} (hb : b ∈ morseBand i j) :
    (∃ s, b.1 = MorseKind.cross s) ∧ i ≤ b.2 ∧ b.2 + 1 ≤ j := by
  simp only [morseBand, morseOfBraid, surfaceBand, List.mem_map, List.mem_append,
    List.mem_range, List.mem_singleton] at hb
  obtain ⟨g, hg, rfl⟩ := hb
  rcases hg with (⟨x, hx, rfl⟩ | rfl) | ⟨x, hx, rfl⟩ <;>
    exact ⟨⟨_, rfl⟩, by simp only; omega, by simp only; omega⟩

/-- The letters of a staircase `morseStairRun a b` are crossings at the positions `a … b+1`. -/
theorem mem_morseStairRun {a c : ℕ} {b : MorseLetter} (hb : b ∈ morseStairRun a c) :
    (∃ s, b.1 = MorseKind.cross s) ∧ a ≤ b.2 ∧ b.2 ≤ c + 1 := by
  simp only [morseStairRun, List.mem_flatMap, List.mem_reverse, List.mem_range] at hb
  obtain ⟨x, hx, hb⟩ := hb
  have := mem_morseBand (by omega : a + x < a + x + 2) hb
  exact ⟨this.1, by omega, by omega⟩

/-- The letters of a walk are crossings at the positions `p … p+len-1`. -/
theorem mem_morseWalk {s : Bool} {p len : ℕ} {b : MorseLetter} (hb : b ∈ morseWalk s p len) :
    b.1 = MorseKind.cross s ∧ p ≤ b.2 ∧ b.2 + 1 ≤ p + len :=
  mem_morseWalk_phaseTools hb

/-- A band peels: `b(i, j+1) = σ_j b(i, j) σ_j⁻¹` for `i < j`. -/
theorem morseBand_succ (i j : ℕ) (hij : i < j) :
    morseBand i (j + 1) = (MorseKind.cross true, j) :: (morseBand i j ++ [(MorseKind.cross false, j)]) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - i - 1, by omega⟩
  have hA : (List.range (k + 1)).map (fun x ↦ (i + 1 + k + 1 - 1 - x, true)) =
      (i + 1 + k, true) :: (List.range k).map (fun x ↦ (i + 1 + k - 1 - x, true)) := by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.cons.injEq, Prod.mk.injEq, and_true]
    refine ⟨by omega, List.map_congr_left fun x _ ↦ ?_⟩
    simp only [Function.comp, Nat.succ_eq_add_one, Prod.mk.injEq, and_true]
    omega
  have hB : (List.range (k + 1)).map (fun x ↦ (i + 1 + x, false)) =
      (List.range k).map (fun x ↦ (i + 1 + x, false)) ++ [(i + 1 + k, false)] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
  simp only [morseBand, morseOfBraid, surfaceBand]
  rw [show i + 1 + k + 1 - i - 1 = k + 1 by omega, show i + 1 + k - i - 1 = k by omega, hA, hB]
  simp

theorem morseOut_morseCupRun (n a b : ℕ) (ha : a ≤ n) :
    morseOut n (morseCupRun a b) = n + 2 * (b + 1 - a) :=
  morseOut_morseCupRun_phaseTools n a b ha

theorem morseOut_morseHeadRun (n c : ℕ) (hn : 1 ≤ n) : morseOut n (morseHeadRun c) = n + 2 * c :=
  (morseOut_fits_headRun_phaseTools n c hn).1

end AJConjecture
