import Mathlib
import AJHandoff.TorusKnot.PairKIsoCore

/-!
# Beads on a doubled long knot

A *band bead* is a tangle `T` on two strands (`morseFits 2 T`, `morseOut 2 T = 2`) placed on the
band `2p, 2p + 1` of a doubled word `morseDouble G`; an *edge bead* is a tangle on one strand (a
curl) placed on one edge. A bead slides along the band following the knot `G`: through a doubled
crossing it moves to the other band (`morseReach_beadD_left`/`_right` of the library, shifted);
around a doubled cap or cup it turns and is rotated by `π` (`isoRot`). `isoTurns G` counts the cups
and caps of `G`; for a connected `G` a bead entering at the bottom end makes that many turns
before it reaches the top end.

Beads used by the isotopy: the negative half twist `−0` and the full twist `−0 −0` (invariant under
`isoRot`), the four curls on an edge, the doubled curls `morseDouble (isoCurlR s 0)` and the
conjugated clasp `C_S = −0 · claspWord · +0` (`isoRot 2 C_S = +0 · claspWord · −0`).
-/

namespace AJConjecture

/-- Rotation by `π` of a letter read on `a` strands below and `b` strands above. -/
def isoRotLetter (a : ℕ) : MorseLetter → MorseLetter
  | (.cup, i) => (.cap, a - i)
  | (.cap, i) => (.cup, a - 2 - i)
  | (.cross s, i) => (.cross s, a - 2 - i)

/-- Rotation by `π` of a word on `n` strands: the word read backwards, cups and caps exchanged,
positions mirrored in each slice. -/
def isoRot (n : ℕ) : MorseWord → MorseWord
  | [] => []
  | l :: w => isoRot (morseLetterOut n l) w ++ [isoRotLetter n l]

/-- The number of cups and caps of a word. -/
def isoTurns (G : MorseWord) : ℕ := (G.filter fun l ↦ match l.1 with
  | .cross _ => false
  | _ => true).length

/-- The conjugated clasp (band bead). -/
def isoClaspS : MorseWord := [isoX false 0] ++ claspWord ++ [isoX true 0]

/-- The rotated conjugated clasp. -/
theorem isoRot_isoClaspS : isoRot 2 isoClaspS = [isoX true 0] ++ claspWord ++ [isoX false 0] := by
  decide

/-- A twist is invariant under rotation. -/
theorem isoRot_replicate_twist (m : ℕ) :
    isoRot 2 (List.replicate m (isoX false 0)) = List.replicate m (isoX false 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, isoRot]
    show isoRot 2 _ ++ [isoX false 0] = _
    rw [ih, ← List.replicate_succ', List.replicate_succ]

/-! ### Generic exchanges of words acting on disjoint strands -/

/-- A fitting word, with extra idle strands on its right, still fits. -/
theorem morseFits_add_right_iso (n e : ℕ) (w : MorseWord) (h : morseFits n w = true) :
    morseFits (n + e) w = true := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    rw [morseFits_cons] at h ⊢
    refine ⟨by omega, ?_⟩
    rw [show morseLetterOut (n + e) l = morseLetterOut n l + e by
      simp only [morseLetterOut]; omega]
    exact ih _ h.2

/-- One letter on the right passes a word acting on the strands to its left. -/
private theorem morseReach_isoLetterComm (n₀ b e : ℕ) (y : MorseLetter) (v : MorseWord)
    (hy : y.2 + morseKindIn y.1 ≤ b) :
    ∀ (M : ℕ) (u X : MorseWord), morseFits M X = true → morseOut n₀ u = M + b + e →
      MorseReach n₀ (u ++ shiftLetter M y :: X ++ v) (u ++ X ++ shiftLetter (morseOut M X) y :: v)
  | M, u, [], _, _ => by simpa [morseOut] using morseReach_refl n₀ (u ++ shiftLetter M y :: v)
  | M, u, x :: X, hX, hu => by
    rw [morseFits_cons] at hX
    have hx1 := hX.1
    obtain ⟨kx, px⟩ := x
    obtain ⟨ky, py⟩ := y
    simp only at hx1 hy
    have hok : morseRuleOk (MorseRule.exch (kx, px) (shiftLetter M (ky, py))) = true := by
      simp only [morseRuleOk, shiftLetter]; exact decide_eq_true (by omega)
    have hl : morseFits (morseOut n₀ u)
        (morseRuleLhs (MorseRule.exch (kx, px) (shiftLetter M (ky, py)))) = true := by
      rw [hu]
      simp only [morseRuleLhs, shiftLetter, morseFits_cons, morseFits_nil, morseLetterOut,
        and_true]
      cases kx <;> cases ky <;> simp only [morseKindIn, morseKindOut] at hx1 hy ⊢ <;> omega
    have hr : morseFits (morseOut n₀ u)
        (morseRuleRhs (MorseRule.exch (kx, px) (shiftLetter M (ky, py)))) = true := by
      rw [hu]
      simp only [morseRuleRhs, shiftLetter, morseFits_cons, morseFits_nil, morseLetterOut,
        and_true]
      cases kx <;> cases ky <;> simp only [morseKindIn, morseKindOut] at hx1 hy ⊢ <;> omega
    have h1 := morseReach_symm (morseReach_isoRule n₀ u (X ++ v) _ hok hl hr)
    have e1 : ((ky, py + M + morseKindOut kx - morseKindIn kx) : MorseLetter) =
        shiftLetter (morseLetterOut M (kx, px)) (ky, py) := by
      simp only [shiftLetter, morseLetterOut, Prod.mk.injEq, true_and]; omega
    simp only [morseRuleLhs, morseRuleRhs, shiftLetter] at h1
    rw [show ((ky, py + M + morseKindOut kx - morseKindIn kx) : MorseLetter) =
      shiftLetter (morseLetterOut M (kx, px)) (ky, py) from e1] at h1
    have h2 := morseReach_isoLetterComm n₀ b e (ky, py) v hy (morseLetterOut M (kx, px))
      (u ++ [(kx, px)]) X hX.2 (by
      rw [morseOut_append, hu]
      simp only [morseOut, morseLetterOut]
      omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append, morseOut] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A word `Y` on `b` strands at the position `M` exchanges with a word `X` acting on the first
`M` strands (`Y` is shifted by the change of the number of strands on its left). -/
theorem morseReach_isoShiftComm (n₀ M b e : ℕ) (u X Y v : MorseWord)
    (hX : morseFits M X = true) (hY : morseFits b Y = true) (hu : morseOut n₀ u = M + b + e) :
    MorseReach n₀ (u ++ morseShiftWord M Y ++ X ++ v)
      (u ++ X ++ morseShiftWord (morseOut M X) Y ++ v) := by
  induction Y generalizing u b with
  | nil => simpa [morseShiftWord] using morseReach_refl n₀ (u ++ X ++ v)
  | cons y Y ih =>
    rw [morseFits_cons] at hY
    have h1 := ih (morseLetterOut b y) (u ++ [shiftLetter M y]) hY.2 (by
      rw [morseOut_append, hu]
      simp only [morseOut, morseLetterOut, shiftLetter]
      omega)
    have h2 := morseReach_isoLetterComm n₀ b e y (morseShiftWord (morseOut M X) Y ++ v) hY.1 M u
      X hX hu
    simp only [morseShiftWord, List.map_cons, List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- Shifts compose. -/
theorem morseShiftWord_shift_iso (a b : ℕ) (w : MorseWord) :
    morseShiftWord a (morseShiftWord b w) = morseShiftWord (b + a) w := by
  simp only [morseShiftWord, List.map_map]
  exact List.map_congr_left fun l _ ↦ by simp [shiftLetter, Nat.add_assoc]

/-- Shifting by zero does nothing. -/
theorem morseShiftWord_zero_iso (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- A tangle on `b` strands placed at `m` on `m + b + e` strands. -/
theorem morseOut_shift_iso (m b e : ℕ) (T : MorseWord) (hT : morseFits b T = true) :
    morseOut (m + b + e) (morseShiftWord m T) = m + morseOut b T + e ∧
      morseFits (m + b + e) (morseShiftWord m T) = true :=
  morseOut_fits_shift b m e T hT

/-- A rotated letter fits on the strands after the letter and gives back the strands before. -/
theorem isoRotLetter_fits (n : ℕ) (l : MorseLetter) (h : l.2 + morseKindIn l.1 ≤ n) :
    (isoRotLetter n l).2 + morseKindIn (isoRotLetter n l).1 ≤ morseLetterOut n l ∧
      morseLetterOut (morseLetterOut n l) (isoRotLetter n l) = n := by
  obtain ⟨k, i⟩ := l
  cases k <;> simp only [isoRotLetter, morseLetterOut, morseKindIn, morseKindOut] at h ⊢ <;> omega

/-- A rotated word fits on the strands at the end of the word and gives back the strands at its
start. -/
theorem isoRot_fits : ∀ (T : MorseWord) (n : ℕ), morseFits n T = true →
    morseFits (morseOut n T) (isoRot n T) = true ∧ morseOut (morseOut n T) (isoRot n T) = n
  | [], _, _ => ⟨rfl, rfl⟩
  | l :: T, n, h => by
    rw [morseFits_cons] at h
    obtain ⟨h1, h2⟩ := isoRot_fits T (morseLetterOut n l) h.2
    have hl := isoRotLetter_fits n l h.1
    simp only [isoRot, morseOut, morseFits_append, morseOut_append, h1, h2, Bool.true_and]
    exact ⟨by rw [morseFits_cons]; exact ⟨hl.1, rfl⟩, hl.2⟩

/-- Rotating a letter twice gives it back. -/
theorem isoRotLetter_isoRotLetter (n : ℕ) (l : MorseLetter) (h : l.2 + morseKindIn l.1 ≤ n) :
    isoRotLetter (morseLetterOut n l) (isoRotLetter n l) = l := by
  obtain ⟨k, i⟩ := l
  cases k <;> simp only [isoRotLetter, morseLetterOut, morseKindIn, morseKindOut,
    Prod.mk.injEq, true_and] at h ⊢ <;> omega

/-- Rotation of a concatenation. -/
theorem isoRot_append (n : ℕ) (x y : MorseWord) :
    isoRot n (x ++ y) = isoRot (morseOut n x) y ++ isoRot n x := by
  induction x generalizing n with
  | nil => simp [isoRot, morseOut]
  | cons l x ih => simp [isoRot, morseOut, ih]

end AJConjecture
