import Mathlib
import AJFamily.Skein.TorusPhaseTwoSwing
import AJFamily.Skein.TorusPhaseTwoPass

/-!
# Stage C of phase II: the edge curls cancel

`phaseTwo_stageC`: the edge curls of `phaseTwoWS k` cancel, giving `phaseTwoWC k`. A curl is
a bead on one strand: it passes crossings and doubled crossings by fixed macros (checked here by
`decide`) or by `morseReach_beadD_pow`, and passes words lying entirely to one side of it by
exchanges. The curls after the doubled crossings travel in two passes, bottom-up and top-down, and
cancel the curls of the `A` blocks.
-/

namespace AJConjecture

/-! ### Words -/

/-- A negative full twist of the input band `(0,1)`. -/
private def curlsTw : MorseWord := [(.cross false, 0), (.cross false, 0)]

/-- A negative left curl on the strand `1`. -/
private def curlsNeg : MorseWord := [(.cup, 1), (.cross false, 2), (.cap, 1)]

/-- A positive left curl on the strand `1`. -/
private def curlsPos : MorseWord := [(.cup, 1), (.cross true, 2), (.cap, 1)]

/-- A positive left curl on the strand `3`. -/
private def curlsPos3 : MorseWord := [(.cup, 3), (.cross true, 4), (.cap, 3)]

/-- A positive right curl on the strand `2` (the return strand at the top and at the bottom). -/
private def curlsR2 : MorseWord := [(.cup, 3), (.cross true, 2), (.cap, 3)]

/-- A negative right curl on the strand `4`. -/
private def curlsR4 : MorseWord := [(.cup, 5), (.cross false, 4), (.cap, 5)]

/-- The doubled closing cup. -/
private def curlsCups : MorseWord := [(.cup, 2), (.cup, 3)]

/-- The fold twist and the doubled closing cap. -/
private def curlsTail : MorseWord := [(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2)]

/-- The hook of the clasp without its last crossing. -/
private def curlsHook : MorseWord := [(.cup, 6), (.cross true, 5), (.cross false, 4)]

/-- The X tip at the strand `3`. -/
private def curlsX3 : MorseWord := [(.cup, 3), (.cross false, 4), (.cap, 3), (.cap, 3)]

/-- The X tip at the strand `5`. -/
private def curlsX5 : MorseWord := [(.cup, 5), (.cross false, 6), (.cap, 5), (.cap, 5)]

/-- Two doubled crossings and a positive curl. -/
private def curlsDDC : MorseWord := phaseTwoD ++ phaseTwoD ++ curlsPos

/-- Two `B` blocks. -/
private def curlsBB : MorseWord := phaseTwoB1 ++ phaseTwoB1

/-- The word during the first pass: `r` curls after `D_(2j)` cancelled. -/
private def curlsWordB (k r : ℕ) : MorseWord :=
  [(.cup, 1)] ++ curlsTw ++ phaseTwoBlk phaseTwoA1 (2 * k - 1 - r) ++ phaseTwoBlk curlsTw r ++
    curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++ phaseTwoBlk curlsDDC r ++
    phaseTwoBlk curlsBB (k - 1 - r) ++ phaseTwoD ++ curlsPos ++ phaseTwoD ++ curlsTail ++
    [(.cap, 1)]

/-- The word during the second pass: `s` curls after `D_(2j+1)` cancelled. -/
private def curlsWordA (k s : ℕ) : MorseWord :=
  [(.cup, 1)] ++ phaseTwoBlk curlsTw (s + 1) ++ phaseTwoBlk phaseTwoA1 (k - 1 - s) ++
    phaseTwoBlk curlsTw k ++ curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++
    phaseTwoBlk curlsDDC (k - 1 - s) ++ phaseTwoBlk phaseTwoD (2 * s + 2) ++ curlsTail ++
    [(.cap, 1)]

/-! ### Generic helpers -/

/-- Shifting by zero strands does nothing. -/
private theorem morseShiftWord_zero_curls (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- A run of blocks grows at the front. -/
private theorem phaseTwoBlk_succ_curls (y : MorseWord) (m : ℕ) :
    phaseTwoBlk y (m + 1) = y ++ phaseTwoBlk y m := by
  simp [phaseTwoBlk, List.replicate_succ]

/-- A run of blocks grows at the end. -/
private theorem phaseTwoBlk_succ'_curls (y : MorseWord) (m : ℕ) :
    phaseTwoBlk y (m + 1) = phaseTwoBlk y m ++ y := by
  simp [phaseTwoBlk, List.replicate_succ']

/-- Blocks of a strand-neutral word are strand-neutral. -/
private theorem morseOut_phaseTwoBlk_curls (n m : ℕ) (y : MorseWord) (hy : morseOut n y = n) :
    morseOut n (phaseTwoBlk y m) = n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [phaseTwoBlk_succ_curls, morseOut_append, hy, ih]

/-- A fixed macro applied after a prefix with the right number of strands. -/
private theorem morseReach_at_curls (n n₀ : ℕ) (u v w w' : MorseWord) (h : MorseReach n w w')
    (hf : morseFits n w = true) (hu : morseOut n₀ u = n) :
    MorseReach n₀ (u ++ w ++ v) (u ++ w' ++ v) := by
  have h' := morseReach_frame n n₀ 0 0 u v w w' h hf (by omega)
  rwa [morseShiftWord_zero_curls, morseShiftWord_zero_curls] at h'

/-- Interchange: a word `Y` lying to the right of a word `X` moves below it (exchanges only). -/
private theorem morseReach_interchange_curls (n₀ d a b : ℕ) (u v X Y : MorseWord)
    (hX : morseFits a X = true) (hY : morseFits b Y = true) (hu : d + a + b ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord d X ++ morseShiftWord (d + morseOut a X) Y ++ v)
      (u ++ morseShiftWord (d + a) Y ++ morseShiftWord d X ++ v) := by
  induction X generalizing a u with
  | nil =>
    simpa [morseShiftWord, morseOut] using morseReach_refl n₀ (u ++ morseShiftWord (d + a) Y ++ v)
  | cons x X ih =>
    simp only [morseFits, Bool.and_eq_true, decide_eq_true_eq] at hX
    obtain ⟨hx, hX⟩ := hX
    have h1 := ih (morseLetterOut a x) (u ++ [shiftLetter d x]) hX (by
      rw [morseOut_append]
      simp only [morseOut, morseLetterOut, shiftLetter] at hx ⊢
      omega)
    obtain ⟨e, he⟩ : ∃ e, morseOut n₀ u = b + (d + a) + e :=
      ⟨morseOut n₀ u - (b + (d + a)), by omega⟩
    have h2 := morseReach_sweep n₀ u (morseShiftWord (d + a) Y) (morseShiftWord d X ++ v)
      (shiftLetter d x)
      (fun c hc ↦ by
        simp only [morseShiftWord, List.mem_map] at hc
        obtain ⟨c0, -, rfl⟩ := hc
        simp only [shiftLetter]
        omega)
      (by
        rw [morseFits_append, he, morseFits_morseShiftWord b (d + a) e Y hY, Bool.true_and,
          show b + (d + a) + e = b + e + (d + a) by omega,
          morseOut_morseShiftWord _ _ _ (by
            have := morseFits_morseShiftWord b 0 e Y hY
            rwa [morseShiftWord_zero_curls, Nat.add_zero] at this),
          morseOut_add_right b e Y hY]
        simp only [morseFits, shiftLetter, Bool.and_true]
        exact decide_eq_true (by omega))
    have hmap : (morseShiftWord (d + a) Y).map (fun c ↦ (c.1, c.2 +
        morseKindOut (shiftLetter d x).1 - morseKindIn (shiftLetter d x).1)) =
        morseShiftWord (d + morseLetterOut a x) Y := by
      simp only [morseShiftWord, List.map_map]
      refine List.map_congr_left fun c _ ↦ ?_
      simp only [Function.comp, shiftLetter, morseLetterOut]
      congr 1
      omega
    rw [hmap] at h2
    rw [show morseShiftWord d (x :: X) = shiftLetter d x :: morseShiftWord d X from rfl,
      show morseOut a (x :: X) = morseOut (morseLetterOut a x) X from rfl]
    simp only [List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A word `T` passes a run of blocks `y` downwards when it passes one block. -/
private theorem morseReach_runPass_curls (n₀ n m : ℕ) (u v y T : MorseWord)
    (h : MorseReach n (y ++ T) (T ++ y)) (hf : morseFits n (y ++ T) = true)
    (hy : morseOut n y = n) (hu : morseOut n₀ u = n) :
    MorseReach n₀ (u ++ phaseTwoBlk y m ++ T ++ v) (u ++ T ++ phaseTwoBlk y m ++ v) := by
  induction m generalizing v with
  | zero => simpa [phaseTwoBlk] using morseReach_refl n₀ (u ++ T ++ v)
  | succ m ih =>
    have h1 := morseReach_at_curls n n₀ (u ++ phaseTwoBlk y m) v _ _ h hf
      (by rw [morseOut_append, hu, morseOut_phaseTwoBlk_curls n m y hy])
    have h2 := ih (y ++ v)
    rw [phaseTwoBlk_succ'_curls]
    simp only [List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- Macro `CAPM`: a negative left curl goes around the cap that follows it and becomes a right curl.
  -/
private theorem morseReach_curlsCAPM :
    MorseReach 2
      [(.cup, 0), (.cross false, 1), (.cap, 0), (.cap, 0)]
      [(.cup, 2), (.cross false, 1), (.cap, 2), (.cap, 0)] :=
  ⟨[(2, .exch (.cap, 0) (.cap, 2), false), (3, .zig 1 false, true),
    (4, .capSlide 0 false true, true), (6, .exch (.cap, 0) (.cap, 2), false),
    (3, .exch (.cross false, 0) (.cup, 2), true), (2, .exch (.cross false, 0) (.cap, 2), true),
    (0, .cupSlide 0 false false, false), (0, .zig 1 true, false)], by decide⟩

/-- Macro `CAPP`: the top curl goes around the cap of the return strand. -/
private theorem morseReach_curlsCAPP :
    MorseReach 3 (curlsPos ++ [(.cap, 1)])
      (curlsR2 ++ [(.cap, 1)]) :=
  ⟨[(2, .exch (.cap, 1) (.cap, 3), false), (3, .zig 2 false, true),
    (4, .capSlide 1 true true, true), (6, .exch (.cap, 1) (.cap, 3), false),
    (3, .exch (.cross true, 1) (.cup, 3), true), (2, .exch (.cross true, 1) (.cap, 3), true),
    (0, .cupSlide 1 true false, false), (0, .zig 2 true, false)], by decide⟩

/-- Macro `CUPP`: a positive right curl on the return strand goes around the bottom cup. -/
private theorem morseReach_curlsCUPP :
    MorseReach 1 ([(.cup, 1)] ++ curlsR2)
      ([(.cup, 1)] ++ curlsPos) :=
  ⟨[(0, .exch (.cup, 1) (.cup, 1), false), (1, .zig 1 false, true),
    (1, .cupSlide 2 true true, true), (0, .exch (.cup, 1) (.cup, 1), false),
    (3, .exch (.cap, 1) (.cross true, 3), true), (4, .exch (.cup, 1) (.cross true, 1), true),
    (5, .capSlide 2 true false, false), (4, .zig 1 true, false)], by decide⟩

/-- Macro `CANPM`: a positive and a negative left curl cancel (one `kink`). -/
private theorem morseReach_curlsCANPM :
    MorseReach 3 (curlsPos ++ curlsNeg)
      [] :=
  ⟨[(3, .kink 1 false, true), (1, .r2 1 false, true), (2, .capSlide 1 true true, false),
    (2, .exch (.cup, 2) (.cap, 2), true), (2, .cupSlide 2 false true, true),
    (1, .exch (.cross false, 1) (.cup, 3), false), (0, .exch (.cup, 1) (.cup, 1), false),
    (5, .exch (.cross false, 1) (.cap, 4), true),
    (4, .exch (.cross false, 1) (.cross false, 3), true), (2, .r3 1 false, false),
    (6, .exch (.cap, 2) (.cap, 4), true), (4, .capSlide 2 false true, false),
    (1, .cupSlide 1 false false, false), (1, .zig 2 true, false), (0, .zig 1 true, false),
    (2, .capSlide 1 false true, true), (1, .r2 1 true, false),
    (2, .exch (.cap, 1) (.cup, 3), false), (2, .cupSlide 2 false false, true),
    (1, .exch (.cup, 2) (.cross false, 2), true), (0, .exch (.cup, 2) (.cup, 2), true),
    (5, .exch (.cap, 1) (.cross false, 4), false),
    (4, .exch (.cross false, 2) (.cross false, 4), false), (2, .r3 3 false, true),
    (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 false false, false),
    (1, .cupSlide 3 false true, false), (1, .zig 2 false, false), (0, .zig 1 false, false)],
    by decide⟩

/-- Macro `CANMP`: a negative and a positive left curl cancel (one `kink`). -/
private theorem morseReach_curlsCANMP :
    MorseReach 3 (curlsNeg ++ curlsPos)
      [] :=
  ⟨[(3, .kink 1 true, true), (1, .r2 1 true, true), (2, .capSlide 1 false true, false),
    (2, .exch (.cup, 2) (.cap, 2), true), (2, .cupSlide 2 true true, true),
    (1, .exch (.cross true, 1) (.cup, 3), false), (0, .exch (.cup, 1) (.cup, 1), false),
    (5, .exch (.cross true, 1) (.cap, 4), true),
    (4, .exch (.cross true, 1) (.cross true, 3), true), (2, .r3 1 true, false),
    (6, .exch (.cap, 2) (.cap, 4), true), (4, .capSlide 2 true true, false),
    (1, .cupSlide 1 true false, false), (1, .zig 2 true, false), (0, .zig 1 true, false),
    (2, .capSlide 1 true true, true), (1, .r2 1 false, false),
    (2, .exch (.cap, 1) (.cup, 3), false), (2, .cupSlide 2 true false, true),
    (1, .exch (.cup, 2) (.cross true, 2), true), (0, .exch (.cup, 2) (.cup, 2), true),
    (5, .exch (.cap, 1) (.cross true, 4), false),
    (4, .exch (.cross true, 2) (.cross true, 4), false), (2, .r3 3 true, true),
    (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 true false, false),
    (1, .cupSlide 3 true true, false), (1, .zig 2 false, false), (0, .zig 1 false, false)],
    by decide⟩

/-- Macro `TW`: a positive left curl passes a negative full twist of the input band. -/
private theorem morseReach_curlsTW :
    MorseReach 3 (curlsTw ++ curlsPos)
      (curlsPos ++ curlsTw) :=
  ⟨[(2, .cupSlide 0 false false, true), (1, .exch (.cup, 0) (.cross false, 0), true),
    (5, .r2 1 false, true), (6, .capSlide 1 true true, false), (3, .r3 0 false, true),
    (5, .exch (.cross false, 0) (.cap, 2), false),
    (2, .exch (.cross false, 0) (.cross false, 2), true), (3, .capSlide 1 false false, false),
    (3, .capSlide 0 true true, true), (2, .r2 0 false, false), (3, .r2 0 true, true),
    (1, .cupSlide 0 true false, false), (1, .cupSlide 1 false true, true),
    (3, .exch (.cross false, 0) (.cross false, 2), true),
    (4, .exch (.cap, 0) (.cross false, 2), true),
    (0, .exch (.cross false, 0) (.cup, 2), false), (1, .r3 0 false, false),
    (2, .capSlide 0 false true, false), (0, .cupSlide 1 true false, true),
    (2, .r2 1 true, false)], by decide⟩

/-- Macro `DC`: a positive left curl passes a doubled crossing (left band to right band). -/
private theorem morseReach_curlsDC :
    MorseReach 7 (phaseTwoD ++ curlsPos)
      (curlsPos3 ++ phaseTwoD) :=
  ⟨[(3, .exch (.cup, 1) (.cross true, 1), true), (3, .cupSlide 1 true true, true),
    (5, .r3 2 true, false), (7, .exch (.cap, 1) (.cross true, 3), true),
    (4, .exch (.cross true, 1) (.cross true, 3), false), (5, .capSlide 1 true true, false),
    (2, .exch (.cross true, 0) (.cup, 2), false),
    (3, .exch (.cross true, 0) (.cross true, 3), false),
    (4, .exch (.cross true, 0) (.cap, 2), false), (1, .exch (.cup, 2) (.cross true, 2), true),
    (1, .cupSlide 2 true true, true), (3, .r3 3 true, false),
    (5, .exch (.cap, 2) (.cross true, 4), true),
    (2, .exch (.cross true, 2) (.cross true, 4), false), (3, .capSlide 2 true true, false),
    (0, .exch (.cross true, 1) (.cup, 3), false),
    (1, .exch (.cross true, 1) (.cross true, 4), false),
    (2, .exch (.cross true, 1) (.cap, 3), false)], by decide⟩

/-- Macro `DDC`: a positive left curl on the right band passes two doubled crossings and a curl. -/
private theorem morseReach_curlsDDC :
    MorseReach 7 (curlsDDC ++ curlsPos3)
      (curlsPos3 ++ curlsDDC) :=
  ⟨[(10, .exch (.cap, 1) (.cup, 5), false), (11, .exch (.cap, 1) (.cross true, 6), false),
    (12, .exch (.cap, 1) (.cap, 5), false), (9, .exch (.cross true, 2) (.cup, 5), false),
    (10, .exch (.cross true, 2) (.cross true, 6), false),
    (11, .exch (.cross true, 2) (.cap, 5), false), (8, .exch (.cup, 1) (.cup, 3), false),
    (9, .exch (.cup, 1) (.cross true, 4), false), (10, .exch (.cup, 1) (.cap, 3), false),
    (7, .exch (.cross true, 1) (.cup, 3), false),
    (8, .exch (.cross true, 1) (.cross true, 4), false),
    (9, .exch (.cross true, 1) (.cap, 3), false), (6, .exch (.cross true, 0) (.cup, 3), false),
    (7, .exch (.cross true, 0) (.cross true, 4), false),
    (8, .exch (.cross true, 0) (.cap, 3), false), (6, .cupSlide 2 true false, true),
    (5, .exch (.cup, 2) (.cross true, 2), true),
    (8, .exch (.cross true, 2) (.cross true, 4), false), (6, .r3 3 true, true),
    (8, .capSlide 2 true false, false), (7, .exch (.cap, 2) (.cross true, 4), true),
    (5, .cupSlide 1 true false, true), (4, .exch (.cup, 1) (.cross true, 1), true),
    (7, .exch (.cross true, 1) (.cross true, 3), false), (5, .r3 2 true, true),
    (7, .capSlide 1 true false, false), (6, .exch (.cap, 1) (.cross true, 3), true),
    (3, .exch (.cup, 1) (.cross true, 1), true), (3, .cupSlide 1 true true, true),
    (5, .r3 2 true, false), (7, .exch (.cap, 1) (.cross true, 3), true),
    (4, .exch (.cross true, 1) (.cross true, 3), false), (5, .capSlide 1 true true, false),
    (2, .exch (.cross true, 0) (.cup, 2), false),
    (3, .exch (.cross true, 0) (.cross true, 3), false),
    (4, .exch (.cross true, 0) (.cap, 2), false), (1, .exch (.cup, 2) (.cross true, 2), true),
    (1, .cupSlide 2 true true, true), (3, .r3 3 true, false),
    (5, .exch (.cap, 2) (.cross true, 4), true),
    (2, .exch (.cross true, 2) (.cross true, 4), false), (3, .capSlide 2 true true, false),
    (0, .exch (.cross true, 1) (.cup, 3), false),
    (1, .exch (.cross true, 1) (.cross true, 4), false),
    (2, .exch (.cross true, 1) (.cap, 3), false)], by decide⟩

/-- Macro `BOT`: a positive left curl on the right band passes the clasp, a doubled crossing and the
  doubled closing cup. -/
private theorem morseReach_curlsBOT :
    MorseReach 3 (curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++ curlsPos3)
      (curlsPos ++ curlsCups ++ phaseTwoD ++ phaseTwoClaspS) :=
  ⟨[(11, .exch (.cup, 3) (.cross true, 4), true),
    (12, .exch (.cross true, 4) (.cross true, 6), true),
    (13, .exch (.cap, 3) (.cross true, 6), true), (10, .exch (.cup, 3) (.cap, 4), true),
    (11, .exch (.cross true, 4) (.cap, 6), true), (12, .exch (.cap, 3) (.cap, 6), true),
    (9, .exch (.cup, 3) (.cross true, 5), true),
    (10, .exch (.cross true, 4) (.cross true, 7), true),
    (11, .exch (.cap, 3) (.cross true, 7), true), (8, .exch (.cup, 3) (.cross true, 5), true),
    (9, .exch (.cross true, 4) (.cross true, 7), true),
    (10, .exch (.cap, 3) (.cross true, 7), true), (7, .exch (.cup, 3) (.cup, 6), true),
    (8, .exch (.cross true, 4) (.cup, 8), true), (9, .exch (.cap, 3) (.cup, 8), true),
    (6, .exch (.cup, 3) (.cross false, 4), true),
    (7, .exch (.cross true, 4) (.cross false, 6), true),
    (8, .exch (.cap, 3) (.cross false, 6), true), (5, .exch (.cross true, 1) (.cup, 3), false),
    (6, .exch (.cross true, 1) (.cross true, 4), false),
    (7, .exch (.cross true, 1) (.cap, 3), false), (4, .exch (.cross true, 0) (.cup, 3), false),
    (5, .exch (.cross true, 0) (.cross true, 4), false),
    (6, .exch (.cross true, 0) (.cap, 3), false), (4, .cupSlide 2 true false, true),
    (3, .exch (.cup, 2) (.cross true, 2), true),
    (6, .exch (.cross true, 2) (.cross true, 4), false), (4, .r3 3 true, true),
    (6, .capSlide 2 true false, false), (5, .exch (.cap, 2) (.cross true, 4), true),
    (3, .cupSlide 1 true false, true), (2, .exch (.cup, 1) (.cross true, 1), true),
    (5, .exch (.cross true, 1) (.cross true, 3), false), (3, .r3 2 true, true),
    (5, .capSlide 1 true false, false), (4, .exch (.cap, 1) (.cross true, 3), true),
    (1, .exch (.cup, 1) (.cup, 3), true), (2, .exch (.cross true, 2) (.cup, 5), true),
    (3, .exch (.cap, 1) (.cup, 5), true), (0, .exch (.cup, 1) (.cup, 2), true),
    (1, .exch (.cross true, 2) (.cup, 4), true), (2, .exch (.cap, 1) (.cup, 4), true)], by decide⟩

/-- Macro `TOPX`: a positive left curl passes the fold twist and the doubled closing cap. -/
private theorem morseReach_curlsTOPX :
    MorseReach 7 (curlsPos ++ curlsTail)
      (curlsTail ++ curlsPos) :=
  ⟨[(2, .exch (.cap, 1) (.cross false, 4), false),
    (1, .exch (.cross true, 2) (.cross false, 4), false),
    (0, .exch (.cup, 1) (.cross false, 2), false),
    (3, .exch (.cap, 1) (.cross false, 4), false),
    (2, .exch (.cross true, 2) (.cross false, 4), false),
    (1, .exch (.cup, 1) (.cross false, 2), false), (4, .exch (.cap, 1) (.cap, 5), false),
    (3, .exch (.cross true, 2) (.cap, 5), false), (2, .exch (.cup, 1) (.cap, 3), false),
    (5, .exch (.cap, 1) (.cap, 4), false), (4, .exch (.cross true, 2) (.cap, 4), false),
    (3, .exch (.cup, 1) (.cap, 2), false)], by decide⟩

/-- Macro `WIN`: the X-tip curl goes around the doubled closing cup, through `D₁`, and cancels the
curl after `D₁`; the clasp then absorbs the fold curl (two `kink`s). -/
private theorem morseReach_curlsWIN :
    MorseReach 3
      (curlsCups ++ phaseTwoD ++ curlsPos ++ curlsHook ++ curlsR4 ++ [(.cross false, 5)] ++ curlsX5)
      (curlsCups ++ phaseTwoD ++ phaseTwoClaspS) :=
  ⟨[(18, .exch (.cap, 5) (.cap, 7), false), (19, .zig 6 false, true),
    (20, .capSlide 5 false true, true), (22, .exch (.cap, 5) (.cap, 7), false),
    (19, .exch (.cross false, 5) (.cup, 7), true),
    (18, .exch (.cross false, 5) (.cap, 7), true), (16, .cupSlide 5 false false, false),
    (16, .zig 6 true, false), (15, .exch (.cross false, 5) (.cup, 7), false),
    (15, .cupSlide 6 false false, true), (17, .r3 5 false, true),
    (19, .exch (.cross false, 5) (.cap, 7), false),
    (16, .exch (.cross false, 5) (.cross false, 7), true),
    (17, .capSlide 6 false false, false), (14, .exch (.cap, 5) (.cup, 8), false),
    (15, .exch (.cap, 5) (.cross false, 7), false), (16, .exch (.cap, 5) (.cap, 8), false),
    (13, .exch (.cross false, 4) (.cup, 8), false),
    (14, .exch (.cross false, 4) (.cross false, 7), false),
    (15, .exch (.cross false, 4) (.cap, 8), false), (12, .exch (.cup, 5) (.cup, 6), false),
    (13, .exch (.cup, 5) (.cross false, 5), false), (14, .exch (.cup, 5) (.cap, 6), false),
    (11, .exch (.cross false, 4) (.cup, 6), false), (11, .cupSlide 5 false false, true),
    (13, .r3 4 false, true), (15, .exch (.cross false, 4) (.cap, 6), false),
    (12, .exch (.cross false, 4) (.cross false, 6), true),
    (13, .capSlide 5 false false, false), (10, .exch (.cup, 5) (.cross true, 5), true),
    (11, .exch (.cross false, 4) (.cross true, 7), true),
    (12, .exch (.cap, 5) (.cross true, 7), true), (9, .exch (.cup, 5) (.cup, 6), true),
    (10, .exch (.cross false, 4) (.cup, 8), true), (11, .exch (.cap, 5) (.cup, 8), true),
    (8, .exch (.cap, 1) (.cup, 7), false), (9, .exch (.cap, 1) (.cross false, 6), false),
    (10, .exch (.cap, 1) (.cap, 7), false), (7, .exch (.cross true, 2) (.cup, 7), false),
    (8, .exch (.cross true, 2) (.cross false, 6), false),
    (9, .exch (.cross true, 2) (.cap, 7), false), (6, .exch (.cup, 1) (.cup, 5), false),
    (7, .exch (.cup, 1) (.cross false, 4), false), (8, .exch (.cup, 1) (.cap, 5), false),
    (5, .exch (.cross true, 1) (.cup, 5), false),
    (6, .exch (.cross true, 1) (.cross false, 4), false),
    (7, .exch (.cross true, 1) (.cap, 5), false), (4, .exch (.cross true, 0) (.cup, 5), false),
    (5, .exch (.cross true, 0) (.cross false, 4), false),
    (6, .exch (.cross true, 0) (.cap, 5), false), (3, .exch (.cross true, 2) (.cup, 5), false),
    (4, .exch (.cross true, 2) (.cross false, 4), false),
    (5, .exch (.cross true, 2) (.cap, 5), false), (2, .exch (.cross true, 1) (.cup, 5), false),
    (3, .exch (.cross true, 1) (.cross false, 4), false),
    (4, .exch (.cross true, 1) (.cap, 5), false), (1, .exch (.cup, 3) (.cup, 3), false),
    (2, .zig 3 false, true), (2, .cupSlide 4 false true, true),
    (1, .exch (.cup, 3) (.cup, 3), false), (4, .exch (.cap, 3) (.cross false, 5), true),
    (5, .exch (.cup, 3) (.cross false, 3), true), (6, .capSlide 4 false false, false),
    (5, .zig 3 true, false), (4, .exch (.cross true, 1) (.cap, 3), true),
    (3, .exch (.cross true, 1) (.cross false, 4), true),
    (2, .exch (.cross true, 1) (.cup, 3), true), (5, .r2 3 false, true),
    (3, .cupSlide 3 false false, false), (5, .capSlide 2 true true, true),
    (4, .r3 2 true, true), (3, .exch (.cross true, 2) (.cup, 4), true),
    (7, .exch (.cap, 2) (.cross true, 4), false),
    (6, .exch (.cross true, 2) (.cross true, 4), false), (4, .cupSlide 3 true true, false),
    (4, .cupSlide 2 false false, true), (6, .r2 2 false, false),
    (6, .exch (.cross true, 0) (.cap, 2), true),
    (5, .exch (.cross true, 0) (.cross false, 3), true),
    (4, .exch (.cross true, 0) (.cup, 2), true), (7, .r2 2 false, true),
    (5, .cupSlide 2 false false, false), (7, .capSlide 1 true true, true),
    (6, .r3 1 true, true), (5, .exch (.cross true, 1) (.cup, 3), true),
    (9, .exch (.cap, 1) (.cross true, 3), false),
    (8, .exch (.cross true, 1) (.cross true, 3), false), (6, .cupSlide 2 true true, false),
    (6, .cupSlide 1 false false, true), (8, .r2 1 false, false), (9, .kink 1 true, true),
    (7, .r2 1 true, true), (8, .capSlide 1 false true, false),
    (8, .exch (.cup, 2) (.cap, 2), true), (8, .cupSlide 2 true true, true),
    (7, .exch (.cross true, 1) (.cup, 3), false), (6, .exch (.cup, 1) (.cup, 1), false),
    (11, .exch (.cross true, 1) (.cap, 4), true),
    (10, .exch (.cross true, 1) (.cross true, 3), true), (8, .r3 1 true, false),
    (12, .exch (.cap, 2) (.cap, 4), true), (10, .capSlide 2 true true, false),
    (7, .cupSlide 1 true false, false), (7, .zig 2 true, false), (6, .zig 1 true, false),
    (8, .capSlide 1 true true, true), (7, .r2 1 false, false),
    (8, .exch (.cap, 1) (.cup, 3), false), (8, .cupSlide 2 true false, true),
    (7, .exch (.cup, 2) (.cross true, 2), true), (6, .exch (.cup, 2) (.cup, 2), true),
    (11, .exch (.cap, 1) (.cross true, 4), false),
    (10, .exch (.cross true, 2) (.cross true, 4), false), (8, .r3 3 true, true),
    (12, .exch (.cap, 1) (.cap, 3), false), (10, .capSlide 2 true false, false),
    (7, .cupSlide 3 true true, false), (7, .zig 2 false, false), (6, .zig 1 false, false),
    (6, .cupSlide 5 false false, true), (8, .r2 5 false, false),
    (7, .exch (.cross false, 4) (.cross false, 6), true),
    (8, .exch (.cup, 5) (.cross false, 6), true),
    (9, .exch (.cross false, 4) (.cross false, 8), true),
    (10, .exch (.cap, 5) (.cross false, 8), true), (8, .zig 4 true, true),
    (9, .zig 5 true, true), (9, .cupSlide 4 true false, true),
    (12, .capSlide 5 true true, true), (14, .exch (.cap, 5) (.cap, 7), false),
    (10, .r3 4 true, true), (12, .exch (.cross true, 4) (.cross true, 6), false),
    (13, .exch (.cross true, 4) (.cap, 7), false), (8, .exch (.cup, 4) (.cup, 4), true),
    (9, .exch (.cross true, 4) (.cup, 6), true), (10, .cupSlide 5 true true, false),
    (10, .exch (.cup, 5) (.cap, 5), false), (10, .capSlide 4 false true, true),
    (9, .r2 4 true, false), (11, .kink 4 true, false),
    (7, .exch (.cup, 4) (.cross false, 4), true), (6, .exch (.cup, 4) (.cup, 5), true),
    (9, .r2 4 true, true), (10, .capSlide 4 false true, false),
    (8, .exch (.cross true, 4) (.cross false, 6), true),
    (7, .exch (.cross true, 4) (.cup, 7), true), (13, .r2 6 false, true),
    (11, .r3 5 false, true), (10, .exch (.cap, 5) (.cross false, 7), false),
    (8, .cupSlide 6 false true, false), (8, .zig 5 false, false),
    (7, .exch (.cross true, 4) (.cross false, 6), false),
    (6, .exch (.cup, 4) (.cross false, 4), false), (7, .cupSlide 4 true true, true),
    (8, .r3 4 true, false), (10, .r2 5 true, false),
    (9, .exch (.cross true, 4) (.cross true, 6), false), (7, .cupSlide 5 true true, true),
    (9, .r3 5 true, true), (11, .capSlide 4 true false, false),
    (10, .exch (.cap, 4) (.cross true, 6), true)], by decide⟩

/-! ### The curl routes -/

/-- The top curl goes around the cap of the return strand, down the return strand, around the
bottom cup, up through `m` full twists and cancels the first `A` curl. -/
private theorem morseReach_curlsTop (m : ℕ) (S : MorseWord) (hS : morseFits 2 S = true)
    (hSo : morseOut 2 S = 2) :
    MorseReach 1 ([(.cup, 1)] ++ phaseTwoBlk curlsTw m ++ curlsNeg ++ S ++ curlsPos ++ [(.cap, 1)])
      ([(.cup, 1)] ++ phaseTwoBlk curlsTw m ++ S ++ [(.cap, 1)]) := by
  have hTw : morseOut 2 curlsTw = 2 := by decide
  have hXf : morseFits 2 (phaseTwoBlk curlsTw m ++ curlsNeg ++ S) = true := by
    simp only [morseFits_append, morseOut_append, morseOut_phaseTwoBlk_curls 2 m _ hTw,
      morseFits_phaseTwoBlk 2 m _ (by decide) hTw, hS,
      show morseFits 2 curlsNeg = true by decide, show morseOut 2 curlsNeg = 2 by decide,
      Bool.and_self]
  have hXo : morseOut 2 (phaseTwoBlk curlsTw m ++ curlsNeg ++ S) = 2 := by
    simp only [morseOut_append, morseOut_phaseTwoBlk_curls 2 m _ hTw,
      show morseOut 2 curlsNeg = 2 by decide, hSo]
  have h1 := morseReach_at_curls 3 1 ([(.cup, 1)] ++ (phaseTwoBlk curlsTw m ++ curlsNeg ++ S)) []
    _ _ morseReach_curlsCAPP (by decide) (by
      rw [morseOut_append, show morseOut 1 [(.cup, 1)] = 2 + 1 from rfl,
        morseOut_add_right 2 1 _ hXf, hXo])
  have h2 := morseReach_interchange_curls 1 0 2 1 [(.cup, 1)] [(.cap, 1)]
    (phaseTwoBlk curlsTw m ++ curlsNeg ++ S) [(.cup, 1), (.cross true, 0), (.cap, 1)] hXf
    (by decide) (by decide)
  rw [hXo, morseShiftWord_zero_curls,
    show morseShiftWord (0 + 2) [(.cup, 1), (.cross true, 0), (.cap, 1)] = curlsR2 from rfl]
    at h2
  have h3 := morseReach_at_curls 1 1 [] (phaseTwoBlk curlsTw m ++ curlsNeg ++ S ++ [(.cap, 1)])
    _ _ morseReach_curlsCUPP (by decide) rfl
  have h4 := morseReach_symm (morseReach_runPass_curls 1 3 m [(.cup, 1)]
    (curlsNeg ++ S ++ [(.cap, 1)]) curlsTw curlsPos morseReach_curlsTW (by decide) (by decide) rfl)
  have h5 := morseReach_at_curls 3 1 ([(.cup, 1)] ++ phaseTwoBlk curlsTw m) (S ++ [(.cap, 1)])
    _ _ morseReach_curlsCANPM (by decide) (by
      rw [morseOut_append, show morseOut 1 [(.cup, 1)] = 3 from rfl,
        morseOut_phaseTwoBlk_curls 3 m _ (by decide)])
  simp only [List.append_assoc, List.append_nil] at h1 h2 h3 h4 h5 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 (morseReach_trans h4 h5)))

/-- A curl after an even doubled crossing travels down to the input band, through the twists, and
cancels the last `A` curl. -/
private theorem morseReach_curlsBottom (r : ℕ) (P rest : MorseWord) (hP : morseOut 1 P = 3) :
    MorseReach 1 (P ++ curlsNeg ++ phaseTwoBlk curlsTw r ++ curlsCups ++ phaseTwoD ++
        phaseTwoClaspS ++ phaseTwoBlk curlsDDC r ++ phaseTwoD ++ curlsPos ++ rest)
      (P ++ phaseTwoBlk curlsTw r ++ curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++
        phaseTwoBlk curlsDDC r ++ phaseTwoD ++ rest) := by
  have hTw : morseOut 3 curlsTw = 3 := by decide
  have hDDC : morseOut 7 curlsDDC = 7 := by decide
  have hU : morseOut 1 (P ++ curlsNeg ++ phaseTwoBlk curlsTw r) = 3 := by
    simp only [morseOut_append, hP, show morseOut 3 curlsNeg = 3 by decide,
      morseOut_phaseTwoBlk_curls 3 r _ hTw]
  have hV : morseOut 1 (P ++ curlsNeg ++ phaseTwoBlk curlsTw r ++ curlsCups ++ phaseTwoD ++
      phaseTwoClaspS) = 7 := by
    rw [morseOut_append, morseOut_append, morseOut_append, hU]
    decide
  have h1 := morseReach_at_curls 7 1 (P ++ curlsNeg ++ phaseTwoBlk curlsTw r ++ curlsCups ++
      phaseTwoD ++ phaseTwoClaspS ++ phaseTwoBlk curlsDDC r) rest _ _ morseReach_curlsDC
    (by decide) (by rw [morseOut_append, hV, morseOut_phaseTwoBlk_curls 7 r _ hDDC])
  have h2 := morseReach_runPass_curls 1 7 r (P ++ curlsNeg ++ phaseTwoBlk curlsTw r ++ curlsCups ++
      phaseTwoD ++ phaseTwoClaspS) (phaseTwoD ++ rest) curlsDDC curlsPos3 morseReach_curlsDDC
    (by decide) hDDC hV
  have h3 := morseReach_at_curls 3 1 (P ++ curlsNeg ++ phaseTwoBlk curlsTw r)
    (phaseTwoBlk curlsDDC r ++ phaseTwoD ++ rest) _ _ morseReach_curlsBOT (by decide) hU
  have h4 := morseReach_runPass_curls 1 3 r (P ++ curlsNeg) (curlsCups ++ phaseTwoD ++
      phaseTwoClaspS ++ phaseTwoBlk curlsDDC r ++ phaseTwoD ++ rest) curlsTw curlsPos
    morseReach_curlsTW (by decide) hTw (by rw [morseOut_append, hP]; decide)
  have h5 := morseReach_at_curls 3 1 P (phaseTwoBlk curlsTw r ++ curlsCups ++ phaseTwoD ++
      phaseTwoClaspS ++ phaseTwoBlk curlsDDC r ++ phaseTwoD ++ rest) _ _ morseReach_curlsCANMP
    (by decide) hP
  simp only [List.append_assoc, List.append_nil] at h1 h2 h3 h4 h5 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 (morseReach_trans h4 h5)))

/-- The middle of the word between the twists and the top curl is neutral on two strands. -/
private theorem curls_middle_neutral (A Dr : MorseWord) (hAf : morseFits 2 A = true)
    (hAo : morseOut 2 A = 2) (hDf : morseFits 6 Dr = true) (hDo : morseOut 6 Dr = 6) :
    morseFits 2 (A ++ curlsCups ++ Dr ++ curlsTail) = true ∧
      morseOut 2 (A ++ curlsCups ++ Dr ++ curlsTail) = 2 := by
  simp only [morseFits_append, morseOut_append, hAf, hAo, hDf, hDo,
    show morseFits 2 curlsCups = true by decide, show morseOut 2 curlsCups = 6 by decide,
    show morseFits 6 curlsTail = true by decide, show morseOut 6 curlsTail = 2 by decide,
    Bool.and_self, and_self]

/-- A curl after an odd doubled crossing travels up through `2j` doubled crossings, past the fold
twist and the doubled closing cap, and then takes the route of the top curl. -/
private theorem morseReach_curlsUp (m j : ℕ) (A Dr : MorseWord) (hAf : morseFits 2 A = true)
    (hAo : morseOut 2 A = 2) (hDf : morseFits 6 Dr = true) (hDo : morseOut 6 Dr = 6) :
    MorseReach 1 ([(.cup, 1)] ++ phaseTwoBlk curlsTw m ++ curlsNeg ++ A ++ curlsCups ++
        phaseTwoD ++ phaseTwoClaspS ++ Dr ++ curlsPos ++ phaseTwoBlk phaseTwoD (2 * j) ++
        curlsTail ++ [(.cap, 1)])
      ([(.cup, 1)] ++ phaseTwoBlk curlsTw m ++ A ++ curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++
        Dr ++ phaseTwoBlk phaseTwoD (2 * j) ++ curlsTail ++ [(.cap, 1)]) := by
  have hD6 : morseOut 6 phaseTwoD = 6 := by decide
  have hD7 : morseOut 7 phaseTwoD = 7 := by decide
  have hU : morseOut 1 ([(.cup, 1)] ++ phaseTwoBlk curlsTw m ++ curlsNeg ++ A ++ curlsCups ++
      phaseTwoD ++ phaseTwoClaspS ++ Dr) = 7 := by
    simp only [morseOut_append, show morseOut 1 [(.cup, 1)] = 3 from rfl,
      morseOut_phaseTwoBlk_curls 3 m _ (show morseOut 3 curlsTw = 3 by decide),
      show morseOut 3 curlsNeg = 3 by decide, show (3 : ℕ) = 2 + 1 from rfl,
      morseOut_add_right 2 1 A hAf, hAo, show morseOut (2 + 1) curlsCups = 7 by decide,
      show morseOut 7 phaseTwoD = 6 + 1 from rfl, show morseOut (6 + 1) phaseTwoClaspS = 6 + 1
        by decide, morseOut_add_right 6 1 Dr hDf, hDo]
  have h1 := morseReach_beadD_pow 1 (2 * j) ([(.cup, 1)] ++ phaseTwoBlk curlsTw m ++ curlsNeg ++
      A ++ curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++ Dr) curlsPos (curlsTail ++ [(.cap, 1)])
    (by decide) (by decide) (by rw [hU]; omega)
  simp only [Nat.mul_mod_right, ↓reduceIte] at h1
  have h2 := morseReach_at_curls 7 1 ([(.cup, 1)] ++ phaseTwoBlk curlsTw m ++ curlsNeg ++ A ++
      curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++ Dr ++ phaseTwoBlk phaseTwoD (2 * j))
    [(.cap, 1)] _ _ morseReach_curlsTOPX (by decide)
    (by rw [morseOut_append, hU, morseOut_phaseTwoBlk_curls 7 _ _ hD7])
  obtain ⟨hSf, hSo⟩ := curls_middle_neutral A (phaseTwoD ++ phaseTwoClaspS ++ Dr ++
    phaseTwoBlk phaseTwoD (2 * j)) hAf hAo (by
      simp only [morseFits_append, morseOut_append, hD6, hDf, hDo,
        show morseFits 6 phaseTwoD = true by decide,
        show morseFits 6 phaseTwoClaspS = true by decide,
        show morseOut 6 phaseTwoClaspS = 6 by decide,
        morseFits_phaseTwoBlk 6 _ _ (by decide) hD6, Bool.and_self])
    (by simp only [morseOut_append, hD6, hDo, show morseOut 6 phaseTwoClaspS = 6 by decide,
      morseOut_phaseTwoBlk_curls 6 _ _ hD6])
  have h3 := morseReach_curlsTop m _ hSf hSo
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-! ### The steps of stage C -/

/-- The X tip moves down to the hook (exchanges). -/
private theorem phaseTwoC_tipDown (k : ℕ) :
    MorseReach 1 (phaseTwoWS k)
      ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ phaseTwoM1 ++ curlsX5 ++
        phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD ++ [(.cross false, 2), (.cross false, 2)] ++
        curlsX3 ++ [(.cap, 2)] ++ curlsPos ++ [(.cap, 1)]) := by
  have hB5 : morseOut 5 phaseTwoB1 = 5 := by decide
  have hXf : morseFits 5 (phaseTwoBlk phaseTwoB1 (2 * k - 1) ++
      (phaseTwoD ++ [(.cross false, 2), (.cross false, 2)] ++ curlsX3)) = true := by
    rw [morseFits_append, morseFits_phaseTwoBlk 5 _ _ (by decide) hB5,
      morseOut_phaseTwoBlk_curls 5 _ _ hB5]
    decide
  have hXo : morseOut 5 (phaseTwoBlk phaseTwoB1 (2 * k - 1) ++
      (phaseTwoD ++ [(.cross false, 2), (.cross false, 2)] ++ curlsX3)) = 3 := by
    rw [morseOut_append, morseOut_phaseTwoBlk_curls 5 _ _ hB5]
    decide
  have h := morseReach_interchange_curls 1 0 5 2
    ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ phaseTwoM1) ([(.cap, 2)] ++ curlsPos ++
      [(.cap, 1)]) _ [(.cup, 0), (.cross false, 1), (.cap, 0), (.cap, 0)] hXf (by decide) (by
      rw [morseOut_append, morseOut_append, show morseOut 1 [(.cup, 1)] = 3 from rfl,
        morseOut_phaseTwoBlk_curls 3 _ _ (by decide)]
      decide)
  rw [hXo, morseShiftWord_zero_curls,
    show morseShiftWord (0 + 3) [(.cup, 0), (.cross false, 1), (.cap, 0), (.cap, 0)] = curlsX3
      from rfl,
    show morseShiftWord (0 + 5) [(.cup, 0), (.cross false, 1), (.cap, 0), (.cap, 0)] = curlsX5
      from rfl] at h
  have hQ : phaseTwoQ1 = phaseTwoD ++ [(.cross false, 2), (.cross false, 2)] ++ curlsX3 ++
      curlsX3 ++ [(.cap, 2)] ++ curlsPos ++ [(.cap, 1)] := rfl
  rw [phaseTwoWS, hQ]
  simp only [List.append_assoc] at h ⊢
  exact h

/-- The fold curl goes around its cap (macro `CAPM`) and down the closing arc into the clasp. -/
private theorem phaseTwoC_foldCurl (k : ℕ) :
    MorseReach 1
      ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ phaseTwoM1 ++ curlsX5 ++
        phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD ++ [(.cross false, 2), (.cross false, 2)] ++
        curlsX3 ++ [(.cap, 2)] ++ curlsPos ++ [(.cap, 1)])
      ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ curlsCups ++ phaseTwoD ++ curlsPos ++
        curlsHook ++ curlsR4 ++ [(.cross false, 5)] ++ curlsX5 ++
        phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD ++ curlsTail ++ curlsPos ++
        [(.cap, 1)]) := by
  set P : MorseWord := [(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) with hPdef
  set Bn : MorseWord := phaseTwoBlk phaseTwoB1 (2 * k - 1) with hBn
  have hP : morseOut 1 P = 3 := by
    rw [hPdef, morseOut_append, show morseOut 1 [(.cup, 1)] = 3 from rfl,
      morseOut_phaseTwoBlk_curls 3 _ _ (by decide)]
  have hB4 : morseOut 4 phaseTwoB1 = 4 := by decide
  have hB7 : morseOut 7 phaseTwoB1 = 7 := by decide
  have hM : phaseTwoM1 = curlsCups ++ phaseTwoD ++ curlsPos ++ curlsHook ++
      [(.cross false, 5)] := rfl
  have hu1 : morseOut 1 (P ++ phaseTwoM1 ++ curlsX5) = 7 := by
    rw [morseOut_append, morseOut_append, hP]
    decide
  have hu2 : morseOut 1 (P ++ phaseTwoM1 ++ curlsX5 ++ Bn) = 7 := by
    rw [morseOut_append, hu1, hBn, morseOut_phaseTwoBlk_curls 7 _ _ hB7]
  -- the fold curl goes around its cap
  have h1 := morseReach_frame 2 1 3 2 (P ++ phaseTwoM1 ++ curlsX5 ++ Bn ++
      (phaseTwoD ++ [(.cross false, 2), (.cross false, 2)])) ([(.cap, 2)] ++ curlsPos ++
      [(.cap, 1)]) _ _ morseReach_curlsCAPM (by decide) (by
    rw [morseOut_append, hu2]
    decide)
  rw [show morseShiftWord 3 [(.cup, 0), (.cross false, 1), (.cap, 0), (.cap, 0)] = curlsX3
      from rfl,
    show morseShiftWord 3 [(.cup, 2), (.cross false, 1), (.cap, 2), (.cap, 0)] =
      curlsR4 ++ [(.cap, 3)] from rfl] at h1
  -- it moves down the closing arc past the blocks
  have hXf : morseFits 4 (Bn ++ (phaseTwoD ++ [(.cross false, 2), (.cross false, 2)])) = true := by
    rw [hBn, morseFits_append, morseFits_phaseTwoBlk 4 _ _ (by decide) hB4,
      morseOut_phaseTwoBlk_curls 4 _ _ hB4]
    decide
  have hXo : morseOut 4 (Bn ++ (phaseTwoD ++ [(.cross false, 2), (.cross false, 2)])) = 4 := by
    rw [hBn, morseOut_append, morseOut_phaseTwoBlk_curls 4 _ _ hB4]
    decide
  have h2 := morseReach_interchange_curls 1 0 4 1 (P ++ phaseTwoM1 ++ curlsX5)
    ([(.cap, 3), (.cap, 2)] ++ curlsPos ++ [(.cap, 1)]) _ [(.cup, 1), (.cross false, 0), (.cap, 1)]
    hXf (by decide) (by rw [hu1]; omega)
  rw [hXo, morseShiftWord_zero_curls,
    show morseShiftWord (0 + 4) [(.cup, 1), (.cross false, 0), (.cap, 1)] = curlsR4 from rfl]
    at h2
  -- and past the X tip into the clasp
  have h3 := morseReach_symm (morseReach_interchange_curls 1 4 1 2
    (P ++ curlsCups ++ phaseTwoD ++ curlsPos ++ curlsHook)
    (Bn ++ phaseTwoD ++ curlsTail ++ curlsPos ++ [(.cap, 1)])
    [(.cup, 1), (.cross false, 0), (.cap, 1)]
    [(.cross false, 0), (.cup, 0), (.cross false, 1), (.cap, 0), (.cap, 0)] (by decide)
    (by decide) (by rw [morseOut_append, morseOut_append, morseOut_append, morseOut_append, hP]
                    decide))
  rw [show morseOut 1 [(.cup, 1), (.cross false, 0), (.cap, 1)] = 1 from rfl,
    show morseShiftWord 4 [(.cup, 1), (.cross false, 0), (.cap, 1)] = curlsR4 from rfl,
    show morseShiftWord (4 + 1) [(.cross false, 0), (.cup, 0), (.cross false, 1), (.cap, 0),
      (.cap, 0)] = [(.cross false, 5)] ++ curlsX5 from rfl] at h3
  have hT : curlsTail = [(.cross false, 2), (.cross false, 2)] ++ [(.cap, 3), (.cap, 2)] := rfl
  rw [hM] at h1 h2 ⊢
  rw [hT] at h3 ⊢
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- Macro `WIN`, applied next to the clasp. -/
private theorem phaseTwoC_clasp (k : ℕ) :
    MorseReach 1
      ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ curlsCups ++ phaseTwoD ++ curlsPos ++
        curlsHook ++ curlsR4 ++ [(.cross false, 5)] ++ curlsX5 ++
        phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD ++ curlsTail ++ curlsPos ++ [(.cap, 1)])
      ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++
        phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD ++ curlsTail ++ curlsPos ++
        [(.cap, 1)]) := by
  have h := morseReach_at_curls 3 1 ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k))
    (phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD ++ curlsTail ++ curlsPos ++ [(.cap, 1)])
    _ _ morseReach_curlsWIN (by decide) (by
      rw [morseOut_append, show morseOut 1 [(.cup, 1)] = 3 from rfl,
        morseOut_phaseTwoBlk_curls 3 _ _ (by decide)])
  simp only [List.append_assoc] at h ⊢
  exact h

/-- No blocks. -/
private theorem phaseTwoBlk_zero_curls (y : MorseWord) : phaseTwoBlk y 0 = [] := rfl

/-- Blocks in pairs. -/
private theorem phaseTwoBlk_two_mul_curls (y : MorseWord) (m : ℕ) :
    phaseTwoBlk y (2 * m) = phaseTwoBlk (y ++ y) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, phaseTwoBlk_succ_curls, phaseTwoBlk_succ_curls,
      phaseTwoBlk_succ_curls, ← ih, List.append_assoc]

/-- The top curl cancels the first `A` curl. -/
private theorem phaseTwoC_top (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1
      ([(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ curlsCups ++ phaseTwoD ++ phaseTwoClaspS ++
        phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD ++ curlsTail ++ curlsPos ++ [(.cap, 1)])
      (curlsWordB k 0) := by
  have hA2 : morseOut 2 phaseTwoA1 = 2 := by decide
  have hB6 : morseOut 6 phaseTwoB1 = 6 := by decide
  obtain ⟨hSf, hSo⟩ := curls_middle_neutral (phaseTwoBlk phaseTwoA1 (2 * k - 1))
    (phaseTwoD ++ phaseTwoClaspS ++ phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoD)
    (morseFits_phaseTwoBlk 2 _ _ (by decide) hA2) (morseOut_phaseTwoBlk_curls 2 _ _ hA2)
    (by
      simp only [morseFits_append, morseOut_append, morseOut_phaseTwoBlk_curls 6 _ _ hB6,
        morseFits_phaseTwoBlk 6 _ _ (by decide) hB6,
        show morseFits 6 phaseTwoD = true by decide, show morseOut 6 phaseTwoD = 6 by decide,
        show morseFits 6 phaseTwoClaspS = true by decide,
        show morseOut 6 phaseTwoClaspS = 6 by decide, Bool.and_self])
    (by simp only [morseOut_append, morseOut_phaseTwoBlk_curls 6 _ _ hB6,
      show morseOut 6 phaseTwoD = 6 by decide, show morseOut 6 phaseTwoClaspS = 6 by decide])
  have h := morseReach_curlsTop 1 _ hSf hSo
  have e1 : phaseTwoBlk phaseTwoA1 (2 * k) =
      phaseTwoBlk curlsTw 1 ++ curlsNeg ++ phaseTwoBlk phaseTwoA1 (2 * k - 1) := by
    rw [show 2 * k = 2 * k - 1 + 1 by omega, phaseTwoBlk_succ_curls, Nat.add_sub_cancel]
    rfl
  have e2 : ∀ x : MorseWord, phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ (phaseTwoD ++ x) =
      phaseTwoBlk curlsBB (k - 1) ++ (phaseTwoD ++ (curlsPos ++ (phaseTwoD ++ x))) := by
    intro x
    rw [show 2 * k - 1 = 2 * (k - 1) + 1 by omega, phaseTwoBlk_succ'_curls,
      phaseTwoBlk_two_mul_curls, List.append_assoc]
    rfl
  have e3 : phaseTwoBlk curlsTw 1 = curlsTw := rfl
  rw [e1, e3]
  rw [e3] at h
  simp only [List.append_assoc] at h
  rw [e2 (curlsTail ++ [(MorseKind.cap, 1)])] at h
  simp only [curlsWordB, Nat.sub_zero, phaseTwoBlk_zero_curls, List.append_nil,
    List.append_assoc] at h ⊢
  exact h

/-- First pass: one curl after an even doubled crossing cancels. -/
private theorem phaseTwoC_passOne_step (k r : ℕ) (hr : r + 2 ≤ k) :
    MorseReach 1 (curlsWordB k r) (curlsWordB k (r + 1)) := by
  have h := morseReach_curlsBottom r ([(.cup, 1)] ++ curlsTw ++
    phaseTwoBlk phaseTwoA1 (2 * k - 1 - (r + 1)) ++ curlsTw) (phaseTwoD ++ curlsPos ++
    phaseTwoBlk curlsBB (k - 1 - (r + 1)) ++ phaseTwoD ++ curlsPos ++ phaseTwoD ++ curlsTail ++
    [(.cap, 1)]) (by
      rw [morseOut_append, morseOut_append, morseOut_append,
        show morseOut 1 [(.cup, 1)] = 3 from rfl, show morseOut 3 curlsTw = 3 from rfl,
        morseOut_phaseTwoBlk_curls 3 _ _ (by decide)]
      rfl)
  have e1 : phaseTwoBlk phaseTwoA1 (2 * k - 1 - r) =
      phaseTwoBlk phaseTwoA1 (2 * k - 1 - (r + 1)) ++ (curlsTw ++ curlsNeg) := by
    rw [show 2 * k - 1 - r = 2 * k - 1 - (r + 1) + 1 by omega, phaseTwoBlk_succ'_curls]
    rfl
  have e2 : phaseTwoBlk curlsBB (k - 1 - r) =
      phaseTwoD ++ curlsPos ++ phaseTwoD ++ curlsPos ++ phaseTwoBlk curlsBB (k - 1 - (r + 1)) := by
    rw [show k - 1 - r = k - 1 - (r + 1) + 1 by omega, phaseTwoBlk_succ_curls]
    rfl
  have e4 : phaseTwoBlk curlsDDC (r + 1) =
      phaseTwoBlk curlsDDC r ++ (phaseTwoD ++ (phaseTwoD ++ curlsPos)) := by
    rw [phaseTwoBlk_succ'_curls]
    rfl
  unfold curlsWordB
  rw [e1, e2, phaseTwoBlk_succ_curls curlsTw r, e4]
  simp only [List.append_assoc] at h ⊢
  exact h

/-- First pass: `r` curls after even doubled crossings cancel. -/
private theorem phaseTwoC_passOne (k : ℕ) :
    ∀ r, r + 1 ≤ k → MorseReach 1 (curlsWordB k 0) (curlsWordB k r) := by
  intro r
  induction r with
  | zero => exact fun _ ↦ morseReach_refl 1 _
  | succ r ih =>
    intro hr
    exact morseReach_trans (ih (by omega)) (phaseTwoC_passOne_step k r hr)

/-- First pass: the last curl after an even doubled crossing cancels. -/
private theorem phaseTwoC_passOne_last (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (curlsWordB k (k - 1)) (curlsWordA k 0) := by
  have h := morseReach_curlsBottom (k - 1) ([(.cup, 1)] ++ curlsTw ++
    phaseTwoBlk phaseTwoA1 (k - 1) ++ curlsTw) (phaseTwoD ++ curlsTail ++ [(.cap, 1)]) (by
      rw [morseOut_append, morseOut_append, morseOut_append,
        show morseOut 1 [(.cup, 1)] = 3 from rfl, show morseOut 3 curlsTw = 3 from rfl,
        morseOut_phaseTwoBlk_curls 3 _ _ (by decide)]
      rfl)
  have e1 : phaseTwoBlk phaseTwoA1 (2 * k - 1 - (k - 1)) =
      phaseTwoBlk phaseTwoA1 (k - 1) ++ (curlsTw ++ curlsNeg) := by
    rw [show 2 * k - 1 - (k - 1) = k - 1 + 1 by omega, phaseTwoBlk_succ'_curls]
    rfl
  have e2 : phaseTwoBlk curlsTw k = curlsTw ++ phaseTwoBlk curlsTw (k - 1) := by
    rw [← phaseTwoBlk_succ_curls, Nat.sub_add_cancel hk]
  have e3 : phaseTwoBlk phaseTwoD (2 * 0 + 2) = phaseTwoD ++ phaseTwoD := rfl
  unfold curlsWordB curlsWordA
  rw [e1, Nat.sub_self, Nat.sub_zero, e2, e3, phaseTwoBlk_zero_curls,
    show phaseTwoBlk curlsTw (0 + 1) = curlsTw from rfl]
  simp only [List.append_assoc, List.nil_append] at h ⊢
  exact h

/-- Second pass: one curl after an odd doubled crossing cancels. -/
private theorem phaseTwoC_passTwo_step (k s : ℕ) (hs : s + 2 ≤ k) :
    MorseReach 1 (curlsWordA k s) (curlsWordA k (s + 1)) := by
  have hA2 : morseOut 2 phaseTwoA1 = 2 := by decide
  have hT2 : morseOut 2 curlsTw = 2 := by decide
  have hDDC : morseOut 6 curlsDDC = 6 := by decide
  have h := morseReach_curlsUp (s + 1 + 1) (s + 1)
    (phaseTwoBlk phaseTwoA1 (k - 1 - (s + 1)) ++ phaseTwoBlk curlsTw k)
    (phaseTwoBlk curlsDDC (k - 1 - (s + 1)) ++ phaseTwoD ++ phaseTwoD)
    (by simp only [morseFits_append, morseOut_phaseTwoBlk_curls 2 _ _ hA2,
      morseFits_phaseTwoBlk 2 _ _ (by decide) hA2,
      morseFits_phaseTwoBlk 2 _ _ (by decide) hT2, Bool.and_self])
    (by simp only [morseOut_append, morseOut_phaseTwoBlk_curls 2 _ _ hA2,
      morseOut_phaseTwoBlk_curls 2 _ _ hT2])
    (by simp only [morseFits_append, morseOut_append, morseOut_phaseTwoBlk_curls 6 _ _ hDDC,
      morseFits_phaseTwoBlk 6 _ _ (by decide) hDDC,
      show morseFits 6 phaseTwoD = true by decide, show morseOut 6 phaseTwoD = 6 by decide,
      Bool.and_self])
    (by simp only [morseOut_append, morseOut_phaseTwoBlk_curls 6 _ _ hDDC,
      show morseOut 6 phaseTwoD = 6 by decide])
  have e1 : phaseTwoBlk phaseTwoA1 (k - 1 - s) =
      curlsTw ++ curlsNeg ++ phaseTwoBlk phaseTwoA1 (k - 1 - (s + 1)) := by
    rw [show k - 1 - s = k - 1 - (s + 1) + 1 by omega, phaseTwoBlk_succ_curls]
    rfl
  have e2 : phaseTwoBlk curlsDDC (k - 1 - s) =
      phaseTwoBlk curlsDDC (k - 1 - (s + 1)) ++ (phaseTwoD ++ (phaseTwoD ++ curlsPos)) := by
    rw [show k - 1 - s = k - 1 - (s + 1) + 1 by omega, phaseTwoBlk_succ'_curls]
    rfl
  have e3 : phaseTwoBlk phaseTwoD (2 * (s + 1) + 2) =
      phaseTwoD ++ phaseTwoD ++ phaseTwoBlk phaseTwoD (2 * (s + 1)) := by
    rw [phaseTwoBlk_succ_curls, phaseTwoBlk_succ_curls, List.append_assoc]
  unfold curlsWordA
  rw [show 2 * s + 2 = 2 * (s + 1) by ring, e1, e2, e3]
  rw [phaseTwoBlk_succ'_curls curlsTw (s + 1)] at h ⊢
  simp only [List.append_assoc] at h ⊢
  exact h

/-- Second pass: `s` curls after odd doubled crossings cancel. -/
private theorem phaseTwoC_passTwo (k : ℕ) :
    ∀ s, s + 1 ≤ k → MorseReach 1 (curlsWordA k 0) (curlsWordA k s) := by
  intro s
  induction s with
  | zero => exact fun _ ↦ morseReach_refl 1 _
  | succ s ih =>
    intro hs
    exact morseReach_trans (ih (by omega)) (phaseTwoC_passTwo_step k s hs)

/-- Twists in a run. -/
private theorem phaseTwoBlk_curlsTw (m : ℕ) :
    phaseTwoBlk curlsTw m = List.replicate (2 * m) (.cross false, 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [phaseTwoBlk_succ_curls, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      List.replicate_succ, List.replicate_succ]
    rfl

/-- The word after the second pass is the word after stage C. -/
private theorem curlsWordA_last (k : ℕ) (hk : 1 ≤ k) : curlsWordA k (k - 1) = phaseTwoWC k := by
  unfold curlsWordA phaseTwoWC
  rw [Nat.sub_self, Nat.sub_add_cancel hk, show 2 * (k - 1) + 2 = 2 * k by omega,
    phaseTwoBlk_zero_curls, phaseTwoBlk_zero_curls, phaseTwoBlk_curlsTw,
    show 4 * k = 2 * k + 2 * k by ring, List.replicate_add]
  simp only [List.append_assoc, List.nil_append]
  rfl

/-- Stage C: all curls cancel. -/
theorem phaseTwo_stageC (k : ℕ) (hk : 1 ≤ k) : MorseReach 1 (phaseTwoWS k) (phaseTwoWC k) := by
  rw [← curlsWordA_last k hk]
  exact morseReach_trans (phaseTwoC_tipDown k) <| morseReach_trans (phaseTwoC_foldCurl k) <|
    morseReach_trans (phaseTwoC_clasp k) <|
    morseReach_trans (phaseTwoC_top k hk) <|
    morseReach_trans (phaseTwoC_passOne k (k - 1) (by omega)) <|
    morseReach_trans (phaseTwoC_passOne_last k hk) (phaseTwoC_passTwo k (k - 1) (by omega))

end AJConjecture
