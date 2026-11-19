import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkCrossMacros
import AJHandoff.TorusKnot.PairKIsoParkClasp
import AJHandoff.TorusKnot.PairKIsoParkComm
import AJHandoff.TorusKnot.PairKIsoBeadStep
import AJHandoff.TorusKnot.PairKIsoDouble

/-!
# Stage C by ports: a twist crosses the clasp (macro `K6`)

A full twist does not pass the clasp (different operators at thickness two), but
`morseReach_isoPark_cross`: `cs · t ~ t · n · n · cs · p · p` (band frame; equal operators at
thickness one and two, `SCR/ISO2/tools/macros.py`). Route, every step a macro or a generic
lemma, framed by `morseReach_frame`:

1. `t ~ dL · R⁺₁ · R⁺₀` after the clasp (`morseReach_isoPark_twistDcurl`; `dL` the doubled
   negative left curl, `R^s_i = isoCurlR s i`);
2. the doubled curl passes the clasp backwards (`morseReach_isoBead_dcurl`: any band bead passes a
   doubled curl, a bead journey through `morseDouble [u0]`, two doubled crossings and
   `morseDouble [n0]`; here the bead is the clasp);
3. after the clasp: `R⁺₁ R⁺₀ → R⁺₀ R⁺₁` (`swapP`), `R⁺₀ = lp → p` through the clasp (`CSLP`),
   `R⁺₁ → p` (`RP`, one `kink`);
4. before the clasp: `dL → dL · R⁺₁ R⁺₀ R⁻₀ R⁻₁` (two `kink`s backwards), step 1 backwards gives
   `t · R⁻₀ · R⁻₁`, then `swapN`, `R⁻₀ = ln → n` through the clasp (`LNCS`), `R⁻₁ → n` (`RN`).

Step 1 is a fixed macro on two strands: on one strand a negative left curl is a negative right
curl (one `kink`), doubled by `morseReach_morseDouble`; the doubled negative right curl splits into
two edge curls and a twist (the first half of the doubled `kink` of `PairKIsoDoubleRules`), and the
edge curls cancel against `R⁺₁ R⁺₀` by the macros `RP`, `RN`, `TP`, `LPT`, `LPP`, `LNLP`, `NP`
(move lists composed and checked by `decide`).
-/

namespace AJConjecture

/-- The doubled negative left curl (band bead). -/
def isoDCurlL : MorseWord := morseDouble (isoCurlL false 0)

/-- The rotation by `π` is an involution. -/
private theorem isoRot_isoRot_cross : ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
    isoRot (morseOut n w) (isoRot n w) = w
  | [], _, _ => rfl
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    have ih := isoRot_isoRot_cross w (morseLetterOut n l) h.2
    have hf := isoRot_fits w (morseLetterOut n l) h.2
    have hb : morseOut n (l :: w) = morseOut (morseLetterOut n l) w := rfl
    rw [hb, isoRot, isoRot_append, hf.2, ih]
    simp only [isoRot, List.nil_append, isoRotLetter_isoRotLetter n l h.1, List.singleton_append]

/-- The doubled negative crossing (on four strands). -/
private def isoDm : MorseWord := morseDouble [isoX false 0]

/-- A doubled negative crossing and a doubled positive crossing cancel. -/
private theorem morseReach_isoDm_D : MorseReach 4 (isoDm ++ phaseTwoD) [] :=
  ⟨[(3, .r2 1 false, false), (2, .r2 2 false, false), (1, .r2 0 false, false),
    (0, .r2 1 false, false)], by decide⟩

/-- A doubled positive crossing and a doubled negative crossing cancel. -/
private theorem morseReach_D_isoDm : MorseReach 4 (phaseTwoD ++ isoDm) [] :=
  ⟨[(3, .r2 1 true, false), (2, .r2 0 true, false), (1, .r2 2 true, false),
    (0, .r2 1 true, false)], by decide⟩

/-- Framing on four strands without shift. -/
private theorem morseReach_frame4_cross (u v : MorseWord) {w w' : MorseWord}
    (h : MorseReach 4 w w') (hw : morseFits 4 w = true) (hu : morseOut 4 u = 4) :
    MorseReach 4 (u ++ w ++ v) (u ++ w' ++ v) := by
  have hf := morseReach_frame 4 4 0 0 u v w w' h hw (by rw [hu])
  have h0 : ∀ x : MorseWord, morseShiftWord 0 x = x := morseShiftWord_zero_iso
  rwa [h0, h0] at hf

/-- A band bead passes a doubled negative crossing, from the left band to the right band. -/
private theorem morseReach_bead_isoDm_left (T : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) :
    MorseReach 4 (T ++ isoDm) (isoDm ++ morseShiftWord 2 T) := by
  have hT4 : morseFits 4 T = true := morseFits_add_right_iso 2 2 T hT
  have hT4o : morseOut 4 T = 4 := by rw [morseOut_add_right 2 2 T hT, hTo]
  have hs : morseOut 4 (morseShiftWord 2 T) = 4 := by
    have := morseOut_morseShiftWord 2 2 T hT
    rwa [hTo] at this
  have hsf : morseFits 4 (morseShiftWord 2 T) = true := morseFits_morseShiftWord 2 2 0 T hT
  have h1 := morseReach_frame4_cross [] (T ++ isoDm) (morseReach_symm morseReach_isoDm_D)
    rfl rfl
  have h2 := morseReach_symm (morseReach_beadD_right 4 isoDm T isoDm hT hTo
    (by decide))
  have h3 := morseReach_frame4_cross (isoDm ++ morseShiftWord 2 T) [] morseReach_D_isoDm
    (by decide) (by rw [morseOut_append, (by decide : morseOut 4 isoDm = 4), hs])
  simp only [List.nil_append, List.append_nil, List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- A band bead passes a doubled negative crossing, from the right band to the left band. -/
private theorem morseReach_bead_isoDm_right (T : MorseWord) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) :
    MorseReach 4 (morseShiftWord 2 T ++ isoDm) (isoDm ++ T) := by
  have hT4o : morseOut 4 T = 4 := by rw [morseOut_add_right 2 2 T hT, hTo]
  have h1 := morseReach_frame4_cross [] (morseShiftWord 2 T ++ isoDm)
    (morseReach_symm morseReach_isoDm_D) rfl rfl
  have h2 := morseReach_symm (morseReach_beadD_left 4 isoDm T isoDm hT hTo (by decide))
  have h3 := morseReach_frame4_cross (isoDm ++ T) [] morseReach_D_isoDm
    (by decide) (by rw [morseOut_append, (by decide : morseOut 4 isoDm = 4), hT4o])
  simp only [List.nil_append, List.append_nil, List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- A band bead passes a doubled left curl (closed form on two strands): around the doubled cup,
through the doubled crossing, around the doubled cap, back down, around the cup, through the
crossing again. -/
private theorem morseReach_isoBead_dcurl_two (B : MorseWord) (hB : morseFits 2 B = true)
    (hBo : morseOut 2 B = 2) : MorseReach 2 (B ++ isoDCurlL) (isoDCurlL ++ B) := by
  have hdL : isoDCurlL = [isoU 0, isoU 1] ++ morseShiftWord 2 isoDm ++ [isoN 1, isoN 0] := by
    decide
  have h0 : ∀ x : MorseWord, morseShiftWord 0 x = x := morseShiftWord_zero_iso
  set R := isoRot 2 B with hR
  have hRf := isoRot_fits B 2 hB
  rw [hBo] at hRf
  have hRR : isoRot 2 R = B := by
    have := isoRot_isoRot_cross B 2 hB
    rwa [hBo] at this
  have hUU : morseDouble [isoU 0] = [isoU 0, isoU 1] := by decide
  have hNN : morseDouble [isoN 0] = [isoN 1, isoN 0] := by decide
  have s1 := morseReach_isoShiftComm 2 0 2 0 [] [isoU 0, isoU 1] B
    (morseShiftWord 2 isoDm ++ [isoN 1, isoN 0]) (by decide) hB rfl
  have s2 := morseReach_frame 4 2 2 0 [isoU 0, isoU 1] [isoN 1, isoN 0] _ _
    (morseReach_bead_isoDm_right B hB hBo) (by
      rw [morseFits_append, morseFits_morseShiftWord 2 2 0 B hB, Bool.true_and,
        morseOut_morseShiftWord 2 2 B hB, hBo]
      decide) (by decide)
  have s3 := morseReach_symm (morseReach_isoBead_cap 2 0 R ([isoU 0, isoU 1] ++
    morseShiftWord 2 isoDm) [] hRf.1 hRf.2 (by decide))
  have s4 := morseReach_isoShiftComm 2 2 4 0 [isoU 0, isoU 1] R isoDm [isoN 1, isoN 0]
    hRf.1 (by decide) (by decide)
  have s5 := morseReach_isoBead_cup 2 0 R [] (morseShiftWord 2 isoDm ++ [isoN 1, isoN 0])
    hRf.1 hRf.2 (by decide)
  have s6 := morseReach_frame 4 2 2 0 [isoU 0, isoU 1] [isoN 1, isoN 0] _ _
    (morseReach_bead_isoDm_left B hB hBo) (by
      rw [morseFits_append, morseFits_add_right_iso 2 2 B hB, Bool.true_and,
        morseOut_add_right 2 2 B hB, hBo]
      decide) (by decide)
  have s7 := morseReach_isoShiftComm 2 4 2 0 ([isoU 0, isoU 1] ++ morseShiftWord 2 isoDm)
    [isoN 1, isoN 0] B [] (by decide) hB (by decide)
  rw [hRf.2] at s4
  rw [show morseOut 4 [isoN 1, isoN 0] = 0 by decide] at s7
  rw [hUU, hNN, hRR] at *
  simp only [morseShiftWord_append, morseShiftWord_shift_iso, Nat.reduceAdd] at s2 s6
  rw [show morseOut 0 [isoU 0, isoU 1] = 4 by decide] at s1
  simp only [h0, Nat.reduceMul, Nat.reduceAdd, List.nil_append, List.append_nil,
    List.append_assoc, List.cons_append] at s1 s2 s3 s4 s5 s6 s7
  rw [hdL]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact morseReach_trans s1 (morseReach_trans s2 (morseReach_trans s3 (morseReach_trans s4
    (morseReach_trans s5 (morseReach_trans s6 s7)))))

/-- Any band bead passes a doubled left curl. -/
theorem morseReach_isoBead_dcurl (n₀ : ℕ) (B u v : MorseWord) (hB : morseFits 2 B = true)
    (hBo : morseOut 2 B = 2) (hu : 2 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ B ++ isoDCurlL ++ v) (u ++ isoDCurlL ++ B ++ v) := by
  have h := morseReach_frame 2 n₀ 0 (morseOut n₀ u - 2) u v _ _
    (morseReach_isoBead_dcurl_two B hB hBo)
    (by rw [morseFits_append, hB, Bool.true_and, hBo]; decide) (by omega)
  have h0 : ∀ x : MorseWord, morseShiftWord 0 x = x := morseShiftWord_zero_iso
  simpa only [h0, List.append_assoc] using h

/-- On one strand, a negative left curl is a negative right curl (one `kink`). -/
private theorem morseReach_isoPark_curlLR :
    MorseReach 1 (isoCurlL false 0) (isoCurlR false 0) :=
  ⟨[(3, .kink 0 true, true), (3, .cupSlide 0 false false, true),
     (2, .exch (.cup, 0) (.cap, 0), true), (1, .exch (.cup, 0) (.cross false, 1), true),
     (0, .exch (.cup, 0) (.cup, 0), true), (5, .r2 0 false, false),
     (3, .capSlide 1 false true, true), (2, .exch (.cross false, 1) (.cross false, 3), true),
     (5, .exch (.cap, 1) (.cross false, 3), false), (3, .r3 2 false, true),
     (1, .cupSlide 1 false true, false), (4, .exch (.cap, 1) (.cap, 3), false),
     (2, .capSlide 2 false false, false), (1, .zig 1 true, false), (0, .zig 0 true, false)],
    by decide⟩

/-- A doubled negative right curl and two positive right curls make a negative full twist (the
doubled curl splits into two edge curls and a twist, as in the doubled `kink` of
`PairKIsoDoubleRules`; then the macros `RP`, `RN`, `TP`, `LPT`, `LPP`, `LNLP`, `NP`). -/
private theorem morseReach_isoPark_dcurlR_twist :
    MorseReach 2 (morseDouble (isoCurlR false 0) ++ isoCurlR true 1 ++ isoCurlR true 0)
      (isoBeadsWord [.t]) :=
  ⟨[(3, .exch (.cross false, 0) (.cross false, 2), false),
     (5, .exch (.cross false, 1) (.cap, 3), false), (4, .exch (.cross false, 0) (.cap, 3), false),
     (1, .cupSlide 2 false false, true), (3, .r3 1 false, true),
     (5, .exch (.cross false, 1) (.cap, 3), false),
     (2, .exch (.cross false, 1) (.cross false, 3), true), (3, .capSlide 2 false false, false),
     (0, .exch (.cup, 2) (.cup, 2), true), (1, .exch (.cross false, 1) (.cup, 4), true),
     (2, .exch (.cap, 2) (.cup, 4), true), (4, .r3 0 false, true),
     (6, .exch (.cross false, 0) (.cap, 2), false), (3, .cupSlide 1 false false, true),
     (5, .r3 0 false, true), (7, .exch (.cross false, 0) (.cap, 2), false),
     (4, .exch (.cross false, 0) (.cross false, 2), true), (5, .capSlide 1 false false, false),
     (11, .zig 1 false, true), (12, .zig 2 false, true), (12, .cupSlide 3 true true, true),
     (15, .capSlide 2 true false, true), (17, .exch (.cap, 1) (.cap, 3), true),
     (13, .r3 3 true, false), (15, .exch (.cross true, 2) (.cross true, 4), true),
     (16, .exch (.cap, 1) (.cross true, 4), true), (11, .exch (.cup, 2) (.cup, 2), false),
     (12, .exch (.cup, 2) (.cross true, 2), false), (13, .cupSlide 2 true false, false),
     (13, .exch (.cap, 1) (.cup, 3), true), (12, .r2 1 false, true),
     (13, .capSlide 1 true true, false), (11, .zig 1 true, true), (12, .zig 2 true, true),
     (12, .cupSlide 1 true false, true), (15, .capSlide 2 true true, true),
     (17, .exch (.cap, 2) (.cap, 4), false), (13, .r3 1 true, true),
     (15, .exch (.cross true, 1) (.cross true, 3), false),
     (16, .exch (.cross true, 1) (.cap, 4), false), (11, .exch (.cup, 1) (.cup, 1), true),
     (12, .exch (.cross true, 1) (.cup, 3), true), (13, .cupSlide 2 true true, false),
     (13, .exch (.cup, 2) (.cap, 2), false), (13, .capSlide 1 false true, true),
     (12, .r2 1 true, false), (14, .kink 1 true, false), (10, .capSlide 1 false true, true),
     (9, .r2 1 true, false), (10, .exch (.cap, 1) (.cup, 3), false),
     (10, .cupSlide 2 false false, true), (9, .exch (.cup, 2) (.cross false, 2), true),
     (8, .exch (.cup, 2) (.cup, 2), true), (13, .exch (.cap, 1) (.cross false, 4), false),
     (12, .exch (.cross false, 2) (.cross false, 4), false), (10, .r3 3 false, true),
     (14, .exch (.cap, 1) (.cap, 3), false), (12, .capSlide 2 false false, false),
     (9, .cupSlide 3 false true, false), (9, .zig 2 false, false), (8, .zig 1 false, false),
     (3, .zig 1 false, true), (4, .zig 2 false, true), (4, .cupSlide 3 false true, true),
     (7, .capSlide 2 false false, true), (9, .exch (.cap, 1) (.cap, 3), true),
     (5, .r3 3 false, false), (7, .exch (.cross false, 2) (.cross false, 4), true),
     (8, .exch (.cap, 1) (.cross false, 4), true), (3, .exch (.cup, 2) (.cup, 2), false),
     (4, .exch (.cup, 2) (.cross false, 2), false), (5, .cupSlide 2 false false, false),
     (5, .exch (.cap, 1) (.cup, 3), true), (4, .r2 1 true, true),
     (5, .capSlide 1 false true, false), (3, .zig 1 true, true), (4, .zig 2 true, true),
     (4, .cupSlide 1 false false, true), (7, .capSlide 2 false true, true),
     (9, .exch (.cap, 2) (.cap, 4), false), (5, .r3 1 false, true),
     (7, .exch (.cross false, 1) (.cross false, 3), false),
     (8, .exch (.cross false, 1) (.cap, 4), false), (3, .exch (.cup, 1) (.cup, 1), true),
     (4, .exch (.cross false, 1) (.cup, 3), true), (5, .cupSlide 2 false true, false),
     (5, .exch (.cup, 2) (.cap, 2), false), (5, .capSlide 1 true true, true),
     (4, .r2 1 false, false), (6, .kink 1 false, false), (2, .capSlide 1 true true, true),
     (1, .r2 1 false, false), (2, .exch (.cap, 1) (.cup, 3), false),
     (2, .cupSlide 2 true false, true), (1, .exch (.cup, 2) (.cross true, 2), true),
     (0, .exch (.cup, 2) (.cup, 2), true), (5, .exch (.cap, 1) (.cross true, 4), false),
     (4, .exch (.cross true, 2) (.cross true, 4), false), (2, .r3 3 true, true),
     (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 true false, false),
     (1, .cupSlide 3 true true, false), (1, .zig 2 false, false), (0, .zig 1 false, false),
     (8, .cupSlide 0 false false, true), (7, .exch (.cup, 0) (.cross false, 0), true),
     (11, .r2 1 false, true), (12, .capSlide 1 true true, false), (9, .r3 0 false, true),
     (11, .exch (.cross false, 0) (.cap, 2), false),
     (8, .exch (.cross false, 0) (.cross false, 2), true), (9, .capSlide 1 false false, false),
     (9, .capSlide 0 true true, true), (8, .r2 0 false, false), (9, .r2 0 true, true),
     (7, .cupSlide 0 true false, false), (7, .cupSlide 1 false true, true),
     (9, .exch (.cross false, 0) (.cross false, 2), true),
     (10, .exch (.cap, 0) (.cross false, 2), true), (6, .exch (.cross false, 0) (.cup, 2), false),
     (7, .r3 0 false, false), (8, .capSlide 0 false true, false), (6, .cupSlide 1 true false, true),
     (8, .r2 1 true, false), (13, .capSlide 1 true false, true),
     (12, .exch (.cross true, 0) (.cross true, 2), false), (15, .r2 0 true, true),
     (13, .r3 0 true, false), (11, .cupSlide 1 true false, false),
     (10, .exch (.cross false, 0) (.cup, 2), false), (9, .exch (.cross false, 0) (.cup, 2), false),
     (11, .r2 0 false, false), (9, .cupSlide 1 false false, true), (11, .r2 0 true, true),
     (12, .r3 0 false, false), (14, .r2 1 false, false),
     (14, .exch (.cross false, 0) (.cap, 2), false), (13, .exch (.cross false, 0) (.cap, 2), false),
     (10, .exch (.cross true, 0) (.cross false, 2), true), (11, .capSlide 1 false false, false),
     (8, .exch (.cup, 1) (.cap, 1), true), (7, .exch (.cup, 1) (.cross true, 2), true),
     (9, .exch (.cross true, 0) (.cap, 3), true), (10, .exch (.cap, 1) (.cap, 3), true),
     (8, .exch (.cross true, 0) (.cross true, 4), true),
     (9, .exch (.cap, 1) (.cross true, 4), true), (6, .exch (.cup, 1) (.cup, 1), true),
     (7, .exch (.cross true, 0) (.cup, 3), true), (8, .exch (.cap, 1) (.cup, 3), true),
     (3, .kink 0 false, false), (3, .kink 1 true, true), (1, .r2 1 true, true),
     (2, .capSlide 1 false true, false), (2, .exch (.cup, 2) (.cap, 2), true),
     (2, .cupSlide 2 true true, true), (1, .exch (.cross true, 1) (.cup, 3), false),
     (0, .exch (.cup, 1) (.cup, 1), false), (5, .exch (.cross true, 1) (.cap, 4), true),
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

/-- A negative full twist is a doubled negative left curl and two positive right curls. -/
theorem morseReach_isoPark_twistDcurl :
    MorseReach 2 (isoBeadsWord [.t]) (isoDCurlL ++ isoCurlR true 1 ++ isoCurlR true 0) := by
  have h1 : MorseReach 2 (morseDouble (isoCurlL false 0)) (morseDouble (isoCurlR false 0)) :=
    morseReach_morseDouble morseReach_isoPark_curlLR (by decide)
  have h2 := morseReach_frame 2 2 0 0 [] (isoCurlR true 1 ++ isoCurlR true 0) _ _ h1
    (by decide) (by decide)
  simp only [morseShiftWord_zero_iso, List.nil_append] at h2
  refine morseReach_symm (morseReach_trans ?_ morseReach_isoPark_dcurlR_twist)
  simpa only [isoDCurlL, List.append_assoc] using h2

/-- After the clasp: the edge curls pass to the right edge, and two `kink`s open after `dL`. -/
private theorem morseReach_isoPark_crossTail :
    MorseReach 2 (isoDCurlL ++ isoClaspU ++ isoCurlR true 1 ++ isoCurlR true 0)
      (isoDCurlL ++ isoCurlR true 1 ++ isoCurlR true 0 ++ isoCurlR false 0 ++ isoCurlR false 1 ++
        isoBeadsWord [.cs, .p, .p]) :=
  ⟨[(16, .exch (.cup, 1) (.cap, 2), true), (15, .exch (.cup, 1) (.cross true, 1), true),
     (14, .exch (.cup, 1) (.cup, 2), true), (17, .exch (.cross true, 0) (.cap, 4), true),
     (16, .exch (.cross true, 0) (.cross true, 3), true), (18, .exch (.cap, 1) (.cap, 4), true),
     (17, .exch (.cap, 1) (.cross true, 3), true), (15, .exch (.cross true, 0) (.cup, 4), true),
     (16, .exch (.cap, 1) (.cup, 4), true), (16, .capSlide 1 true false, true),
     (15, .exch (.cross true, 0) (.cross true, 2), false), (18, .r2 0 true, true),
     (19, .exch (.cross false, 0) (.cap, 2), false), (16, .r3 0 true, false),
     (14, .cupSlide 1 true false, false), (14, .exch (.cross true, 0) (.cup, 2), true),
     (13, .r2 0 false, false), (12, .exch (.cap, 0) (.cup, 4), false),
     (13, .exch (.cap, 0) (.cross true, 3), false), (14, .exch (.cap, 0) (.cap, 4), false),
     (11, .exch (.cross true, 1) (.cup, 4), false),
     (12, .exch (.cross true, 1) (.cross true, 3), false),
     (13, .exch (.cross true, 1) (.cap, 4), false), (10, .exch (.cross true, 1) (.cup, 4), false),
     (11, .exch (.cross true, 1) (.cross true, 3), false),
     (12, .exch (.cross true, 1) (.cap, 4), false), (9, .exch (.cup, 2) (.cup, 2), false),
     (13, .zig 3 false, true), (14, .capSlide 2 true true, true),
     (13, .exch (.cross true, 2) (.cup, 4), true), (12, .exch (.cross true, 2) (.cap, 4), true),
     (10, .cupSlide 2 true false, false), (10, .zig 3 true, false),
     (9, .exch (.cup, 2) (.cup, 2), false), (10, .cupSlide 1 false false, true),
     (14, .capSlide 1 true true, true), (13, .exch (.cross true, 1) (.cross true, 3), true),
     (16, .exch (.cap, 1) (.cross true, 3), false), (12, .r2 1 false, false),
     (12, .r3 2 true, true), (11, .r2 2 false, false),
     (10, .exch (.cup, 1) (.cross true, 1), false), (13, .exch (.cap, 1) (.cross true, 3), false),
     (14, .capSlide 1 true false, true), (12, .r3 2 true, false),
     (14, .exch (.cross true, 1) (.cross true, 3), true),
     (11, .exch (.cup, 1) (.cross true, 1), false), (12, .cupSlide 1 true false, false),
     (14, .exch (.cap, 0) (.cap, 2), true), (13, .exch (.cap, 0) (.cross true, 3), true),
     (12, .exch (.cap, 0) (.cup, 2), true), (15, .exch (.cap, 0) (.cross false, 2), false),
     (16, .capSlide 0 false false, true), (17, .r2 2 false, true), (15, .r3 1 false, true),
     (18, .exch (.cross false, 0) (.cross true, 2), true), (14, .r2 1 true, false),
     (13, .exch (.cup, 0) (.cross false, 0), false), (14, .cupSlide 0 false false, false),
     (20, .zig 1 false, true), (21, .zig 2 false, true), (21, .cupSlide 3 true true, true),
     (24, .capSlide 2 true false, true), (26, .exch (.cap, 1) (.cap, 3), true),
     (22, .r3 3 true, false), (24, .exch (.cross true, 2) (.cross true, 4), true),
     (25, .exch (.cap, 1) (.cross true, 4), true), (20, .exch (.cup, 2) (.cup, 2), false),
     (21, .exch (.cup, 2) (.cross true, 2), false), (22, .cupSlide 2 true false, false),
     (22, .exch (.cap, 1) (.cup, 3), true), (21, .r2 1 false, true),
     (22, .capSlide 1 true true, false), (20, .zig 1 true, true), (21, .zig 2 true, true),
     (21, .cupSlide 1 true false, true), (24, .capSlide 2 true true, true),
     (26, .exch (.cap, 2) (.cap, 4), false), (22, .r3 1 true, true),
     (24, .exch (.cross true, 1) (.cross true, 3), false),
     (25, .exch (.cross true, 1) (.cap, 4), false), (20, .exch (.cup, 1) (.cup, 1), true),
     (21, .exch (.cross true, 1) (.cup, 3), true), (22, .cupSlide 2 true true, false),
     (22, .exch (.cup, 2) (.cap, 2), false), (22, .capSlide 1 false true, true),
     (21, .r2 1 true, false), (23, .kink 1 true, false), (19, .capSlide 1 false true, true),
     (18, .r2 1 true, false), (19, .exch (.cap, 1) (.cup, 3), false),
     (19, .cupSlide 2 false false, true), (18, .exch (.cup, 2) (.cross false, 2), true),
     (17, .exch (.cup, 2) (.cup, 2), true), (22, .exch (.cap, 1) (.cross false, 4), false),
     (21, .exch (.cross false, 2) (.cross false, 4), false), (19, .r3 3 false, true),
     (23, .exch (.cap, 1) (.cap, 3), false), (21, .capSlide 2 false false, false),
     (18, .cupSlide 3 false true, false), (18, .zig 2 false, false), (17, .zig 1 false, false),
     (8, .kink 1 true, true), (11, .kink 0 true, true)], by decide⟩

/-- Before the clasp: the negative edge curls pass to the right edge. -/
private theorem morseReach_isoPark_crossHead :
    MorseReach 2 (isoBeadsWord [.t] ++ isoCurlR false 0 ++ isoCurlR false 1 ++
        isoBeadsWord [.cs, .p, .p])
      (isoBeadsWord [.t, .n, .n, .cs, .p, .p]) :=
  ⟨[(4, .exch (.cap, 1) (.cup, 4), false), (3, .exch (.cross false, 0) (.cup, 4), false),
     (5, .exch (.cap, 1) (.cross false, 3), false), (6, .exch (.cap, 1) (.cap, 4), false),
     (4, .exch (.cross false, 0) (.cross false, 3), false),
     (5, .exch (.cross false, 0) (.cap, 4), false), (2, .exch (.cup, 1) (.cup, 2), false),
     (3, .exch (.cup, 1) (.cross false, 1), false), (4, .exch (.cup, 1) (.cap, 2), false),
     (7, .capSlide 1 true false, true), (9, .exch (.cross true, 0) (.cap, 2), true),
     (10, .r2 1 true, true), (8, .r3 0 true, true),
     (7, .exch (.cross true, 0) (.cross true, 2), true), (6, .r2 0 false, false),
     (5, .cupSlide 1 true false, false), (5, .exch (.cross true, 0) (.cup, 2), true),
     (8, .exch (.cap, 2) (.cup, 4), false), (7, .exch (.cross false, 1) (.cup, 4), false),
     (6, .exch (.cup, 2) (.cup, 2), false), (9, .capSlide 2 true false, true),
     (11, .exch (.cross true, 1) (.cap, 3), true), (12, .r2 2 true, true), (10, .r3 1 true, true),
     (9, .exch (.cross true, 1) (.cross true, 3), true), (8, .r2 1 false, false),
     (7, .cupSlide 2 true false, false), (7, .exch (.cross true, 1) (.cup, 3), true),
     (8, .r2 1 true, true), (9, .exch (.cross false, 1) (.cup, 3), false),
     (9, .cupSlide 2 false false, true), (11, .r3 1 false, true),
     (14, .exch (.cross true, 1) (.cap, 3), true), (13, .r2 1 false, false),
     (10, .exch (.cross false, 1) (.cross false, 3), true), (11, .capSlide 2 false false, false),
     (9, .zig 1 true, true), (9, .cupSlide 0 false false, true),
     (11, .exch (.cross false, 0) (.cap, 2), false), (15, .exch (.cap, 0) (.cap, 2), true),
     (12, .exch (.cross false, 0) (.cup, 2), false), (13, .capSlide 0 false true, false),
     (12, .zig 1 false, false), (11, .exch (.cap, 0) (.cap, 2), true),
     (8, .exch (.cup, 0) (.cross true, 1), true), (7, .exch (.cup, 0) (.cross true, 1), true),
     (9, .exch (.cross false, 1) (.cross true, 3), true),
     (10, .exch (.cap, 0) (.cross true, 3), true),
     (8, .exch (.cross false, 1) (.cross true, 3), true),
     (9, .exch (.cap, 0) (.cross true, 3), true), (6, .exch (.cup, 0) (.cup, 2), true),
     (7, .exch (.cross false, 1) (.cup, 4), true), (8, .exch (.cap, 0) (.cup, 4), true),
     (5, .exch (.cup, 0) (.cross true, 0), true), (8, .r2 2 false, true),
     (9, .exch (.cap, 0) (.cross true, 2), true), (9, .capSlide 0 false false, true),
     (7, .r3 1 false, false), (9, .exch (.cross false, 0) (.cross false, 2), true),
     (6, .r2 2 true, false), (5, .cupSlide 0 false false, false), (5, .zig 1 false, true),
     (6, .zig 2 false, true), (6, .cupSlide 3 false true, true), (9, .capSlide 2 false false, true),
     (11, .exch (.cap, 1) (.cap, 3), true), (7, .r3 3 false, false),
     (9, .exch (.cross false, 2) (.cross false, 4), true),
     (10, .exch (.cap, 1) (.cross false, 4), true), (5, .exch (.cup, 2) (.cup, 2), false),
     (6, .exch (.cup, 2) (.cross false, 2), false), (7, .cupSlide 2 false false, false),
     (7, .exch (.cap, 1) (.cup, 3), true), (6, .r2 1 true, true),
     (7, .capSlide 1 false true, false), (5, .zig 1 true, true), (6, .zig 2 true, true),
     (6, .cupSlide 1 false false, true), (9, .capSlide 2 false true, true),
     (11, .exch (.cap, 2) (.cap, 4), false), (7, .r3 1 false, true),
     (9, .exch (.cross false, 1) (.cross false, 3), false),
     (10, .exch (.cross false, 1) (.cap, 4), false), (5, .exch (.cup, 1) (.cup, 1), true),
     (6, .exch (.cross false, 1) (.cup, 3), true), (7, .cupSlide 2 false true, false),
     (7, .exch (.cup, 2) (.cap, 2), false), (7, .capSlide 1 true true, true),
     (6, .r2 1 false, false), (8, .kink 1 false, false), (4, .capSlide 1 true true, true),
     (3, .r2 1 false, false), (4, .exch (.cap, 1) (.cup, 3), false),
     (4, .cupSlide 2 true false, true), (3, .exch (.cup, 2) (.cross true, 2), true),
     (2, .exch (.cup, 2) (.cup, 2), true), (7, .exch (.cap, 1) (.cross true, 4), false),
     (6, .exch (.cross true, 2) (.cross true, 4), false), (4, .r3 3 true, true),
     (8, .exch (.cap, 1) (.cap, 3), false), (6, .capSlide 2 true false, false),
     (3, .cupSlide 3 true true, false), (3, .zig 2 false, false), (2, .zig 1 false, false)],
    by decide⟩

/-- Macro `K6`: a twist after the clasp crosses it, leaving two positive right-edge curls after
it and two negative ones before it. -/
theorem morseReach_isoPark_cross :
    MorseReach 2 (isoBeadsWord [.cs, .t]) (isoBeadsWord [.t, .n, .n, .cs, .p, .p]) := by
  have h1 := morseReach_frame 2 2 0 0 isoClaspU [] _ _ morseReach_isoPark_twistDcurl
    (by decide) (by decide)
  have h2 := morseReach_isoBead_dcurl 2 isoClaspU [] (isoCurlR true 1 ++ isoCurlR true 0)
    (by decide) (by decide) (by decide)
  have h4 := morseReach_frame 2 2 0 0 []
    (isoCurlR false 0 ++ isoCurlR false 1 ++ isoBeadsWord [.cs, .p, .p]) _ _
    (morseReach_symm morseReach_isoPark_twistDcurl) (by decide) (by decide)
  simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil, List.append_assoc]
    at h1 h2 h4
  have h3 := morseReach_isoPark_crossTail
  have h5 := morseReach_isoPark_crossHead
  simp only [List.append_assoc] at h3 h5
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 (morseReach_trans h4 h5)))

end AJConjecture
