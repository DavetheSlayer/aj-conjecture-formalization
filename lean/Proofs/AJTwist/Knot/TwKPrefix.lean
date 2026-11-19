import Mathlib
import AJTwist.Knot.TwKFence

/-!
# The chain prefix is a twist of the band at its bottom end

Normal forms of the four chain blocks (three strands: the return strand at `0`, the band at
`1, 2`), in band coordinates shifted by one:

| block | normal form | source |
|---|---|---|
| `twIncP` | `−0 −0 · u1 −2 n1` (`phaseTwoA1`) | library macro `A` |
| `twDecP` | `u1 +2 n1` (positive left curl) | library macro `DEC` (`isoStDec 1`) |
| `twIncN` | `u1 −2 n1` (negative left curl) | new, 5 letters |
| `twDecN` | `+0 +0 · u1 +2 n1` | new, 5 letters |

All four were checked outside Lean (equal Kauffman-bracket operators at thickness one and two,
`SCR/K/tools/chk_local.py`). In `twPrefix ℓ` the curls cancel in pairs (`kink`), and what remains
is `u1 +0` followed by `2ℓ` signed half twists of the band: `twTwistWord (2ℓ)` (checked,
`SCR/K/tools/chk_rel.py`, thickness one and two for `|ℓ| ≤ 2`).
-/

namespace AJConjecture

/-- `k` signed half twists of the two strands `0, 1` as a Morse word (positive `k`: positive
crossings); its thick operator is `halfTwistZ c k`. -/
def twTwistWord (k : ℤ) : MorseWord := List.replicate k.natAbs (isoX (decide (0 < k)) 0)

/-- Macro `A` for the ascending positive block. -/
theorem morseReach_twIncP : MorseReach 3 twIncP (morseShiftWord 1 phaseTwoA1) := by
  rw [show twIncP = phaseTwoMacroA_lhs by decide,
    show morseShiftWord 1 phaseTwoA1 = phaseTwoMacroA_rhs by decide]
  exact morseReach_phaseTwoMacroA

/-- Macro `DEC` for the descending positive block. -/
theorem morseReach_twDecP : MorseReach 3 twDecP (morseShiftWord 1 (isoCurlL true 1)) := by
  rw [show twDecP = isoStDec 1 by decide,
    show morseShiftWord 1 (isoCurlL true 1) = [isoU 2, isoX true 3, isoN 2] by decide]
  exact morseReach_isoMacroDEC

/-- The ascending negative block is a negative left curl. -/
theorem morseReach_twIncN : MorseReach 3 twIncN (morseShiftWord 1 (isoCurlL false 1)) := by
  exact ⟨[(0, .cupSlide 2 false false, true), (2, .r2 2 false, false),
      (2, .capSlide 1 false true, false)], by decide⟩

/-- The descending negative block is a positive full twist and a positive left curl. -/
theorem morseReach_twDecN :
    MorseReach 3 twDecN (morseShiftWord 1 ([isoX true 0, isoX true 0] ++ isoCurlL true 1)) := by
  exact ⟨[(2, .r2 3 true, true), (3, .exch (.cross false, 1) (.cross false, 3), true),
      (4, .capSlide 2 false false, false), (3, .r2 2 true, true), (1, .r3 2 true, false),
      (4, .capSlide 1 false false, false), (4, .capSlide 1 true false, true),
      (2, .r3 2 true, false), (4, .exch (.cross true, 1) (.cross true, 3), true),
      (0, .exch (.cup, 1) (.cross true, 1), false), (1, .exch (.cup, 1) (.cross true, 1), false),
      (2, .cupSlide 1 true false, false)], by decide⟩

/-- A negative left curl passes a positive full twist of the band. -/
private theorem morseReach_curlN_twistP_twKPrefix :
    MorseReach 2 (isoCurlL false 1 ++ [isoX true 0, isoX true 0])
      ([isoX true 0, isoX true 0] ++ isoCurlL false 1) := by
  exact ⟨[(1, .r2 1 true, true), (2, .capSlide 1 false true, false),
      (2, .exch (.cross true, 0) (.cap, 2), true), (3, .capSlide 1 true true, true),
      (1, .r3 0 true, true), (0, .cupSlide 0 true true, false),
      (3, .capSlide 1 true false, true), (5, .exch (.cross true, 0) (.cap, 2), true),
      (1, .exch (.cross true, 0) (.cross true, 2), false),
      (2, .exch (.cross true, 0) (.cross true, 2), false), (3, .r3 0 true, false),
      (0, .exch (.cup, 0) (.cross true, 0), false), (1, .exch (.cup, 0) (.cross true, 0), false),
      (2, .cupSlide 0 true false, false), (4, .capSlide 1 false true, true),
      (3, .r2 1 true, false)], by decide⟩

/-- Reachability between words from three strands to three strands, with the arities of both
sides. -/
private def TwReach3 (w w' : MorseWord) : Prop :=
  MorseReach 3 w w' ∧ (morseFits 3 w = true ∧ morseOut 3 w = 3) ∧
    (morseFits 3 w' = true ∧ morseOut 3 w' = 3)

/-- A word from three strands to three strands reaches itself. -/
private theorem twReach3_refl {w : MorseWord} (hf : morseFits 3 w = true)
    (ho : morseOut 3 w = 3) : TwReach3 w w :=
  ⟨morseReach_refl 3 w, ⟨hf, ho⟩, ⟨hf, ho⟩⟩

/-- The source of a replacement reaches itself. -/
private theorem twReach3_left {w w' : MorseWord} (h : TwReach3 w w') : TwReach3 w w :=
  twReach3_refl h.2.1.1 h.2.1.2

/-- The target of a replacement reaches itself. -/
private theorem twReach3_right {w w' : MorseWord} (h : TwReach3 w w') : TwReach3 w' w' :=
  twReach3_refl h.2.2.1 h.2.2.2

/-- Replacements compose. -/
private theorem twReach3_trans {a b c : MorseWord} (h₁ : TwReach3 a b) (h₂ : TwReach3 b c) :
    TwReach3 a c :=
  ⟨morseReach_trans h₁.1 h₂.1, h₁.2.1, h₂.2.2⟩

/-- Replacements of consecutive words compose. -/
private theorem twReach3_append {a a' b b' : MorseWord} (ha : TwReach3 a a')
    (hb : TwReach3 b b') : TwReach3 (a ++ b) (a' ++ b') := by
  obtain ⟨ra, ⟨fa, oa⟩, ⟨fa', oa'⟩⟩ := ha
  obtain ⟨rb, ⟨fb, ob⟩, ⟨fb', ob'⟩⟩ := hb
  have h1 := morseReach_frame 3 3 0 0 [] b a a' ra fa rfl
  have h2 := morseReach_frame 3 3 0 0 a' [] b b' rb fb (by rw [oa'])
  simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil] at h1 h2
  refine ⟨morseReach_trans h1 h2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [morseFits_append, fa, oa, fb]; rfl
  · rw [morseOut_append, oa, ob]
  · rw [morseFits_append, fa', oa', fb']; rfl
  · rw [morseOut_append, oa', ob']

/-- The empty word. -/
private theorem twReach3_nil : TwReach3 [] [] := twReach3_refl rfl rfl

/-- A run of blocks, first block split off. -/
private theorem phaseTwoBlk_succ_twKPrefix (w : MorseWord) (m : ℕ) :
    phaseTwoBlk w (m + 1) = w ++ phaseTwoBlk w m := by
  simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons]

/-- A run of blocks, last block split off. -/
private theorem phaseTwoBlk_succ'_twKPrefix (w : MorseWord) (m : ℕ) :
    phaseTwoBlk w (m + 1) = phaseTwoBlk w m ++ w := by
  simp only [phaseTwoBlk, List.replicate_succ', List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- A run of equal blocks is replaced block by block. -/
private theorem twReach3_blk {x y : MorseWord} (h : TwReach3 x y) (k : ℕ) :
    TwReach3 (phaseTwoBlk x k) (phaseTwoBlk y k) := by
  induction k with
  | zero => exact twReach3_nil
  | succ k ih =>
    rw [phaseTwoBlk_succ_twKPrefix, phaseTwoBlk_succ_twKPrefix]
    exact twReach3_append h ih

/-- A replacement on two strands, moved to the strands `1, 2` of three. -/
private theorem twReach3_shift {w w' : MorseWord} (h : MorseReach 2 w w')
    (hf : morseFits 2 w = true) (ho : morseOut 2 w = 2) (hf' : morseFits 2 w' = true)
    (ho' : morseOut 2 w' = 2) : TwReach3 (morseShiftWord 1 w) (morseShiftWord 1 w') := by
  have h1 := morseReach_frame 2 3 1 0 [] [] w w' h hf rfl
  simp only [List.nil_append, List.append_nil] at h1
  obtain ⟨o, f⟩ := morseOut_fits_shift 2 1 0 w hf
  obtain ⟨o', f'⟩ := morseOut_fits_shift 2 1 0 w' hf'
  exact ⟨h1, ⟨f, by rw [o, ho]⟩, ⟨f', by rw [o', ho']⟩⟩

/-- A word that commutes with a block commutes with a run of the block. -/
private theorem twReach3_comm_blk {c x : MorseWord} (hc : TwReach3 c c) (hx : TwReach3 x x)
    (hcx : TwReach3 (c ++ x) (x ++ c)) (j : ℕ) :
    TwReach3 (c ++ phaseTwoBlk x j) (phaseTwoBlk x j ++ c) := by
  induction j with
  | zero =>
    simpa only [phaseTwoBlk, List.replicate_zero, List.flatten_nil, List.append_nil,
      List.nil_append] using hc
  | succ j ih =>
    have s1 : TwReach3 (c ++ x ++ phaseTwoBlk x j) (x ++ c ++ phaseTwoBlk x j) :=
      twReach3_append hcx (twReach3_blk hx j)
    have s2 : TwReach3 (x ++ (c ++ phaseTwoBlk x j)) (x ++ (phaseTwoBlk x j ++ c)) :=
      twReach3_append hx ih
    rw [phaseTwoBlk_succ_twKPrefix]
    simp only [List.append_assoc] at s1 s2 ⊢
    exact twReach3_trans s1 s2

/-- Curls `c` in front of a run of blocks `x d`, where `c` commutes with `x` and cancels with
`d`, cancel against the `d`. -/
private theorem twReach3_curls {c x d : MorseWord} (hc : TwReach3 c c) (hx : TwReach3 x x)
    (hd : TwReach3 d d) (hcx : TwReach3 (c ++ x) (x ++ c)) (hcd : TwReach3 (c ++ d) [])
    (a : ℕ) : ∀ j : ℕ,
      TwReach3 (phaseTwoBlk c a ++ (phaseTwoBlk x j ++ phaseTwoBlk (x ++ d) a))
        (phaseTwoBlk x (j + a)) := by
  induction a with
  | zero =>
    intro j
    simpa only [phaseTwoBlk, List.replicate_zero, List.flatten_nil, List.nil_append,
      List.append_nil, Nat.add_zero] using twReach3_blk hx j
  | succ a ih =>
    intro j
    have s1 : TwReach3
        (c ++ (phaseTwoBlk c a ++ (phaseTwoBlk x j ++ phaseTwoBlk (x ++ d) a)) ++ (x ++ d))
        (c ++ phaseTwoBlk x (j + a) ++ (x ++ d)) :=
      twReach3_append (twReach3_append hc (ih j)) (twReach3_append hx hd)
    have s2 : TwReach3 (c ++ phaseTwoBlk x (j + a) ++ (x ++ d))
        (phaseTwoBlk x (j + a) ++ c ++ (x ++ d)) :=
      twReach3_append (twReach3_comm_blk hc hx hcx (j + a)) (twReach3_append hx hd)
    have s3 : TwReach3 (phaseTwoBlk x (j + a) ++ (c ++ x) ++ d)
        (phaseTwoBlk x (j + a) ++ (x ++ c) ++ d) :=
      twReach3_append (twReach3_append (twReach3_blk hx (j + a)) hcx) hd
    have s4 : TwReach3 (phaseTwoBlk x (j + a) ++ x ++ (c ++ d))
        (phaseTwoBlk x (j + a) ++ x ++ []) :=
      twReach3_append (twReach3_append (twReach3_blk hx (j + a)) hx) hcd
    rw [phaseTwoBlk_succ_twKPrefix c, phaseTwoBlk_succ'_twKPrefix (x ++ d), ← Nat.add_assoc,
      phaseTwoBlk_succ'_twKPrefix x (j + a)]
    simp only [List.append_assoc, List.append_nil] at s1 s2 s3 s4 ⊢
    exact twReach3_trans s1 (twReach3_trans s2 (twReach3_trans s3 s4))

/-- The positive left curl of the band, on the strands `1, 2` of three. -/
private abbrev twP3 : MorseWord := morseShiftWord 1 (isoCurlL true 1)

/-- The negative left curl of the band, on the strands `1, 2` of three. -/
private abbrev twN3 : MorseWord := morseShiftWord 1 (isoCurlL false 1)

/-- The full twist of sign `s` of the band, on the strands `1, 2` of three. -/
private abbrev twT3 (s : Bool) : MorseWord := morseShiftWord 1 [isoX s 0, isoX s 0]

/-- The positive curl is a word from three strands to three strands. -/
private theorem twReach3_P : TwReach3 twP3 twP3 := twReach3_refl (by decide) (by decide)

/-- The negative curl is a word from three strands to three strands. -/
private theorem twReach3_N : TwReach3 twN3 twN3 := twReach3_refl (by decide) (by decide)

/-- The full twist is a word from three strands to three strands. -/
private theorem twReach3_T (s : Bool) : TwReach3 (twT3 s) (twT3 s) := by
  cases s <;> exact twReach3_refl (by decide) (by decide)

/-- `p n` cancels (library macro `PN`). -/
private theorem twReach3_PN : TwReach3 (twP3 ++ twN3) [] :=
  twReach3_shift morseReach_isoPark_PN (by decide) (by decide) (by decide) (by decide)

/-- `n p` cancels (library macro `NP`). -/
private theorem twReach3_NP : TwReach3 (twN3 ++ twP3) [] :=
  twReach3_shift morseReach_isoPark_NP (by decide) (by decide) (by decide) (by decide)

/-- `p` passes a negative full twist (library macro `TP`). -/
private theorem twReach3_Pt : TwReach3 (twP3 ++ twT3 false) (twT3 false ++ twP3) :=
  twReach3_shift (morseReach_symm morseReach_isoPark_TP) (by decide) (by decide) (by decide)
    (by decide)

/-- `n` passes a positive full twist. -/
private theorem twReach3_NT : TwReach3 (twN3 ++ twT3 true) (twT3 true ++ twN3) :=
  twReach3_shift morseReach_curlN_twistP_twKPrefix (by decide) (by decide) (by decide)
    (by decide)

/-- The ascending positive block and its normal form. -/
private theorem twReach3_twIncP : TwReach3 twIncP (twT3 false ++ twN3) :=
  ⟨morseReach_twIncP, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The descending positive block and its normal form. -/
private theorem twReach3_twDecP : TwReach3 twDecP twP3 :=
  ⟨morseReach_twDecP, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The ascending negative block and its normal form. -/
private theorem twReach3_twIncN : TwReach3 twIncN twN3 :=
  ⟨morseReach_twIncN, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The descending negative block and its normal form. -/
private theorem twReach3_twDecN : TwReach3 twDecN (twT3 true ++ twP3) :=
  ⟨morseReach_twDecN, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The chain for `ℓ = -(n + 1)`: `n + 1` negative full twists of the band. -/
private theorem twReach3_chain_neg (n : ℕ) :
    TwReach3 (phaseTwoBlk twDecP n ++ phaseTwoBlk twIncP (n + 1) ++ twDecP)
      (phaseTwoBlk (twT3 false) (n + 1)) := by
  have s0 : TwReach3 (phaseTwoBlk twDecP n ++ phaseTwoBlk twIncP (n + 1) ++ twDecP)
      (phaseTwoBlk twP3 n ++ phaseTwoBlk (twT3 false ++ twN3) (n + 1) ++ twP3) :=
    twReach3_append (twReach3_append (twReach3_blk twReach3_twDecP n)
      (twReach3_blk twReach3_twIncP (n + 1))) twReach3_twDecP
  have g := twReach3_curls twReach3_P (twReach3_T false) twReach3_N twReach3_Pt twReach3_PN n 0
  have s1 := twReach3_append g (twReach3_append (twReach3_T false) twReach3_NP)
  have z : phaseTwoBlk (twT3 false) 0 = [] := rfl
  rw [phaseTwoBlk_succ'_twKPrefix (twT3 false ++ twN3)] at s0
  rw [phaseTwoBlk_succ'_twKPrefix (twT3 false)]
  simp only [List.append_assoc, List.append_nil, List.nil_append, Nat.zero_add, z] at s0 s1 ⊢
  exact twReach3_trans s0 s1

/-- The chain for `ℓ = n + 1`: `n + 1` positive full twists of the band. -/
private theorem twReach3_chain_pos (n : ℕ) :
    TwReach3 (phaseTwoBlk twIncN (n + 3) ++ twDecP ++ phaseTwoBlk twDecN (n + 1) ++ twDecP)
      (phaseTwoBlk (twT3 true) (n + 1)) := by
  have s0 : TwReach3
      (phaseTwoBlk twIncN (n + 3) ++ twDecP ++ phaseTwoBlk twDecN (n + 1) ++ twDecP)
      (phaseTwoBlk twN3 (n + 3) ++ twP3 ++ phaseTwoBlk (twT3 true ++ twP3) (n + 1) ++ twP3) :=
    twReach3_append (twReach3_append (twReach3_append (twReach3_blk twReach3_twIncN (n + 3))
      twReach3_twDecP) (twReach3_blk twReach3_twDecN (n + 1))) twReach3_twDecP
  have hB : TwReach3 (phaseTwoBlk (twT3 true ++ twP3) (n + 1))
      (phaseTwoBlk (twT3 true ++ twP3) (n + 1)) :=
    twReach3_blk (twReach3_append (twReach3_T true) twReach3_P) (n + 1)
  have s1 : TwReach3
      (twN3 ++ phaseTwoBlk twN3 (n + 1) ++ (twN3 ++ twP3) ++
        phaseTwoBlk (twT3 true ++ twP3) (n + 1) ++ twP3)
      (twN3 ++ phaseTwoBlk twN3 (n + 1) ++ [] ++
        phaseTwoBlk (twT3 true ++ twP3) (n + 1) ++ twP3) :=
    twReach3_append (twReach3_append (twReach3_append (twReach3_append twReach3_N
      (twReach3_blk twReach3_N (n + 1))) twReach3_NP) hB) twReach3_P
  have g := twReach3_curls twReach3_N (twReach3_T true) twReach3_P twReach3_NT twReach3_NP
    (n + 1) 0
  have s2 := twReach3_append (twReach3_append twReach3_N g) twReach3_P
  have s3 := twReach3_append
    (twReach3_comm_blk twReach3_N (twReach3_T true) twReach3_NT (n + 1)) twReach3_P
  have s4 := twReach3_append (twReach3_blk (twReach3_T true) (n + 1)) twReach3_NP
  have z : phaseTwoBlk (twT3 true) 0 = [] := rfl
  rw [show n + 3 = n + 1 + 1 + 1 from rfl, phaseTwoBlk_succ'_twKPrefix twN3 (n + 1 + 1),
    phaseTwoBlk_succ_twKPrefix twN3 (n + 1)] at s0
  simp only [List.append_assoc, List.append_nil, List.nil_append, Nat.zero_add, z]
    at s0 s1 s2 s3 s4 ⊢
  exact twReach3_trans s0 (twReach3_trans s1 (twReach3_trans s2 (twReach3_trans s3 s4)))

/-- A run of full twists of the band is the shifted run of half twists. -/
private theorem morseShiftWord_twTwistWord_twKPrefix (s : Bool) (m : ℕ) (k : ℤ)
    (hk : k.natAbs = 2 * m) (hs : decide (0 < k) = s) :
    morseShiftWord 1 (twTwistWord k) = phaseTwoBlk (twT3 s) m := by
  rw [twTwistWord, hk, hs]
  clear hk hs
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [phaseTwoBlk_succ_twKPrefix, ← ih, show 2 * (m + 1) = 2 + 2 * m by ring,
      List.replicate_add, morseShiftWord_append]
    rfl

/-- The chain prefix is `u1 +0` followed by a word from three strands to three strands that
reaches the shifted run of half twists. -/
private theorem exists_twPrefix_body_twKPrefix (ℓ : ℤ) :
    ∃ b : MorseWord, twPrefix ℓ = [isoU 1, isoX true 0] ++ b ∧
      TwReach3 b (morseShiftWord 1 (twTwistWord (2 * ℓ))) := by
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, ℓ = -((n : ℤ) + 1) := ⟨(-ℓ).toNat - 1, by omega⟩
    refine ⟨phaseTwoBlk twDecP n ++ phaseTwoBlk twIncP (n + 1) ++ twDecP, ?_, ?_⟩
    · rw [twPrefix, ite_eq_right (by omega), ite_eq_left (by omega),
        show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, Nat.add_sub_cancel]
    · rw [morseShiftWord_twTwistWord_twKPrefix false (n + 1) _ (by omega)
        (decide_eq_false (by omega))]
      exact twReach3_chain_neg n
  · exact ⟨[], rfl, twReach3_nil⟩
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, ℓ = (n : ℤ) + 1 := ⟨ℓ.toNat - 1, by omega⟩
    refine ⟨phaseTwoBlk twIncN (n + 3) ++ twDecP ++ phaseTwoBlk twDecN (n + 1) ++ twDecP,
      ?_, ?_⟩
    · rw [twPrefix, ite_eq_right (by omega), ite_eq_right (by omega),
        show ((n : ℤ) + 1).natAbs = n + 1 by omega]
    · rw [morseShiftWord_twTwistWord_twKPrefix true (n + 1) _ (by omega)
        (decide_eq_true (by omega))]
      exact twReach3_chain_pos n

/-- The chain prefix is `u1 +0` followed by `2ℓ` half twists of the band. -/
theorem morseReach_twPrefix (ℓ : ℤ) :
    MorseReach 1 (twPrefix ℓ)
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (2 * ℓ))) := by
  obtain ⟨b, hb, hr⟩ := exists_twPrefix_body_twKPrefix ℓ
  have h := morseReach_frame 3 1 0 0 [isoU 1, isoX true 0] [] b _ hr.1 hr.2.1.1 rfl
  simp only [morseShiftWord_zero_iso, List.append_nil] at h
  rw [hb]
  exact h

/-- The long closure of the twisted word reaches the strip word of the untwisted list with
`2ℓ` half twists inserted at the bottom end of the band. -/
theorem morseReach_tw_source_bottom {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    MorseReach 1 (morseLongClosure (twStrands r s ℓ) (twWhiteheadWord r s ℓ σ))
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (2 * ℓ)) ++ twStripTail r s σ) := by
  obtain ⟨b, hb, hr⟩ := exists_twPrefix_body_twKPrefix ℓ
  have hfit : morseFits 1 (twPrefix ℓ) = true := by
    rw [hb, morseFits_append, show morseOut 1 [isoU 1, isoX true 0] = 3 from rfl, hr.2.1.1]
    rfl
  have h2 := morseReach_frame 1 1 0 0 [] (twStripTail r s σ) (twPrefix ℓ) _
    (morseReach_twPrefix ℓ) hfit rfl
  simp only [morseShiftWord_zero_iso, List.nil_append] at h2
  exact morseReach_trans (morseReach_tw_source_fence h ℓ σ) h2

end AJConjecture
