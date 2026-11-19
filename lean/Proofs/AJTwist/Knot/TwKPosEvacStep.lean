import Mathlib
import AJTwist.Knot.TwKPosEvacDefs

/-!
# One step of the snowball

`morseReach_isoSnowStep`: in a doubled word with beads (`isoSlotWord 1 G β` between a prefix `u`
and a suffix `v`), the whole content of the slot of a segment `x` of the knot moves to the slot of
the next segment `y = isoTraceStep G x` (`isoSnowStep β x y`).

Route (the cases of `isoJ_step_up`, `isoJ_step_down` of `PairKIsoBeadSlide`, which move one bead
through the doubled word without other beads; here the other beads are part of the frame):
split the word at the level `k` of `x` (a lemma `isoSlotWord 1 G β = (levels < k) ++ isoLayer …
(β k) ++ morseDoubleLetter l ++ (levels > k)`); inside a layer, tangles on different bands
commute (`morseReach_isoBead_commR`, `morseReach_isoShiftComm`), so the moving tangle `T` can be
brought next to the doubled letter and, after the step, to its place in the layer of `y`. Then

* going up across the letter `k`: a doubled crossing on the band of `T`
  (`morseReach_isoBead_D`, `morseReach_beadD_right` of the library), a letter on other bands
  (exchange, as `morseReach_isoBead_commL/R`), and `T` arrives below the content of the slot of
  `y`;
* at a doubled cap on the band of `T`: `morseReach_isoBead_cap` (and its mirror for the right
  leg, by `isoRot_isoRot`); `T` stays at the level `k`, rotated, on top of the content of the
  slot of `y`;
* going down across the letter `k - 1`, and at a doubled cup: the same lemmas read backwards
  (`morseReach_symm`), `morseReach_isoBead_cup`.

The definition of `isoSnowStep` was evaluated in Lean against the simulation
(`SCR/KP/leancheck/EvalEvac.lean`): the slot words agree letter for letter at every step.
-/

namespace AJConjecture

/-! ### Doubled letters and the passage of a band bead -/

/-- A doubled crossing, letter by letter. -/
private theorem morseDoubleLetter_cross_evacStep (s : Bool) (i : ℕ) :
    morseDoubleLetter (MorseKind.cross s, i) =
      [(MorseKind.cross s, 2 * i + 1), (MorseKind.cross s, if s then 2 * i + 2 else 2 * i),
        (MorseKind.cross s, if s then 2 * i else 2 * i + 2), (MorseKind.cross s, 2 * i + 1)] := by
  cases s <;> simp [morseDoubleLetter, morseOfBraid, cable, cableGen, List.range_succ]

/-- A doubled letter fits on the doubled strands. -/
private theorem morseDoubleLetter_fits_evacStep (n e : ℕ) (l : MorseLetter)
    (h : l.2 + morseKindIn l.1 ≤ n) :
    morseFits (2 * n + e) (morseDoubleLetter l) = true ∧
      morseOut (2 * n + e) (morseDoubleLetter l) = 2 * morseLetterOut n l + e := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [morseDoubleLetter, morseFits_cons, morseFits_nil, morseOut, morseLetterOut,
      morseKindIn, morseKindOut, and_true] at h ⊢
    omega
  | cap =>
    simp only [morseDoubleLetter, morseFits_cons, morseFits_nil, morseOut, morseLetterOut,
      morseKindIn, morseKindOut, and_true] at h ⊢
    omega
  | cross s =>
    rw [morseDoubleLetter_cross_evacStep]
    cases s <;> simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, and_true, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;> omega

/-- A shifted doubled crossing. -/
private theorem morseDouble_cross_shift_evacStep (s : Bool) (i : ℕ) :
    morseShiftWord (2 * i) (morseDouble [(MorseKind.cross s, 0)]) =
      morseDouble [(MorseKind.cross s, i)] := by
  simp only [morseDouble, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    morseDoubleLetter_cross_evacStep]
  cases s <;> simp [morseShiftWord, shiftLetter] <;> omega

/-- A band bead passes a doubled crossing of either sign at position `0`, in both directions. -/
private theorem morseReach_beadX_base_evacStep (s : Bool) (B : MorseWord)
    (hB : morseFits 2 B = true) (hBo : morseOut 2 B = 2) :
    MorseReach 4 (B ++ morseDouble [(MorseKind.cross s, 0)])
        (morseDouble [(MorseKind.cross s, 0)] ++ morseShiftWord 2 B) ∧
      MorseReach 4 (morseShiftWord 2 B ++ morseDouble [(MorseKind.cross s, 0)])
        (morseDouble [(MorseKind.cross s, 0)] ++ B) := by
  cases s with
  | true =>
    have hD : morseDouble [(MorseKind.cross true, 0)] = phaseTwoD := by decide
    rw [hD]
    exact ⟨by simpa using morseReach_beadD_left 4 [] B [] hB hBo le_rfl,
      by simpa using morseReach_beadD_right 4 [] B [] hB hBo le_rfl⟩
  | false =>
    have hD : morseDouble [(MorseKind.cross false, 0)] =
        morseWalkL false 0 2 ++ morseWalkL false 1 2 := by decide
    have hW : morseWalkL false 0 2 ++ morseWalkL false 1 2 =
        [(MorseKind.cross false, 1)] ++ [(MorseKind.cross false, 0), (MorseKind.cross false, 2)] ++
          [(MorseKind.cross false, 1)] := by decide
    have hE : ∀ x y : MorseWord, morseOut 4 x = 4 →
        MorseReach 4 (x ++ [(MorseKind.cross false, 1)] ++
            [(MorseKind.cross false, 0), (MorseKind.cross false, 2)] ++
              ([(MorseKind.cross false, 1)] ++ y))
          (x ++ [(MorseKind.cross false, 1)] ++
            [(MorseKind.cross false, 2), (MorseKind.cross false, 0)] ++
              ([(MorseKind.cross false, 1)] ++ y)) := by
      intro x y hx
      have h := morseReach_isoRule 4 (x ++ [(MorseKind.cross false, 1)])
        ([(MorseKind.cross false, 1)] ++ y)
        (.exch (MorseKind.cross false, 0) (MorseKind.cross false, 2))
        rfl (by rw [morseOut_append, hx]; rfl) (by rw [morseOut_append, hx]; rfl)
      simpa [morseRuleLhs, morseRuleRhs, morseKindIn, morseKindOut] using h
    rw [hD]
    refine ⟨?_, ?_⟩
    · have h1 := morseReach_passL 4 0 2 false [] B (morseWalkL false 1 2) hB (by decide)
        (by rw [hBo]; decide)
      have h2 := morseReach_passL 4 1 2 false (morseWalkL false 0 2) B [] hB (by decide)
        (by rw [hBo]; decide)
      rw [hBo, morseShiftWord_zero_iso] at h1
      rw [hBo] at h2
      simp only [List.nil_append, List.append_nil, Nat.zero_add] at h1 h2
      simpa only [List.append_assoc] using morseReach_trans h1 h2
    · have h1 := morseReach_symm (morseReach_pass 4 1 2 false [] B (morseWalk false 0 2) hB
        (by decide))
      have h2 := morseReach_symm (morseReach_pass 4 0 2 false (morseWalk false 1 2) B [] hB
        (by decide))
      rw [hBo] at h1 h2
      rw [morseShiftWord_zero_iso] at h2
      have hx : morseOut 4 (morseShiftWord 2 B) = 4 := by
        have := (morseOut_shift_iso 2 2 0 B hB).1; rwa [hBo] at this
      have h0 := hE (morseShiftWord 2 B) [] hx
      have h3 := morseReach_symm (hE [] B rfl)
      have hw1 : morseWalk false 1 2 = [(MorseKind.cross false, 1), (MorseKind.cross false,
          2)] := by
        decide
      have hw0 : morseWalk false 0 2 = [(MorseKind.cross false, 0), (MorseKind.cross false,
          1)] := by
        decide
      rw [hw1, hw0] at h1 h2
      rw [hW]
      simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
        show (1 : ℕ) + 1 = 2 from rfl, Nat.zero_add] at h0 h1 h2 h3 ⊢
      exact morseReach_trans h0 (morseReach_trans h1 (morseReach_trans h2 h3))

/-- A band bead passes a doubled crossing of either sign, in both directions. -/
private theorem morseReach_beadX_evacStep (n₀ i : ℕ) (s : Bool) (B u v : MorseWord)
    (hB : morseFits 2 B = true) (hBo : morseOut 2 B = 2) (hu : 2 * i + 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (2 * i) B ++ morseDoubleLetter (MorseKind.cross s, i) ++ v)
        (u ++ morseDoubleLetter (MorseKind.cross s, i) ++ morseShiftWord (2 * i + 2) B ++ v) ∧
      MorseReach n₀
        (u ++ morseShiftWord (2 * i + 2) B ++ morseDoubleLetter (MorseKind.cross s, i) ++ v)
        (u ++ morseDoubleLetter (MorseKind.cross s, i) ++ morseShiftWord (2 * i) B ++ v) := by
  obtain ⟨h1, h2⟩ := morseReach_beadX_base_evacStep s B hB hBo
  have hD4 : morseFits 4 (morseDouble [(MorseKind.cross s, 0)]) = true := by cases s <;> decide
  have hf1 : morseFits 4 (B ++ morseDouble [(MorseKind.cross s, 0)]) = true := by
    rw [morseFits_append, morseFits_add_right_iso 2 2 B hB, morseOut_add_right 2 2 B hB, hBo, hD4]
    rfl
  have hf2 : morseFits 4 (morseShiftWord 2 B ++ morseDouble [(MorseKind.cross s, 0)]) = true := by
    have h := morseOut_shift_iso 2 2 0 B hB
    rw [hBo] at h
    rw [morseFits_append, h.2, h.1, hD4]
    rfl
  have hL := morseDouble_cross_shift_evacStep s i
  have hdl : morseDouble [(MorseKind.cross s, i)] = morseDoubleLetter (MorseKind.cross s, i) := by
    simp [morseDouble]
  rw [hdl] at hL
  have k1 := morseReach_frame 4 n₀ (2 * i) (morseOut n₀ u - 2 * i - 4) u v _ _ h1 hf1 (by omega)
  have k2 := morseReach_frame 4 n₀ (2 * i) (morseOut n₀ u - 2 * i - 4) u v _ _ h2 hf2 (by omega)
  simp only [morseShiftWord_append, morseShiftWord_shift_iso, hL, Nat.add_comm 2 (2 * i)] at k1 k2
  exact ⟨by simpa only [List.append_assoc] using k1, by simpa only [List.append_assoc] using k2⟩

/-- The letters of a doubled letter lie at twice its position or to the right. -/
private theorem mem_morseDoubleLetter_evacStep {l x : MorseLetter}
    (hx : x ∈ morseDoubleLetter l) : 2 * l.2 ≤ x.2 := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [morseDoubleLetter, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  | cap =>
    simp only [morseDoubleLetter, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  | cross s =>
    rw [morseDoubleLetter_cross_evacStep] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    cases s <;> rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- A bead passes a doubled letter lying on its left. -/
private theorem morseReach_passL_evacStep (n₀ c p q e : ℕ) (l : MorseLetter) (B u v : MorseWord)
    (hB : morseFits 2 B = true) (hBo : morseOut 2 B = 2) (hl : l.2 + morseKindIn l.1 ≤ p)
    (hp : p + 1 ≤ c) (hq : morseLetterOut p l = q) (hu : morseOut n₀ u = 2 * c + e) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p) B ++ morseDoubleLetter l ++ v)
      (u ++ morseDoubleLetter l ++ morseShiftWord (2 * q) B ++ v) := by
  have hd := morseDoubleLetter_fits_evacStep p 0 l hl
  rw [Nat.add_zero, Nat.add_zero, hq] at hd
  have h := morseReach_isoBead_commL n₀ (2 * p) 2 (2 * c + e - 2 * p - 2) B u
    (morseDoubleLetter l) v hB hBo hd.1 (by omega)
  rwa [hd.2] at h

/-- A bead passes a doubled letter lying on its right. -/
private theorem morseReach_passR_evacStep (n₀ c p e : ℕ) (l : MorseLetter) (B u v : MorseWord)
    (hB : morseFits 2 B = true) (hBo : morseOut 2 B = 2) (hl : p + 1 ≤ l.2)
    (hlc : l.2 + morseKindIn l.1 ≤ c) (hp : p + 1 ≤ c) (hu : morseOut n₀ u = 2 * c + e) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p) B ++ morseDoubleLetter l ++ v)
      (u ++ morseDoubleLetter l ++ morseShiftWord (2 * p) B ++ v) := by
  have hd := morseDoubleLetter_fits_evacStep c e l hlc
  exact morseReach_isoBead_commR n₀ (2 * p) 2 B u (morseDoubleLetter l) v hB hBo
    (fun x hx ↦ by have := mem_morseDoubleLetter_evacStep hx; omega) (by rw [hu]; exact hd.1)
    (by omega)

/-- The band `p` below the letter `l` continues as the band `q` above it. -/
private def IsoPassEvacStep (l : MorseLetter) (p q : ℕ) : Prop :=
  match l with
  | (.cross _, i) => (p = i ∧ q = i + 1) ∨ (p = i + 1 ∧ q = i) ∨ (p ≠ i ∧ p ≠ i + 1 ∧ q = p)
  | (.cup, i) => (p < i ∧ q = p) ∨ (i ≤ p ∧ q = p + 2)
  | (.cap, i) => (p < i ∧ q = p) ∨ (i + 2 ≤ p ∧ q + 2 = p)

/-- A band that continues through a letter arrives on a band above it. -/
private theorem isoPass_lt_evacStep {l : MorseLetter} {p q n : ℕ} (h : IsoPassEvacStep l p q)
    (hl : l.2 + morseKindIn l.1 ≤ n) :
    (p < n → q < morseLetterOut n l) ∧ (q < morseLetterOut n l → p < n) := by
  obtain ⟨k, i⟩ := l
  cases k <;> simp only [IsoPassEvacStep, morseLetterOut, morseKindIn, morseKindOut] at h hl ⊢ <;>
    omega

/-- A band bead passes a doubled letter along its band. -/
private theorem morseReach_isoPass_evacStep (n₀ n e p q : ℕ) (l : MorseLetter)
    (T u v : MorseWord) (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2)
    (hl : l.2 + morseKindIn l.1 ≤ n) (hp : p < n) (hpq : IsoPassEvacStep l p q)
    (hu : morseOut n₀ u = 2 * n + e) :
    MorseReach n₀ (u ++ morseShiftWord (2 * p) T ++ morseDoubleLetter l ++ v)
      (u ++ morseDoubleLetter l ++ morseShiftWord (2 * q) T ++ v) := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cross s =>
    simp only [IsoPassEvacStep] at hpq
    simp only [morseKindIn] at hl
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, rfl⟩
    · have h := (morseReach_beadX_evacStep n₀ p s T u v hT hTo (by rw [hu]; omega)).1
      rwa [show 2 * (p + 1) = 2 * p + 2 by ring]
    · have h := (morseReach_beadX_evacStep n₀ q s T u v hT hTo (by rw [hu]; omega)).2
      rwa [show 2 * (q + 1) = 2 * q + 2 by ring]
    · rcases Nat.lt_or_ge q i with h3 | h3
      · exact morseReach_passR_evacStep n₀ n q e (MorseKind.cross s, i) T u v hT hTo
          (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hu
      · exact morseReach_passL_evacStep n₀ n q q e (MorseKind.cross s, i) T u v hT hTo
          (by simp only [morseKindIn]; omega) (by omega)
          (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hu
  | cup =>
    simp only [IsoPassEvacStep] at hpq
    simp only [morseKindIn] at hl
    rcases hpq with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · exact morseReach_passR_evacStep n₀ n q e (MorseKind.cup, i) T u v hT hTo
        (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hu
    · exact morseReach_passL_evacStep n₀ n p (p + 2) e (MorseKind.cup, i) T u v hT hTo
        (by simp only [morseKindIn]; omega) (by omega)
        (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hu
  | cap =>
    simp only [IsoPassEvacStep] at hpq
    simp only [morseKindIn] at hl
    rcases hpq with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · exact morseReach_passR_evacStep n₀ n q e (MorseKind.cap, i) T u v hT hTo
        (by simp only; omega) (by simp only [morseKindIn]; omega) (by omega) hu
    · exact morseReach_passL_evacStep n₀ n p q e (MorseKind.cap, i) T u v hT hTo
        (by simp only [morseKindIn]; omega) (by omega)
        (by simp only [morseLetterOut, morseKindIn, morseKindOut]; omega) hu

/-! ### Layers -/

/-- A layer on one more band. -/
private theorem isoLayer_succ_evacStep (m : ℕ) (β : ℕ → MorseWord) :
    isoLayer (m + 1) β = isoLayer m β ++ morseShiftWord (2 * m) (β m) := by
  simp [isoLayer, List.range_succ, List.flatMap_append]

/-- A layer on `m` bands depends on the tangles of these bands only. -/
private theorem isoLayer_congr_evacStep (m : ℕ) (β γ : ℕ → MorseWord)
    (h : ∀ p < m, β p = γ p) : isoLayer m β = isoLayer m γ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [isoLayer_succ_evacStep, isoLayer_succ_evacStep, ih fun p hp ↦ h p (by omega),
      h m (by omega)]

/-- A layer of beads fits on the strands of its bands and keeps the number of strands. -/
private theorem isoLayer_fits_evacStep (N : ℕ) (β : ℕ → MorseWord)
    (hβ : ∀ p, morseFits 2 (β p) = true ∧ morseOut 2 (β p) = 2) :
    ∀ m, 2 * m ≤ N → morseFits N (isoLayer m β) = true ∧ morseOut N (isoLayer m β) = N
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
    have ih := isoLayer_fits_evacStep N β hβ m (by omega)
    have hs := morseOut_shift_iso (2 * m) 2 (N - 2 * m - 2) (β m) (hβ m).1
    rw [(hβ m).2, show 2 * m + 2 + (N - 2 * m - 2) = N by omega] at hs
    rw [isoLayer_succ_evacStep, morseFits_append, morseOut_append, ih.1, ih.2, hs.1, hs.2]
    exact ⟨rfl, rfl⟩

/-- A tangle above a layer joins the top of the slot of its band. -/
private theorem morseReach_isoLayer_top_evacStep (n₀ N : ℕ) (T : MorseWord)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) :
    ∀ (m p : ℕ) (β : ℕ → MorseWord) (u v : MorseWord),
      (∀ q, morseFits 2 (β q) = true ∧ morseOut 2 (β q) = 2) → p < m → 2 * m ≤ N →
      morseOut n₀ u = N →
      MorseReach n₀ (u ++ isoLayer m β ++ morseShiftWord (2 * p) T ++ v)
        (u ++ isoLayer m (Function.update β p (β p ++ T)) ++ v)
  | 0, p, _, _, _, _, hp, _, _ => absurd hp (Nat.not_lt_zero p)
  | m + 1, p, β, u, v, hβ, hp, hm, hu => by
    rw [isoLayer_succ_evacStep, isoLayer_succ_evacStep]
    by_cases hpm : p = m
    · subst hpm
      rw [Function.update_self, isoLayer_congr_evacStep p (Function.update β p (β p ++ T)) β
        (fun q hq ↦ Function.update_of_ne (by omega) _ _), morseShiftWord_append]
      simp only [List.append_assoc]
      exact morseReach_refl _ _
    · have hlay := isoLayer_fits_evacStep N β hβ m (by omega)
      have hs := morseOut_shift_iso (2 * m) 2 (N - 2 * m - 2) (β m) (hβ m).1
      rw [show 2 * m + 2 + (N - 2 * m - 2) = N by omega] at hs
      have h1 := morseReach_symm (morseReach_isoBead_commR n₀ (2 * p) 2 T (u ++ isoLayer m β)
        (morseShiftWord (2 * m) (β m)) v hT hTo (fun l hl ↦ by
          simp only [morseShiftWord, List.mem_map] at hl
          obtain ⟨l', -, rfl⟩ := hl
          simp only [shiftLetter]
          omega) (by rw [morseOut_append, hu, hlay.2]; exact hs.2)
        (by rw [morseOut_append, hu, hlay.2]; omega))
      have h2 := morseReach_isoLayer_top_evacStep n₀ N T hT hTo m p β u
        (morseShiftWord (2 * m) (β m) ++ v) hβ (by omega) (by omega) hu
      rw [Function.update_of_ne (Ne.symm hpm)]
      simp only [List.append_assoc] at h1 h2 ⊢
      exact morseReach_trans h1 h2

/-- A tangle below a layer joins the bottom of the slot of its band. -/
private theorem morseReach_isoLayer_bot_evacStep (n₀ N : ℕ) (T : MorseWord)
    (hT : morseFits 2 T = true) (hTo : morseOut 2 T = 2) :
    ∀ (m p : ℕ) (β : ℕ → MorseWord) (u v : MorseWord),
      (∀ q, morseFits 2 (β q) = true ∧ morseOut 2 (β q) = 2) → p < m → 2 * m ≤ N →
      morseOut n₀ u = N →
      MorseReach n₀ (u ++ morseShiftWord (2 * p) T ++ isoLayer m β ++ v)
        (u ++ isoLayer m (Function.update β p (T ++ β p)) ++ v)
  | 0, p, _, _, _, _, hp, _, _ => absurd hp (Nat.not_lt_zero p)
  | m + 1, p, β, u, v, hβ, hp, hm, hu => by
    rw [isoLayer_succ_evacStep, isoLayer_succ_evacStep]
    by_cases hpm : p = m
    · subst hpm
      rw [Function.update_self, isoLayer_congr_evacStep p (Function.update β p (T ++ β p)) β
        (fun q hq ↦ Function.update_of_ne (by omega) _ _), morseShiftWord_append]
      have hlay := isoLayer_fits_evacStep (2 * p) β hβ p le_rfl
      have h1 := morseReach_isoBead_commL n₀ (2 * p) 2 (N - 2 * p - 2) T u (isoLayer p β)
        (morseShiftWord (2 * p) (β p) ++ v) hT hTo hlay.1 (by omega)
      rw [hlay.2] at h1
      simpa only [List.append_assoc] using h1
    · have h2 := morseReach_isoLayer_bot_evacStep n₀ N T hT hTo m p β u
        (morseShiftWord (2 * m) (β m) ++ v) hβ (by omega) (by omega) hu
      rw [Function.update_of_ne (Ne.symm hpm)]
      simpa only [List.append_assoc] using h2

/-! ### A tangle moves between two slots -/

/-- An emptied slot of a layer of tangles. -/
private theorem isoLayer_valid_update_evacStep (b : ℕ → MorseWord) (p : ℕ) (w : MorseWord)
    (hb : ∀ j, morseFits 2 (b j) = true ∧ morseOut 2 (b j) = 2)
    (hw : morseFits 2 w = true ∧ morseOut 2 w = 2) (j : ℕ) :
    morseFits 2 (Function.update b p w j) = true ∧ morseOut 2 (Function.update b p w j) = 2 := by
  by_cases hj : j = p
  · subst hj
    rw [Function.update_self]
    exact hw
  · rw [Function.update_of_ne hj]
    exact hb j

/-- Refilling an emptied slot. -/
private theorem update_update_nil_evacStep (b : ℕ → MorseWord) (p : ℕ) :
    Function.update (Function.update b p []) p (Function.update b p [] p ++ b p) = b ∧
      Function.update (Function.update b p []) p (b p ++ Function.update b p [] p) = b := by
  simp

/-- The content of a slot below a word `D` moves to a slot above it. -/
private theorem morseReach_slotUp_evacStep (n₀ N N' m m' p q : ℕ) (D u v : MorseWord)
    (b c : ℕ → MorseWord) (hb : ∀ j, morseFits 2 (b j) = true ∧ morseOut 2 (b j) = 2)
    (hc : ∀ j, morseFits 2 (c j) = true ∧ morseOut 2 (c j) = 2) (hp : p < m) (hq : q < m')
    (hm : 2 * m ≤ N) (hm' : 2 * m' ≤ N') (hD : morseOut N D = N') (hu : morseOut n₀ u = N)
    (hloc : ∀ u' v' : MorseWord, morseOut n₀ u' = N →
      MorseReach n₀ (u' ++ morseShiftWord (2 * p) (b p) ++ D ++ v')
        (u' ++ D ++ morseShiftWord (2 * q) (b p) ++ v')) :
    MorseReach n₀ (u ++ isoLayer m b ++ D ++ isoLayer m' c ++ v)
      (u ++ isoLayer m (Function.update b p []) ++ D ++
        isoLayer m' (Function.update c q (b p ++ c q)) ++ v) := by
  have hb₀ := isoLayer_valid_update_evacStep b p [] hb ⟨rfl, rfl⟩
  have hl₀ := isoLayer_fits_evacStep N (Function.update b p []) hb₀ m hm
  have h1 := morseReach_symm (morseReach_isoLayer_top_evacStep n₀ N (b p) (hb p).1 (hb p).2 m p
    (Function.update b p []) u (D ++ isoLayer m' c ++ v) hb₀ hp hm hu)
  rw [(update_update_nil_evacStep b p).1] at h1
  have h2 := hloc (u ++ isoLayer m (Function.update b p [])) (isoLayer m' c ++ v)
    (by rw [morseOut_append, hu, hl₀.2])
  have h3 := morseReach_isoLayer_bot_evacStep n₀ N' (b p) (hb p).1 (hb p).2 m' q c
    (u ++ isoLayer m (Function.update b p []) ++ D) v hc hq hm'
    (by rw [morseOut_append, morseOut_append, hu, hl₀.2, hD])
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- The content of a slot above a word `D` moves to a slot below it. -/
private theorem morseReach_slotDown_evacStep (n₀ N N' m m' p q : ℕ) (D u v : MorseWord)
    (b c : ℕ → MorseWord) (hb : ∀ j, morseFits 2 (b j) = true ∧ morseOut 2 (b j) = 2)
    (hc : ∀ j, morseFits 2 (c j) = true ∧ morseOut 2 (c j) = 2) (hp : p < m') (hq : q < m)
    (hm : 2 * m ≤ N) (hm' : 2 * m' ≤ N') (hD : morseOut N D = N') (hu : morseOut n₀ u = N)
    (hloc : ∀ u' v' : MorseWord, morseOut n₀ u' = N →
      MorseReach n₀ (u' ++ D ++ morseShiftWord (2 * p) (c p) ++ v')
        (u' ++ morseShiftWord (2 * q) (c p) ++ D ++ v')) :
    MorseReach n₀ (u ++ isoLayer m b ++ D ++ isoLayer m' c ++ v)
      (u ++ isoLayer m (Function.update b q (b q ++ c p)) ++ D ++
        isoLayer m' (Function.update c p []) ++ v) := by
  have hc₀ := isoLayer_valid_update_evacStep c p [] hc ⟨rfl, rfl⟩
  have hl := isoLayer_fits_evacStep N b hb m hm
  have h1 := morseReach_symm (morseReach_isoLayer_bot_evacStep n₀ N' (c p) (hc p).1 (hc p).2 m' p
    (Function.update c p []) (u ++ isoLayer m b ++ D) v hc₀ hp hm'
    (by rw [morseOut_append, morseOut_append, hu, hl.2, hD]))
  rw [(update_update_nil_evacStep c p).2] at h1
  have h2 := hloc (u ++ isoLayer m b) (isoLayer m' (Function.update c p []) ++ v)
    (by rw [morseOut_append, hu, hl.2])
  have h3 := morseReach_isoLayer_top_evacStep n₀ N (c p) (hc p).1 (hc p).2 m q b u
    (D ++ isoLayer m' (Function.update c p []) ++ v) hb hq hm hu
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- The content of a slot leaves the top of its layer and comes back, changed, to the top of
another slot of the same layer. -/
private theorem morseReach_slotCap_evacStep (n₀ N m p q : ℕ) (T' u v : MorseWord)
    (b : ℕ → MorseWord) (hb : ∀ j, morseFits 2 (b j) = true ∧ morseOut 2 (b j) = 2)
    (hT' : morseFits 2 T' = true ∧ morseOut 2 T' = 2) (hp : p < m) (hq : q < m)
    (hm : 2 * m ≤ N) (hu : morseOut n₀ u = N)
    (hloc : ∀ u' : MorseWord, morseOut n₀ u' = N →
      MorseReach n₀ (u' ++ morseShiftWord (2 * p) (b p) ++ v)
        (u' ++ morseShiftWord (2 * q) T' ++ v)) :
    MorseReach n₀ (u ++ isoLayer m b ++ v)
      (u ++ isoLayer m (Function.update (Function.update b p []) q
        (Function.update b p [] q ++ T')) ++ v) := by
  have hb₀ := isoLayer_valid_update_evacStep b p [] hb ⟨rfl, rfl⟩
  have hl₀ := isoLayer_fits_evacStep N (Function.update b p []) hb₀ m hm
  have h1 := morseReach_symm (morseReach_isoLayer_top_evacStep n₀ N (b p) (hb p).1 (hb p).2 m p
    (Function.update b p []) u v hb₀ hp hm hu)
  rw [(update_update_nil_evacStep b p).1] at h1
  have h2 := hloc (u ++ isoLayer m (Function.update b p [])) (by rw [morseOut_append, hu, hl₀.2])
  have h3 := morseReach_isoLayer_top_evacStep n₀ N T' hT'.1 hT'.2 m q
    (Function.update b p []) u v hb₀ hq hm hu
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- The content of a slot leaves the bottom of its layer and comes back, changed, to the bottom
of another slot of the same layer. -/
private theorem morseReach_slotCup_evacStep (n₀ N m p q : ℕ) (T' u v : MorseWord)
    (c : ℕ → MorseWord) (hc : ∀ j, morseFits 2 (c j) = true ∧ morseOut 2 (c j) = 2)
    (hT' : morseFits 2 T' = true ∧ morseOut 2 T' = 2) (hp : p < m) (hq : q < m)
    (hm : 2 * m ≤ N) (hu : morseOut n₀ u = N)
    (hloc : ∀ v' : MorseWord,
      MorseReach n₀ (u ++ morseShiftWord (2 * p) (c p) ++ v')
        (u ++ morseShiftWord (2 * q) T' ++ v')) :
    MorseReach n₀ (u ++ isoLayer m c ++ v)
      (u ++ isoLayer m (Function.update (Function.update c p []) q
        (T' ++ Function.update c p [] q)) ++ v) := by
  have hc₀ := isoLayer_valid_update_evacStep c p [] hc ⟨rfl, rfl⟩
  have h1 := morseReach_symm (morseReach_isoLayer_bot_evacStep n₀ N (c p) (hc p).1 (hc p).2 m p
    (Function.update c p []) u v hc₀ hp hm hu)
  rw [(update_update_nil_evacStep c p).2] at h1
  have h2 := hloc (isoLayer m (Function.update c p []) ++ v)
  have h3 := morseReach_isoLayer_bot_evacStep n₀ N T' hT'.1 hT'.2 m q
    (Function.update c p []) u v hc₀ hq hm hu
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

/-! ### Slot words -/

/-- The slot word above its bottom layer. -/
private def isoSlotTailEvacStep (n : ℕ) : MorseWord → (ℕ → ℕ → MorseWord) → MorseWord
  | [], _ => []
  | l :: G, β => morseDoubleLetter l ++ isoSlotWord (morseLetterOut n l) G (fun k ↦ β (k + 1))

/-- A slot word is its bottom layer and the rest. -/
private theorem isoSlotWord_eq_tail_evacStep (n : ℕ) (G : MorseWord) (β : ℕ → ℕ → MorseWord) :
    isoSlotWord n G β = isoLayer n (β 0) ++ isoSlotTailEvacStep n G β := by
  cases G <;> simp [isoSlotWord, isoSlotTailEvacStep]

/-- A slot word with its two lowest layers. -/
private theorem isoSlotWord_two_evacStep (n : ℕ) (l : MorseLetter) (G : MorseWord)
    (β γ : ℕ → ℕ → MorseWord) (h : ∀ k, γ (k + 2) = β (k + 2)) :
    isoSlotWord n (l :: G) γ = isoLayer n (γ 0) ++ morseDoubleLetter l ++
      (isoLayer (morseLetterOut n l) (γ 1) ++
        isoSlotTailEvacStep (morseLetterOut n l) G (fun k ↦ β (k + 1))) := by
  have h1 : isoSlotWord n (l :: G) γ = isoLayer n (γ 0) ++ morseDoubleLetter l ++
      isoSlotWord (morseLetterOut n l) G (fun k ↦ γ (k + 1)) := rfl
  rw [h1, isoSlotWord_eq_tail_evacStep]
  congr 2
  cases G with
  | nil => rfl
  | cons l' G' =>
    simp only [isoSlotTailEvacStep]
    congr 2
    funext k
    exact h k

/-- The tangle in a slot. -/
private theorem isoSlotValid_update_evacStep (β : ℕ → ℕ → MorseWord) (k p : ℕ) (w : MorseWord)
    (hβ : IsoSlotValid β) (hw : morseFits 2 w = true ∧ morseOut 2 w = 2) :
    IsoSlotValid (Function.update β k (Function.update (β k) p w)) := by
  intro j q
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self]
    exact isoLayer_valid_update_evacStep (β j) p w (hβ j) hw q
  · rw [Function.update_of_ne hj]
    exact hβ j q

/-- The moved slots still hold tangles from two strands to two strands. -/
theorem isoSlotValid_isoSnowStep (β : ℕ → ℕ → MorseWord) (x y : ℕ × ℕ × Bool)
    (hβ : IsoSlotValid β) : IsoSlotValid (isoSnowStep β x y) := by
  obtain ⟨k, p, d⟩ := x
  obtain ⟨k', p', d'⟩ := y
  have hβ₀ := isoSlotValid_update_evacStep β k p [] hβ ⟨rfl, rfl⟩
  have happ : ∀ a b : MorseWord, morseFits 2 a = true ∧ morseOut 2 a = 2 →
      morseFits 2 b = true ∧ morseOut 2 b = 2 →
      morseFits 2 (a ++ b) = true ∧ morseOut 2 (a ++ b) = 2 := fun a b ha hb ↦ by
    rw [morseFits_append, morseOut_append, ha.1, ha.2, hb.1, hb.2]
    exact ⟨rfl, rfl⟩
  have hrot : morseFits 2 (isoRot 2 (β k p)) = true ∧ morseOut 2 (isoRot 2 (β k p)) = 2 := by
    have h := isoRot_fits (β k p) 2 (hβ k p).1
    rwa [(hβ k p).2] at h
  cases d <;> cases d' <;>
    exact isoSlotValid_update_evacStep _ k' p' _ hβ₀ (by
      first
      | exact happ _ _ (hβ k p) (hβ₀ k' p')
      | exact happ _ _ (hβ₀ k' p') (hβ k p)
      | exact happ _ _ hrot (hβ₀ k' p')
      | exact happ _ _ (hβ₀ k' p') hrot)

/-! ### The step at the lowest letter -/

/-- The step upwards from the bottom level: the band continues, or turns at a cap. -/
private theorem isoTraceStep_up_cases_evacStep (l : MorseLetter) (G : MorseWord) (p : ℕ)
    (y : ℕ × ℕ × Bool) (hy : isoTraceStep (l :: G) (0, p, true) = some y) :
    (∃ q, y = (1, q, true) ∧ IsoPassEvacStep l p q) ∨
      ∃ i, l = (MorseKind.cap, i) ∧
        ((p = i ∧ y = (0, i + 1, false)) ∨ (p = i + 1 ∧ y = (0, i, false))) := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cross s =>
    simp only [isoTraceStep, List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    refine Or.inl ⟨_, rfl, ?_⟩
    simp only [IsoPassEvacStep]
    split_ifs <;> omega
  | cup =>
    simp only [isoTraceStep, List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    refine Or.inl ⟨_, rfl, ?_⟩
    simp only [IsoPassEvacStep]
    split_ifs <;> omega
  | cap =>
    simp only [isoTraceStep, List.getElem?_cons_zero] at hy
    split_ifs at hy with h1 h2
    · exact Or.inr ⟨i, rfl, Or.inl ⟨h1, (Option.some.inj hy).symm⟩⟩
    · exact Or.inr ⟨i, rfl, Or.inr ⟨h2, (Option.some.inj hy).symm⟩⟩
    all_goals
      rw [← Option.some.inj hy]
      refine Or.inl ⟨_, rfl, ?_⟩
      simp only [IsoPassEvacStep]
      first | omega | exact Or.inl ⟨by omega, trivial⟩

/-- The step downwards to the bottom level: the band continues, or turns at a cup. -/
private theorem isoTraceStep_down_cases_evacStep (l : MorseLetter) (G : MorseWord) (p : ℕ)
    (y : ℕ × ℕ × Bool) (hy : isoTraceStep (l :: G) (1, p, false) = some y) :
    (∃ q, y = (0, q, false) ∧ IsoPassEvacStep l q p) ∨
      ∃ i, l = (MorseKind.cup, i) ∧
        ((p = i ∧ y = (1, i + 1, true)) ∨ (p = i + 1 ∧ y = (1, i, true))) := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cross s =>
    simp only [isoTraceStep, List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    refine Or.inl ⟨_, rfl, ?_⟩
    simp only [IsoPassEvacStep]
    split_ifs <;> omega
  | cap =>
    simp only [isoTraceStep, List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    refine Or.inl ⟨_, rfl, ?_⟩
    simp only [IsoPassEvacStep]
    split_ifs <;> omega
  | cup =>
    simp only [isoTraceStep, List.getElem?_cons_zero] at hy
    split_ifs at hy with h1 h2
    · exact Or.inr ⟨i, rfl, Or.inl ⟨h1, (Option.some.inj hy).symm⟩⟩
    · exact Or.inr ⟨i, rfl, Or.inr ⟨h2, (Option.some.inj hy).symm⟩⟩
    all_goals
      rw [← Option.some.inj hy]
      refine Or.inl ⟨_, rfl, ?_⟩
      simp only [IsoPassEvacStep]
      first | omega | exact Or.inl ⟨by omega, trivial⟩

/-- One step of the snowball upwards from the bottom level. -/
private theorem morseReach_isoSnowStep_up_evacStep (n₀ n e p : ℕ) (l : MorseLetter)
    (G u v : MorseWord) (β : ℕ → ℕ → MorseWord) (y : ℕ × ℕ × Bool)
    (hl : l.2 + morseKindIn l.1 ≤ n) (hβ : IsoSlotValid β) (hu : morseOut n₀ u = 2 * n + e)
    (hp : p < n) (hy : isoTraceStep (l :: G) (0, p, true) = some y) :
    MorseReach n₀ (u ++ isoSlotWord n (l :: G) β ++ v)
      (u ++ isoSlotWord n (l :: G) (isoSnowStep β (0, p, true) y) ++ v) := by
  have hd := morseDoubleLetter_fits_evacStep n e l hl
  rcases isoTraceStep_up_cases_evacStep l G p y hy with ⟨q, rfl, hpq⟩ | ⟨i, rfl, hc⟩
  · have hq := (isoPass_lt_evacStep hpq hl).1 hp
    rw [isoSlotWord_two_evacStep n l G β β (fun _ ↦ rfl),
      isoSlotWord_two_evacStep n l G β (isoSnowStep β (0, p, true) (1, q, true))
        (fun k ↦ by simp [isoSnowStep])]
    have h0 : isoSnowStep β (0, p, true) (1, q, true) 0 = Function.update (β 0) p [] := by
      simp [isoSnowStep]
    have h1 : isoSnowStep β (0, p, true) (1, q, true) 1 =
        Function.update (β 1) q (β 0 p ++ β 1 q) := by
      simp [isoSnowStep]
    rw [h0, h1]
    have h := morseReach_slotUp_evacStep n₀ (2 * n + e) (2 * morseLetterOut n l + e) n
      (morseLetterOut n l) p q (morseDoubleLetter l) u
      (isoSlotTailEvacStep (morseLetterOut n l) G (fun k ↦ β (k + 1)) ++ v) (β 0) (β 1) (hβ 0)
      (hβ 1) hp hq (by omega) (by omega) hd.2 hu (fun u' v' hu' ↦
        morseReach_isoPass_evacStep n₀ n e p q l (β 0 p) u' v' (hβ 0 p).1 (hβ 0 p).2 hl hp hpq
          hu')
    simpa only [List.append_assoc] using h
  · have hT := hβ 0 p
    have hR : morseFits 2 (isoRot 2 (β 0 p)) = true ∧ morseOut 2 (isoRot 2 (β 0 p)) = 2 := by
      have h := isoRot_fits (β 0 p) 2 hT.1
      rwa [hT.2] at h
    have hRR : isoRot 2 (isoRot 2 (β 0 p)) = β 0 p := by
      have h := isoRot_isoRot 2 (β 0 p) hT.1
      rwa [hT.2] at h
    have hD : morseDouble [isoN i] = morseDoubleLetter (MorseKind.cap, i) := by
      simp [morseDouble, isoN]
    simp only [morseKindIn] at hl
    obtain ⟨q, hq, rfl, hloc⟩ : ∃ q, q < n ∧ y = (0, q, false) ∧
        ∀ u' v' : MorseWord, morseOut n₀ u' = 2 * n + e →
          MorseReach n₀ (u' ++ morseShiftWord (2 * p) (β 0 p) ++
            (morseDoubleLetter (MorseKind.cap, i) ++ v'))
            (u' ++ morseShiftWord (2 * q) (isoRot 2 (β 0 p)) ++
              (morseDoubleLetter (MorseKind.cap, i) ++ v')) := by
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨p + 1, by omega, rfl, fun u' v' hu' ↦ ?_⟩
        have h := morseReach_isoBead_cap n₀ p (β 0 p) u' v' hT.1 hT.2 (by rw [hu']; omega)
        rw [hD] at h
        rw [show 2 * (p + 1) = 2 * p + 2 by ring]
        simpa only [List.append_assoc] using h
      · refine ⟨i, by omega, rfl, fun u' v' hu' ↦ ?_⟩
        have h := morseReach_symm (morseReach_isoBead_cap n₀ i (isoRot 2 (β 0 (i + 1))) u' v'
          hR.1 hR.2 (by rw [hu']; omega))
        rw [hD, hRR] at h
        rw [show 2 * (i + 1) = 2 * i + 2 by ring]
        simpa only [List.append_assoc] using h
    rw [isoSlotWord_two_evacStep n _ G β β (fun _ ↦ rfl),
      isoSlotWord_two_evacStep n _ G β (isoSnowStep β (0, p, true) (0, q, false))
        (fun k ↦ by simp [isoSnowStep])]
    have h0 : isoSnowStep β (0, p, true) (0, q, false) 0 =
        Function.update (Function.update (β 0) p []) q
          (Function.update (β 0) p [] q ++ isoRot 2 (β 0 p)) := by
      simp [isoSnowStep]
    have h1 : isoSnowStep β (0, p, true) (0, q, false) 1 = β 1 := by
      simp [isoSnowStep]
    rw [h0, h1]
    have h := morseReach_slotCap_evacStep n₀ (2 * n + e) n p q (isoRot 2 (β 0 p)) u
      (morseDoubleLetter (MorseKind.cap, i) ++ (isoLayer (morseLetterOut n (MorseKind.cap, i))
        (β 1) ++ isoSlotTailEvacStep (morseLetterOut n (MorseKind.cap, i)) G
          (fun k ↦ β (k + 1))) ++ v) (β 0) (hβ 0) hR hp hq (by omega) hu
      (fun u' hu' ↦ by simpa only [List.append_assoc] using hloc u' _ hu')
    simpa only [List.append_assoc] using h

/-- One step of the snowball downwards to the bottom level. -/
private theorem morseReach_isoSnowStep_down_evacStep (n₀ n e p : ℕ) (l : MorseLetter)
    (G u v : MorseWord) (β : ℕ → ℕ → MorseWord) (y : ℕ × ℕ × Bool)
    (hl : l.2 + morseKindIn l.1 ≤ n) (hβ : IsoSlotValid β) (hu : morseOut n₀ u = 2 * n + e)
    (hp : p < morseLetterOut n l) (hy : isoTraceStep (l :: G) (1, p, false) = some y) :
    MorseReach n₀ (u ++ isoSlotWord n (l :: G) β ++ v)
      (u ++ isoSlotWord n (l :: G) (isoSnowStep β (1, p, false) y) ++ v) := by
  have hd := morseDoubleLetter_fits_evacStep n e l hl
  rcases isoTraceStep_down_cases_evacStep l G p y hy with ⟨q, rfl, hpq⟩ | ⟨i, rfl, hc⟩
  · have hq := (isoPass_lt_evacStep hpq hl).2 hp
    rw [isoSlotWord_two_evacStep n l G β β (fun _ ↦ rfl),
      isoSlotWord_two_evacStep n l G β (isoSnowStep β (1, p, false) (0, q, false))
        (fun k ↦ by simp [isoSnowStep])]
    have h0 : isoSnowStep β (1, p, false) (0, q, false) 0 =
        Function.update (β 0) q (β 0 q ++ β 1 p) := by
      simp [isoSnowStep]
    have h1 : isoSnowStep β (1, p, false) (0, q, false) 1 = Function.update (β 1) p [] := by
      simp [isoSnowStep]
    rw [h0, h1]
    have h := morseReach_slotDown_evacStep n₀ (2 * n + e) (2 * morseLetterOut n l + e) n
      (morseLetterOut n l) p q (morseDoubleLetter l) u
      (isoSlotTailEvacStep (morseLetterOut n l) G (fun k ↦ β (k + 1)) ++ v) (β 0) (β 1) (hβ 0)
      (hβ 1) hp hq (by omega) (by omega) hd.2 hu (fun u' v' hu' ↦ morseReach_symm
        (morseReach_isoPass_evacStep n₀ n e q p l (β 1 p) u' v' (hβ 1 p).1 (hβ 1 p).2 hl hq hpq
          hu'))
    simpa only [List.append_assoc] using h
  · have hT := hβ 1 p
    have hR : morseFits 2 (isoRot 2 (β 1 p)) = true ∧ morseOut 2 (isoRot 2 (β 1 p)) = 2 := by
      have h := isoRot_fits (β 1 p) 2 hT.1
      rwa [hT.2] at h
    have hRR : isoRot 2 (isoRot 2 (β 1 p)) = β 1 p := by
      have h := isoRot_isoRot 2 (β 1 p) hT.1
      rwa [hT.2] at h
    have hD : morseDouble [isoU i] = morseDoubleLetter (MorseKind.cup, i) := by
      simp [morseDouble, isoU]
    simp only [morseKindIn] at hl
    simp only [morseLetterOut, morseKindIn, morseKindOut] at hp
    have hl₀ := isoLayer_fits_evacStep (2 * n + e) (β 0) (hβ 0) n (by omega)
    have hu₀ : morseOut n₀ (u ++ isoLayer n (β 0)) = 2 * n + e := by
      rw [morseOut_append, hu, hl₀.2]
    obtain ⟨q, hq, rfl, hloc⟩ : ∃ q, q < n + 2 ∧ y = (1, q, true) ∧
        ∀ v' : MorseWord,
          MorseReach n₀ (u ++ isoLayer n (β 0) ++ morseDoubleLetter (MorseKind.cup, i) ++
            morseShiftWord (2 * p) (β 1 p) ++ v')
            (u ++ isoLayer n (β 0) ++ morseDoubleLetter (MorseKind.cup, i) ++
              morseShiftWord (2 * q) (isoRot 2 (β 1 p)) ++ v') := by
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨p + 1, by omega, rfl, fun v' ↦ ?_⟩
        have h := morseReach_isoBead_cup n₀ p (β 1 p) (u ++ isoLayer n (β 0)) v' hT.1 hT.2
          (by rw [hu₀]; omega)
        rw [hD] at h
        rw [show 2 * (p + 1) = 2 * p + 2 by ring]
        exact h
      · refine ⟨i, by omega, rfl, fun v' ↦ ?_⟩
        have h := morseReach_symm (morseReach_isoBead_cup n₀ i (isoRot 2 (β 1 (i + 1)))
          (u ++ isoLayer n (β 0)) v' hR.1 hR.2 (by rw [hu₀]; omega))
        rw [hD, hRR] at h
        rw [show 2 * (i + 1) = 2 * i + 2 by ring]
        exact h
    rw [isoSlotWord_two_evacStep n _ G β β (fun _ ↦ rfl),
      isoSlotWord_two_evacStep n _ G β (isoSnowStep β (1, p, false) (1, q, true))
        (fun k ↦ by simp [isoSnowStep])]
    have h0 : isoSnowStep β (1, p, false) (1, q, true) 0 = β 0 := by
      simp [isoSnowStep]
    have h1 : isoSnowStep β (1, p, false) (1, q, true) 1 =
        Function.update (Function.update (β 1) p []) q
          (isoRot 2 (β 1 p) ++ Function.update (β 1) p [] q) := by
      simp [isoSnowStep]
    rw [h0, h1]
    have h := morseReach_slotCup_evacStep n₀ (2 * (n + 2) + e) (n + 2) p q (isoRot 2 (β 1 p))
      (u ++ isoLayer n (β 0) ++ morseDoubleLetter (MorseKind.cup, i))
      (isoSlotTailEvacStep (n + 2) G (fun k ↦ β (k + 1)) ++ v) (β 1) (hβ 1) hR hp hq (by omega)
      (by
        rw [morseOut_append, hu₀, hd.2]
        simp only [morseLetterOut, morseKindIn, morseKindOut]
        omega) hloc
    have hn : morseLetterOut n (MorseKind.cup, i) = n + 2 := by
      simp only [morseLetterOut, morseKindIn, morseKindOut]
      omega
    rw [hn]
    simpa only [List.append_assoc] using h

/-! ### The step at any level -/

/-- The snowball step above the bottom level is the step of the word without its first letter. -/
private theorem isoSnowStep_succ_evacStep (β : ℕ → ℕ → MorseWord) (k p k' p' : ℕ)
    (d d' : Bool) :
    isoSnowStep β (k + 1, p, d) (k' + 1, p', d') 0 = β 0 ∧
      (fun j ↦ isoSnowStep β (k + 1, p, d) (k' + 1, p', d') (j + 1)) =
        isoSnowStep (fun j ↦ β (j + 1)) (k, p, d) (k', p', d') := by
  refine ⟨by simp [isoSnowStep], ?_⟩
  funext j
  cases d <;> cases d' <;> simp [isoSnowStep, Function.update_apply]

/-- The step upwards above the first letter. -/
private theorem isoTraceStep_cons_up_evacStep (l : MorseLetter) (G : MorseWord) (k p : ℕ)
    (y : ℕ × ℕ × Bool) (hy : isoTraceStep (l :: G) (k + 1, p, true) = some y) :
    ∃ y', isoTraceStep G (k, p, true) = some y' ∧ y = (y'.1 + 1, y'.2) := by
  simp only [isoTraceStep, List.getElem?_cons_succ] at hy ⊢
  cases hl : G[k]? with
  | none => simp [hl] at hy
  | some l' =>
    obtain ⟨kd, i⟩ := l'
    rw [hl] at hy
    cases kd with
    | cross s => exact ⟨_, rfl, (Option.some.inj hy).symm⟩
    | cup => exact ⟨_, rfl, (Option.some.inj hy).symm⟩
    | cap =>
      simp only at hy ⊢
      split_ifs at hy ⊢ <;> exact ⟨_, rfl, (Option.some.inj hy).symm⟩

/-- The step downwards above the first letter. -/
private theorem isoTraceStep_cons_down_evacStep (l : MorseLetter) (G : MorseWord) (k p : ℕ)
    (y : ℕ × ℕ × Bool) (hy : isoTraceStep (l :: G) (k + 2, p, false) = some y) :
    ∃ y', isoTraceStep G (k + 1, p, false) = some y' ∧ y = (y'.1 + 1, y'.2) := by
  simp only [isoTraceStep, List.getElem?_cons_succ] at hy ⊢
  cases hl : G[k]? with
  | none => simp [hl] at hy
  | some l' =>
    obtain ⟨kd, i⟩ := l'
    rw [hl] at hy
    cases kd with
    | cross s => exact ⟨_, rfl, (Option.some.inj hy).symm⟩
    | cap => exact ⟨_, rfl, (Option.some.inj hy).symm⟩
    | cup =>
      simp only at hy ⊢
      split_ifs at hy ⊢ <;> exact ⟨_, rfl, (Option.some.inj hy).symm⟩

/-- The snowball step above the first letter of a word. -/
private theorem morseReach_isoSnowStep_cons_evacStep (n₀ n k p k' p' : ℕ) (d d' : Bool)
    (l : MorseLetter) (G u v : MorseWord) (β : ℕ → ℕ → MorseWord)
    (h : MorseReach n₀
      (u ++ isoLayer n (β 0) ++ morseDoubleLetter l ++
        isoSlotWord (morseLetterOut n l) G (fun j ↦ β (j + 1)) ++ v)
      (u ++ isoLayer n (β 0) ++ morseDoubleLetter l ++
        isoSlotWord (morseLetterOut n l) G
          (isoSnowStep (fun j ↦ β (j + 1)) (k, p, d) (k', p', d')) ++ v)) :
    MorseReach n₀ (u ++ isoSlotWord n (l :: G) β ++ v)
      (u ++ isoSlotWord n (l :: G) (isoSnowStep β (k + 1, p, d) (k' + 1, p', d')) ++ v) := by
  have hs := isoSnowStep_succ_evacStep β k p k' p' d d'
  have h1 : ∀ γ : ℕ → ℕ → MorseWord, isoSlotWord n (l :: G) γ =
      isoLayer n (γ 0) ++ morseDoubleLetter l ++
        isoSlotWord (morseLetterOut n l) G (fun k ↦ γ (k + 1)) := fun _ ↦ rfl
  rw [h1, h1, hs.1, hs.2]
  simpa only [List.append_assoc] using h

/-- One step of the snowball, for a word read from `n` strands. -/
private theorem morseReach_isoSnowStep_gen_evacStep (n₀ e : ℕ) (v : MorseWord) :
    ∀ (G : MorseWord) (n : ℕ) (u : MorseWord) (β : ℕ → ℕ → MorseWord) (x y : ℕ × ℕ × Bool),
      morseFits n G = true → IsoSlotValid β → morseOut n₀ u = 2 * n + e →
      x.2.1 < morseOut n (G.take x.1) → isoTraceStep G x = some y →
      MorseReach n₀ (u ++ isoSlotWord n G β ++ v)
        (u ++ isoSlotWord n G (isoSnowStep β x y) ++ v)
  | [], _, _, _, (k, p, true), _, _, _, _, _, hy => by simp [isoTraceStep] at hy
  | [], _, _, _, (0, p, false), _, _, _, _, _, hy => by simp [isoTraceStep] at hy
  | [], _, _, _, (k + 1, p, false), _, _, _, _, _, hy => by simp [isoTraceStep] at hy
  | l :: G, _, _, _, (0, p, false), _, _, _, _, _, hy => by simp [isoTraceStep] at hy
  | l :: G, n, u, β, (0, p, true), y, hG, hβ, hu, hx, hy => by
    rw [morseFits_cons] at hG
    exact morseReach_isoSnowStep_up_evacStep n₀ n e p l G u v β y hG.1 hβ hu hx hy
  | l :: G, n, u, β, (1, p, false), y, hG, hβ, hu, hx, hy => by
    rw [morseFits_cons] at hG
    exact morseReach_isoSnowStep_down_evacStep n₀ n e p l G u v β y hG.1 hβ hu hx hy
  | l :: G, n, u, β, (k + 1, p, true), y, hG, hβ, hu, hx, hy => by
    rw [morseFits_cons] at hG
    obtain ⟨⟨k', p', d'⟩, hy', rfl⟩ := isoTraceStep_cons_up_evacStep l G k p y hy
    have hl₀ := isoLayer_fits_evacStep (2 * n + e) (β 0) (hβ 0) n (by omega)
    have hd := morseDoubleLetter_fits_evacStep n e l hG.1
    exact morseReach_isoSnowStep_cons_evacStep n₀ n k p k' p' true d' l G u v β
      (morseReach_isoSnowStep_gen_evacStep n₀ e v G (morseLetterOut n l)
        (u ++ isoLayer n (β 0) ++ morseDoubleLetter l) (fun j ↦ β (j + 1)) (k, p, true)
        (k', p', d') hG.2 (fun j q ↦ hβ (j + 1) q)
        (by rw [morseOut_append, morseOut_append, hu, hl₀.2, hd.2]) hx hy')
  | l :: G, n, u, β, (k + 2, p, false), y, hG, hβ, hu, hx, hy => by
    rw [morseFits_cons] at hG
    obtain ⟨⟨k', p', d'⟩, hy', rfl⟩ := isoTraceStep_cons_down_evacStep l G k p y hy
    have hl₀ := isoLayer_fits_evacStep (2 * n + e) (β 0) (hβ 0) n (by omega)
    have hd := morseDoubleLetter_fits_evacStep n e l hG.1
    exact morseReach_isoSnowStep_cons_evacStep n₀ n (k + 1) p k' p' false d' l G u v β
      (morseReach_isoSnowStep_gen_evacStep n₀ e v G (morseLetterOut n l)
        (u ++ isoLayer n (β 0) ++ morseDoubleLetter l) (fun j ↦ β (j + 1)) (k + 1, p, false)
        (k', p', d') hG.2 (fun j q ↦ hβ (j + 1) q)
        (by rw [morseOut_append, morseOut_append, hu, hl₀.2, hd.2]) hx hy')

/-- One step of the snowball along the knot. -/
theorem morseReach_isoSnowStep (G u v : MorseWord) (β : ℕ → ℕ → MorseWord) (n₀ e : ℕ)
    (x y : ℕ × ℕ × Bool) (hG : morseFits 1 G = true) (hβ : IsoSlotValid β)
    (hu : morseOut n₀ u = 2 + e)
    (hx : x.1 ≤ G.length ∧ x.2.1 < morseOut 1 (G.take x.1))
    (hy : isoTraceStep G x = some y) :
    MorseReach n₀ (u ++ isoSlotWord 1 G β ++ v)
      (u ++ isoSlotWord 1 G (isoSnowStep β x y) ++ v) :=
  morseReach_isoSnowStep_gen_evacStep n₀ e v G 1 u β x y hG hβ (by rw [hu]) hx.2 hy

end AJConjecture
