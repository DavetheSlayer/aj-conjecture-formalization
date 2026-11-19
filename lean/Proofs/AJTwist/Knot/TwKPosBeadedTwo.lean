import Mathlib
import AJTwist.Knot.TwKPosWords
import AJTwist.Knot.TwKPosEvacDefs

/-!
# The core and the doubled core with beads for the companion `T(2, s)`

* `twkCore2_eq`, `morseFits_twkCore2`, `isoConnected_twkCore2`: the core `twkCore2 s` is the long
  closure of the torus braid `σ₀^s` on two strands; for odd `s` it is one long arc: the trace
  goes up through the `s` crossings (ending on the right strand), turns at the cap, comes down
  the closing strand, turns at the cup and goes up through the crossings again.
* `isoBeaded_twkQ2Body`: `twkQ2Body s σ` is `morseDouble (twkCore2 s)` with `s` blocks `A1` (the
  `s - 1` bottom blocks and the block of the top-right climb), `s` positive left curls (round
  `0`, the `s - 2` rounds, the top curl) and the clasp on the band of the closing strand.

Checked outside Lean (`SCR/KP/tools/evac_test.py`): the word `twkQ2Body s σ` is letter for letter
the slot word of these beads for `s = 3, 5`; the trace of `twkCore2 3` was evaluated in Lean
(`SCR/KP/leancheck/EvalEvac.lean`).
-/

namespace AJConjecture

/-- The core for `r = 2` is the long closure of the torus braid `σ₀^s`. -/
theorem twkCore2_eq (s : ℕ) : twkCore2 s = morseLongClosure 2 (torusPairWord 2 s) := by
  have h : morseOfBraid (torusPairWord 2 s) = List.replicate s (isoX true 0) := by
    simp only [torusPairWord, morseOfBraid]
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append, ih, List.replicate_succ]
      rfl
  rw [twkCore2, morseLongClosure, h]
  rfl

/-- A run of crossings of the first two strands fits and keeps the number of strands. -/
private theorem morseFits_replicate_twKBeadedTwo (n : ℕ) (hn : 2 ≤ n) (s : ℕ) :
    morseFits n (List.replicate s (isoX true 0)) = true ∧
      morseOut n (List.replicate s (isoX true 0)) = n := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ s ih =>
    rw [List.replicate_succ, morseFits_cons]
    simp only [morseOut, morseLetterOut, isoX, morseKindIn, morseKindOut, Nat.add_sub_cancel]
    exact ⟨⟨by omega, ih.1⟩, ih.2⟩

/-- The core for `r = 2` is a tangle from one strand to one strand. -/
theorem morseFits_twkCore2 (s : ℕ) :
    morseFits 1 (twkCore2 s) = true ∧ morseOut 1 (twkCore2 s) = 1 := by
  have h := morseFits_replicate_twKBeadedTwo 3 (by omega) s
  simp only [twkCore2, morseFits_append, morseOut_append,
    show morseOut 1 [isoU 1] = 3 from rfl, h.1, h.2]
  exact ⟨rfl, rfl⟩

/-! ### The trace of the core -/

/-- `n` steps along the knot from a segment; `none` if an end is met first. -/
private def isoIterTwo (w : MorseWord) : ℕ → ℕ × ℕ × Bool → Option (ℕ × ℕ × Bool)
  | 0, x => some x
  | n + 1, x => (isoTraceStep w x).bind (isoIterTwo w n)

/-- Walks compose. -/
private theorem isoIterTwo_trans {w : MorseWord} {a b : ℕ} {x y z : ℕ × ℕ × Bool}
    (h1 : isoIterTwo w a x = some y) (h2 : isoIterTwo w b y = some z) :
    isoIterTwo w (a + b) x = some z := by
  induction a generalizing x with
  | zero =>
    simp only [isoIterTwo, Option.some.injEq] at h1
    subst h1
    simpa using h2
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, isoIterTwo]
    rw [isoIterTwo] at h1
    cases hx : isoTraceStep w x with
    | none => rw [hx] at h1; simp at h1
    | some x1 =>
      rw [hx, Option.bind_some] at h1
      rw [Option.bind_some]
      exact ih h1

/-- One step is a walk of length one. -/
private theorem isoIterTwo_one {w : MorseWord} {x y : ℕ × ℕ × Bool}
    (h : isoTraceStep w x = some y) : isoIterTwo w 1 x = some y := by
  simp [isoIterTwo, h]

/-- A walk followed by one step. -/
private theorem isoIterTwo_succ {w : MorseWord} {a : ℕ} {x y z : ℕ × ℕ × Bool}
    (h1 : isoIterTwo w a x = some y) (h2 : isoTraceStep w y = some z) :
    isoIterTwo w (a + 1) x = some z :=
  isoIterTwo_trans h1 (isoIterTwo_one h2)

/-- A segment reached within the budget is on the trace. -/
private theorem mem_isoTrace_of_isoIterTwo (w : MorseWord) :
    ∀ (n fuel : ℕ) (x y : ℕ × ℕ × Bool), isoIterTwo w n x = some y → n ≤ fuel →
      y ∈ isoTrace w fuel x
  | 0, fuel, x, y, h, _ => by
    simp only [isoIterTwo, Option.some.injEq] at h
    subst h
    cases fuel with
    | zero => simp [isoTrace]
    | succ f =>
      unfold isoTrace
      cases isoTraceStep w x <;> simp
  | n + 1, fuel, x, y, h, hn => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [isoIterTwo] at h
    cases hx : isoTraceStep w x with
    | none => rw [hx] at h; simp at h
    | some x1 =>
      rw [hx, Option.bind_some] at h
      simp only [isoTrace, hx]
      exact List.mem_cons_of_mem _ (mem_isoTrace_of_isoIterTwo w n f x1 y h (by omega))

/-- The first letter of the core. -/
private theorem twkCore2_getElem?_zero (s : ℕ) : (twkCore2 s)[0]? = some (MorseKind.cup, 1) := rfl

/-- The crossings of the core. -/
private theorem twkCore2_getElem?_cross (s k : ℕ) (hk : k < s) :
    (twkCore2 s)[k + 1]? = some (MorseKind.cross true, 0) := by
  rw [twkCore2, List.append_assoc, List.singleton_append, List.getElem?_cons_succ,
    List.getElem?_append_left (by simpa using hk), List.getElem?_replicate, ite_eq_left hk]
  rfl

/-- The last letter of the core. -/
private theorem twkCore2_getElem?_cap (s : ℕ) :
    (twkCore2 s)[s + 1]? = some (MorseKind.cap, 1) := by
  rw [twkCore2, List.append_assoc, List.singleton_append, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp)]
  simp [isoN]

/-- Going up through the crossings on the first two strands. -/
private theorem isoIterTwo_up (s p : ℕ) (hp : p ≤ 1) :
    ∀ j, j ≤ s → isoIterTwo (twkCore2 s) j (1, p, true) = some (1 + j, (p + j) % 2, true)
  | 0, _ => by
    rw [isoIterTwo, Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  | j + 1, hj => by
    have ih := isoIterTwo_up s p hp j (by omega)
    refine isoIterTwo_succ ih ?_
    have h2 := Nat.mod_two_eq_zero_or_one (p + j)
    rw [show 1 + j = j + 1 by omega]
    simp only [isoTraceStep, twkCore2_getElem?_cross s j (by omega), Option.some.injEq,
      Prod.mk.injEq, and_true]
    constructor
    · omega
    · split_ifs <;> omega

/-- Going down the closing strand. -/
private theorem isoIterTwo_down (s : ℕ) :
    ∀ j, j ≤ s → isoIterTwo (twkCore2 s) j (s + 1, 2, false) = some (s + 1 - j, 2, false)
  | 0, _ => rfl
  | j + 1, hj => by
    refine (isoIterTwo_succ (isoIterTwo_down s j (by omega)) ?_)
    rw [show s + 1 - j = (s - j - 1) + 1 + 1 by omega]
    simp [isoTraceStep, twkCore2_getElem?_cross s (s - j - 1) (by omega)]
    omega

/-- The number of strands of the core at each level. -/
private theorem morseOut_take_twkCore2 (s k : ℕ) (hk : k ≤ s + 2) :
    morseOut 1 ((twkCore2 s).take k) = if k = 0 ∨ k = s + 2 then 1 else 3 := by
  have hlen : (twkCore2 s).length = s + 2 := by simp [twkCore2]
  by_cases h0 : k = 0
  · subst h0
    rfl
  by_cases h1 : k = s + 2
  · rw [ite_eq_left (Or.inr h1), h1, ← hlen, List.take_length]
    exact (morseFits_twkCore2 s).2
  · rw [ite_eq_right (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [twkCore2, List.append_assoc, List.singleton_append, List.take_succ_cons,
      List.take_append_of_le_length (by simp; omega), List.take_replicate]
    exact (morseFits_replicate_twKBeadedTwo 3 (by omega) _).2

/-- The closure of an odd power of `σ₀` on two strands is one long arc. -/
theorem isoConnected_twkCore2 {s : ℕ} (hs : Odd s) : IsoConnected (twkCore2 s) := by
  obtain ⟨m, rfl⟩ := hs
  have hlen : (twkCore2 (2 * m + 1)).length = 2 * m + 3 := by simp [twkCore2]
  have hA : isoIterTwo (twkCore2 (2 * m + 1)) 1 (0, 0, true) = some (1, 0, true) :=
    isoIterTwo_one (by simp [isoTraceStep, twkCore2_getElem?_zero])
  have hB : ∀ j, j ≤ 2 * m + 1 →
      isoIterTwo (twkCore2 (2 * m + 1)) (1 + j) (0, 0, true) = some (1 + j, j % 2, true) :=
    fun j hj ↦ by
      simpa using isoIterTwo_trans hA (isoIterTwo_up (2 * m + 1) 0 (by omega) j hj)
  have hC : isoIterTwo (twkCore2 (2 * m + 1)) (2 * m + 3) (0, 0, true) =
      some (2 * m + 2, 2, false) := by
    have := hB (2 * m + 1) le_rfl
    rw [show (2 * m + 1) % 2 = 1 by omega, show 1 + (2 * m + 1) = 2 * m + 1 + 1 by omega] at this
    exact isoIterTwo_succ this (by simp [isoTraceStep, twkCore2_getElem?_cap])
  have hD : ∀ j, j ≤ 2 * m + 1 →
      isoIterTwo (twkCore2 (2 * m + 1)) (2 * m + 3 + j) (0, 0, true) =
        some (2 * m + 2 - j, 2, false) :=
    fun j hj ↦ isoIterTwo_trans hC (isoIterTwo_down (2 * m + 1) j hj)
  have hE : isoIterTwo (twkCore2 (2 * m + 1)) (4 * m + 5) (0, 0, true) = some (1, 1, true) := by
    have := hD (2 * m + 1) le_rfl
    rw [show 2 * m + 2 - (2 * m + 1) = 0 + 1 by omega,
      show 2 * m + 3 + (2 * m + 1) = 4 * m + 4 by omega] at this
    exact isoIterTwo_succ this (by simp [isoTraceStep, twkCore2_getElem?_zero])
  have hF : ∀ j, j ≤ 2 * m + 1 →
      isoIterTwo (twkCore2 (2 * m + 1)) (4 * m + 5 + j) (0, 0, true) =
        some (1 + j, (1 + j) % 2, true) :=
    fun j hj ↦ isoIterTwo_trans hE (isoIterTwo_up (2 * m + 1) 1 le_rfl j hj)
  have hG : isoIterTwo (twkCore2 (2 * m + 1)) (6 * m + 7) (0, 0, true) =
      some (2 * m + 3, 0, true) := by
    have := hF (2 * m + 1) le_rfl
    rw [show (1 + (2 * m + 1)) % 2 = 0 by omega,
      show 1 + (2 * m + 1) = 2 * m + 1 + 1 by omega,
      show 4 * m + 5 + (2 * m + 1) = 6 * m + 6 by omega] at this
    exact isoIterTwo_succ this (by simp [isoTraceStep, twkCore2_getElem?_cap])
  intro k hk p hp
  rw [hlen] at hk
  rw [morseOut_take_twkCore2 _ _ (by omega)] at hp
  have hfuel : 6 * m + 7 ≤ ((twkCore2 (2 * m + 1)).length + 1) *
      (2 * (twkCore2 (2 * m + 1)).length + 2) * 2 := by
    rw [hlen]
    nlinarith
  have hmem : ∀ n y, isoIterTwo (twkCore2 (2 * m + 1)) n (0, 0, true) = some y → n ≤ 6 * m + 7 →
      y ∈ isoTrace (twkCore2 (2 * m + 1)) (((twkCore2 (2 * m + 1)).length + 1) *
        (2 * (twkCore2 (2 * m + 1)).length + 2) * 2) (0, 0, true) :=
    fun n y hy hn ↦ mem_isoTrace_of_isoIterTwo _ n _ _ y hy (by omega)
  by_cases h0 : k = 0
  · rw [ite_eq_left (Or.inl h0)] at hp
    obtain rfl : p = 0 := by omega
    subst h0
    exact ⟨true, hmem 0 _ rfl (by omega)⟩
  by_cases h1 : k = 2 * m + 3
  · rw [ite_eq_left (Or.inr (by omega))] at hp
    obtain rfl : p = 0 := by omega
    subst h1
    exact ⟨true, hmem _ _ hG le_rfl⟩
  rw [ite_eq_right (by omega)] at hp
  obtain ⟨j, rfl⟩ : ∃ j, k = 1 + j := ⟨k - 1, by omega⟩
  by_cases h2 : p = 2
  · subst h2
    have hd := hD (2 * m + 1 - j) (by omega)
    rw [show 2 * m + 2 - (2 * m + 1 - j) = 1 + j by omega] at hd
    exact ⟨false, hmem _ _ hd (by omega)⟩
  by_cases h3 : p = j % 2
  · subst h3
    exact ⟨true, hmem _ _ (hB j (by omega)) (by omega)⟩
  · have h4 : p = (1 + j) % 2 := by omega
    subst h4
    exact ⟨true, hmem _ _ (hF j (by omega)) (by omega)⟩

/-- Beaded words compose. -/
private theorem isoBeaded_append_twKBeadedTwo {n : ℕ} {G W G' W' : MorseWord}
    {Bs Bs' : List MorseWord} (h : IsoBeaded n G W Bs)
    (h' : IsoBeaded (morseOut n G) G' W' Bs') :
    IsoBeaded n (G ++ G') (W ++ W') (Bs ++ Bs') := by
  induction h' with
  | nil => simpa using h
  | letter l _ ih =>
    rw [← List.append_assoc, ← List.append_assoc]
    exact IsoBeaded.letter l ih
  | bead p T _ hp hT hTo ih =>
    rw [← List.append_assoc, ← List.append_assoc]
    exact IsoBeaded.bead p T ih (by rw [morseOut_append]; exact hp) hT hTo

/-- `a` blocks `A1`, `b` positive left curls and `c` clasps. -/
private def twkBeadList2 (σ : Bool) (a b c : ℕ) : List MorseWord :=
  List.replicate a phaseTwoA1 ++ List.replicate b (isoCurlL true 1) ++
    List.replicate c (claspSWord σ)

/-- A piece of a beaded word: `W` is the doubled word of `G`, read from `n` thin strands and
ending on `m`, with `a` blocks `A1`, `b` positive curls and `c` clasps. -/
private def TwkBd2 (σ : Bool) (n m : ℕ) (G W : MorseWord) (a b c : ℕ) : Prop :=
  ∃ Bs : List MorseWord, IsoBeaded n G W Bs ∧ morseOut n G = m ∧ Bs.Perm (twkBeadList2 σ a b c)

/-- Pieces compose. -/
private theorem TwkBd2.append {σ : Bool} {n m k : ℕ} {G W G' W' : MorseWord} {a b c a' b' c' : ℕ}
    (h : TwkBd2 σ n m G W a b c) (h' : TwkBd2 σ m k G' W' a' b' c') :
    TwkBd2 σ n k (G ++ G') (W ++ W') (a + a') (b + b') (c + c') := by
  obtain ⟨Bs, hB, hm, hp⟩ := h
  obtain ⟨Bs', hB', hk, hp'⟩ := h'
  subst hm
  refine ⟨Bs ++ Bs', isoBeaded_append_twKBeadedTwo hB hB', by rw [morseOut_append, hk], ?_⟩
  refine (hp.append hp').trans (List.perm_iff_count.2 fun x ↦ ?_)
  simp only [twkBeadList2, List.replicate_add, List.count_append]
  omega

/-- Changing the presentation of a piece. -/
private theorem TwkBd2.of_eq {σ : Bool} {n m n' m' : ℕ} {G W G' W' : MorseWord}
    {a b c a' b' c' : ℕ} (h : TwkBd2 σ n m G W a b c) (hn : n = n') (hm : m = m') (hG : G = G')
    (hW : W = W') (ha : a = a') (hb : b = b') (hc : c = c') :
    TwkBd2 σ n' m' G' W' a' b' c' := by
  subst hn hm hG hW ha hb hc
  exact h

/-- The empty piece. -/
private theorem twkBd2_nil (σ : Bool) (n : ℕ) : TwkBd2 σ n n [] [] 0 0 0 :=
  ⟨[], IsoBeaded.nil n, rfl, List.Perm.refl _⟩

/-- Letters of the core without beads. -/
private theorem twkBd2_letters (σ : Bool) (n : ℕ) (G : MorseWord) :
    TwkBd2 σ n (morseOut n G) G (morseDouble G) 0 0 0 := by
  refine ⟨[], ?_, rfl, List.Perm.refl _⟩
  induction G using List.reverseRecOn with
  | nil => exact IsoBeaded.nil n
  | append_singleton G l ih =>
    have := IsoBeaded.letter l ih
    simpa only [morseDouble, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using this

/-- Letters of the core without beads, with the number of strands at the end. -/
private theorem twkBd2_letters_out (σ : Bool) (n m : ℕ) (G : MorseWord) (h : morseOut n G = m) :
    TwkBd2 σ n m G (morseDouble G) 0 0 0 :=
  h ▸ twkBd2_letters σ n G

/-- A block `A1` on the band `p`. -/
private theorem twkBd2_A1 (σ : Bool) (n p : ℕ) (hp : p < n) :
    TwkBd2 σ n n [] (morseShiftWord (2 * p) phaseTwoA1) 1 0 0 :=
  ⟨[] ++ [phaseTwoA1], IsoBeaded.bead p phaseTwoA1 (IsoBeaded.nil n) hp (by decide) (by decide),
    rfl, List.Perm.refl _⟩

/-- A positive left curl on the band `p`. -/
private theorem twkBd2_curl (σ : Bool) (n p : ℕ) (hp : p < n) :
    TwkBd2 σ n n [] (morseShiftWord (2 * p) (isoCurlL true 1)) 0 1 0 :=
  ⟨[] ++ [isoCurlL true 1],
    IsoBeaded.bead p (isoCurlL true 1) (IsoBeaded.nil n) hp (by decide) (by decide),
    rfl, List.Perm.refl _⟩

/-- The clasp on the band `p`. -/
private theorem twkBd2_clasp (σ : Bool) (n p : ℕ) (hp : p < n) :
    TwkBd2 σ n n [] (morseShiftWord (2 * p) (claspSWord σ)) 0 0 1 :=
  ⟨[] ++ [claspSWord σ], IsoBeaded.bead p (claspSWord σ) (IsoBeaded.nil n) hp
    (by cases σ <;> decide) (by cases σ <;> decide), rfl, List.Perm.refl _⟩

/-- A run of equal pieces. -/
private theorem TwkBd2.blk {σ : Bool} {n : ℕ} {G W : MorseWord} {a b c : ℕ}
    (h : TwkBd2 σ n n G W a b c) (k : ℕ) :
    TwkBd2 σ n n (phaseTwoBlk G k) (phaseTwoBlk W k) (k * a) (k * b) (k * c) := by
  induction k with
  | zero => exact (twkBd2_nil σ n).of_eq rfl rfl rfl rfl (by ring) (by ring) (by ring)
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact (h.append ih).of_eq rfl rfl rfl rfl (by ring) (by ring) (by ring)

/-- A run of pieces without letters. -/
private theorem TwkBd2.blk_nil {σ : Bool} {n : ℕ} {W : MorseWord} {a b c : ℕ}
    (h : TwkBd2 σ n n [] W a b c) (k : ℕ) :
    TwkBd2 σ n n [] (phaseTwoBlk W k) (k * a) (k * b) (k * c) :=
  (h.blk k).of_eq rfl rfl (by simp [phaseTwoBlk]) rfl rfl rfl rfl

/-- A run of one-letter blocks. -/
private theorem phaseTwoBlk_singleton_twKBeadedTwo (x : MorseLetter) (k : ℕ) :
    phaseTwoBlk [x] k = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    rw [ih]
    rfl

/-- The junction word for `r = 2` as a piece: the doubled core with its beads, counted. -/
private theorem twkBd2_twkQ2Body (σ : Bool) (k : ℕ) :
    TwkBd2 σ 1 1 (twkCore2 (k + 2)) (twkQ2Body (k + 2) σ) (k + 2) (k + 2) 1 := by
  have pA : TwkBd2 σ 1 1 [] phaseTwoA1 1 0 0 :=
    (twkBd2_A1 σ 1 0 (by omega)).of_eq rfl rfl rfl (morseShiftWord_zero_iso _) rfl rfl rfl
  have pTop : TwkBd2 σ 1 1 [] (isoCurlL true 1) 0 1 0 :=
    (twkBd2_curl σ 1 0 (by omega)).of_eq rfl rfl rfl (morseShiftWord_zero_iso _) rfl rfl rfl
  have pR0 : TwkBd2 σ 1 3 [isoU 1, isoX true 0] (isoBR0 0 2) 0 1 0 :=
    ((twkBd2_letters_out σ 1 3 [isoU 1, isoX true 0] rfl).append
      (twkBd2_curl σ 3 0 (by omega))).of_eq rfl rfl rfl rfl rfl rfl rfl
  have pClasp : TwkBd2 σ 3 3 [] (morseShiftWord 4 (claspSWord σ)) 0 0 1 :=
    twkBd2_clasp σ 3 2 (by omega)
  have pRound : TwkBd2 σ 3 3 [isoX true 0] (isoBRound 0 2) 0 1 0 :=
    ((twkBd2_letters_out σ 3 3 [isoX true 0] rfl).append
      (twkBd2_curl σ 3 0 (by omega))).of_eq rfl rfl rfl rfl rfl rfl rfl
  have pD : TwkBd2 σ 3 3 [isoX true 0] phaseTwoD 0 0 0 :=
    (twkBd2_letters_out σ 3 3 [isoX true 0] rfl).of_eq rfl rfl rfl rfl rfl rfl rfl
  have pA2 : TwkBd2 σ 3 3 [] (morseShiftWord 2 phaseTwoA1) 1 0 0 := twkBd2_A1 σ 3 1 (by omega)
  have pCap : TwkBd2 σ 3 1 [isoN 1] (morseDouble [isoN 1]) 0 0 0 :=
    twkBd2_letters_out σ 3 1 [isoN 1] rfl
  have hall := (pA.blk_nil (k + 1)).append (pR0.append (pClasp.append ((pRound.blk k).append
    (pD.append (pA2.append (pCap.append pTop))))))
  refine hall.of_eq rfl rfl ?_ ?_ (by omega) (by omega) (by omega)
  · rw [twkCore2, phaseTwoBlk_singleton_twKBeadedTwo,
      show k + 2 = (k + 1) + 1 by omega, List.replicate_succ, List.replicate_succ']
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.append_nil]
  · rw [twkQ2Body, show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel]
    simp only [List.append_assoc]

/-- `twkQ2Body s σ` is the doubled core for `r = 2` with `s` blocks `A1`, `s` positive curls and
the clasp. -/
theorem isoBeaded_twkQ2Body {s : ℕ} (hs : 3 ≤ s) (σ : Bool) :
    ∃ Bs : List MorseWord, IsoBeaded 1 (twkCore2 s) (twkQ2Body s σ) Bs ∧
      Bs.Perm (List.replicate s phaseTwoA1 ++ List.replicate s (isoCurlL true 1) ++
        [claspSWord σ]) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  obtain ⟨Bs, hB, -, hp⟩ := twkBd2_twkQ2Body σ k
  exact ⟨Bs, hB, hp⟩

end AJConjecture
