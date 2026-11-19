import Mathlib
import AJHandoff.TorusKnot.PairKIsoWords

/-!
# The core of the annulus

`pairCore r s` (`r ≥ 3`, `q = r - 2`) is the one-strand long knot followed by the band after stage
N: the nested cups `u₀ ⋯ u_{q-1}` (closing arcs on the left), the cup `u_{q+r-1}` of round `0`,
`s` rounds `morseWalkL true q (r - 1)` of the conveyor (the strand at `q + r - 1` moves to `q`
under the other `r - 1`), and the caps `n_{q-1}, n_{q+r-3}, n_{q-2}, …, n₀`. It is a diagram of
the right-handed `T(r, s)` with writhe `(r - 1)s` (checked: Jones polynomial of `T(r, s)`,
`SCR/ISO/tools/words.py`); the band after stage N is `morseDouble (pairCore r s)` with beads.

`pairCoreHead`/`pairCoreTail` split it after the first crossing of round `0`, where the clasp sits
after stage P. `IsoConnected` (every segment of the word lies on the long arc, read off the
step function `isoTraceStep`) is the hypothesis of the bead journeys of `PairKIsoBeadSlide`; for
`pairCore` it holds because `(σ_{r-2} ⋯ σ₀)^s` permutes the `r` strands of the conveyor
cyclically when `gcd(r, s) = 1`.
-/

namespace AJConjecture

/-- The core of the annulus of `Wh⁻₀(T(r, s))`, `r ≥ 3`. -/
def pairCore (r s : ℕ) : MorseWord :=
  (List.range (r - 2)).map isoU ++ [isoU (2 * r - 3)] ++
    phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) s ++ [isoN (r - 3), isoN (2 * r - 5)] ++
    (List.range (r - 3)).reverse.map isoN

/-- The core up to the first crossing of round `0`. -/
def pairCoreHead (r : ℕ) : MorseWord :=
  (List.range (r - 2)).map isoU ++ [isoU (2 * r - 3), isoX true (2 * r - 4)]

/-- The rest of the core. -/
def pairCoreTail (r s : ℕ) : MorseWord :=
  morseWalkL true (r - 2) (r - 2) ++ phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) (s - 1) ++
    [isoN (r - 3), isoN (2 * r - 5)] ++ (List.range (r - 3)).reverse.map isoN

/-- One step along the knot: the segment `(k, p, up)` is the strand at the position `p` between
the letters `k - 1` and `k`, traversed upwards if `up`. `none` at the two ends. -/
def isoTraceStep (w : MorseWord) : ℕ × ℕ × Bool → Option (ℕ × ℕ × Bool)
  | (k, p, true) =>
    match w[k]? with
    | none => none
    | some (.cross _, i) => some (k + 1, if p = i then i + 1 else if p = i + 1 then i else p, true)
    | some (.cup, i) => some (k + 1, if i ≤ p then p + 2 else p, true)
    | some (.cap, i) =>
      if p = i then some (k, i + 1, false) else if p = i + 1 then some (k, i, false)
      else some (k + 1, if i + 1 < p then p - 2 else p, true)
  | (0, _, false) => none
  | (k + 1, p, false) =>
    match w[k]? with
    | none => none
    | some (.cross _, i) => some (k, if p = i + 1 then i else if p = i then i + 1 else p, false)
    | some (.cup, i) =>
      if p = i then some (k + 1, i + 1, true) else if p = i + 1 then some (k + 1, i, true)
      else some (k, if i + 1 < p then p - 2 else p, false)
    | some (.cap, i) => some (k, if i ≤ p then p + 2 else p, false)

/-- The segments visited along the knot from the bottom end, with a step budget. -/
def isoTrace (w : MorseWord) : ℕ → ℕ × ℕ × Bool → List (ℕ × ℕ × Bool)
  | 0, x => [x]
  | fuel + 1, x =>
    match isoTraceStep w x with
    | none => [x]
    | some y => x :: isoTrace w fuel y

/-- Every segment of the word lies on the long arc from the bottom end. -/
def IsoConnected (w : MorseWord) : Prop :=
  ∀ k ≤ w.length, ∀ p < morseOut 1 (w.take k), ∃ d : Bool,
    (k, p, d) ∈ isoTrace w ((w.length + 1) * (2 * w.length + 2) * 2) (0, 0, true)

/-- A leftward walk grows at the front. -/
private theorem morseWalkL_succ_core (s : Bool) (p len : ℕ) :
    morseWalkL s p (len + 1) = (MorseKind.cross s, p + len) :: morseWalkL s p len := by
  simp [morseWalkL, List.range_succ]

/-- A leftward walk fits on the strands to its right and keeps their number. -/
private theorem morseWalkL_fits_core (n : ℕ) (s : Bool) (p len : ℕ) (h : p + len + 1 ≤ n) :
    morseFits n (morseWalkL s p len) = true ∧ morseOut n (morseWalkL s p len) = n := by
  induction len with
  | zero => exact ⟨rfl, rfl⟩
  | succ len ih =>
    rw [morseWalkL_succ_core, morseFits_cons]
    simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut, Nat.add_sub_cancel]
    exact ⟨⟨by omega, (ih (by omega)).1⟩, (ih (by omega)).2⟩

/-- A repeated block that keeps the number of strands fits and keeps it. -/
private theorem phaseTwoBlk_fits_core (n : ℕ) (w : MorseWord) (hf : morseFits n w = true)
    (ho : morseOut n w = n) :
    ∀ m, morseFits n (phaseTwoBlk w m) = true ∧ morseOut n (phaseTwoBlk w m) = n
  | 0 => ⟨rfl, rfl⟩
  | m + 1 => by
    rw [phaseTwoBlk, List.replicate_succ, List.flatten_cons, morseFits_append, morseOut_append,
      ho, hf]
    exact phaseTwoBlk_fits_core n w hf ho m

/-- The core splits after the first crossing of round `0`. -/
theorem pairCore_eq_head_tail {r s : ℕ} (hr : 3 ≤ r) (hs : 1 ≤ s) :
    pairCore r s = pairCoreHead r ++ pairCoreTail r s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hw : morseWalkL true (r - 2) (r - 1) =
      isoX true (2 * r - 4) :: morseWalkL true (r - 2) (r - 2) := by
    rw [show r - 1 = r - 2 + 1 by omega, morseWalkL_succ_core,
      show r - 2 + (r - 2) = 2 * r - 4 by omega]
    rfl
  simp only [pairCore, pairCoreHead, pairCoreTail, phaseTwoBlk, List.replicate_succ,
    List.flatten_cons, Nat.add_sub_cancel, hw, List.append_assoc, List.cons_append,
    List.nil_append]

set_option linter.unusedVariables false in
/-- The core is a diagram from one strand to one strand. -/
theorem morseFits_pairCore {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    morseFits 1 (pairCore r s) = true ∧ morseOut 1 (pairCore r s) = 1 := by
  have h1 : morseFits 1 ((List.range (r - 2)).map isoU) = true :=
    morseFits_isoCups 1 (r - 2) (fun t ↦ t) fun t _ ↦ by omega
  have o1 : morseOut 1 ((List.range (r - 2)).map isoU) = 2 * r - 3 := by
    rw [morseOut_of_cups _ _ (by simp [isoU])]
    simp only [List.length_map, List.length_range]
    omega
  have hW := morseWalkL_fits_core (2 * r - 1) true (r - 2) (r - 1) (by omega)
  have h3 := phaseTwoBlk_fits_core _ _ hW.1 hW.2 s
  have h5 : morseFits (2 * r - 5) ((List.range (r - 3)).reverse.map isoN) = true :=
    morseFits_isoCaps (2 * r - 5) (r - 3) (fun t ↦ t) fun t _ ↦ by omega
  have o5 : morseOut (2 * r - 5) ((List.range (r - 3)).reverse.map isoN) = 1 := by
    rw [morseOut_of_caps _ _ (by simp [isoN])]
    simp only [List.length_map, List.length_reverse, List.length_range]
    omega
  simp only [pairCore, morseFits_append, morseOut_append, h1, o1, Bool.true_and]
  simp only [morseOut, morseLetterOut, isoU, isoN, morseKindIn, morseKindOut]
  rw [show 2 * r - 3 + 2 - 0 = 2 * r - 1 by omega, h3.1, h3.2,
    show 2 * r - 1 + 0 - 2 + 0 - 2 = 2 * r - 5 by omega, h5, o5]
  refine ⟨?_, rfl⟩
  simp only [morseFits, morseKindIn, morseLetterOut, morseKindOut, Bool.and_true,
    Bool.and_eq_true]
  exact ⟨decide_eq_true (by omega), decide_eq_true (by omega), decide_eq_true (by omega)⟩

/-! ### Walking along a word -/

/-- `n` steps along the knot from a segment; `none` if an end is met first. -/
private def isoIter (w : MorseWord) : ℕ → ℕ × ℕ × Bool → Option (ℕ × ℕ × Bool)
  | 0, x => some x
  | n + 1, x => (isoTraceStep w x).bind (isoIter w n)

/-- Walks compose. -/
private theorem isoIter_trans {w : MorseWord} {a b : ℕ} {x y z : ℕ × ℕ × Bool}
    (h1 : isoIter w a x = some y) (h2 : isoIter w b y = some z) : isoIter w (a + b) x = some z := by
  induction a generalizing x with
  | zero =>
    simp only [isoIter, Option.some.injEq] at h1
    subst h1
    simpa using h2
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, isoIter]
    rw [isoIter] at h1
    cases hx : isoTraceStep w x with
    | none => rw [hx] at h1; simp at h1
    | some x1 =>
      rw [hx, Option.bind_some] at h1
      rw [Option.bind_some]
      exact ih h1

/-- One step is a walk of length one. -/
private theorem isoIter_one {w : MorseWord} {x y : ℕ × ℕ × Bool} (h : isoTraceStep w x = some y) :
    isoIter w 1 x = some y := by
  simp [isoIter, h]

/-- A segment reached within the budget is on the trace. -/
private theorem mem_isoTrace_of_iter (w : MorseWord) :
    ∀ (n fuel : ℕ) (x y : ℕ × ℕ × Bool), isoIter w n x = some y → n ≤ fuel →
      y ∈ isoTrace w fuel x
  | 0, fuel, x, y, h, _ => by
    simp only [isoIter, Option.some.injEq] at h
    subst h
    cases fuel with
    | zero => simp [isoTrace]
    | succ f =>
      unfold isoTrace
      cases isoTraceStep w x <;> simp
  | n + 1, fuel, x, y, h, hn => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [isoIter] at h
    cases hx : isoTraceStep w x with
    | none => rw [hx] at h; simp at h
    | some x1 =>
      rw [hx, Option.bind_some] at h
      simp only [isoTrace, hx]
      exact List.mem_cons_of_mem _ (mem_isoTrace_of_iter w n f x1 y h (by omega))

/-- Going up through a crossing. -/
private theorem isoTraceStep_up_cross {w : MorseWord} {k p i : ℕ} {b : Bool}
    (h : w[k]? = some (.cross b, i)) :
    isoTraceStep w (k, p, true) =
      some (k + 1, if p = i then i + 1 else if p = i + 1 then i else p, true) := by
  simp [isoTraceStep, h]

/-- Going up through a cup. -/
private theorem isoTraceStep_up_cup {w : MorseWord} {k p i : ℕ} (h : w[k]? = some (.cup, i)) :
    isoTraceStep w (k, p, true) = some (k + 1, if i ≤ p then p + 2 else p, true) := by
  simp [isoTraceStep, h]

/-- Going up past a cap that does not end the strand. -/
private theorem isoTraceStep_up_cap {w : MorseWord} {k p i : ℕ} (h : w[k]? = some (.cap, i))
    (h1 : p ≠ i) (h2 : p ≠ i + 1) :
    isoTraceStep w (k, p, true) = some (k + 1, if i + 1 < p then p - 2 else p, true) := by
  simp [isoTraceStep, h, h1, h2]

/-- Going up into the right end of a cap. -/
private theorem isoTraceStep_up_capR {w : MorseWord} {k i : ℕ} (h : w[k]? = some (.cap, i)) :
    isoTraceStep w (k, i + 1, true) = some (k, i, false) := by
  simp [isoTraceStep, h]

/-- Going up into the left end of a cap. -/
private theorem isoTraceStep_up_capL {w : MorseWord} {k i : ℕ} (h : w[k]? = some (.cap, i)) :
    isoTraceStep w (k, i, true) = some (k, i + 1, false) := by
  simp [isoTraceStep, h]

/-- Going down through a crossing. -/
private theorem isoTraceStep_down_cross {w : MorseWord} {k p i : ℕ} {b : Bool}
    (h : w[k]? = some (.cross b, i)) :
    isoTraceStep w (k + 1, p, false) =
      some (k, if p = i + 1 then i else if p = i then i + 1 else p, false) := by
  simp [isoTraceStep, h]

/-- Going down past a cup that does not end the strand. -/
private theorem isoTraceStep_down_cup {w : MorseWord} {k p i : ℕ} (h : w[k]? = some (.cup, i))
    (h1 : p ≠ i) (h2 : p ≠ i + 1) :
    isoTraceStep w (k + 1, p, false) = some (k, if i + 1 < p then p - 2 else p, false) := by
  simp [isoTraceStep, h, h1, h2]

/-- Going down into the left end of a cup. -/
private theorem isoTraceStep_down_cupL {w : MorseWord} {k i : ℕ} (h : w[k]? = some (.cup, i)) :
    isoTraceStep w (k + 1, i, false) = some (k + 1, i + 1, true) := by
  simp [isoTraceStep, h]

/-- Going down into the right end of a cup. -/
private theorem isoTraceStep_down_cupR {w : MorseWord} {k i : ℕ} (h : w[k]? = some (.cup, i)) :
    isoTraceStep w (k + 1, i + 1, false) = some (k + 1, i, true) := by
  simp [isoTraceStep, h]

/-- Going down through a cap. -/
private theorem isoTraceStep_down_cap {w : MorseWord} {k p i : ℕ} (h : w[k]? = some (.cap, i)) :
    isoTraceStep w (k + 1, p, false) = some (k, if i ≤ p then p + 2 else p, false) := by
  simp [isoTraceStep, h]

/-! ### The letters of the core -/

/-- The core with `r = q + 2`. -/
private def coreW (q s : ℕ) : MorseWord :=
  (List.range q).map isoU ++ [isoU (2 * q + 1)] ++
    phaseTwoBlk (morseWalkL true q (q + 1)) s ++ [isoN (q - 1), isoN (2 * q - 1)] ++
    (List.range (q - 1)).reverse.map isoN

/-- The core in terms of `q = r - 2`. -/
private theorem pairCore_eq_coreW (q s : ℕ) : pairCore (q + 2) s = coreW q s := by
  simp only [pairCore, coreW, show 2 * (q + 2) - 3 = 2 * q + 1 by omega, Nat.add_sub_cancel,
    show q + 2 - 1 = q + 1 by omega, show q + 2 - 3 = q - 1 by omega,
    show 2 * (q + 2) - 5 = 2 * q - 1 by omega]

/-- The length of a repeated block. -/
private theorem length_phaseTwoBlk_core (w : MorseWord) (s : ℕ) :
    (phaseTwoBlk w s).length = s * w.length := by
  simp [phaseTwoBlk]

/-- The length of one conveyor round. -/
private theorem length_walk_core (q : ℕ) : (morseWalkL true q (q + 1)).length = q + 1 := by
  simp [morseWalkL]

/-- The letters of a repeated block. -/
private theorem phaseTwoBlk_getElem?_core (w : MorseWord) :
    ∀ (s m c : ℕ), m < s → c < w.length → (phaseTwoBlk w s)[m * w.length + c]? = w[c]?
  | s + 1, 0, c, _, hc => by
    rw [phaseTwoBlk, List.replicate_succ, List.flatten_cons, zero_mul, zero_add,
      List.getElem?_append_left hc]
  | s + 1, m + 1, c, hm, hc => by
    rw [phaseTwoBlk, List.replicate_succ, List.flatten_cons,
      List.getElem?_append_right (by rw [add_mul, one_mul]; omega),
      show (m + 1) * w.length + c - w.length = m * w.length + c by rw [add_mul, one_mul]; omega]
    exact phaseTwoBlk_getElem?_core w s m c (by omega) hc

/-- The letters of one conveyor round. -/
private theorem walk_getElem?_core {q c : ℕ} (hc : c ≤ q) :
    (morseWalkL true q (q + 1))[c]? = some (.cross true, 2 * q - c) := by
  rw [morseWalkL, List.getElem?_map, List.getElem?_reverse (by simp; omega),
    List.getElem?_range (by simp only [List.length_range]; omega)]
  simp only [List.length_range, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- The length of the core. -/
private theorem length_coreW (q s : ℕ) (hq : 1 ≤ q) :
    (coreW q s).length = 2 * q + 2 + s * (q + 1) := by
  simp only [coreW, List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_nil, length_phaseTwoBlk_core, length_walk_core, List.length_reverse]
  omega

/-- The core as a bracketed concatenation. -/
private theorem coreW_assoc (q s : ℕ) : coreW q s = (List.range q).map isoU ++
    (isoU (2 * q + 1) :: (phaseTwoBlk (morseWalkL true q (q + 1)) s ++
      (isoN (q - 1) :: isoN (2 * q - 1) :: (List.range (q - 1)).reverse.map isoN))) := by
  simp [coreW]

/-- The first cups. -/
private theorem coreW_getElem?_cup {q s k : ℕ} (hk : k < q) :
    (coreW q s)[k]? = some (.cup, k) := by
  rw [coreW_assoc, List.getElem?_append_left (by simpa using hk), List.getElem?_map,
    List.getElem?_range hk]
  rfl

/-- The cup of round `0`. -/
private theorem coreW_getElem?_cupR (q s : ℕ) : (coreW q s)[q]? = some (.cup, 2 * q + 1) := by
  rw [coreW_assoc, List.getElem?_append_right (by simp)]
  simp [isoU]

/-- The crossings of the conveyor. -/
private theorem coreW_getElem?_cross {q s m c : ℕ} (hm : m < s) (hc : c ≤ q) :
    (coreW q s)[q + 1 + m * (q + 1) + c]? = some (.cross true, 2 * q - c) := by
  rw [coreW_assoc, List.getElem?_append_right (by simp; omega), List.length_map,
    List.length_range, show q + 1 + m * (q + 1) + c - q = (m * (q + 1) + c) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_left (by
      rw [length_phaseTwoBlk_core, length_walk_core]
      have : (m + 1) * (q + 1) ≤ s * (q + 1) := Nat.mul_le_mul_right _ hm
      rw [add_mul, one_mul] at this
      omega)]
  have := phaseTwoBlk_getElem?_core (morseWalkL true q (q + 1)) s m c hm
    (by rw [length_walk_core]; omega)
  rw [length_walk_core] at this
  rw [this, walk_getElem?_core hc]

/-- The first cap. -/
private theorem coreW_getElem?_cap0 (q s : ℕ) :
    (coreW q s)[q + 1 + s * (q + 1)]? = some (.cap, q - 1) := by
  rw [coreW_assoc, List.getElem?_append_right (by simp; omega), List.length_map,
    List.length_range, show q + 1 + s * (q + 1) - q = s * (q + 1) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_right (by
      rw [length_phaseTwoBlk_core, length_walk_core]),
    length_phaseTwoBlk_core, length_walk_core, Nat.sub_self]
  rfl

/-- The second cap. -/
private theorem coreW_getElem?_cap1 (q s : ℕ) :
    (coreW q s)[q + 2 + s * (q + 1)]? = some (.cap, 2 * q - 1) := by
  rw [coreW_assoc, List.getElem?_append_right (by simp; omega), List.length_map,
    List.length_range, show q + 2 + s * (q + 1) - q = s * (q + 1) + 1 + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_right (by
      rw [length_phaseTwoBlk_core, length_walk_core]; omega),
    length_phaseTwoBlk_core, length_walk_core, show s * (q + 1) + 1 - s * (q + 1) = 0 + 1 by omega]
  rfl

/-- The closing caps. -/
private theorem coreW_getElem?_capT {q s i : ℕ} (hi1 : 1 ≤ i) (hi : i + 1 ≤ q) :
    (coreW q s)[q + 2 + s * (q + 1) + i]? = some (.cap, q - 1 - i) := by
  rw [coreW_assoc, List.getElem?_append_right (by simp; omega), List.length_map,
    List.length_range, show q + 2 + s * (q + 1) + i - q = s * (q + 1) + (i + 1) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_right (by
      rw [length_phaseTwoBlk_core, length_walk_core]; omega),
    length_phaseTwoBlk_core, length_walk_core,
    show s * (q + 1) + (i + 1) - s * (q + 1) = (i - 1) + 1 + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_map,
    List.getElem?_reverse (by simp; omega), List.getElem?_range (by simp; omega)]
  simp only [List.length_range, Option.map_some, isoN, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- Past the last letter. -/
private theorem coreW_getElem?_end (q s : ℕ) (hq : 1 ≤ q) :
    (coreW q s)[2 * q + 2 + s * (q + 1)]? = none := by
  rw [List.getElem?_eq_none]
  rw [length_coreW q s hq]

/-! ### Arithmetic of the conveyor -/

/-- With `gcd(r, s) = 1`, the residues `c + a s` for `a < r` are all residues. -/
private theorem exists_pass_core {r s : ℕ} (c x : ℕ) (hr : 0 < r) (hcop : Nat.Coprime r s)
    (hx : x < r) : ∃ a < r, (c + a * s) % r = x := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime s r).mpr hcop.symm
  refine ⟨(((x : ZMod r) - c) * ↑u⁻¹).val, ZMod.val_lt _, ?_⟩
  have h : ((c + (((x : ZMod r) - c) * ↑u⁻¹).val * s : ℕ) : ZMod r) = x := by
    push_cast
    rw [ZMod.natCast_zmod_val, ← hu, mul_assoc, Units.inv_mul, mul_one]
    ring
  rw [← ZMod.val_natCast, h, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

/-- With `gcd(r, s) = 1`, the residue `c + a s` returns to `c` only at `a ≡ 0`. -/
private theorem pass_ne_core {r s : ℕ} (c a : ℕ) (hcop : Nat.Coprime r s) (ha : 0 < a)
    (har : a < r) : (c + a * s) % r ≠ c % r := by
  intro h
  have h' : c + a * s ≡ c [MOD r] := h
  have h2 : r ∣ a * s := by simpa using h'
  have h3 : r ∣ a := hcop.dvd_of_dvd_mul_right h2
  exact absurd (Nat.le_of_dvd ha h3) (by omega)

/-- A segment index of the conveyor is a round and a crossing count. -/
private theorem conveyor_index_core {q s k : ℕ} (h1 : q + 1 ≤ k) (h2 : k < q + 1 + s * (q + 1)) :
    ∃ m c, m < s ∧ c ≤ q ∧ k = q + 1 + m * (q + 1) + c := by
  refine ⟨(k - (q + 1)) / (q + 1), (k - (q + 1)) % (q + 1), ?_, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  · have := Nat.mod_lt (k - (q + 1)) (show q + 1 > 0 by omega)
    omega
  · have := Nat.div_add_mod (k - (q + 1)) (q + 1)
    rw [Nat.mul_comm] at this
    omega

/-- The number of strands between the letters of the core. -/
private theorem coreW_out {q s : ℕ} (hq : 1 ≤ q) :
    ∀ k ≤ 2 * q + 2 + s * (q + 1), morseOut 1 ((coreW q s).take k) =
      if k ≤ q then 2 * k + 1 else if k ≤ q + 1 + s * (q + 1) then 2 * q + 3
      else 2 * q + 3 - 2 * (k - (q + 1 + s * (q + 1)))
  | 0, _ => by simp [morseOut]
  | k + 1, hk => by
    have hlen := length_coreW q s hq
    rw [List.take_add_one, morseOut_append, coreW_out hq k (by omega)]
    have hlet : ∃ l, (coreW q s)[k]? = some l ∧ morseLetterOut
        (if k ≤ q then 2 * k + 1 else if k ≤ q + 1 + s * (q + 1) then 2 * q + 3
          else 2 * q + 3 - 2 * (k - (q + 1 + s * (q + 1)))) l =
        if k + 1 ≤ q then 2 * (k + 1) + 1 else if k + 1 ≤ q + 1 + s * (q + 1) then 2 * q + 3
          else 2 * q + 3 - 2 * (k + 1 - (q + 1 + s * (q + 1))) := by
      by_cases hkq : k < q
      · refine ⟨_, coreW_getElem?_cup hkq, ?_⟩
        simp only [morseLetterOut, morseKindIn, morseKindOut]
        split_ifs <;> omega
      by_cases hkq' : k = q
      · subst hkq'
        refine ⟨_, coreW_getElem?_cupR k s, ?_⟩
        simp only [morseLetterOut, morseKindIn, morseKindOut]
        split_ifs <;> omega
      by_cases hkK : k < q + 1 + s * (q + 1)
      · obtain ⟨m, c, hm, hc, rfl⟩ := conveyor_index_core (by omega) hkK
        refine ⟨_, coreW_getElem?_cross hm hc, ?_⟩
        simp only [morseLetterOut, morseKindIn, morseKindOut]
        split_ifs <;> omega
      by_cases hkK' : k = q + 1 + s * (q + 1)
      · rw [hkK']
        refine ⟨_, coreW_getElem?_cap0 q s, ?_⟩
        simp only [morseLetterOut, morseKindIn, morseKindOut]
        split_ifs <;> omega
      by_cases hkK1 : k = q + 2 + s * (q + 1)
      · rw [hkK1]
        refine ⟨_, coreW_getElem?_cap1 q s, ?_⟩
        simp only [morseLetterOut, morseKindIn, morseKindOut]
        split_ifs <;> omega
      · obtain ⟨i, rfl⟩ : ∃ i, k = q + 2 + s * (q + 1) + i := ⟨k - (q + 2 + s * (q + 1)), by omega⟩
        refine ⟨_, coreW_getElem?_capT (by omega) (by omega), ?_⟩
        simp only [morseLetterOut, morseKindIn, morseKindOut]
        split_ifs <;> omega
    obtain ⟨l, hl, hout⟩ := hlet
    rw [hl, Option.toList_some, morseOut, morseOut, hout]

/-! ### The walks along the core -/

/-- Closes an equation of segments. -/
local macro "core_trip" : tactic =>
  `(tactic| ((simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and]) <;>
    (try split_ifs) <;> omega))

/-- A walk followed by one step. -/
private theorem isoIter_snoc {w : MorseWord} {n : ℕ} {x y z : ℕ × ℕ × Bool}
    (h : isoIter w n x = some y) (hs : isoTraceStep w y = some z) : isoIter w (n + 1) x = some z :=
  isoIter_trans h (isoIter_one hs)

/-- From the bottom end up through the nested cups. -/
private theorem walk_init_core (q s : ℕ) :
    ∀ k ≤ q, isoIter (coreW q s) k (0, 0, true) = some (k, 2 * k, true)
  | 0, _ => rfl
  | k + 1, hk => isoIter_snoc (walk_init_core q s k (by omega)) (by
      rw [isoTraceStep_up_cup (coreW_getElem?_cup (by omega))]; core_trip)

/-- Up through the cup of round `0`. -/
private theorem step_q_up_core {q s p : ℕ} (hp : p ≤ 2 * q) :
    isoTraceStep (coreW q s) (q, p, true) = some (q + 1, p, true) := by
  rw [isoTraceStep_up_cup (coreW_getElem?_cupR q s)]; core_trip

/-- The position of a conveyor strand after `c` crossings of a round. -/
private def convP (q c j : ℕ) : ℕ :=
  if j = q + 1 then q + 1 - c else if q + 1 - c ≤ j then j + 1 else j

/-- Up through part of a conveyor round. -/
private theorem walk_round_core {q s m j : ℕ} (hm : m < s) (hj : j ≤ q + 1) :
    ∀ c ≤ q + 1, isoIter (coreW q s) c (q + 1 + m * (q + 1), q + j, true) =
      some (q + 1 + m * (q + 1) + c, q + convP q c j, true)
  | 0, _ => by simp only [isoIter, convP]; core_trip
  | c + 1, hc => isoIter_snoc (walk_round_core hm hj c (by omega)) (by
      rw [isoTraceStep_up_cross (coreW_getElem?_cross hm (by omega))]
      simp only [convP]
      core_trip)

/-- One full round is a cyclic shift. -/
private theorem convP_full {q j : ℕ} (hj : j ≤ q + 1) :
    convP q (q + 1) j = (j + 1) % (q + 2) := by
  simp only [convP]
  split_ifs with h1 h2
  · subst h1
    rw [show q + 1 + 1 = q + 2 by omega, Nat.mod_self]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
  · omega

/-- Up through whole conveyor rounds. -/
private theorem walk_rounds_core {q s j : ℕ} (hj : j ≤ q + 1) :
    ∀ m ≤ s, isoIter (coreW q s) (m * (q + 1)) (q + 1, q + j, true) =
      some (q + 1 + m * (q + 1), q + (j + m) % (q + 2), true)
  | 0, _ => by simp only [zero_mul, isoIter, add_zero, Nat.mod_eq_of_lt (show j < q + 2 by omega)]
  | m + 1, hm => by
    have hlt := Nat.mod_lt (j + m) (show q + 2 > 0 by omega)
    have h := isoIter_trans (walk_rounds_core (s := s) hj m (by omega))
      (walk_round_core (m := m) (by omega) (by omega : (j + m) % (q + 2) ≤ q + 1) (q + 1) le_rfl)
    rw [convP_full (by omega), Nat.mod_add_mod, show m * (q + 1) + (q + 1) = (m + 1) * (q + 1) by
      ring, show q + 1 + m * (q + 1) + (q + 1) = q + 1 + (m + 1) * (q + 1) by ring,
      show j + m + 1 = j + (m + 1) by omega] at h
    exact h

/-- Down through the conveyor on a strand it does not touch. -/
private theorem walk_conv_down_core {q s p : ℕ} (hp : p < q ∨ p = 2 * q + 2) :
    ∀ d ≤ s * (q + 1), isoIter (coreW q s) d (q + 1 + s * (q + 1), p, false) =
      some (q + 1 + s * (q + 1) - d, p, false)
  | 0, _ => by simp [isoIter]
  | d + 1, hd => by
    obtain ⟨m, c, hm, hc, hk⟩ := conveyor_index_core (q := q) (s := s)
      (k := q + 1 + s * (q + 1) - (d + 1)) (by omega) (by omega)
    have hl := coreW_getElem?_cross hm hc
    rw [← hk] at hl
    refine isoIter_snoc (walk_conv_down_core hp d (by omega)) ?_
    rw [show q + 1 + s * (q + 1) - d = (q + 1 + s * (q + 1) - (d + 1)) + 1 by omega,
      isoTraceStep_down_cross hl]
    core_trip

/-- Down past the cup of round `0` on a left leg. -/
private theorem step_q_down_core {q s p : ℕ} (hp : p < q) :
    isoTraceStep (coreW q s) (q + 1, p, false) = some (q, p, false) := by
  rw [isoTraceStep_down_cup (coreW_getElem?_cupR q s) (by omega) (by omega)]; core_trip

/-- Down into the cup of round `0`. -/
private theorem step_q_turn_core (q s : ℕ) :
    isoTraceStep (coreW q s) (q + 1, 2 * q + 2, false) = some (q + 1, 2 * q + 1, true) :=
  isoTraceStep_down_cupR (coreW_getElem?_cupR q s)

/-- Down a left leg through the nested cups. -/
private theorem walk_cups_down_core {q s p : ℕ} (hp : p < q) :
    ∀ d ≤ q - 1 - p, isoIter (coreW q s) d (q, p, false) = some (q - d, p, false)
  | 0, _ => by simp [isoIter]
  | d + 1, hd => isoIter_snoc (walk_cups_down_core hp d (by omega)) (by
      rw [show q - d = (q - (d + 1)) + 1 by omega,
        isoTraceStep_down_cup (coreW_getElem?_cup (by omega)) (by omega) (by omega)]
      core_trip)

/-- Turning at the bottom of a nested cup. -/
private theorem step_cup_turn_core {q s p : ℕ} (hp : p < q) :
    isoTraceStep (coreW q s) (p + 1, p, false) = some (p + 1, p + 1, true) :=
  isoTraceStep_down_cupL (coreW_getElem?_cup hp)

/-- Up a right leg through the nested cups. -/
private theorem walk_cups_up_core {q s p : ℕ} (hp : p < q) :
    ∀ j ≤ q - 1 - p, isoIter (coreW q s) j (p + 1, p + 1, true) =
      some (p + 1 + j, p + 1 + 2 * j, true)
  | 0, _ => by simp [isoIter]
  | j + 1, hj => isoIter_snoc (walk_cups_up_core hp j (by omega)) (by
      rw [isoTraceStep_up_cup (coreW_getElem?_cup (by omega))]; core_trip)

/-- The conveyor output `0` turns into the first cap. -/
private theorem step_cap0_turn_core {q s : ℕ} (hq : 1 ≤ q) :
    isoTraceStep (coreW q s) (q + 1 + s * (q + 1), q, true) =
      some (q + 1 + s * (q + 1), q - 1, false) := by
  have h := isoTraceStep_up_capR (k := q + 1 + s * (q + 1)) (coreW_getElem?_cap0 q s)
  rwa [show q - 1 + 1 = q by omega] at h

/-- The other conveyor outputs pass the first cap. -/
private theorem step_cap0_pass_core {q s t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) :
    isoTraceStep (coreW q s) (q + 1 + s * (q + 1), q + t, true) =
      some (q + 1 + s * (q + 1) + 1, q + t - 2, true) := by
  have h := coreW_getElem?_cap0 q s
  rw [isoTraceStep_up_cap h (show q + t ≠ q - 1 by omega) (show q + t ≠ q - 1 + 1 by omega)]
  core_trip

/-- Up through the closing caps. -/
private theorem walk_caps_up_core {q s t : ℕ} (ht : 1 ≤ t) (htq : t ≤ q) :
    ∀ i, 1 ≤ i → i ≤ t → isoIter (coreW q s) i (q + 1 + s * (q + 1) + 1, q + t - 2, true) =
      some (q + 1 + s * (q + 1) + 1 + i, q + t - 2 * i, true)
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => isoIter_one (by
      have h := coreW_getElem?_cap1 q s
      rw [show q + 2 + s * (q + 1) = q + 1 + s * (q + 1) + 1 by omega] at h
      rw [isoTraceStep_up_cap h (by omega) (by omega)]
      core_trip)
  | i + 2, _, hi => isoIter_snoc (walk_caps_up_core ht htq (i + 1) (by omega) (by omega)) (by
      have h := coreW_getElem?_capT (q := q) (s := s) (i := i + 1) (by omega) (by omega)
      rw [show q + 2 + s * (q + 1) + (i + 1) = q + 1 + s * (q + 1) + 1 + (i + 1) by omega] at h
      rw [isoTraceStep_up_cap h (by omega) (by omega)]
      core_trip)

/-- A conveyor output `t ∈ [1, q - 1]` turns into its closing cap. -/
private theorem step_capT_turn_core {q s t : ℕ} (ht : 1 ≤ t) (htq : t + 1 ≤ q) :
    isoTraceStep (coreW q s) (q + 1 + s * (q + 1) + 1 + t, q - t, true) =
      some (q + 1 + s * (q + 1) + 1 + t, q - 1 - t, false) := by
  have h := coreW_getElem?_capT (q := q) (s := s) (i := t) ht htq
  rw [show q + 2 + s * (q + 1) + t = q + 1 + s * (q + 1) + 1 + t by omega] at h
  have h2 := isoTraceStep_up_capR h
  rwa [show q - 1 - t + 1 = q - t by omega] at h2

/-- Down a left leg through the caps. -/
private theorem walk_caps_down_core {q s t : ℕ} (ht : 1 ≤ t) (htq : t + 1 ≤ q) :
    ∀ d ≤ t + 1, isoIter (coreW q s) d (q + 1 + s * (q + 1) + 1 + t, q - 1 - t, false) =
      some (q + 1 + s * (q + 1) + 1 + t - d, q - 1 - t, false)
  | 0, _ => by simp [isoIter]
  | d + 1, hd => isoIter_snoc (walk_caps_down_core ht htq d (by omega)) (by
      rw [show q + 1 + s * (q + 1) + 1 + t - d = (q + 1 + s * (q + 1) + t - d) + 1 by omega]
      by_cases hdt : d + 1 < t
      · have h := coreW_getElem?_capT (q := q) (s := s) (i := t - d - 1) (by omega) (by omega)
        rw [show q + 2 + s * (q + 1) + (t - d - 1) = q + 1 + s * (q + 1) + t - d by omega] at h
        rw [isoTraceStep_down_cap h]
        core_trip
      by_cases hdt' : d + 1 = t
      · have h := coreW_getElem?_cap1 q s
        rw [show q + 2 + s * (q + 1) = q + 1 + s * (q + 1) + t - d by omega] at h
        rw [isoTraceStep_down_cap h]
        core_trip
      · have h := coreW_getElem?_cap0 q s
        rw [show q + 1 + s * (q + 1) = q + 1 + s * (q + 1) + t - d by omega] at h
        rw [isoTraceStep_down_cap h]
        core_trip)

/-- The conveyor output `q + 1` turns into the second cap. -/
private theorem step_cap1_turn_core {q s : ℕ} (hq : 1 ≤ q) :
    isoTraceStep (coreW q s) (q + 1 + s * (q + 1) + 1, 2 * q - 1, true) =
      some (q + 1 + s * (q + 1) + 1, 2 * q, false) := by
  have h := coreW_getElem?_cap1 q s
  rw [show q + 2 + s * (q + 1) = q + 1 + s * (q + 1) + 1 by omega] at h
  have h2 := isoTraceStep_up_capL h
  rwa [show 2 * q - 1 + 1 = 2 * q by omega] at h2

/-- Down from the second cap past the first. -/
private theorem step_cap0_down_core {q s : ℕ} (hq : 1 ≤ q) :
    isoTraceStep (coreW q s) (q + 1 + s * (q + 1) + 1, 2 * q, false) =
      some (q + 1 + s * (q + 1), 2 * q + 2, false) := by
  rw [isoTraceStep_down_cap (coreW_getElem?_cap0 q s)]; core_trip

/-! ### The passes of the knot through the conveyor -/

/-- The segment `z` is reached from the bottom end within `b` steps. -/
private def CoreRch (q s b : ℕ) (z : ℕ × ℕ × Bool) : Prop :=
  ∃ n ≤ b, isoIter (coreW q s) n (0, 0, true) = some z

/-- Reaching extends along a walk. -/
private theorem CoreRch.iter {q s b n : ℕ} {x y : ℕ × ℕ × Bool} (h : CoreRch q s b x)
    (hw : isoIter (coreW q s) n x = some y) : CoreRch q s (b + n) y := by
  obtain ⟨m, hm, hx⟩ := h
  exact ⟨m + n, by omega, isoIter_trans hx hw⟩

/-- Reaching extends by one step. -/
private theorem CoreRch.step {q s b : ℕ} {x y : ℕ × ℕ × Bool} (h : CoreRch q s b x)
    (hw : isoTraceStep (coreW q s) x = some y) : CoreRch q s (b + 1) y :=
  h.iter (isoIter_one hw)

/-- Reaching is monotone in the budget. -/
private theorem CoreRch.mono {q s b b' : ℕ} {x : ℕ × ℕ × Bool} (h : CoreRch q s b x)
    (hb : b ≤ b') : CoreRch q s b' x := by
  obtain ⟨m, hm, hx⟩ := h
  exact ⟨m, by omega, hx⟩

/-- From the cap end of a left leg down to the bottom of the conveyor and back up the right leg:
the return of the conveyor output `2q - 1 - p` to its input. -/
private theorem walk_leg_return_core {q s p : ℕ} (hp : p < q) :
    isoIter (coreW q s) (s * (q + 1) + 2 * (q - 1 - p) + 3) (q + 1 + s * (q + 1), p, false) =
      some (q + 1, 2 * q - 1 - p, true) := by
  have h1 := walk_conv_down_core (s := s) (Or.inl hp) (s * (q + 1)) le_rfl
  have h2 := isoIter_one (step_q_down_core (s := s) hp)
  have h3 := walk_cups_down_core (s := s) hp (q - 1 - p) le_rfl
  have h4 := isoIter_one (step_cup_turn_core (s := s) hp)
  have h5 := walk_cups_up_core (s := s) hp (q - 1 - p) le_rfl
  have h6 := isoIter_one (step_q_up_core (q := q) (s := s) (p := 2 * q - 1 - p) (by omega))
  rw [show q + 1 + s * (q + 1) - s * (q + 1) = q + 1 by omega] at h1
  rw [show q - (q - 1 - p) = p + 1 by omega] at h3
  rw [show p + 1 + (q - 1 - p) = q by omega, show p + 1 + 2 * (q - 1 - p) = 2 * q - 1 - p by
    omega] at h5
  have := isoIter_trans (isoIter_trans (isoIter_trans (isoIter_trans (isoIter_trans h1 h2) h3)
    h4) h5) h6
  rwa [show s * (q + 1) + 1 + (q - 1 - p) + 1 + (q - 1 - p) + 1 =
    s * (q + 1) + 2 * (q - 1 - p) + 3 by omega] at this

/-- From a conveyor output `t ∈ [1, q - 1]` to the cap end of its left leg. -/
private theorem walk_top_leg_core {q s t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) (htq : t + 1 ≤ q) :
    isoIter (coreW q s) (2 * t + 3) (q + 1 + s * (q + 1), q + t, true) =
      some (q + 1 + s * (q + 1), q - 1 - t, false) := by
  have h1 := isoIter_one (step_cap0_pass_core (s := s) hq ht)
  have h2 := walk_caps_up_core (q := q) (s := s) ht (by omega) t ht le_rfl
  have h3 := isoIter_one (step_capT_turn_core (s := s) ht htq)
  have h4 := walk_caps_down_core (s := s) ht htq (t + 1) le_rfl
  rw [show q + t - 2 * t = q - t by omega] at h2
  rw [show q + 1 + s * (q + 1) + 1 + t - (t + 1) = q + 1 + s * (q + 1) by omega] at h4
  have := isoIter_trans (isoIter_trans (isoIter_trans h1 h2) h3) h4
  rwa [show 1 + t + 1 + (t + 1) = 2 * t + 3 by omega] at this

/-- From a conveyor output `t ≤ q - 1` to the cap end of its left leg. -/
private theorem walk_top_leg_core' {q s t : ℕ} (hq : 1 ≤ q) (htq : t + 1 ≤ q) :
    ∃ n ≤ 2 * q + 1, isoIter (coreW q s) n (q + 1 + s * (q + 1), q + t, true) =
      some (q + 1 + s * (q + 1), q - 1 - t, false) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact ⟨1, by omega, isoIter_one (by simpa using step_cap0_turn_core (s := s) hq)⟩
  · exact ⟨2 * t + 3, by omega, walk_top_leg_core hq ht htq⟩

/-- Every conveyor output other than the top end returns to the same conveyor input. -/
private theorem walk_return_core {q s t : ℕ} (hq : 1 ≤ q) (ht : t ≤ q + 1) (htq : t ≠ q) :
    ∃ n ≤ s * (q + 1) + 4 * q + 6, isoIter (coreW q s) n (q + 1 + s * (q + 1), q + t, true) =
      some (q + 1, q + t, true) := by
  by_cases ht1 : t = q + 1
  · subst ht1
    have h1 := isoIter_one (step_cap0_pass_core (s := s) hq (t := q + 1) (by omega))
    have h2 := isoIter_one (step_cap1_turn_core (s := s) hq)
    have h3 := isoIter_one (step_cap0_down_core (s := s) hq)
    have h4 := walk_conv_down_core (s := s) (p := 2 * q + 2) (Or.inr rfl) (s * (q + 1)) le_rfl
    have h5 := isoIter_one (step_q_turn_core q s)
    rw [show q + (q + 1) - 2 = 2 * q - 1 by omega, show q + (q + 1) = 2 * q + 1 by omega] at h1
    rw [show q + 1 + s * (q + 1) - s * (q + 1) = q + 1 by omega] at h4
    refine ⟨1 + 1 + 1 + s * (q + 1) + 1, by omega, ?_⟩
    rw [show q + (q + 1) = 2 * q + 1 by omega]
    exact isoIter_trans (isoIter_trans (isoIter_trans (isoIter_trans h1 h2) h3) h4) h5
  · obtain ⟨n, hn, h1⟩ := walk_top_leg_core' (s := s) hq (t := t) (by omega)
    have h2 := walk_leg_return_core (q := q) (s := s) (p := q - 1 - t) (by omega)
    rw [show 2 * q - 1 - (q - 1 - t) = q + t by omega] at h2
    exact ⟨n + (s * (q + 1) + 2 * (q - 1 - (q - 1 - t)) + 3), by omega, isoIter_trans h1 h2⟩

/-- The `a`-th pass enters the conveyor at the input `q + a s mod (q + 2)`. -/
private theorem pass_start_core {q s : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s) :
    ∀ a < q + 2, CoreRch q s (q + 1 + a * (2 * (s * (q + 1)) + 4 * q + 10))
      (q + 1, q + (q + a * s) % (q + 2), true)
  | 0, _ => by
    have h := isoIter_snoc (walk_init_core q s q le_rfl) (step_q_up_core (s := s) (p := 2 * q)
      le_rfl)
    refine ⟨q + 1, by omega, ?_⟩
    rw [h, zero_mul, add_zero, Nat.mod_eq_of_lt (by omega), two_mul]
  | a + 1, ha => by
    have h1 := (pass_start_core hq hcop a (by omega)).iter
      (walk_rounds_core (s := s) (q := q) (j := (q + a * s) % (q + 2))
        (by have := Nat.mod_lt (q + a * s) (show q + 2 > 0 by omega); omega) s le_rfl)
    rw [Nat.mod_add_mod, show q + a * s + s = q + (a + 1) * s by ring] at h1
    have hne := pass_ne_core q (a + 1) hcop (by omega) ha
    rw [Nat.mod_eq_of_lt (show q < q + 2 by omega)] at hne
    obtain ⟨n, hn, h2⟩ := walk_return_core (s := s) hq
      (by have := Nat.mod_lt (q + (a + 1) * s) (show q + 2 > 0 by omega); omega) hne
    exact (h1.iter h2).mono (by nlinarith)

/-- Every conveyor input is reached. -/
private theorem start_reach_core {q s : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s) {j : ℕ}
    (hj : j ≤ q + 1) :
    CoreRch q s (q + 1 + (q + 1) * (2 * (s * (q + 1)) + 4 * q + 10)) (q + 1, q + j, true) := by
  obtain ⟨a, ha, haj⟩ := exists_pass_core (s := s) q j (by omega) hcop (by omega)
  have h := pass_start_core hq hcop a ha
  rw [haj] at h
  have := Nat.mul_le_mul_right (2 * (s * (q + 1)) + 4 * q + 10) (show a ≤ q + 1 by omega)
  exact h.mono (by omega)

/-- Every conveyor output is reached. -/
private theorem top_reach_core {q s : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s) {t : ℕ}
    (ht : t ≤ q + 1) :
    CoreRch q s (q + 1 + (q + 1) * (2 * (s * (q + 1)) + 4 * q + 10) + s * (q + 1))
      (q + 1 + s * (q + 1), q + t, true) := by
  obtain ⟨a, ha, hat⟩ := exists_pass_core (s := s) (q + s) t (by omega) hcop (by omega)
  have h := (pass_start_core hq hcop a ha).iter
    (walk_rounds_core (s := s) (q := q) (j := (q + a * s) % (q + 2))
      (by have := Nat.mod_lt (q + a * s) (show q + 2 > 0 by omega); omega) s le_rfl)
  rw [Nat.mod_add_mod, show q + a * s + s = q + s + a * s by ring, hat] at h
  have := Nat.mul_le_mul_right (2 * (s * (q + 1)) + 4 * q + 10) (show a ≤ q + 1 by omega)
  exact h.mono (by omega)

/-- The budget within which every conveyor output is reached. -/
private def coreBt (q s : ℕ) : ℕ :=
  q + 1 + (q + 1) * (2 * (s * (q + 1)) + 4 * q + 10) + s * (q + 1)

/-- The budget within which every segment is reached. -/
private def coreBf (q s : ℕ) : ℕ := q + 1 + (q + 2) * (2 * (s * (q + 1)) + 4 * q + 10)

/-- The return paths fit in the final budget. -/
private theorem coreBt_le (q s : ℕ) : coreBt q s + s * (q + 1) + 4 * q + 6 ≤ coreBf q s := by
  simp only [coreBt, coreBf]
  nlinarith

/-- The conveyor inputs fit in the final budget. -/
private theorem coreBs_le (q s : ℕ) :
    q + 1 + (q + 1) * (2 * (s * (q + 1)) + 4 * q + 10) + s * (q + 1) ≤ coreBf q s := by
  simp only [coreBf]
  nlinarith

/-- The cap end of every left leg is reached. -/
private theorem leg_top_core {q s p : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s) (hp : p < q) :
    CoreRch q s (coreBt q s + (2 * q + 1)) (q + 1 + s * (q + 1), p, false) := by
  obtain ⟨n, hn, h⟩ := walk_top_leg_core' (s := s) hq (t := q - 1 - p) (by omega)
  rw [show q - 1 - (q - 1 - p) = p by omega] at h
  exact ((top_reach_core hq hcop (t := q - 1 - p) (by omega)).iter h).mono (by
    simp only [coreBt]; omega)

/-- The left legs inside the conveyor. -/
private theorem leg_conv_core {q s p d : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hp : p < q) (hd : d ≤ s * (q + 1)) :
    CoreRch q s (coreBf q s) (q + 1 + s * (q + 1) - d, p, false) :=
  ((leg_top_core hq hcop hp).iter (walk_conv_down_core (Or.inl hp) d hd)).mono (by
    have := coreBt_le q s; omega)

/-- The left legs among the nested cups. -/
private theorem leg_cups_core {q s p d : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hp : p < q) (hd : d ≤ q - 1 - p) : CoreRch q s (coreBf q s) (q - d, p, false) := by
  have h1 := walk_conv_down_core (s := s) (Or.inl hp) (s * (q + 1)) le_rfl
  rw [show q + 1 + s * (q + 1) - s * (q + 1) = q + 1 by omega] at h1
  exact ((((leg_top_core hq hcop hp).iter h1).step (step_q_down_core hp)).iter
    (walk_cups_down_core hp d hd)).mono (by have := coreBt_le q s; omega)

/-- The right legs among the nested cups. -/
private theorem leg_up_core {q s p j : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hp : p < q) (hj : j ≤ q - 1 - p) :
    CoreRch q s (coreBf q s) (p + 1 + j, p + 1 + 2 * j, true) := by
  have h1 := walk_conv_down_core (s := s) (Or.inl hp) (s * (q + 1)) le_rfl
  rw [show q + 1 + s * (q + 1) - s * (q + 1) = q + 1 by omega] at h1
  have h3 := walk_cups_down_core (s := s) hp (q - 1 - p) le_rfl
  rw [show q - (q - 1 - p) = p + 1 by omega] at h3
  exact (((((leg_top_core hq hcop hp).iter h1).step (step_q_down_core hp)).iter h3).step
    (step_cup_turn_core hp) |>.iter (walk_cups_up_core hp j hj)).mono (by
      have := coreBt_le q s; omega)

/-- The left legs among the caps. -/
private theorem leg_caps_core {q s t i : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (ht : 1 ≤ t) (htq : t + 1 ≤ q) (hi : i ≤ t) :
    CoreRch q s (coreBf q s) (q + 1 + s * (q + 1) + 1 + i, q - 1 - t, false) := by
  have h2 := walk_caps_up_core (q := q) (s := s) ht (by omega) t ht le_rfl
  rw [show q + t - 2 * t = q - t by omega] at h2
  have h4 := walk_caps_down_core (s := s) ht htq (t - i) (by omega)
  rw [show q + 1 + s * (q + 1) + 1 + t - (t - i) = q + 1 + s * (q + 1) + 1 + i by omega] at h4
  exact (((((top_reach_core hq hcop (t := t) (by omega)).step (step_cap0_pass_core hq ht)).iter
    h2).step (step_capT_turn_core ht htq)).iter h4).mono (by
      have := coreBt_le q s; simp only [coreBt] at this; omega)

/-- The conveyor outputs among the caps, just after the first cap. -/
private theorem top_cap0_core {q s t : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (ht : 1 ≤ t) (htq : t ≤ q + 1) :
    CoreRch q s (coreBf q s) (q + 1 + s * (q + 1) + 1, q + t - 2, true) :=
  ((top_reach_core hq hcop htq).step (step_cap0_pass_core hq ht)).mono (by
    have := coreBt_le q s; simp only [coreBt] at this; omega)

/-- The conveyor outputs among the closing caps. -/
private theorem top_caps_core {q s t i : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (ht : 1 ≤ t) (htq : t ≤ q) (hi : 1 ≤ i) (hit : i ≤ t) :
    CoreRch q s (coreBf q s) (q + 1 + s * (q + 1) + 1 + i, q + t - 2 * i, true) :=
  (((top_reach_core hq hcop (t := t) (by omega)).step (step_cap0_pass_core hq ht)).iter
    (walk_caps_up_core ht htq i hi hit)).mono (by
      have := coreBt_le q s; simp only [coreBt] at this; omega)

/-- The idle strand of the cup of round `0`, down from the second cap. -/
private theorem eprime_core {q s d : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hd : d ≤ s * (q + 1)) :
    CoreRch q s (coreBf q s) (q + 1 + s * (q + 1) + 1, 2 * q, false) ∧
      CoreRch q s (coreBf q s) (q + 1 + s * (q + 1) - d, 2 * q + 2, false) := by
  have h1 := step_cap0_pass_core (s := s) hq (t := q + 1) (by omega)
  rw [show q + (q + 1) - 2 = 2 * q - 1 by omega] at h1
  have hA := ((top_reach_core hq hcop (t := q + 1) le_rfl).step h1).step (step_cap1_turn_core hq)
  refine ⟨hA.mono (by have := coreBt_le q s; simp only [coreBt] at this; omega), ?_⟩
  exact ((hA.step (step_cap0_down_core hq)).iter
    (walk_conv_down_core (Or.inr rfl) d hd)).mono (by
      have := coreBt_le q s; simp only [coreBt] at this; omega)

/-- The inverse of the position after `c` crossings of a round. -/
private def convQ (q c x : ℕ) : ℕ :=
  if x = q + 1 - c then q + 1 else if q + 1 - c < x then x - 1 else x

/-- `convQ` inverts `convP`. -/
private theorem convP_convQ {q c x : ℕ} (hc : c ≤ q) (hx : x ≤ q + 1) :
    convQ q c x ≤ q + 1 ∧ convP q c (convQ q c x) = x := by
  simp only [convQ, convP]
  split_ifs <;> omega

/-- The strands of the conveyor. -/
private theorem conveyor_core {q s m c x : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hm : m < s) (hc : c ≤ q) (hx : x ≤ q + 1) :
    CoreRch q s (coreBf q s) (q + 1 + m * (q + 1) + c, q + x, true) := by
  obtain ⟨hQ, hPQ⟩ := convP_convQ hc hx
  obtain ⟨a, ha, haj⟩ := exists_pass_core (s := 1) m (convQ q c x) (show 0 < q + 2 by omega)
    (Nat.coprime_one_right _) (by omega)
  rw [mul_one, Nat.add_comm] at haj
  have h1 := (start_reach_core hq hcop (j := a) (by omega)).iter
    (walk_rounds_core (s := s) (q := q) (j := a) (by omega) m hm.le)
  rw [haj] at h1
  have h2 := h1.iter (walk_round_core hm hQ c (by omega))
  rw [hPQ] at h2
  have h3 := Nat.mul_le_mul_right (q + 1) hm
  rw [Nat.succ_mul] at h3
  exact h2.mono (by have := coreBs_le q s; omega)

/-- Reaching a segment given by equal coordinates. -/
private theorem CoreRch.congr {q s b k k' p p' : ℕ} {d : Bool} (h : CoreRch q s b (k, p, d))
    (hk : k = k') (hp : p = p') : CoreRch q s b (k', p', d) := hk ▸ hp ▸ h

/-- The segments among the nested cups are reached. -/
private theorem cover_cups_core {q s k p : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hk : k ≤ q) (hp : p < 2 * k + 1) : ∃ d, CoreRch q s (coreBf q s) (k, p, d) := by
  by_cases hp1 : p = 2 * k
  · subst hp1
    refine ⟨true, k, ?_, walk_init_core q s k hk⟩
    simp only [coreBf]
    omega
  by_cases hp2 : p < k
  · exact ⟨false, (leg_cups_core (d := q - k) hq hcop (show p < q by omega) (by omega)).congr
      (by omega) rfl⟩
  · exact ⟨true, (leg_up_core (p := 2 * k - p - 1) (j := p - k) hq hcop (by omega)
      (by omega)).congr (by omega) (by omega)⟩

/-- The segments of the conveyor are reached. -/
private theorem cover_conveyor_core {q s k p : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hk1 : q + 1 ≤ k) (hk2 : k ≤ q + 1 + s * (q + 1)) (hp : p < 2 * q + 3) :
    ∃ d, CoreRch q s (coreBf q s) (k, p, d) := by
  by_cases hp1 : p < q
  · exact ⟨false, (leg_conv_core (d := q + 1 + s * (q + 1) - k) hq hcop hp1 (by omega)).congr
      (by omega) rfl⟩
  by_cases hp2 : p = 2 * q + 2
  · exact ⟨false, ((eprime_core (d := q + 1 + s * (q + 1) - k) hq hcop (by omega)).2).congr
      (by omega) hp2.symm⟩
  by_cases hkK : k = q + 1 + s * (q + 1)
  · exact ⟨true, ((top_reach_core hq hcop (t := p - q) (by omega)).mono
      (by have := coreBt_le q s; simp only [coreBt] at this; omega)).congr hkK.symm (by omega)⟩
  · obtain ⟨m, c, hm, hc, rfl⟩ := conveyor_index_core (q := q) (s := s) (k := k) (by omega)
      (by omega)
    exact ⟨true, (conveyor_core (x := p - q) hq hcop hm hc (by omega)).congr rfl (by omega)⟩

/-- The segments among the caps are reached. -/
private theorem cover_caps_core {q s i p : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime (q + 2) s)
    (hi : i ≤ q) (hp : p < 2 * q + 1 - 2 * i) :
    ∃ d, CoreRch q s (coreBf q s) (q + 1 + s * (q + 1) + 1 + i, p, d) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · by_cases hp1 : p + 2 ≤ q
    · exact ⟨false, (leg_caps_core (t := q - 1 - p) (i := 0) hq hcop (by omega) (by omega)
        (by omega)).congr rfl (by omega)⟩
    by_cases hp2 : p ≤ 2 * q - 1
    · exact ⟨true, (top_cap0_core (t := p + 2 - q) hq hcop (by omega) (by omega)).congr rfl
        (by omega)⟩
    · exact ⟨false, ((eprime_core (d := 0) hq hcop (by omega)).1).congr rfl (by omega)⟩
  · by_cases hp1 : p + 1 + i ≤ q
    · exact ⟨false, (leg_caps_core (t := q - 1 - p) (i := i) hq hcop (by omega) (by omega)
        (by omega)).congr rfl (by omega)⟩
    · exact ⟨true, (top_caps_core (t := p + 2 * i - q) (i := i) hq hcop (by omega) (by omega)
        hi1 (by omega)).congr rfl (by omega)⟩

/-- The final budget is within the fuel of `IsoConnected`. -/
private theorem coreBf_le_fuel (q s : ℕ) (hs : 1 ≤ s) :
    coreBf q s ≤ (2 * q + 2 + s * (q + 1) + 1) * (2 * (2 * q + 2 + s * (q + 1)) + 2) * 2 := by
  simp only [coreBf]
  have h1 : q + 1 ≤ s * (q + 1) := Nat.le_mul_of_pos_left _ hs
  nlinarith

/-- The core is connected (one component). -/
theorem isoConnected_pairCore {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    IsoConnected (pairCore r s) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 2 := ⟨r - 2, by omega⟩
  have hq : 1 ≤ q := by omega
  have hcop : Nat.Coprime (q + 2) s := h.2.2
  have hs : 1 ≤ s := by have := h.2.1; omega
  rw [pairCore_eq_coreW]
  intro k hk p hp
  rw [length_coreW q s hq] at hk
  rw [coreW_out hq k hk] at hp
  have hcov : ∃ d, CoreRch q s (coreBf q s) (k, p, d) := by
    by_cases hk1 : k ≤ q
    · simp only [hk1, ↓reduceIte] at hp
      exact cover_cups_core hq hcop hk1 hp
    simp only [hk1, ↓reduceIte] at hp
    by_cases hk2 : k ≤ q + 1 + s * (q + 1)
    · simp only [hk2, ↓reduceIte] at hp
      exact cover_conveyor_core hq hcop (by omega) hk2 hp
    simp only [hk2, ↓reduceIte] at hp
    obtain ⟨i, rfl⟩ : ∃ i, k = q + 1 + s * (q + 1) + 1 + i :=
      ⟨k - (q + 1 + s * (q + 1) + 1), by omega⟩
    exact cover_caps_core hq hcop (by omega) (by omega)
  obtain ⟨d, n, hn, hiter⟩ := hcov
  refine ⟨d, mem_isoTrace_of_iter _ n _ _ _ hiter ?_⟩
  rw [length_coreW q s hq]
  have := coreBf_le_fuel q s hs
  omega

end AJConjecture
