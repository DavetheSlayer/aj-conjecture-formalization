import Mathlib
import AJHandoff.TorusKnot.PairKIsoBeadSlide

/-!
# Doubled long knots with beads: definitions

A *bead* is a tangle from two strands to two strands placed on a band `2p, 2p + 1` of a doubled
word `morseDouble G`. The library moves one bead along a doubled connected long knot that
carries nothing else (`morseReach_isoBandBead_journey`). Here the doubled word carries many
beads, and all of them are moved to the top end at once (`TwKPosEvac`): no bead has to pass
another one, and the beads may be arbitrary tangles (for instance a clasp of either sign), so no
alphabet of beads and no port bookkeeping is needed.

* `IsoBeaded n G W Bs`: `W` is `morseDouble G` (read from `n` thin strands) with the beads `Bs`
  inserted on bands, in the order of the word. This is the form in which the junction words are
  recognised (`TwKPosBeaded`).
* `isoSlotWord n G β`: the same in normal form, used in the proof: `β k p` is the tangle on the
  band `p` at the level `k` (below the letter `k` of `G`; `k = G.length` is the top level).
* `isoSnowStep β x y`: the content of the slot of the segment `x` of the knot moves to the slot
  of the next segment `y = isoTraceStep G x`, where it is put below (going up) or on top (going
  down) of what is there, rotated by `π` when the knot turns at a cap or a cup. Following the
  whole knot from the bottom end, the moving stack collects every bead (a *snowball*).
* `IsoRotPerm Bs L`: `L` lists the tangles `Bs` in some order, each one as it is or rotated.

Simulated outside Lean (`SCR/KP/tools/evac.py`, `evac_test.py`): for the words of
`TwKPosWords`, `(r, s) ∈ {(2,3), (2,5), (3,4), (3,5), (4,5)}`, both clasp signs, the words
`isoSlotWord` along the snowball have equal Kauffman-bracket operators (thickness one).
-/

namespace AJConjecture

/-- `W` is the doubled word of `G` (read from `n` thin strands) with the band beads `Bs`
inserted, in the order of the word. -/
inductive IsoBeaded : ℕ → MorseWord → MorseWord → List MorseWord → Prop
  | nil (n : ℕ) : IsoBeaded n [] [] []
  | letter {n : ℕ} {G W : MorseWord} {Bs : List MorseWord} (l : MorseLetter) :
      IsoBeaded n G W Bs → IsoBeaded n (G ++ [l]) (W ++ morseDoubleLetter l) Bs
  | bead {n : ℕ} {G W : MorseWord} {Bs : List MorseWord} (p : ℕ) (T : MorseWord) :
      IsoBeaded n G W Bs → p < morseOut n G → morseFits 2 T = true → morseOut 2 T = 2 →
      IsoBeaded n G (W ++ morseShiftWord (2 * p) T) (Bs ++ [T])

/-- `L` lists the tangles `Bs` in some order, each one as it is or rotated by `π`. -/
def IsoRotPerm (Bs L : List MorseWord) : Prop :=
  ∃ L' : List MorseWord, L'.Perm Bs ∧ List.Forall₂ (fun a b ↦ b = a ∨ b = isoRot 2 a) L' L

/-- A layer of beads on `m` bands: the tangle `β p` on the band `p`, for `p < m`. -/
def isoLayer (m : ℕ) (β : ℕ → MorseWord) : MorseWord :=
  (List.range m).flatMap fun p ↦ morseShiftWord (2 * p) (β p)

/-- The doubled word of `G` (read from `n` thin strands) with the layer `β k` below its letter
`k` and the layer `β G.length` at the top. -/
def isoSlotWord (n : ℕ) : MorseWord → (ℕ → ℕ → MorseWord) → MorseWord
  | [], β => isoLayer n (β 0)
  | l :: G, β =>
    isoLayer n (β 0) ++ morseDoubleLetter l ++
      isoSlotWord (morseLetterOut n l) G (fun k ↦ β (k + 1))

/-- The beads of `isoSlotWord n G β`, level by level. -/
def isoSlotBeads (n : ℕ) : MorseWord → (ℕ → ℕ → MorseWord) → List MorseWord
  | [], β => (List.range n).map (β 0)
  | l :: G, β =>
    (List.range n).map (β 0) ++ isoSlotBeads (morseLetterOut n l) G (fun k ↦ β (k + 1))

/-- Every slot holds a tangle from two strands to two strands. -/
def IsoSlotValid (β : ℕ → ℕ → MorseWord) : Prop :=
  ∀ k p, morseFits 2 (β k p) = true ∧ morseOut 2 (β k p) = 2

/-- The content of the slot of the segment `x = (k, p, up)` moves to the slot of the next
segment `y`: below the content of that slot when it arrives going up, on top of it when it
arrives going down, rotated when the direction changes. -/
def isoSnowStep (β : ℕ → ℕ → MorseWord) (x y : ℕ × ℕ × Bool) : ℕ → ℕ → MorseWord :=
  let T := β x.1 x.2.1
  let β₀ := Function.update β x.1 (Function.update (β x.1) x.2.1 [])
  let old := β₀ y.1 y.2.1
  let new := match x.2.2, y.2.2 with
    | true, true => T ++ old
    | true, false => old ++ isoRot 2 T
    | false, false => old ++ T
    | false, true => isoRot 2 T ++ old
  Function.update β₀ y.1 (Function.update (β₀ y.1) y.2.1 new)

/-- Without beads the slot word is the doubled word. -/
theorem isoSlotWord_nil (n : ℕ) (G : MorseWord) :
    isoSlotWord n G (fun _ _ ↦ []) = morseDouble G := by
  induction G generalizing n with
  | nil => simp [isoSlotWord, isoLayer, morseShiftWord, morseDouble]
  | cons l G ih =>
    have h0 : isoLayer n (fun _ ↦ []) = [] := by simp [isoLayer, morseShiftWord]
    have h : isoSlotWord n (l :: G) (fun _ _ ↦ []) = isoLayer n (fun _ ↦ []) ++
        morseDoubleLetter l ++ isoSlotWord (morseLetterOut n l) G (fun _ _ ↦ []) := rfl
    rw [h, h0, ih]
    rfl

/-- A doubled letter fits on the doubled strands. -/
private theorem morseDoubleLetter_fits_evacDefs (n e : ℕ) (l : MorseLetter)
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
    have hD : morseDoubleLetter (MorseKind.cross s, i) =
        [(MorseKind.cross s, 2 * i + 1), (MorseKind.cross s, if s then 2 * i + 2 else 2 * i),
          (MorseKind.cross s, if s then 2 * i else 2 * i + 2), (MorseKind.cross s, 2 * i + 1)] := by
      cases s <;> simp [morseDoubleLetter, morseOfBraid, cable, cableGen, List.range_succ]
    rw [hD]
    cases s <;> simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, and_true, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;> omega

/-- A layer of beads fits on the doubled strands and keeps their number. -/
private theorem isoLayer_fits_evacDefs (n e : ℕ) (β : ℕ → MorseWord)
    (hβ : ∀ p, morseFits 2 (β p) = true ∧ morseOut 2 (β p) = 2) :
    ∀ m ≤ n, morseFits (2 * n + e) (isoLayer m β) = true ∧
      morseOut (2 * n + e) (isoLayer m β) = 2 * n + e
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
    have ih := isoLayer_fits_evacDefs n e β hβ m (by omega)
    have hs := morseOut_shift_iso (2 * m) 2 (2 * n + e - 2 * m - 2) (β m) (hβ m).1
    rw [(hβ m).2, show 2 * m + 2 + (2 * n + e - 2 * m - 2) = 2 * n + e by omega] at hs
    have hL : isoLayer (m + 1) β = isoLayer m β ++ morseShiftWord (2 * m) (β m) := by
      simp [isoLayer, List.range_succ, List.flatMap_append]
    rw [hL, morseFits_append, morseOut_append, ih.1, ih.2, hs.1, hs.2]
    exact ⟨rfl, rfl⟩

/-- A slot word fits where the doubled word fits and has the same number of strands at its
end. -/
theorem morseFits_isoSlotWord (n e : ℕ) (G : MorseWord) (β : ℕ → ℕ → MorseWord)
    (hG : morseFits n G = true) (hβ : IsoSlotValid β) :
    morseFits (2 * n + e) (isoSlotWord n G β) = true ∧
      morseOut (2 * n + e) (isoSlotWord n G β) = 2 * morseOut n G + e := by
  induction G generalizing n β with
  | nil => exact isoLayer_fits_evacDefs n e (β 0) (hβ 0) n le_rfl
  | cons l G ih =>
    rw [morseFits_cons] at hG
    have h0 := isoLayer_fits_evacDefs n e (β 0) (hβ 0) n le_rfl
    have hl := morseDoubleLetter_fits_evacDefs n e l hG.1
    have h1 := ih (morseLetterOut n l) (fun k ↦ β (k + 1)) hG.2 (fun k p ↦ hβ (k + 1) p)
    simp only [isoSlotWord, morseFits_append, morseOut_append, h0.1, h0.2, hl.1, hl.2, h1.1,
      h1.2, Bool.and_self, morseOut, true_and]

/-- The identity is a rotated permutation, and rotated permutations compose with
permutations of the beads. -/
theorem isoRotPerm_of_perm {Bs Bs' L : List MorseWord} (h : Bs.Perm Bs') (hL : IsoRotPerm Bs L) :
    IsoRotPerm Bs' L := by
  obtain ⟨L', hp, hf⟩ := hL
  exact ⟨L', hp.trans h, hf⟩

end AJConjecture
