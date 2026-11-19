import Mathlib
import AJFamily.Skein.TorusPhaseTwoMacros
import AJFamily.Skein.TorusStripWord
import AJFamily.Skein.TorusTargetWord

/-!
# Phase II: the words between the stages

The words at which the stages of phase II meet: `phaseTwoW0 k` (the strip word cut into blocks) and
`phaseTwoWN k`, `phaseTwoWS k`, `phaseTwoWC k`, `phaseTwoWT k`, `phaseTwoWG k` (after the stages N,
S, C, T, G). Letters are written `u i` (cup), `n i` (cap) and `±i` (crossing); `D = +1 +2 +0 +1` is
the doubled positive crossing of two bands.
-/

namespace AJConjecture

/-- `m` copies of a word, concatenated. -/
def phaseTwoBlk (w : MorseWord) (m : ℕ) : MorseWord := (List.replicate m w).flatten

/-- The doubled positive crossing `D` of the bands `(0,1)` and `(2,3)`. -/
def phaseTwoD : MorseWord :=
  [(.cross true, 1), (.cross true, 2), (.cross true, 0), (.cross true, 1)]

/-- The clasp of the strip after stage C (on the closing arc, strands `4, 5`):
`−4 u6 +5 +5 n4 +4`. -/
def phaseTwoClaspS : MorseWord :=
  [(.cross false, 4), (.cup, 6), (.cross true, 5), (.cross true, 5), (.cap, 4), (.cross true, 4)]

/-- The strip word in blocks: `P · A^n · M' · B'^n · Q'` with `M = M' (+2 +1)`, `B' = (+2 +1) B₀`,
`B = B₀ (+2 +1)`, `Q' = (+2 +1) Q` (the macro left sides). -/
def phaseTwoW0 (k : ℕ) : MorseWord :=
  stripP ++ phaseTwoBlk phaseTwoMacroA_lhs (2 * k - 1) ++ phaseTwoMacroM_lhs ++
    phaseTwoBlk phaseTwoMacroB_lhs (2 * k - 1) ++ phaseTwoMacroQ_lhs

/-- After stage N. -/
def phaseTwoWN (k : ℕ) : MorseWord :=
  stripP ++ phaseTwoBlk phaseTwoMacroA_rhs (2 * k - 1) ++ phaseTwoMacroM_rhs ++
    phaseTwoBlk phaseTwoMacroB_rhs (2 * k - 1) ++ phaseTwoMacroQ_rhs

/-- The A block after the swing. -/
def phaseTwoA1 : MorseWord := [(.cross false, 0), (.cross false, 0), (.cup, 1), (.cross false, 2), (.cap, 1)]

/-- The B block after the swing. -/
def phaseTwoB1 : MorseWord := phaseTwoD ++ [(.cup, 1), (.cross true, 2), (.cap, 1)]

/-- The middle block after the swing. -/
def phaseTwoM1 : MorseWord :=
  [(.cup, 2), (.cup, 3)] ++ phaseTwoD ++ [(.cup, 1), (.cross true, 2), (.cap, 1), (.cup, 6),
    (.cross true, 5), (.cross false, 4), (.cross false, 5)]

/-- The tail block after the swing. -/
def phaseTwoQ1 : MorseWord :=
  phaseTwoD ++ [(.cross false, 2), (.cross false, 2), (.cup, 3), (.cross false, 4), (.cap, 3),
    (.cap, 3), (.cup, 3), (.cross false, 4), (.cap, 3), (.cap, 3), (.cap, 2), (.cup, 1),
    (.cross true, 2), (.cap, 1), (.cap, 1)]

/-- After stage S. -/
def phaseTwoWS (k : ℕ) : MorseWord :=
  [(.cup, 1)] ++ phaseTwoBlk phaseTwoA1 (2 * k) ++ phaseTwoM1 ++
    phaseTwoBlk phaseTwoB1 (2 * k - 1) ++ phaseTwoQ1

/-- After stage C. -/
def phaseTwoWC (k : ℕ) : MorseWord :=
  [(.cup, 1)] ++ List.replicate (4 * k) (.cross false, 0) ++ [(.cup, 2), (.cup, 3)] ++ phaseTwoD ++
    phaseTwoClaspS ++ phaseTwoBlk phaseTwoD (2 * k) ++
    [(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2), (.cap, 1)]

/-- After stage T. -/
def phaseTwoWT (k : ℕ) : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3)] ++ phaseTwoD ++ phaseTwoClaspS ++
    List.replicate (2 * (2 * k + 1)) (.cross false, 4) ++ phaseTwoBlk phaseTwoD (2 * k) ++
    [(.cap, 3), (.cap, 2), (.cap, 1)]

/-- After stage G: the target word with the clasp conjugated by a half twist. -/
def phaseTwoWG (k : ℕ) : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3)] ++ phaseTwoBlk phaseTwoD (2 * k + 1) ++ [(.cap, 3), (.cap, 2)] ++
    List.replicate (2 * (2 * k + 1)) (.cross false, 0) ++
    ((.cross true, 0) :: claspWord ++ [(.cross false, 0)]) ++ [(.cap, 1)]

/-- The strip word in blocks (rotation of the junction letters `+2 +1` into the next block). -/
theorem stripWord_eq_phaseTwoW0 (k : ℕ) : stripWord k = phaseTwoW0 k := by
  set t : MorseWord := [(.cross true, 2), (.cross true, 1)] with ht
  set B₀ : MorseWord := [(.cup, 2), (.cross false, 2), (.cross false, 3), (.cross false, 4), (.cap, 5)]
    with hB₀
  have hA : phaseTwoMacroA_lhs = stripA := by decide
  have hM : stripM = phaseTwoMacroM_lhs ++ t := by decide
  have hB : stripB = B₀ ++ t := by decide
  have hB' : phaseTwoMacroB_lhs = t ++ B₀ := by decide
  have hQ : phaseTwoMacroQ_lhs = t ++ stripQ := by decide
  have rot : ∀ m : ℕ, t ++ (List.replicate m (B₀ ++ t)).flatten =
      (List.replicate m (t ++ B₀)).flatten ++ t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
      rw [ih]
  simp only [stripWord, phaseTwoW0, phaseTwoBlk, hA, hM, hB, hB', hQ, List.append_assoc]
  rw [← List.append_assoc t _ stripQ, rot]
  simp only [List.append_assoc]

/-- The target word in blocks: `morseOfBraid (cable 2 (torusWord k)) = D^(2k+1)`. -/
theorem torusTargetWord_eq_blocks (k : ℕ) :
    torusTargetWord k =
      [(.cup, 1), (.cup, 2), (.cup, 3)] ++ phaseTwoBlk phaseTwoD (2 * k + 1) ++ [(.cap, 3), (.cap, 2)] ++
        List.replicate (2 * (2 * k + 1)) (.cross false, 0) ++ claspWord ++ [(.cap, 1)] := by
  have h : morseOfBraid (cable 2 (torusWord k)) = phaseTwoBlk phaseTwoD (2 * k + 1) := by
    rw [torusWord, cable, morseOfBraid, phaseTwoBlk, List.flatMap_replicate, List.map_flatten,
      List.map_replicate]
    rfl
  rw [torusTargetWord, h]

end AJConjecture
