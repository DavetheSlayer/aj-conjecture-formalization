import Mathlib
import AJTwist.Knot.TwKPosMacros
import AJHandoff.TorusKnot.PairKIsoStripDefs
import AJHandoff.TorusKnot.PairKIsoCore

/-!
# The junction words of the band-and-clasp isotopy with a clasp of either sign

`σ = true` is the negative clasp of the library, `σ = false` the positive clasp. All words below
are tangles; the long knot is obtained by putting `u1 +0 · (twists)` (return strand on the left)
or `u1 · (twists)` (return strand on the right) in front.

For `r ≥ 3` (`q = r - 2`):

* `twkStripTail r s σ`: the strip word of the library without its first two letters `u1 +0`, with
  the two Hopf letters of sign `σ` (`twkStHopf`, `twkStFinal`). It is the fence word of
  `twBlocks r s 0 σ` without `u1 +0` (`TwKPosFence`).
* `twkNTail r s σ`: after stage N. Every block is in normal form (`twkBandMid`, band coordinates
  shifted by one), the hook keeps its sign, the tip is the library's `isoFinalNF` preceded by
  `twkTipTw σ` negative full twists of the Hopf pair.
* `twkSTail r s σ`: after the swing of the return strand to the right (the word is
  `u1 · twists · A1 · twkSTail`).
* `twkQBody r s σ`: the tip moved down to the hook (they form the raw clasp bead `twkKRaw σ`,
  which is the clasp `claspSWord σ` by `morseReach_twkKRaw`) and the outer cap of the top-right
  climb moved next to its inner cap. `twkQBody r s σ` is the doubled core
  `morseDouble (pairCore r s)` with beads: `(r - 1) s` blocks `A1` (a negative full twist and a
  negative curl), `(r - 1) s` positive curls and the clasp `claspSWord σ` (`TwKPosBeaded`). The
  knot is `u1 · twists · twkQBody · n1`.

For `r = 2` the same four words `twkStrip2Tail`, `twkN2Tail`, `twkS2Tail`, `twkQ2Body` over the
core `twkCore2 s` (the long closure of `σ₀^s` on two strands). Here the strip is the generic
fence word of `pairBlocks 2 s` (not the older `stripWord` of `AJFamily`).

Checked outside Lean (`SCR/KP/tools/final_words.py`): for `(r, s) ∈ {(2,3), (2,5), (3,4)}`,
`|ℓ| ≤ 2` and `(3,5), (4,5)`, `ℓ = 0`, both `σ`: the fence word of `twBlocks r s 0 σ` is
`u1 +0 · twkStripTail` letter for letter, and the four words with `2ℓ` half twists in front have
the Kauffman-bracket operator (thickness one) of the band-and-clasp word with `2ℓ - 2(r-1)s`
half twists and the clasp of sign `σ`. The Lean definitions were evaluated and agree letter for
letter with the Python words (`SCR/KP/leancheck/EvalWords.lean`).
-/

namespace AJConjecture

/-! ### Strip level -/

/-- The first Hopf block of sign `σ` (`σ = true`: `isoStHopf q r`). -/
def twkStHopf (q r : ℕ) (σ : Bool) : MorseWord :=
  [isoU (2 * q + 3 + 2 * r)] ++ isoBand (2 * q + 1 + 2 * r) (2 * q + 3 + 2 * r) (!σ)

/-- The second Hopf block of sign `σ` with the last two caps (`σ = true`: `isoStFinal`). -/
def twkStFinal (σ : Bool) : MorseWord := isoBand 1 3 (!σ) ++ [isoN 3, isoN 1]

/-- The strip word with clasp sign `σ`, without its first two letters `u1 +0` (`r ≥ 3`). -/
def twkStripTail (r s : ℕ) (σ : Bool) : MorseWord :=
  (List.range (r - 2 - 1)).flatMap (fun i ↦ isoStLC (i + 1)) ++
    isoStLC (r - 2) ++ phaseTwoBlk (isoStDec (r - 2)) (pairRunDown r s - 1) ++
    phaseTwoBlk (isoStInc (r - 2)) (pairRunUp r s + 1) ++ isoStR0 (r - 2) r ++
    twkStHopf (r - 2) r σ ++ phaseTwoBlk (isoStRound (r - 2) r) (s - 2) ++ isoStLast (r - 2) r ++
    isoStTrc (r - 2) ++ (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoStRd (i + 1)) ++
    isoStRd0 ++ twkStFinal σ

/-- For the negative clasp it is the strip word of the library. -/
theorem twkStripTail_true (r s : ℕ) :
    [isoU 1, isoX true 0] ++ twkStripTail r s true = pairStrip r s := by
  simp [twkStripTail, pairStrip, twkStHopf, twkStFinal, isoStHopf, isoStFinal]

/-! ### Stage N -/

/-- The hook of sign `σ` in the band region (`σ = true`: `isoBHopf q r`). -/
def twkBHopf (q r : ℕ) (σ : Bool) : MorseWord :=
  morseShiftWord (2 * q + 2 * r - 1) [isoU 3, isoX true 2, isoX (!σ) 1, isoX false 2]

/-- The band region of the normal form with the hook of sign `σ`. -/
def twkBandMid (r s : ℕ) (σ : Bool) : MorseWord :=
  (List.range (r - 2 - 1)).flatMap (fun i ↦ isoBLC (i + 1)) ++ isoBLC (r - 2) ++
    phaseTwoBlk (isoBDec (r - 2)) (pairRunDown r s - 1) ++
    phaseTwoBlk (isoBInc (r - 2)) (pairRunUp r s + 1) ++ isoBR0 (r - 2) r ++ twkBHopf (r - 2) r σ ++
    phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++ isoBLast (r - 2) r ++ isoBTrc (r - 2) ++
    (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoBRd (i + 1))

/-- The word after stage N without `u1 +0`: three strands (the return strand on the left, the
band on `1, 2`) to one. -/
def twkNTail (r s : ℕ) (σ : Bool) : MorseWord :=
  morseShiftWord 1 (twkBandMid r s σ) ++ [isoX true 0, isoN 1] ++
    morseShiftWord 3 (twkTw (twkTipTw σ)) ++ isoFinalNF

/-- For the negative clasp: the word `pairWN` of the library. -/
theorem twkNTail_true (r s : ℕ) :
    [isoU 1, isoX true 0] ++ twkNTail r s true = pairWN r s := by
  simp [twkNTail, pairWN, twkBandMid, pairBandMid, twkBHopf, isoBHopf, twkTw, twkTipTw,
    morseShiftWord]

/-! ### Stage S -/

/-- The word after stage S without `u1 · A1`: three strands (the band on `0, 1`, the return
strand on the right) to one. -/
def twkSTail (r s : ℕ) (σ : Bool) : MorseWord :=
  twkBandMid r s σ ++ morseShiftWord 4 (twkTw (twkTipTw σ)) ++ morseShiftWord 3 isoXTip ++
    [isoN 2] ++ isoCurlL true 1 ++ [isoN 1]

/-! ### The doubled core with beads -/

/-- The doubled core with beads, between the first cup and the last cap (`r ≥ 3`). -/
def twkQBody (r s : ℕ) (σ : Bool) : MorseWord :=
  phaseTwoA1 ++ (List.range (r - 2 - 1)).flatMap (fun i ↦ isoBLC (i + 1)) ++ isoBLC (r - 2) ++
    phaseTwoBlk (isoBDec (r - 2)) (pairRunDown r s - 1) ++
    phaseTwoBlk (isoBInc (r - 2)) (pairRunUp r s + 1) ++ isoBR0 (r - 2) r ++
    morseShiftWord (2 * (r - 2) + 2 * r) (claspSWord σ) ++
    phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++ isoBLast (r - 2) r ++
    morseShiftWord (4 * (r - 2) - 2) phaseTwoA1 ++ morseDouble [isoN (2 * r - 5)] ++
    (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoBRd (i + 1)) ++ isoCurlL true 1

/-! ### The case `r = 2` -/

/-- The core for `r = 2`: the long closure of `σ₀^s` on two strands. -/
def twkCore2 (s : ℕ) : MorseWord := [isoU 1] ++ List.replicate s (isoX true 0) ++ [isoN 1]

/-- The generic fence word of `twBlocks 2 s 0 σ` without `u1 +0`: the `s - 2` blocks of the
increasing run, round `0`, the hook, `s - 2` rounds, the descent to the disc `0`, the top-right
climb, the second Hopf block. -/
def twkStrip2Tail (s : ℕ) (σ : Bool) : MorseWord :=
  phaseTwoBlk (isoStInc 0) (s - 2) ++ isoStR0 0 2 ++ twkStHopf 0 2 σ ++
    phaseTwoBlk (isoStRound 0 2) (s - 2) ++ (isoBand 0 3 true ++ [isoN 3]) ++
    (isoBand 1 3 true ++ [isoN 1]) ++ twkStFinal σ

/-- The band region of the normal form for `r = 2`, up to the last round. -/
def twkMid2 (s : ℕ) (σ : Bool) : MorseWord :=
  phaseTwoBlk (isoBInc 0) (s - 2) ++ isoBR0 0 2 ++ twkBHopf 0 2 σ ++
    phaseTwoBlk (isoBRound 0 2) (s - 2) ++ phaseTwoD

/-- After stage N, `r = 2`, without `u1 +0`. -/
def twkN2Tail (s : ℕ) (σ : Bool) : MorseWord :=
  morseShiftWord 1 (twkMid2 s σ) ++ [isoX true 0, isoN 1] ++ morseShiftWord 1 phaseTwoA1 ++
    [isoN 2] ++ morseShiftWord 3 (twkTw (twkTipTw σ)) ++ isoFinalNF

/-- After stage S, `r = 2`, without `u1 · A1`. -/
def twkS2Tail (s : ℕ) (σ : Bool) : MorseWord :=
  twkMid2 s σ ++ morseShiftWord 2 phaseTwoA1 ++ [isoN 3] ++
    morseShiftWord 4 (twkTw (twkTipTw σ)) ++ morseShiftWord 3 isoXTip ++ [isoN 2] ++
    isoCurlL true 1 ++ [isoN 1]

/-- The doubled core with beads for `r = 2`, between the first cup and the last cap. -/
def twkQ2Body (s : ℕ) (σ : Bool) : MorseWord :=
  phaseTwoBlk phaseTwoA1 (s - 1) ++ isoBR0 0 2 ++ morseShiftWord 4 (claspSWord σ) ++
    phaseTwoBlk (isoBRound 0 2) (s - 2) ++ phaseTwoD ++ morseShiftWord 2 phaseTwoA1 ++
    morseDouble [isoN 1] ++ isoCurlL true 1

end AJConjecture
