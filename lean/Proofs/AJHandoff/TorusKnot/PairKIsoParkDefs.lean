import Mathlib
import AJHandoff.TorusKnot.PairKIsoEndDefs

/-!
# Stage C by ports: beads, the port word, the stacks

Stage C (`pairWPb → pairWC`) is organised around **ports**. With `q = r - 2`, the band of the core
`pairCore r s = pairCups r ++ pairConv r s ++ pairCaps r` passes the conveyor
`pairConv r s = (walkL q (r-1))^s` on the bands `q, …, 2q + 1`; the *port* `a < r` is the band
`q + a` at level `0` (after the doubled cups, before the doubled conveyor). Every bead of the
word is first moved to a port (`PairKIsoParkNorm*`); the port word `pairParkW` lists the stacks
of beads at the bottom end, at the `r` ports and at the top end.

A stack is a list of bead symbols (`IsoBead`), read in the *band frame* of an upward band:

* `t`: negative full twist `−0 −0`;
* `p`, `n`: positive / negative left curl on the right edge (`isoCurlL s 1`);
* `lp`, `ln`: positive / negative right curl on the left edge (`isoCurlR s 0`, the rotations of
  `p`, `n` by `π`);
* `cs`: the clasp in the band frame, `isoClaspU = isoRot 2 isoClaspS` (the clasp of `pairWPb`
  lies on a downward band; at the port `r - 1` it is read upward);
* `rp`, `ec`: used only in stage E: the travelling curl `isoCurlR true 1` and the end piece
  `−0 · u1 −2 n1 · −0 · claspWord`.

Every bead word is a tangle from two strands to two strands, so stacks need no side conditions.
The orbit of the ports along the knot is `pairParkA r s k = (q + k s) mod r` (`k < r`): the
knot runs from the bottom end through the ports `a_0 = q, a_1, …, a_{r-1}` to the top end, the
right arc (with the clasp) arriving at `a_{K*} = r - 1`, `K* = pairParkKs r s`.
-/

namespace AJConjecture

/-- The beads of stage C (band frame). -/
inductive IsoBead
  | t
  | p
  | n
  | lp
  | ln
  | cs
  | rp
  | ec
  deriving DecidableEq, Repr

/-- The Morse word of a bead (on two strands). -/
def isoBeadWord : IsoBead → MorseWord
  | .t => [isoX false 0, isoX false 0]
  | .p => isoCurlL true 1
  | .n => isoCurlL false 1
  | .lp => isoCurlR true 0
  | .ln => isoCurlR false 0
  | .cs => isoClaspU
  | .rp => isoCurlR true 1
  | .ec => [isoX false 0] ++ isoCurlL false 1 ++ [isoX false 0] ++ claspWord

/-- The Morse word of a stack of beads. -/
def isoBeadsWord (L : List IsoBead) : MorseWord := L.flatMap isoBeadWord

/-- The cups of the core: `q` nested left arcs and the cup of the right arc. -/
def pairCups (r : ℕ) : MorseWord := (List.range (r - 2)).map isoU ++ [isoU (2 * r - 3)]

/-- The conveyor of the core: `s` rounds `walkL q (r - 1)`. -/
def pairConv (r s : ℕ) : MorseWord := phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) s

/-- The caps of the core. -/
def pairCaps (r : ℕ) : MorseWord :=
  [isoN (r - 3), isoN (2 * r - 5)] ++ (List.range (r - 3)).reverse.map isoN

/-- The core is cups, conveyor, caps. -/
theorem pairCore_eq_parts (r s : ℕ) : pairCore r s = pairCups r ++ pairConv r s ++ pairCaps r := by
  simp [pairCore, pairCups, pairConv, pairCaps, List.append_assoc]

/-- The port word: the bottom stack `bot`, the doubled cups, the stack `S a` on the band
`q + a` of every port `a < r`, the doubled conveyor and caps, the top stack, the last cap. -/
def pairParkW (r s : ℕ) (bot : List IsoBead) (S : ℕ → List IsoBead) (top : List IsoBead) :
    MorseWord :=
  [isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
    (List.range r).flatMap (fun a ↦ morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord (S a))) ++
    morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1]

/-- The port orbit: the `k`-th port along the knot, `(q + k s) mod r`. -/
def pairParkA (r s k : ℕ) : ℕ := (r - 2 + k * s) % r

/-- The index `K*` of the port reached by the right arc (`pairParkA r s K* = r - 1`). -/
def pairParkKs (r s : ℕ) : ℕ :=
  ((List.range r).filter (fun k ↦ pairParkA r s k = r - 1)).headD 0

/-- The number of round curls carried to the port `a`: rounds `t ∈ [1, s - 2]` with
`t + 1 + a ≡ 0 (mod r)`. -/
def pairRho (r s a : ℕ) : ℕ := ((List.range (s - 2)).filter (fun t ↦ (t + 2 + a) % r = 0)).length

/-- The stacks of the port normal form `pairParkW1` (band frame, bottom to top):
port `0`: the twist of the last round, the `E - 1` decreasing-run curls (moved from the left leg,
hence `lp`), the `z + 1` increasing-run blocks `t n`, the round curls; ports `1 … q - 1`: the
twist of a right descent (its curls cancelled against the curl of the left climb), the round
curls; port `q`: the round curls; port `r - 1`: the twist before the right arc, the clasp, the
round curls. -/
def pairParkS1 (r s a : ℕ) : List IsoBead :=
  (if a = 0 then
      [.t] ++ List.replicate (pairRunDown r s - 1) .lp ++
        (List.replicate (pairRunUp r s + 1) [IsoBead.t, .n]).flatten
    else if a < r - 2 then [.t]
    else if a = r - 2 then []
    else [.t, .cs]) ++ List.replicate (pairRho r s a) .p

/-- The port normal form of `pairWPb`. -/
def pairParkW1 (r s : ℕ) : MorseWord := pairParkW r s [.t, .n] (pairParkS1 r s) [.p]

/-- The forward snowball after the bottom hop and `k` port hops: the bottom stack and the stacks of
the ports `a_0, …, a_k`. -/
def pairParkSnowF (r s k : ℕ) : List IsoBead :=
  [.t, .n] ++ (List.range (k + 1)).flatMap (fun j ↦ pairParkS1 r s (pairParkA r s j))

/-- The stacks after the forward snowball reached the port `a_k`. -/
def pairParkSF (r s k a : ℕ) : List IsoBead :=
  if a = pairParkA r s k then pairParkSnowF r s k
  else if (List.range k).any (fun j ↦ pairParkA r s j = a) then [] else pairParkS1 r s a

/-- The word after the forward snowball reached the port `a_k`. -/
def pairParkWF (r s k : ℕ) : MorseWord := pairParkW r s [] (pairParkSF r s k) [.p]

/-- The backward snowball after `m ≥ 1` hops from the top end: the stacks of the ports
`a_{r-m+1}, …, a_{r-1}` and the top curl. -/
def pairParkSnowB (r s m : ℕ) : List IsoBead :=
  (List.range (m - 1)).flatMap (fun i ↦ pairParkS1 r s (pairParkA r s (r - m + 1 + i))) ++ [.p]

/-- The stacks after `m ≥ 1` backward hops (on top of the completed forward snowball). -/
def pairParkSB (r s m a : ℕ) : List IsoBead :=
  if a = pairParkA r s (r - m) then pairParkSF r s (pairParkKs r s) a ++ pairParkSnowB r s m
  else if (List.range (m - 1)).any (fun i ↦ pairParkA r s (r - m + 1 + i) = a) then []
  else pairParkSF r s (pairParkKs r s) a

/-- The word after `m ≥ 1` backward hops. -/
def pairParkWB (r s m : ℕ) : MorseWord := pairParkW r s [] (pairParkSB r s m) []

/-- All the beads, collected at the port `r - 1` (band frame, in the order along the knot). -/
def pairParkSigma (r s : ℕ) : List IsoBead :=
  [.t, .n] ++ (List.range r).flatMap (fun k ↦ pairParkS1 r s (pairParkA r s k)) ++ [.p]

/-- Only the port `r - 1` holds beads. -/
def pairParkAt (r : ℕ) (L : List IsoBead) (a : ℕ) : List IsoBead := if a = r - 1 then L else []

/-- Everything at the port `r - 1`. -/
def pairParkW3 (r s : ℕ) : MorseWord := pairParkW r s [] (pairParkAt r (pairParkSigma r s)) []

end AJConjecture
