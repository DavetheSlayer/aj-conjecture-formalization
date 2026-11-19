import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkOrbit

/-!
# Stage C by ports: the junction words after the snowballs

When all beads sit at the port `r - 1` (`pairParkW3`), the stack is
`pairParkSigma r s = Lb ++ [cs] ++ La` (`pairParkLb`, `pairParkLa`: the beads met before and
after the clasp along the knot). The processing at the port (`PairKIsoParkProc`) leaves
`T^C · cS(-w) · cs · cS(w)` with `C = (r - 1) s` twists and the signed curl stacks
`cS(±w)` (`isoCurlStack`, `w = pairParkWa r s`). Then:

* `pairParkW5`: `cS(w)` carried forward to the top end (`PairKIsoParkBack`);
* `pairParkW6`: `cS(w)` carried through the return strand to the bottom end (`PairKIsoParkWrap`);
* `pairParkW7`: `T^C · cS(-w)` carried backward to the bottom end;
* `pairParkW8`: the curls cancelled; `pairParkW8` is `pairWC` up to moving the clasp back around
  the cup of the right arc.

Validated outside Lean (`SCR/ISO2/tools/park.py`): for `(3,4), (3,5), (4,5), (5,6), (3,7),
(4,7), (5,7)` the words `pairWPb, pairParkW1, pairParkW3, pairParkW4, …, pairWC` have the same
Kauffman bracket (thickness one) and writhe `2C - 2`.
-/

namespace AJConjecture

/-- The number of twists of a stack. -/
def isoBeadCountT (L : List IsoBead) : ℕ := L.count .t

/-- The writhe of the curls of a stack. -/
def isoBeadWr (L : List IsoBead) : ℤ :=
  ((L.count .p + L.count .lp : ℕ) : ℤ) - ((L.count .n + L.count .ln : ℕ) : ℤ)

/-- A signed stack of right-edge curls: `w` positive curls if `0 ≤ w`, else `-w` negative ones. -/
def isoCurlStack (w : ℤ) : List IsoBead :=
  if 0 ≤ w then List.replicate w.toNat .p else List.replicate (-w).toNat .n

/-- The beads met before the clasp along the knot (band frame). -/
def pairParkLb (r s : ℕ) : List IsoBead :=
  [.t, .n] ++ (List.range (pairParkKs r s)).flatMap (fun k ↦ pairParkS1 r s (pairParkA r s k)) ++
    [.t]

/-- The beads met after the clasp along the knot (band frame). -/
def pairParkLa (r s : ℕ) : List IsoBead :=
  List.replicate (pairRho r s (r - 1)) .p ++
    (List.range (r - 1 - pairParkKs r s)).flatMap
      (fun i ↦ pairParkS1 r s (pairParkA r s (pairParkKs r s + 1 + i))) ++ [.p]

/-- The curl writhe left after the clasp once its twists have crossed. -/
def pairParkWa (r s : ℕ) : ℤ := isoBeadWr (pairParkLa r s) + 2 * (isoBeadCountT (pairParkLa r s))

/-- The processed stack at the port `r - 1`. -/
def pairParkStack4 (r s : ℕ) : List IsoBead :=
  List.replicate (pairC r s) .t ++ isoCurlStack (-pairParkWa r s) ++ [.cs] ++
    isoCurlStack (pairParkWa r s)

/-- After the processing at the port `r - 1`. -/
def pairParkW4 (r s : ℕ) : MorseWord := pairParkW r s [] (pairParkAt r (pairParkStack4 r s)) []

/-- The port stack once the curls after the clasp have left. -/
def pairParkStack5 (r s : ℕ) : List IsoBead :=
  List.replicate (pairC r s) .t ++ isoCurlStack (-pairParkWa r s) ++ [.cs]

/-- The curls after the clasp at the top end. -/
def pairParkW5 (r s : ℕ) : MorseWord :=
  pairParkW r s [] (pairParkAt r (pairParkStack5 r s)) (isoCurlStack (pairParkWa r s))

/-- The same curls at the bottom end (through the return strand). -/
def pairParkW6 (r s : ℕ) : MorseWord :=
  pairParkW r s (isoCurlStack (pairParkWa r s)) (pairParkAt r (pairParkStack5 r s)) []

/-- The twists and the curls before the clasp at the bottom end. -/
def pairParkW7 (r s : ℕ) : MorseWord :=
  pairParkW r s (isoCurlStack (pairParkWa r s) ++ List.replicate (pairC r s) .t ++
    isoCurlStack (-pairParkWa r s)) (pairParkAt r [.cs]) []

/-- All curls cancelled: the twists at the bottom end, the clasp at the port `r - 1`. -/
def pairParkW8 (r s : ℕ) : MorseWord :=
  pairParkW r s (List.replicate (pairC r s) .t) (pairParkAt r [.cs]) []

/-- The beads at the port `r - 1` split at the clasp. -/
theorem pairParkSigma_split {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    pairParkSigma r s = pairParkLb r s ++ [.cs] ++ pairParkLa r s := by
  obtain ⟨hK1, hKr, hKA, -⟩ := pairParkKs_spec h hr
  have hrange : List.range r = List.range (pairParkKs r s) ++ [pairParkKs r s] ++
      (List.range (r - 1 - pairParkKs r s)).map (fun i ↦ pairParkKs r s + 1 + i) := by
    conv_lhs => rw [show r = (pairParkKs r s + 1) + (r - 1 - pairParkKs r s) by omega]
    rw [List.range_add, List.range_succ]
  have hS : pairParkS1 r s (r - 1) = [.t, .cs] ++ List.replicate (pairRho r s (r - 1)) .p := by
    rw [pairParkS1]
    split_ifs <;> first | omega | rfl
  simp only [pairParkSigma, pairParkLb, pairParkLa, hrange, List.flatMap_append,
    List.flatMap_cons, hKA, hS, List.flatMap_map,
    List.append_assoc, List.cons_append, List.nil_append]

end AJConjecture
