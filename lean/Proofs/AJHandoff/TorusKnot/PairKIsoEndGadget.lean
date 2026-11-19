import Mathlib
import AJHandoff.TorusKnot.PairKIsoEndDefs
import AJHandoff.TorusKnot.PairKIsoParkGadget
import AJHandoff.TorusKnot.PairKIsoParkWrap

/-!
# Stage G: the clasp and the twists travel to the top end

`morseReach_pairWC_WG1`: the clasp slides from the right strand along the rest of the knot to the
top end. The trace from its position to the top end makes an **odd** number of turns (the core
traverses the right strand downwards; `SCR/ISO2/tools/parity.py`), so it arrives rotated, as
`isoClaspU = +0 · claspWord · −0`. In port words: `pairWC` is `pairParkW8` (clasp at the port
`r - 1`, read upward; `morseReach_pairParkW8_WC` backwards), and the clasp hops forward through
the empty ports to the top end (`morseReach_park_portToTop`); with all ports empty the port word is
`pairWG1` (`pairParkW_empty`, `isoBeadsWord_replicate_t`).

`morseReach_pairWG1_WG2`: the `2C` negative half twists, a stack at the bottom end, travel along the
whole knot (`morseReach_park_bottomToTop`) and arrive in front of the clasp.

Both proofs are complete modulo the port lemmas.
-/

namespace AJConjecture

/-- The clasp travels to the top end. -/
theorem morseReach_pairWC_WG1 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWC r s) (pairWG1 r s) := by
  have h1 := morseReach_symm (morseReach_pairParkW8_WC h hr)
  have h2 := morseReach_park_portToTop h hr (List.replicate (pairC r s) .t) [] [] [.cs]
  have e1 : pairParkAt r ([] ++ [IsoBead.cs]) = pairParkAt r [.cs] := rfl
  have e2 : pairParkAt r ([] : List IsoBead) = fun _ ↦ [] := by
    funext a; simp [pairParkAt]
  rw [e1, e2, pairParkW_empty] at h2
  have e3 : [isoU 1] ++ isoBeadsWord (List.replicate (pairC r s) .t) ++
      morseDouble (pairCore r s) ++ isoBeadsWord ([IsoBead.cs] ++ []) ++ [isoN 1] =
        pairWG1 r s := by
    have hT := isoBeadsWord_replicate_t (pairC r s)
    simp only [isoBeadsWord, pairC] at hT
    simp only [pairWG1, isoBeadsWord, List.append_nil, List.flatMap_cons, List.flatMap_nil,
      isoBeadWord, hT, pairC]
  rw [e3] at h2
  exact morseReach_trans h1 h2

/-- The twists travel to the top end. -/
theorem morseReach_pairWG1_WG2 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWG1 r s) (pairWG2 r s) := by
  have h1 := morseReach_park_bottomToTop h hr (List.replicate (pairC r s) .t) [.cs]
  rw [pairParkW_empty, pairParkW_empty] at h1
  have e1 : [isoU 1] ++ isoBeadsWord (List.replicate (pairC r s) .t) ++
      morseDouble (pairCore r s) ++ isoBeadsWord [IsoBead.cs] ++ [isoN 1] = pairWG1 r s := by
    have hT := isoBeadsWord_replicate_t (pairC r s)
    simp only [isoBeadsWord, pairC] at hT
    simp only [pairWG1, isoBeadsWord, List.append_nil, List.flatMap_cons, List.flatMap_nil,
      isoBeadWord, hT, pairC]
  have e2 : [isoU 1] ++ isoBeadsWord ([] : List IsoBead) ++ morseDouble (pairCore r s) ++
      isoBeadsWord (List.replicate (pairC r s) .t ++ [IsoBead.cs]) ++ [isoN 1] = pairWG2 r s := by
    have hT := isoBeadsWord_replicate_t (pairC r s)
    simp only [isoBeadsWord, pairC] at hT
    simp only [pairWG2, isoBeadsWord, List.flatMap_append, List.flatMap_nil, List.flatMap_cons,
      List.append_nil, isoBeadWord, hT, pairC, List.append_assoc]
  rw [e1, e2] at h1
  exact h1

end AJConjecture
