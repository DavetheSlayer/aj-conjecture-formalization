import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkArcL
import AJHandoff.TorusKnot.PairKIsoParkArcR

/-!
# Stage C by ports: one hop along the knot

`morseReach_park_hop`: the top part `L` of the stack of the port `a` travels forward along the
knot to the next port `b = (a + s) mod r`: it leaves the port (`morseReach_park_exit`), rides the
conveyor (`morseReach_park_ride`) and passes the arc closing the output band `b`: a left arc
(`b < q`), the right arc (`b = r - 1`) or the top end (`b = q`). It arrives at the bottom of the
stack of the port `b` (or of the top stack). Read backwards it is the backward hop. Both
snowballs, the clean journeys of `PairKIsoParkBack` and the normalisation use only this lemma
and `morseReach_park_bottom`.
-/

namespace AJConjecture

/-- One hop: the top part of the stack of the port `a` moves to the bottom of the stack of the
next port along the knot, or to the top end. -/
theorem morseReach_park_hop (r s a : ℕ) (bot top X L : List IsoBead) (S : ℕ → List IsoBead)
    (hr : 3 ≤ r) (ha : a < r) (hab : (a + s) % r ≠ a) :
    MorseReach 1 (pairParkW r s bot (Function.update S a (X ++ L)) top)
      (if (a + s) % r = r - 2 then pairParkW r s bot (Function.update S a X) (L ++ top)
       else pairParkW r s bot (Function.update (Function.update S a X) ((a + s) % r)
         (L ++ S ((a + s) % r))) top) := by
  have hT := morseFits_isoBeadsWord L 0
  have h1 := morseReach_park_exit r s a bot top X L S hr ha
  have h2 := morseReach_park_ride r s a bot top (Function.update S a X) (isoBeadsWord L) hr ha
    hT.1 hT.2
  have hlt : (a + s) % r < r := Nat.mod_lt _ (by omega)
  have hS : Function.update S a X ((a + s) % r) = S ((a + s) % r) :=
    Function.update_of_ne hab _ _
  split_ifs with hq
  · have h3 := morseReach_park_top r s bot top L (Function.update S a X) hr
    rw [hq] at h2
    exact morseReach_trans h1 (morseReach_trans h2 h3)
  · rcases Nat.lt_or_ge ((a + s) % r) (r - 2) with hb | hb
    · have h3 := morseReach_park_leftArc r s ((a + s) % r) bot top L (Function.update S a X) hr hb
      rw [hS] at h3
      exact morseReach_trans h1 (morseReach_trans h2 h3)
    · have hb' : (a + s) % r = r - 1 := by omega
      have h3 := morseReach_park_rightArc r s bot top L (Function.update S a X) hr
      rw [← hb'] at h3
      rw [hS] at h3
      exact morseReach_trans h1 (morseReach_trans h2 h3)

end AJConjecture
