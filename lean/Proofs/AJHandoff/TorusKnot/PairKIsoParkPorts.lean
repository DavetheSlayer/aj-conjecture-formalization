import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkRound

/-!
# Stage C by ports: a stack leaves its port and rides the conveyor

`pairParkWI`: the port word with a moving tangle `T` on the band `q + a` above all port stacks
(about to enter the conveyor); `pairParkWO`: with `T` on the band `q + b` after the conveyor
(about to enter the caps).

* `morseReach_park_exit`: the top part `L` of the stack of the port `a` leaves it (exchanges
  past the stacks of the ports `a + 1, …, r - 1`, which lie on bands to its right);
* `morseReach_park_ride`: the moving tangle rides the whole conveyor, from the port `a` to the
  output band `(a + s) mod r` (`morseReach_park_conv` framed by the port word);
* `morseReach_park_bottom`: the bottom stack moves to the bottom of the port `q` (it is on the
  band of the bottom end; exchanges past the doubled cups, the left ones shifting it by two
  bands each).
-/

namespace AJConjecture

/-- The port word with a moving tangle `T` on the band `q + a` above the port stacks. -/
def pairParkWI (r s : ℕ) (bot : List IsoBead) (S : ℕ → List IsoBead) (a : ℕ) (T : MorseWord)
    (top : List IsoBead) : MorseWord :=
  [isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
    (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
    morseShiftWord (2 * (r - 2 + a)) T ++
    morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1]

/-- The port word with a moving tangle `T` on the band `q + b` after the conveyor. -/
def pairParkWO (r s : ℕ) (bot : List IsoBead) (S : ℕ → List IsoBead) (b : ℕ) (T : MorseWord)
    (top : List IsoBead) : MorseWord :=
  [isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
    (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
    morseDouble (pairConv r s) ++ morseShiftWord (2 * (r - 2 + b)) T ++
    morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1]


/-- The top part of a port stack leaves the port. -/
theorem morseReach_park_exit (r s a : ℕ) (bot top X L : List IsoBead) (S : ℕ → List IsoBead)
    (hr : 3 ≤ r) (ha : a < r) :
    MorseReach 1 (pairParkW r s bot (Function.update S a (X ++ L)) top)
      (pairParkWI r s bot (Function.update S a X) a (isoBeadsWord L) top) := by
  rw [pairParkW, pairParkWI, portW_update_split_park r a S _ ha, portW_update_split_park r a S _ ha,
    isoBeadsWord_append_park, morseShiftWord_append]
  set A := (List.range a).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))
  set C := ((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i)).flatMap
    (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))
  have hA := morseFits_portW_all_park r S (List.range a) (fun c hc ↦ by simp at hc; omega) hr
  have hC := morseFits_portW_all_park r S ((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i))
    (fun c hc ↦ by simp at hc; omega) hr
  have hX := morseFits_port_one_park r a X ha hr
  have hu : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++ A ++
      morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord X)) = 4 * r - 1 := by
    rw [morseOut_append, morseOut_append, morseOut_park_prefix r bot hr, hA.2, hX.2]
  have h := morseReach_isoBead_commR 1 (2 * (r - 2 + a)) 2 (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++ A ++
      morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord X)) C
    (morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    (morseFits_isoBeadsWord L 0).1 (morseFits_isoBeadsWord L 0).2
    (fun l hl ↦ by
      obtain ⟨c, hc, hl⟩ := mem_portW_park hl
      simp at hc; omega)
    (by rw [hu]; exact hC.1) (by rw [hu]; omega)
  simpa only [List.append_assoc] using h

/-- The moving tangle rides the conveyor. -/
theorem morseReach_park_ride (r s a : ℕ) (bot top : List IsoBead) (S : ℕ → List IsoBead)
    (T : MorseWord) (hr : 3 ≤ r) (ha : a < r) (hT : morseFits 2 T = true)
    (hTo : morseOut 2 T = 2) :
    MorseReach 1 (pairParkWI r s bot S a T top) (pairParkWO r s bot S ((a + s) % r) T top) := by
  have hP := morseFits_portW_all_park r S (List.range r) (fun c hc ↦ List.mem_range.1 hc) hr
  have h := morseReach_park_conv 1 r a s T
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1]) hr ha hT hTo
    (by rw [morseOut_append, morseOut_park_prefix r bot hr, hP.2]; omega)
  simpa only [pairParkWI, pairParkWO, pairConv, List.append_assoc] using h

/-- The bottom stack moves to the bottom of the port `q`. -/
theorem morseReach_park_bottom (r s : ℕ) (bot top : List IsoBead) (S : ℕ → List IsoBead)
    (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW r s bot S top)
      (pairParkW r s [] (Function.update S (r - 2) (bot ++ S (r - 2))) top) := by
  rw [pairParkW, pairParkW, portW_update_split_park r (r - 2) S _ (by omega), portW_split_park r
      (r - 2) S
    (by omega), isoBeadsWord_append_park, morseShiftWord_append]
  set A := (List.range (r - 2)).flatMap
    (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))
  set C := ((List.range (r - 1 - (r - 2))).map (fun i ↦ r - 2 + 1 + i)).flatMap
    (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))
  have hb := morseFits_isoBeadsWord bot 0
  -- past the doubled left cups
  have hL := morseDouble_cups_fits_park 0 (r - 2) 0 le_rfl
  rw [← cups_zero_park] at hL
  have h1 := morseReach_isoBead_commL 1 0 2 1 (isoBeadsWord bot) [isoU 1]
    (morseDouble ((List.range (r - 2)).map isoU))
    (morseDouble [isoU (2 * r - 3)] ++ A ++ morseShiftWord (2 * (r - 2 + (r - 2)))
      (isoBeadsWord (S (r - 2))) ++ C ++ morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++
      isoBeadsWord top ++ [isoN 1]) hb.1 hb.2 hL.1 rfl
  rw [morseShiftWord_zero_iso, hL.2] at h1
  -- past the doubled cup of the right arc
  have hu2 : morseOut 1 ([isoU 1] ++ morseDouble ((List.range (r - 2)).map isoU)) =
      4 * (r - 2) + 3 := by
    rw [morseOut_append, show morseOut 1 [isoU 1] = 3 from rfl]
    have := (morseDouble_cups_fits_park 0 (r - 2) 3 (by omega)).2
    rw [← cups_zero_park] at this
    rw [this]; omega
  have h2 := morseReach_isoBead_commR 1 (0 + 4 * (r - 2)) 2 (isoBeadsWord bot)
    ([isoU 1] ++ morseDouble ((List.range (r - 2)).map isoU)) (morseDouble [isoU (2 * r - 3)])
    (A ++ morseShiftWord (2 * (r - 2 + (r - 2))) (isoBeadsWord (S (r - 2))) ++ C ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hb.1 hb.2
    (fun l hl ↦ by
      simp only [morseDouble, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        morseDoubleLetter, isoU, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only <;> omega)
    (by rw [hu2]; simp only [morseDouble, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      morseDoubleLetter, isoU, morseFits_cons, morseFits_nil, morseLetterOut, morseKindIn,
      morseKindOut, and_true]; omega)
    (by rw [hu2]; omega)
  -- past the ports on the left of the port `q`
  have hA := morseFits_portW_park r S (List.range (r - 2)) (4 * (r - 2))
    (fun c hc ↦ by simp at hc; omega)
  have hu3 : morseOut 1 ([isoU 1] ++ morseDouble ((List.range (r - 2)).map isoU) ++
      morseDouble [isoU (2 * r - 3)]) = 4 * (r - 2) + 4 + 3 := by
    rw [morseOut_append, hu2]; simp [morseDouble, morseDoubleLetter, isoU, morseOut,
      morseLetterOut, morseKindIn, morseKindOut]
  have h3 := morseReach_isoBead_commL 1 (4 * (r - 2)) 2 5 (isoBeadsWord bot)
    ([isoU 1] ++ morseDouble ((List.range (r - 2)).map isoU) ++ morseDouble [isoU (2 * r - 3)])
    A (morseShiftWord (2 * (r - 2 + (r - 2))) (isoBeadsWord (S (r - 2))) ++ C ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hb.1 hb.2 hA.1 (by rw [hu3])
  rw [hA.2, show 4 * (r - 2) = 2 * (r - 2 + (r - 2)) by ring] at h3
  have hcups : morseDouble (pairCups r) = morseDouble ((List.range (r - 2)).map isoU) ++
      morseDouble [isoU (2 * r - 3)] := by
    rw [pairCups, morseDouble, List.flatMap_append]; rfl
  rw [hcups]
  simp only [List.append_assoc, List.nil_append, isoBeadsWord, List.flatMap_nil,
    Nat.zero_add] at h1 h2 h3 ⊢
  rw [show 4 * (r - 2) = 2 * (r - 2 + (r - 2)) by ring] at h1 h2
  exact morseReach_trans h1 (morseReach_trans h2 h3)

end AJConjecture
