import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkWords
import AJHandoff.TorusKnot.PairKIsoParkSnow

/-!
# Stage C by ports: the processed stacks travel back to the ends

All ports except `r - 1` are empty in `pairParkW4`, so the journeys are clean: no stack is met.

* `morseReach_pairParkW4_W5`: the curl stack after the clasp, `cS(w)`, is the top part of the
  port `r - 1 = a_{K*}`; it hops forward through the (empty) ports `a_{K*+1}, …, a_{r-1}` and
  then to the top end (`morseReach_park_hop` with `X` the rest of the stack, then with `X = []`;
  induction on the number of hops, `pairParkA_succ`).
* `morseReach_pairParkW6_W7`: the part before the clasp, `T^C · cS(-w)`, is the bottom part of
  the port `r - 1`; it hops backward through the empty ports `a_{K*-1}, …, a_0 = q`
  (`morseReach_park_hop` read backwards) and joins the bottom stack
  (`morseReach_park_bottom` read backwards, after the bottom curls `cS(w)`).
-/

namespace AJConjecture

/-- The curls after the clasp go to the top end. -/
theorem morseReach_pairParkW4_W5 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW4 r s) (pairParkW5 r s) := by
  obtain ⟨-, hKr, hKA, hKu⟩ := pairParkKs_spec h hr
  have h1 := morseReach_park_cleanToTop h hr _ (pairParkKs r s) rfl hKr [] []
    (pairParkStack5 r s) (isoCurlStack (pairParkWa r s)) (pairParkAt r (pairParkStack4 r s))
    (fun j hj1 hj2 ↦ by
      have hne : pairParkA r s j ≠ r - 1 := fun he ↦ by have := hKu j hj2 he; omega
      simp [pairParkAt, hne])
    (by simp [pairParkAt, hKA, pairParkStack4, pairParkStack5])
  have e : Function.update (pairParkAt r (pairParkStack4 r s)) (pairParkA r s (pairParkKs r s))
      (pairParkStack5 r s) = pairParkAt r (pairParkStack5 r s) := by
    funext c
    rw [hKA]
    by_cases hc : c = r - 1
    · subst hc; simp [pairParkAt]
    · simp [pairParkAt, hc]
  rw [e, List.append_nil] at h1
  exact h1

/-- The twists and the curls before the clasp go to the bottom end. -/
theorem morseReach_pairParkW6_W7 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW6 r s) (pairParkW7 r s) := by
  obtain ⟨hK1, hKr, hKA, hKu⟩ := pairParkKs_spec h hr
  have hA0 := (pairParkA_succ h hr 0).2.1
  have hq1 : r - 2 ≠ r - 1 := by omega
  have hb6 := morseReach_park_bottom r s (isoCurlStack (pairParkWa r s)) []
    (pairParkAt r (pairParkStack5 r s)) hr
  have hb7 := morseReach_park_bottom r s (isoCurlStack (pairParkWa r s) ++
    List.replicate (pairC r s) .t ++ isoCurlStack (-pairParkWa r s)) [] (pairParkAt r [.cs]) hr
  have hj := morseReach_park_cleanToPort h hr _ 0 (pairParkKs r s) rfl hK1 hKr [] []
    (isoCurlStack (pairParkWa r s))
    (List.replicate (pairC r s) .t ++ isoCurlStack (-pairParkWa r s))
    (Function.update (pairParkAt r [.cs]) (r - 2) (isoCurlStack (pairParkWa r s) ++
      List.replicate (pairC r s) .t ++ isoCurlStack (-pairParkWa r s) ++
        pairParkAt r [.cs] (r - 2)))
    (fun i hi1 hi2 ↦ by
      have h1 : pairParkA r s i ≠ r - 2 := (pairParkA_succ h hr i).2.2.2.1 (by omega) (by omega)
      have h2 : pairParkA r s i ≠ r - 1 := fun he ↦ by have := hKu i (by omega) he; omega
      simp [pairParkAt, h1, h2])
    (by simp [hA0, pairParkAt, hq1])
  have e : Function.update (Function.update (Function.update (pairParkAt r [.cs]) (r - 2)
      (isoCurlStack (pairParkWa r s) ++ List.replicate (pairC r s) .t ++
        isoCurlStack (-pairParkWa r s) ++ pairParkAt r [.cs] (r - 2)))
      (pairParkA r s 0) (isoCurlStack (pairParkWa r s))) (pairParkA r s (pairParkKs r s))
      (List.replicate (pairC r s) .t ++ isoCurlStack (-pairParkWa r s) ++
        Function.update (pairParkAt r [.cs]) (r - 2) (isoCurlStack (pairParkWa r s) ++
          List.replicate (pairC r s) .t ++ isoCurlStack (-pairParkWa r s) ++
            pairParkAt r [.cs] (r - 2)) (pairParkA r s (pairParkKs r s))) =
      Function.update (pairParkAt r (pairParkStack5 r s)) (r - 2)
        (isoCurlStack (pairParkWa r s) ++ pairParkAt r (pairParkStack5 r s) (r - 2)) := by
    funext c
    rw [hA0, hKA]
    by_cases hc1 : c = r - 1
    · subst hc1; simp [pairParkAt, hq1.symm, pairParkStack5]
    · by_cases hc2 : c = r - 2
      · subst hc2; simp [pairParkAt, hq1]
      · simp [pairParkAt, hc1, hc2]
  rw [e] at hj
  exact morseReach_trans hb6 (morseReach_symm (morseReach_trans hb7 hj))

end AJConjecture
