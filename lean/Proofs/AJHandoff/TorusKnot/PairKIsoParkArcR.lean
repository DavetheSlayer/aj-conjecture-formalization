import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkPorts

/-!
# Stage C by ports: a stack passes the right arc, or reaches the top end

* `morseReach_park_rightArc`: the output band `2q + 1` (index `r - 1`) is closed by the right arc:
  the cap `morseDouble [n_{2q-1}]` (after `n_{q-1}`), the right strand on the band `2q + 2`
  (right of everything), the cup `morseDouble [u_{2q+1}]` whose left leg is the port `r - 1`.
  A stack after the conveyor on the band `2q + 1` reaches the bottom of the port `r - 1`:
  exchange past `n_{q-1}` (`commL`, shift `-2`), turn (`morseReach_isoBead_cap`), down the right
  strand past everything (`commL` with the whole middle of the word on the left), turn
  (`morseReach_isoBead_cup` read backwards), `isoRot_isoRot`.
* `morseReach_park_top`: the output band `2q` (index `q`) is the top end: the stack passes the
  caps (`commL`, `q - 1` left caps and `n_{q-1}` shift it to the band `0`; `n_{2q-1}` lies on
  its right) and joins the top stack.
-/

namespace AJConjecture

/-- The two doubled caps after the conveyor, and the rest. -/
private theorem morseDouble_pairCaps_split_park (r : ℕ) :
    morseDouble (pairCaps r) = morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
      morseDouble ((List.range (r - 3)).reverse.map isoN) := by
  simp only [pairCaps, morseDouble, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The doubled cap of the innermost left arc. -/
private theorem morseFits_capInner_park (r n : ℕ) (hr : 3 ≤ r) (hn : 2 * r - 2 ≤ n) :
    morseFits n (morseDouble [isoN (r - 3)]) = true ∧
      morseOut n (morseDouble [isoN (r - 3)]) = n - 4 := by
  have e : morseDouble [isoN (r - 3)] =
      [(MorseKind.cap, 2 * (r - 3) + 1), (MorseKind.cap, 2 * (r - 3))] := rfl
  rw [e]
  simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
    morseKindOut, and_true]
  omega

/-- The doubled cap of the right arc. -/
private theorem morseFits_capRight_park (r n : ℕ) (hr : 3 ≤ r) (hn : 4 * r - 6 ≤ n) :
    morseFits n (morseDouble [isoN (2 * r - 5)]) = true ∧
      morseOut n (morseDouble [isoN (2 * r - 5)]) = n - 4 ∧
      ∀ l ∈ morseDouble [isoN (2 * r - 5)], 2 * (2 * r - 5) ≤ l.2 := by
  have e : morseDouble [isoN (2 * r - 5)] =
      [(MorseKind.cap, 2 * (2 * r - 5) + 1), (MorseKind.cap, 2 * (2 * r - 5))] := rfl
  rw [e]
  simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
    morseKindOut, and_true, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  omega

/-- A stack passes the right arc and lands at the bottom of the port `r - 1`. -/
theorem morseReach_park_rightArc (r s : ℕ) (bot top L : List IsoBead) (S : ℕ → List IsoBead)
    (hr : 3 ≤ r) :
    MorseReach 1 (pairParkWO r s bot S (r - 1) (isoBeadsWord L) top)
      (pairParkW r s bot (Function.update S (r - 1) (L ++ S (r - 1))) top) := by
  have hT := morseFits_isoBeadsWord L 0
  have hR := isoRot_fits (isoBeadsWord L) 2 hT.1
  rw [hT.2] at hR
  have hP := morseFits_portW_all_park r S (List.range r) (fun c hc ↦ List.mem_range.1 hc) hr
  have hV := morseDouble_pairConv_fits_park r s (4 * r - 1) hr (by omega)
  have hpre := morseOut_park_prefix r bot hr
  have hu0 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s)) = 4 * r - 1 := by
    rw [morseOut_append, morseOut_append, hpre, hP.2, hV.2.1]
  -- 1. past the cap of the innermost left arc
  have h1 := morseReach_isoBead_commL 1 (2 * (r - 2 + (r - 1))) 2 3 (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s)) (morseDouble [isoN (r - 3)])
    (morseDouble [isoN (2 * r - 5)] ++ morseDouble ((List.range (r - 3)).reverse.map isoN) ++
      isoBeadsWord top ++ [isoN 1]) hT.1 hT.2
    (morseFits_capInner_park r _ hr (by omega)).1 (by rw [hu0]; omega)
  rw [(morseFits_capInner_park r _ hr (by omega)).2,
    show 2 * (r - 2 + (r - 1)) - 4 = 2 * (2 * r - 5) by omega] at h1
  -- 2. turn around the cap of the right arc
  have h2 := morseReach_isoBead_cap 1 (2 * r - 5) (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)])
    (morseDouble ((List.range (r - 3)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1]) hT.1 hT.2
    (by rw [morseOut_append, hu0, (morseFits_capInner_park r _ hr (by omega)).2]; omega)
  rw [show 2 * (2 * r - 5) + 2 = 4 * r - 8 by omega] at h2
  -- 3. down the right strand: past the cap of the innermost left arc
  have h3 := morseReach_isoBead_commL 1 (4 * r - 4) 2 1 (isoRot 2 (isoBeadsWord L))
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s)) (morseDouble [isoN (r - 3)])
    (morseDouble [isoN (2 * r - 5)] ++ morseDouble ((List.range (r - 3)).reverse.map isoN) ++
      isoBeadsWord top ++ [isoN 1]) hR.1 hR.2
    (morseFits_capInner_park r _ hr (by omega)).1 (by rw [hu0]; omega)
  rw [(morseFits_capInner_park r _ hr (by omega)).2] at h3
  -- 4. past the conveyor
  have hVf := morseDouble_pairConv_fits_park r s (4 * r - 4) hr le_rfl
  have h4 := morseReach_isoBead_commL 1 (4 * r - 4) 2 1 (isoRot 2 (isoBeadsWord L))
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (morseDouble (pairConv r s))
    (morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
      morseDouble ((List.range (r - 3)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1])
    hR.1 hR.2 hVf.1 (by rw [morseOut_append, hpre, hP.2]; omega)
  rw [hVf.2.1] at h4
  -- 5. past the ports
  have hPf := morseFits_portW_park r S (List.range r) (4 * r - 4)
    (fun c hc ↦ by simp at hc; omega)
  have h5 := morseReach_isoBead_commL 1 (4 * r - 4) 2 1 (isoRot 2 (isoBeadsWord L))
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r))
    ((List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
      morseDouble ((List.range (r - 3)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1])
    hR.1 hR.2 hPf.1 (by rw [hpre]; omega)
  rw [hPf.2] at h5
  -- 6. turn around the cup of the right arc
  have hcups : morseDouble (pairCups r) =
      morseDouble ((List.range (r - 2)).map isoU) ++ morseDouble [isoU (2 * r - 3)] := by
    simp only [pairCups, morseDouble, List.flatMap_append]
  have hL0 := morseDouble_cups_fits_park 0 (r - 2) 3 (by omega)
  rw [← cups_zero_park] at hL0
  have h6 := morseReach_symm (morseReach_isoBead_cup 1 (2 * r - 3) (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble ((List.range (r - 2)).map isoU))
    ((List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
      morseDouble ((List.range (r - 3)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2
    (by rw [morseOut_append, morseOut_append, show morseOut 1 [isoU 1] = 2 + 1 from rfl,
      (morseFits_isoBeadsWord bot 1).2, hL0.2]; omega))
  rw [show 2 * (2 * r - 3) + 2 = 4 * r - 4 by omega,
    show 2 * (2 * r - 3) = 2 * (r - 2 + (r - 1)) by omega] at h6
  -- 7. up to the port `r - 1`
  have hA := morseFits_portW_park r S (List.range (r - 1)) (2 * (r - 2 + (r - 1)))
    (fun c hc ↦ by simp at hc; omega)
  have h7 := morseReach_isoBead_commL 1 (2 * (r - 2 + (r - 1))) 2 3 (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r))
    ((List.range (r - 1)).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (morseShiftWord (2 * (r - 2 + (r - 1))) (isoBeadsWord (S (r - 1))) ++
      ((List.range (r - 1 - (r - 1))).map (fun i ↦ r - 1 + 1 + i)).flatMap
        (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
      morseDouble ((List.range (r - 3)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2 hA.1 (by rw [hpre]; omega)
  rw [hA.2] at h7
  rw [pairParkWO, pairParkW, morseDouble_pairCaps_split_park,
    portW_update_split_park r (r - 1) S _ (by omega), isoBeadsWord_append_park,
    morseShiftWord_append]
  rw [portW_split_park r (r - 1) S (by omega)] at h1 h2 h3 h4 h5 h6 ⊢
  rw [hcups] at h1 h2 h3 h4 h5 h7 ⊢
  simp only [List.append_assoc] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans (morseReach_symm h3)
    (morseReach_trans (morseReach_symm h4) (morseReach_trans (morseReach_symm h5)
      (morseReach_trans h6 h7)))))

/-- A stack on the output band of the top end joins the top stack. -/
theorem morseReach_park_top (r s : ℕ) (bot top L : List IsoBead) (S : ℕ → List IsoBead)
    (hr : 3 ≤ r) :
    MorseReach 1 (pairParkWO r s bot S (r - 2) (isoBeadsWord L) top)
      (pairParkW r s bot S (L ++ top)) := by
  have hT := morseFits_isoBeadsWord L 0
  have hP := morseFits_portW_all_park r S (List.range r) (fun c hc ↦ List.mem_range.1 hc) hr
  have hV := morseDouble_pairConv_fits_park r s (4 * r - 1) hr (by omega)
  have hu0 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s)) = 4 * r - 1 := by
    rw [morseOut_append, morseOut_append, morseOut_park_prefix r bot hr, hP.2, hV.2.1]
  have h1 := morseReach_isoBead_commL 1 (2 * (r - 2 + (r - 2))) 2 5 (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s)) (morseDouble [isoN (r - 3)])
    (morseDouble [isoN (2 * r - 5)] ++ morseDouble ((List.range (r - 3)).reverse.map isoN) ++
      isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2 (morseFits_capInner_park r _ hr (by omega)).1 (by rw [hu0]; omega)
  rw [(morseFits_capInner_park r _ hr (by omega)).2] at h1
  have hu1 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)]) = 4 * r - 5 := by
    rw [morseOut_append, hu0, (morseFits_capInner_park r _ hr (by omega)).2]; omega
  have hn2 := morseFits_capRight_park r (4 * r - 5) hr (by omega)
  have h2 := morseReach_isoBead_commR 1 (2 * (r - 2 + (r - 2)) - 4) 2 (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)]) (morseDouble [isoN (2 * r - 5)])
    (morseDouble ((List.range (r - 3)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2 (fun l hl ↦ by have := hn2.2.2 l hl; omega) (by rw [hu1]; exact hn2.1)
    (by rw [hu1]; omega)
  have hu2 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++
      morseDouble [isoN (2 * r - 5)]) = 4 * r - 9 := by
    rw [morseOut_append, hu1, hn2.2.1]; omega
  have hK := morseDouble_caps_fits_park 0 (r - 3) (2 * (r - 2 + (r - 2)) - 4) (by omega)
  rw [← caps_zero_park] at hK
  have h3 := morseReach_isoBead_commL 1 (2 * (r - 2 + (r - 2)) - 4) 2 1 (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)])
    (morseDouble ((List.range (r - 3)).reverse.map isoN)) (isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2 hK.1 (by rw [hu2]; omega)
  rw [hK.2, show 2 * (r - 2 + (r - 2)) - 4 - 4 * (r - 3) = 0 by omega,
    morseShiftWord_zero_iso] at h3
  rw [pairParkWO, pairParkW, morseDouble_pairCaps_split_park, isoBeadsWord_append_park]
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 h3)

end AJConjecture
