import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkPorts

/-!
# Stage C by ports: a stack passes a left arc

For `b < q` the output band `q + b` is closed by the left arc `j = q - 1 - b`: the cap
`morseDouble [n_j]` (the cap `n_{q-1}` for `b = 0`, else the `(b + 1)`-st of the remaining left
caps), the left leg on the band `j` (left of the whole conveyor and of all ports) and the cup
`morseDouble [u_j]`, whose right leg is the port `b`.

`morseReach_park_leftArc`: a stack after the conveyor on the band `q + b` reaches the bottom of
the port `b`. Steps (all generic): exchanges past the caps before `n_j` (`commL`/`commR`), the
turn around the doubled cap (`morseReach_isoBead_cap` read backwards: band `j + 1 → j`, rotated),
down the left leg past the doubled conveyor, the port stacks, the doubled cups `u_{q-1} … u_{j+1}`
(`morseReach_isoBead_commR`, the bead is on the left), the turn around the doubled cup
(`morseReach_isoBead_cup`: band `j → j + 1`, rotated back, `isoRot_isoRot`), and exchanges up to
the port area (`commL` past the inner cups, two bands each, `commR` past `u_{2q+1}` and past the
ports `0 … b - 1`).
-/

namespace AJConjecture


/-- The two doubled caps after the conveyor, and the rest. -/
private theorem morseDouble_pairCaps_split_arcL (r : ℕ) :
    morseDouble (pairCaps r) = morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
      morseDouble ((List.range (r - 3)).reverse.map isoN) := by
  simp only [pairCaps, morseDouble, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- A doubled cap, as two letters. -/
private theorem morseDouble_isoN_arcL (p : ℕ) :
    morseDouble [isoN p] = [(MorseKind.cap, 2 * p + 1), (MorseKind.cap, 2 * p)] := rfl

/-- A doubled cup, as two letters. -/
private theorem morseDouble_isoU_arcL (p : ℕ) :
    morseDouble [isoU p] = [(MorseKind.cup, 2 * p), (MorseKind.cup, 2 * p + 1)] := rfl

/-- The rotated stack, back down the left leg `j`, around its cup and up to the port `b`. -/
private theorem morseReach_park_leftLeg (r s b : ℕ) (bot top L : List IsoBead)
    (S : ℕ → List IsoBead) (hr : 3 ≤ r) (hb : b < r - 2) :
    MorseReach 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s) ++
        morseShiftWord (2 * (r - 3 - b)) (isoRot 2 (isoBeadsWord L)) ++
        morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
      (pairParkW r s bot (Function.update S b (L ++ S b)) top) := by
  have hT := morseFits_isoBeadsWord L 0
  have hR := isoRot_fits (isoBeadsWord L) 2 hT.1
  rw [hT.2] at hR
  have hRR : isoRot 2 (isoRot 2 (isoBeadsWord L)) = isoBeadsWord L := by
    have := isoRot_isoRot 2 (isoBeadsWord L) hT.1
    rwa [hT.2] at this
  have hpre := morseOut_park_prefix r bot hr
  have hP := morseFits_portW_all_park r S (List.range r) (fun c hc ↦ List.mem_range.1 hc) hr
  -- the cups split at the cup `u_j`
  have hcups : morseDouble (pairCups r) = morseDouble ((List.range (r - 3 - b)).map isoU) ++
      morseDouble [isoU (r - 3 - b)] ++
      (morseDouble ((List.range b).map fun i ↦ isoU (r - 3 - b + 1 + i)) ++
        morseDouble [isoU (2 * r - 3)]) := by
    rw [pairCups, show r - 2 = (r - 3 - b) + 1 + b by omega, cups_split_park]
    simp only [morseDouble, List.flatMap_append, List.append_assoc]
  have hC0f := morseDouble_cups_fits_park 0 (r - 3 - b) 3 (by omega)
  rw [← cups_zero_park] at hC0f
  have hb3 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot) = 3 := by
    rw [morseOut_append, show morseOut 1 [isoU 1] = 2 + 1 from rfl,
      (morseFits_isoBeadsWord bot 1).2]
  have hu0 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range
      (r - 3 - b)).map isoU))) = 4 * (r - 3 - b) + 3 := by
    rw [morseOut_append, hb3, hC0f.2]; omega
  have hC1f := morseDouble_cups_fits_park (r - 3 - b + 1) b (4 * (r - 3 - b) + 3 + 4) (by omega)
  have hu1 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range
      (r - 3 - b)).map isoU)) ++ morseDouble [isoU (r - 3 - b)]) =
      4 * (r - 3 - b) + 3 + 4 := by
    rw [morseOut_append, hu0, morseDouble_isoU_arcL]
    simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]; omega
  have hU2 : ∀ n, 4 * r - 5 ≤ n → morseFits n (morseDouble [isoU (2 * r - 3)]) = true ∧
      morseOut n (morseDouble [isoU (2 * r - 3)]) = n + 4 := by
    intro n hn
    rw [morseDouble_isoU_arcL]
    simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, and_true]
    omega
  have hW : ∀ l ∈ (morseDouble ((List.range b).map fun i ↦ isoU (r - 3 - b + 1 + i))) ++
      morseDouble [isoU (2 * r - 3)], 2 * (r - 3 - b) + 2 ≤ l.2 := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · have := (mem_morseDouble_cups_park hl).2; omega
    · rw [morseDouble_isoU_arcL] at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only <;> omega
  have hWf : morseFits (morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range
      (r - 3 - b)).map isoU)) ++
      morseDouble [isoU (r - 3 - b)])) ((morseDouble ((List.range b).map fun i ↦ isoU
          (r - 3 - b + 1 + i))) ++ morseDouble [isoU (2 * r - 3)]) = true := by
    rw [hu1, morseFits_append, hC1f.1, hC1f.2, (hU2 _ (by omega)).1]; rfl
  -- 1. up the left leg: past the conveyor, the ports, the inner cups and the right arc cup
  have hV := morseDouble_pairConv_fits_park r s (4 * r - 1) hr (by omega)
  have hu2 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))) =
      4 * r - 1 := by
    rw [morseOut_append, hpre, hP.2]
  have h1 := morseReach_isoBead_commR 1 (2 * (r - 3 - b)) 2 (isoRot 2 (isoBeadsWord L))
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (morseDouble (pairConv r s)) (morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hR.1 hR.2 (fun l hl ↦ by have := (hV.2.2 l hl).1; omega) (by rw [hu2]; exact hV.1)
    (by rw [hu2]; omega)
  have h2 := morseReach_isoBead_commR 1 (2 * (r - 3 - b)) 2 (isoRot 2 (isoBeadsWord L))
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r))
    ((List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hR.1 hR.2 (fun l hl ↦ by obtain ⟨c, -, hc⟩ := mem_portW_park hl; omega)
    (by rw [hpre]; exact hP.1) (by rw [hpre]; omega)
  have h3 := morseReach_isoBead_commR 1 (2 * (r - 3 - b)) 2 (isoRot 2 (isoBeadsWord L))
    ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range (r - 3 - b)).map isoU)) ++
        morseDouble [isoU (r - 3 - b)])
    ((morseDouble ((List.range b).map fun i ↦ isoU (r - 3 - b + 1 + i))) ++ morseDouble [isoU
        (2 * r - 3)])
    ((List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hR.1 hR.2 hW hWf (by rw [hu1]; omega)
  -- 2. around the cup `u_j`
  have h4 := morseReach_isoBead_cup 1 (r - 3 - b) (isoRot 2 (isoBeadsWord L))
    ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range (r - 3 - b)).map isoU)))
    ((morseDouble ((List.range b).map fun i ↦ isoU (r - 3 - b + 1 + i))) ++ morseDouble [isoU
        (2 * r - 3)] ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hR.1 hR.2 (by rw [hu0]; omega)
  rw [hRR] at h4
  -- 3. up the right leg of the arc `j` to the port level
  have hC1f' := morseDouble_cups_fits_park (r - 3 - b + 1) b (2 * (r - 3 - b) + 2) (by omega)
  have h5 := morseReach_isoBead_commL 1 (2 * (r - 3 - b) + 2) 2 (4 * (r - 3 - b) + 3 + 4 -
      (2 * (r - 3 - b) + 2) - 2) (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range (r - 3 - b)).map isoU)) ++
        morseDouble [isoU (r - 3 - b)]) (morseDouble ((List.range b).map fun i ↦ isoU
            (r - 3 - b + 1 + i)))
    (morseDouble [isoU (2 * r - 3)] ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2 hC1f'.1 (by rw [hu1]; omega)
  rw [hC1f'.2, show 2 * (r - 3 - b) + 2 + 4 * b = 2 * (r - 2 + b) by omega] at h5
  have hu3 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range
      (r - 3 - b)).map isoU)) ++ morseDouble [isoU (r - 3 - b)] ++
      (morseDouble ((List.range b).map fun i ↦ isoU (r - 3 - b + 1 + i)))) = 4 * r - 5 := by
    rw [morseOut_append, hu1, hC1f.2]; omega
  have h6 := morseReach_isoBead_commR 1 (2 * (r - 2 + b)) 2 (isoBeadsWord L)
    ([isoU 1] ++ isoBeadsWord bot ++ (morseDouble ((List.range (r - 3 - b)).map isoU)) ++
        morseDouble [isoU (r - 3 - b)] ++ (morseDouble ((List.range b).map fun i ↦ isoU
            (r - 3 - b + 1 + i))))
    (morseDouble [isoU (2 * r - 3)])
    ((List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2 (fun l hl ↦ hW l (List.mem_append_right _ hl) |> fun _ ↦ by
      rw [morseDouble_isoU_arcL] at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only <;> omega)
    (by rw [hu3]; exact (hU2 _ (by omega)).1) (by rw [hu3]; omega)
  -- 4. past the ports on the left of the port `b`
  have hA := morseFits_portW_park r S (List.range b) (2 * (r - 2 + b))
    (fun c hc ↦ by simp at hc; omega)
  have h7 := morseReach_isoBead_commL 1 (2 * (r - 2 + b)) 2 (4 * r - 1 - 2 * (r - 2 + b) - 2)
    (isoBeadsWord L) ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r))
    ((List.range b).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (morseShiftWord (2 * (r - 2 + b)) (isoBeadsWord (S b)) ++
      ((List.range (r - 1 - b)).map (fun i ↦ b + 1 + i)).flatMap
        (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    hT.1 hT.2 hA.1 (by rw [hpre]; omega)
  rw [hA.2] at h7
  rw [pairParkW, portW_update_split_park r b S _ (by omega), isoBeadsWord_append_park,
    morseShiftWord_append]
  rw [portW_split_park r b S (by omega)] at h1 h2 h3 h4 h5 h6 ⊢
  rw [hcups] at h1 h2 h7 ⊢
  simp only [List.append_assoc] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact morseReach_trans (morseReach_symm h1) (morseReach_trans (morseReach_symm h2)
    (morseReach_trans (morseReach_symm h3) (morseReach_trans h4 (morseReach_trans h5
      (morseReach_trans h6 h7)))))

/-- A stack passes the left arc of the output band `q + b` and lands at the bottom of the port
`b`. -/
theorem morseReach_park_leftArc (r s b : ℕ) (bot top L : List IsoBead) (S : ℕ → List IsoBead)
    (hr : 3 ≤ r) (hb : b < r - 2) :
    MorseReach 1 (pairParkWO r s bot S b (isoBeadsWord L) top)
      (pairParkW r s bot (Function.update S b (L ++ S b)) top) := by
  have hT := morseFits_isoBeadsWord L 0
  have hR := isoRot_fits (isoBeadsWord L) 2 hT.1
  rw [hT.2] at hR
  have hRR : isoRot 2 (isoRot 2 (isoBeadsWord L)) = isoBeadsWord L := by
    have := isoRot_isoRot 2 (isoBeadsWord L) hT.1
    rwa [hT.2] at this
  have hP := morseFits_portW_all_park r S (List.range r) (fun c hc ↦ List.mem_range.1 hc) hr
  have hV := morseDouble_pairConv_fits_park r s (4 * r - 1) hr (by omega)
  have hu0 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s)) = 4 * r - 1 := by
    rw [morseOut_append, morseOut_append, morseOut_park_prefix r bot hr, hP.2, hV.2.1]
  have hD := morseReach_park_leftLeg r s b bot top L S hr hb
  rw [pairParkWO]
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · -- the cap `n_{q-1}` closes the band at once
    have h := morseReach_symm (morseReach_isoBead_cap 1 (r - 3) (isoRot 2 (isoBeadsWord L))
      ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s))
      (morseDouble [isoN (2 * r - 5)] ++ morseDouble ((List.range (r - 3)).reverse.map isoN) ++
        isoBeadsWord top ++ [isoN 1]) hR.1 hR.2 (by rw [hu0]; omega))
    rw [hRR, show 2 * (r - 3) + 2 = 2 * (r - 2 + 0) by omega] at h
    rw [morseDouble_pairCaps_split_arcL] at hD ⊢
    simp only [Nat.sub_zero] at hD
    simp only [List.append_assoc] at h hD ⊢
    exact morseReach_trans h hD
  · -- exchanges past the caps before `n_j`, then the turn
    have hn1 : ∀ n, 2 * r - 2 ≤ n → morseFits n (morseDouble [isoN (r - 3)]) = true ∧
        morseOut n (morseDouble [isoN (r - 3)]) = n - 4 := by
      intro n hn
      rw [morseDouble_isoN_arcL]
      simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
        morseKindOut, and_true]
      omega
    have hn2 : ∀ n, 4 * r - 6 ≤ n → morseFits n (morseDouble [isoN (2 * r - 5)]) = true ∧
        morseOut n (morseDouble [isoN (2 * r - 5)]) = n - 4 := by
      intro n hn
      rw [morseDouble_isoN_arcL]
      simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
        morseKindOut, and_true]
      omega
    have hK : morseDouble ((List.range (r - 3)).reverse.map isoN) =
        morseDouble ((List.range (b - 1)).reverse.map fun i ↦ isoN (r - 3 - b + 1 + i)) ++
        morseDouble [isoN (r - 3 - b)] ++
        morseDouble ((List.range (r - 3 - b)).reverse.map isoN) := by
      rw [show r - 3 = (r - 3 - b) + 1 + (b - 1) by omega, caps_split_park]
      simp only [morseDouble, List.flatMap_append]
      rw [show r - 3 - b + 1 + (b - 1) - b = r - 3 - b by omega]
    have hK1 := morseDouble_caps_fits_park (r - 3 - b + 1) (b - 1) (2 * (r - 2 + b) - 4)
      (by omega)
    have hK1' := morseDouble_caps_fits_park (r - 3 - b + 1) (b - 1) (4 * r - 9) (by omega)
    have h1 := morseReach_isoBead_commL 1 (2 * (r - 2 + b)) 2 (4 * r - 1 - 2 * (r - 2 + b) - 2)
      (isoBeadsWord L)
      ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s)) (morseDouble [isoN (r - 3)])
      (morseDouble [isoN (2 * r - 5)] ++ morseDouble ((List.range (r - 3)).reverse.map isoN) ++
        isoBeadsWord top ++ [isoN 1]) hT.1 hT.2 (hn1 _ (by omega)).1 (by rw [hu0]; omega)
    rw [(hn1 _ (by omega)).2] at h1
    have hu1 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)]) = 4 * r - 5 := by
      rw [morseOut_append, hu0, (hn1 _ (by omega)).2]; omega
    have h2 := morseReach_isoBead_commR 1 (2 * (r - 2 + b) - 4) 2 (isoBeadsWord L)
      ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)]) (morseDouble [isoN (2 * r - 5)])
      (morseDouble ((List.range (r - 3)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1])
      hT.1 hT.2
      (fun l hl ↦ by
        rw [morseDouble_isoN_arcL] at hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> simp only <;> omega)
      (by rw [hu1]; exact (hn2 _ (by omega)).1) (by rw [hu1]; omega)
    have hu2 : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++
        morseDouble [isoN (2 * r - 5)]) = 4 * r - 9 := by
      rw [morseOut_append, hu1, (hn2 _ (by omega)).2]; omega
    rw [hK] at h1 h2
    have h3 := morseReach_isoBead_commL 1 (2 * (r - 2 + b) - 4) 2
      (4 * r - 9 - (2 * (r - 2 + b) - 4) - 2) (isoBeadsWord L)
      ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)])
      (morseDouble ((List.range (b - 1)).reverse.map fun i ↦ isoN (r - 3 - b + 1 + i)))
      (morseDouble [isoN (r - 3 - b)] ++ morseDouble ((List.range (r - 3 - b)).reverse.map isoN) ++
        isoBeadsWord top ++ [isoN 1]) hT.1 hT.2 hK1.1 (by rw [hu2]; omega)
    rw [hK1.2, show 2 * (r - 2 + b) - 4 - 4 * (b - 1) = 2 * (r - 3 - b) + 2 by omega] at h3
    have h4 := morseReach_symm (morseReach_isoBead_cap 1 (r - 3 - b) (isoRot 2 (isoBeadsWord L))
      ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s) ++ morseDouble [isoN (r - 3)] ++ morseDouble [isoN
            (2 * r - 5)] ++
        morseDouble ((List.range (b - 1)).reverse.map fun i ↦ isoN (r - 3 - b + 1 + i)))
      (morseDouble ((List.range (r - 3 - b)).reverse.map isoN) ++ isoBeadsWord top ++ [isoN 1])
      hR.1 hR.2 (by rw [morseOut_append, hu2, hK1'.2]; omega))
    rw [hRR] at h4
    have hW : morseFits (4 * r - 1) (morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
        morseDouble ((List.range (b - 1)).reverse.map fun i ↦ isoN
            (r - 3 - b + 1 + i))) = true := by
      rw [morseFits_append, morseFits_append, morseOut_append, (hn1 _ (by omega)).1,
        (hn1 _ (by omega)).2, (hn2 _ (by omega)).1, (hn2 _ (by omega)).2,
        show 4 * r - 1 - 4 - 4 = 4 * r - 9 by omega, hK1'.1]
      rfl
    have h5 := morseReach_isoBead_commR 1 (2 * (r - 3 - b)) 2 (isoRot 2 (isoBeadsWord L))
      ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
        (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
        morseDouble (pairConv r s))
      (morseDouble [isoN (r - 3)] ++ morseDouble [isoN (2 * r - 5)] ++
        morseDouble ((List.range (b - 1)).reverse.map fun i ↦ isoN (r - 3 - b + 1 + i)))
      (morseDouble [isoN (r - 3 - b)] ++ morseDouble ((List.range (r - 3 - b)).reverse.map isoN) ++
        isoBeadsWord top ++ [isoN 1]) hR.1 hR.2
      (fun l hl ↦ by
        simp only [List.mem_append] at hl
        rcases hl with (hl | hl) | hl
        · rw [morseDouble_isoN_arcL] at hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> simp only <;> omega
        · rw [morseDouble_isoN_arcL] at hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> simp only <;> omega
        · have := (mem_morseDouble_caps_park hl).2; omega)
      (by rw [hu0]; exact hW) (by rw [hu0]; omega)
    rw [morseDouble_pairCaps_split_arcL, hK] at hD ⊢
    simp only [List.append_assoc] at h1 h2 h3 h4 h5 hD ⊢
    exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3
      (morseReach_trans h4 (morseReach_trans (morseReach_symm h5) hD))))

end AJConjecture
