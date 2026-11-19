import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkSwing

/-!
# The core is the long closure of the torus braid read backwards (crux, one strand)

`pairCore r s` closes the conveyor `β = (σ_{r-2} ⋯ σ₀)^s` (`pairRevTorusWord r s`, shifted by
`q = r - 2`) with `q` nested arcs on the left (the strands `0, …, q - 1` of the conveyor), the
open strand `q` (the base point) and one arc on the right (the strand `r - 1`): it is the closure
of `β` cut at the strand `q`, `pairCloseAt r q β` (`pairCloseAt_core`).

The junction words are `pairCloseAt r k β`, `k = q, q - 1, …, 0`; `k = 0` is
`morseLongClosure r β` (`pairCloseAt_zero`). One step (`morseReach_pairCloseAt_step`) swings the
innermost left arc over the conveyor to the right (`morseReach_pairCloseAt_swing`, one `kink`),
which conjugates `β` by `δ̄ = σ_{r-2} ⋯ σ₀`; since `β = δ̄^s` commutes with `δ̄`, the conjugate
reduces to `β` (`morseReach_pairRevTorus_conj`, framed by `morseReach_frame` inside the closure).
All words have writhe `(r - 1)s` and the Kauffman bracket of `T(r, s)`; the rotation numbers go
`r - 3, r - 5, …, -(r - 1)`, one `kink` per step (`SCR/ISO2/tools/reclose.py`, for `(3,4), (3,5),
(4,5), (5,6), (3,7), (4,7)`).
-/

namespace AJConjecture

/-- The core is the closure of the torus braid read backwards, cut at the strand `r - 2`. -/
theorem pairCloseAt_core (r s : ℕ) (hr : 3 ≤ r) :
    pairCloseAt r (r - 2) (pairRevTorusWord r s) = pairCore r s := by
  have h1 : r - 1 - (r - 2) = 1 := by omega
  have h2 : r - 2 ≠ 0 := by omega
  have h3 : r - 2 - 1 = r - 3 := by omega
  have hb : morseShiftWord (r - 2) (morseOfBraid (pairRevTorusWord r s)) =
      phaseTwoBlk (morseWalkL true (r - 2) (r - 1)) s := by
    simp only [morseShiftWord, morseOfBraid, pairRevTorusWord, phaseTwoBlk, morseWalkL,
      List.map_flatten, List.map_replicate, List.map_map]
    congr 2
    refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
    omega
  simp only [pairCloseAt, pairCore, h1, h2, h3, hb, ↓reduceIte, List.range_one, List.map_cons,
    List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, isoU, isoN,
    List.append_assoc, List.cons_append]
  rw [show 2 * (r - 2) + 1 + 0 = 2 * r - 3 by omega, show 2 * (r - 2) - 1 + 0 = 2 * r - 5 by omega]

/-- Cut at the strand `0`, the closure is the long closure. -/
theorem pairCloseAt_zero (m : ℕ) (β : BraidWord) :
    pairCloseAt m 0 β = morseLongClosure m β := by
  have hs : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp only [pairCloseAt, morseLongClosure, List.range_zero, List.map_nil, List.nil_append,
    Nat.sub_zero, Nat.mul_zero, Nat.zero_add, ↓reduceIte, morseShiftWord, hs, List.map_id, isoU,
    isoN]
  congr 2
  refine List.map_congr_left fun j _ ↦ ?_
  rw [Nat.add_comm]

/-- A braid word on `n` strands fits on `n` strands as a Morse word. -/
private theorem morseFits_morseOfBraid_reclose {n : ℕ} {w : BraidWord} (hw : IsOnStrands n w) :
    morseFits n (morseOfBraid w) = true := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    have ih' := ih fun x hx ↦ hw x (List.mem_cons_of_mem _ hx)
    simp only [morseOfBraid, List.map_cons, morseFits_cons] at ih' ⊢
    refine ⟨by simp only [morseKindIn]; omega, ?_⟩
    simpa only [morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel] using ih'

/-- A word of cups adds two strands per cup. -/
private theorem morseOut_map_cup_reclose (n : ℕ) (L : List ℕ) (f : ℕ → MorseLetter)
    (hf : ∀ j, (f j).1 = MorseKind.cup) : morseOut n (L.map f) = n + 2 * L.length := by
  induction L generalizing n with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, morseOut, List.length_cons, morseLetterOut, hf, morseKindOut,
      morseKindIn]
    rw [ih]
    omega

set_option linter.unusedVariables false in
/-- One re-closing step: the cut moves from the strand `k` to the strand `k - 1`. -/
theorem morseReach_pairCloseAt_step {r s k : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (hk : 1 ≤ k)
    (hkr : k ≤ r - 2) :
    MorseReach 1 (pairCloseAt r k (pairRevTorusWord r s))
      (pairCloseAt r (k - 1) (pairRevTorusWord r s)) := by
  have hR : IsOnStrands r (pairRevTorusWord r s) := fun g hg ↦ by
    simp only [pairRevTorusWord, List.mem_flatten, List.mem_replicate] at hg
    obtain ⟨l, ⟨-, rfl⟩, hg⟩ := hg
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    dsimp only
    omega
  have hD : IsOnStrands r (pairDeltaBar r) := fun g hg ↦ by
    simp only [pairDeltaBar, List.mem_map, List.mem_reverse, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    dsimp only
    omega
  have hDi : IsOnStrands r (isoBraidInv (pairDeltaBar r)) := fun g hg ↦ by
    simp only [isoBraidInv, List.mem_map, List.mem_reverse] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact hD x hx
  have hall : IsOnStrands r (pairDeltaBar r ++ pairRevTorusWord r s ++
      isoBraidInv (pairDeltaBar r)) := fun g hg ↦ by
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hD g hg
    · exact hR g hg
    · exact hDi g hg
  have h1 := morseReach_pairCloseAt_swing r k (pairRevTorusWord r s) hk (by omega) hR
  refine morseReach_trans h1 ?_
  have h2 := morseReach_frame r 1 (k - 1) (r - 1 - (k - 1))
    ((List.range (k - 1)).map isoU ++
      (List.range (r - 1 - (k - 1))).map (fun j ↦ isoU (2 * (k - 1) + 1 + j)))
    (if k - 1 = 0 then (List.range (r - 1)).reverse.map (fun j ↦ isoN (j + 1))
     else [isoN (k - 1 - 1)] ++
       (List.range (r - 1 - (k - 1))).reverse.map (fun j ↦ isoN (2 * (k - 1) - 1 + j)) ++
       (List.range (k - 1 - 1)).reverse.map isoN) _ _
    (morseReach_pairRevTorus_conj r s (by omega)) (morseFits_morseOfBraid_reclose hall)
    (by
      rw [morseOut_append, morseOut_map_cup_reclose _ _ _ fun _ ↦ rfl,
        morseOut_map_cup_reclose _ _ _ fun _ ↦ rfl]
      simp only [List.length_range]
      omega)
  exact h2

/-- The core reaches the long closure of the torus braid read backwards. -/
theorem morseReach_pairCore_rev {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairCore r s) (morseLongClosure r (pairRevTorusWord r s)) := by
  have key : ∀ k ≤ r - 2, MorseReach 1 (pairCloseAt r k (pairRevTorusWord r s))
      (pairCloseAt r 0 (pairRevTorusWord r s)) := by
    intro k hk
    induction k with
    | zero => exact morseReach_refl 1 _
    | succ k ih =>
      exact morseReach_trans (morseReach_pairCloseAt_step h hr (by omega) hk) (ih (by omega))
  have := key (r - 2) le_rfl
  rwa [pairCloseAt_core r s hr, pairCloseAt_zero] at this

end AJConjecture
