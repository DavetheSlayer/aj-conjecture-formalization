import Mathlib
import AJHandoff.TorusKnot.PairKWhDClosure
import AJHandoff.TorusKnot.PairKWhDOrientReach
import AJHandoff.TorusKnot.PairKIsotopy

/-!
# The braid closures are the Whitehead doubles of the torus knots

* `whDouble_torusPairKnot`: for the long closure `C` of `(σ_0 ⋯ σ_(r-2))^s`, the generic
  `whDouble C` is literally the library's target word `pairTargetWord r s`: the blackboard
  framing of `C` is the braid writhe `(r - 1)s` (`morseWrithe_braidLongDiagram`), so the
  correction `bandUntwist` is the `2(r - 1)s` negative crossings of the target word.
* `morseReach_pairWhiteheadKnot_whDouble`: the closed braid `pairWhiteheadKnot r s h`, cut open,
  reaches `whDouble` of the cut-open `T(r, s)` (`morseReach_pair_source_target`).
* `morseReach_whiteheadTorusKnot_whDouble`: the same for the library's family
  `whiteheadTorusKnot k` (`r = 2`, `s = 2k + 1`).
* `orientWrithes_whDouble_torusPairKnot`: `whDouble` of the cut-open `T(r, s)` is a long-knot
  diagram (one component) of oriented writhe `2(r - 1)s - 2`, transported from the braid side.
-/

namespace AJConjecture

/-- The writhe of `(σ_0 ⋯ σ_(r-2))^s` is `(r - 1)s`. -/
private theorem writhe_torusPairWord_whd (r s : ℕ) :
    writhe (torusPairWord r s) = (((r - 1) * s : ℕ) : ℤ) := by
  simp only [writhe, torusPairWord, List.map_flatten, List.map_replicate, List.sum_flatten,
    List.sum_replicate, List.map_map, Function.comp_def, ite_true, List.map_const',
    List.length_range]
  push_cast
  ring

/-- The blackboard framing of the cut-open `T(r, s)` is `(r - 1)s`. -/
theorem morseWrithe_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    morseWrithe (braidLongDiagram (torusPairKnot r s h)) = (((r - 1) * s : ℕ) : ℤ) := by
  rw [morseWrithe_braidLongDiagram]
  exact writhe_torusPairWord_whd r s

/-- **The target word is the generic Whitehead double** of the cut-open torus knot. -/
theorem whDouble_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    whDouble (braidLongDiagram (torusPairKnot r s h)) = pairTargetWord r s := by
  rw [whDouble, whBand, morseWrithe_torusPairKnot h, bandUntwist,
    ite_eq_left (Int.natCast_nonneg _), Int.toNat_natCast]
  rfl

/-- **The closed braid `pairWhiteheadKnot r s h`, cut open, reaches the untwisted
negative-clasp Whitehead double of the cut-open `T(r, s)`.** -/
theorem morseReach_pairWhiteheadKnot_whDouble {r s : ℕ} (h : IsTorusPair r s) :
    MorseReach 1 (braidLongDiagram (pairWhiteheadKnot r s h))
      (whDouble (braidLongDiagram (torusPairKnot r s h))) := by
  rw [whDouble_torusPairKnot h]
  exact morseReach_pair_source_target h

/-- The same for the library's family `whiteheadTorusKnot k` (`r = 2`, `s = 2k + 1`). -/
theorem morseReach_whiteheadTorusKnot_whDouble (k : ℕ) (hk : 1 ≤ k)
    (h : IsTorusPair 2 (2 * k + 1)) :
    MorseReach 1 (braidLongDiagram (whiteheadTorusKnot k hk))
      (whDouble (braidLongDiagram (torusPairKnot 2 (2 * k + 1) h))) := by
  rw [whDouble_torusPairKnot h, pairTargetWord_two]
  exact morseReach_trans (morseReach_source_strip k hk) (morseReach_strip_target k hk)

/-- `whDouble` of the cut-open `T(r, s)` has exactly one orientation with both ends upward (one
component), of oriented writhe `2(r - 1)s - 2`: two negative clasp crossings and `2(r - 1)s`
positive twist crossings. -/
theorem orientWrithes_whDouble_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    orientWrithes (whDouble (braidLongDiagram (torusPairKnot r s h))) =
      [2 * (((r - 1) * s : ℕ) : ℤ) - 2] := by
  have hp := orientWrithes_perm_of_morseReach (morseFits_braidLongDiagram _).1
    (morseReach_pairWhiteheadKnot_whDouble h)
  rw [orientWrithes_braidLongDiagram, show (pairWhiteheadKnot r s h).word = pairWhiteheadWord r s
    from rfl, writhe_pairWhiteheadWord h] at hp
  exact (List.singleton_perm.1 hp).symm

/-- `whDouble` of the cut-open `T(r, s)` is a long-knot diagram. -/
theorem isLongKnotDiagram_whDouble_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    IsLongKnotDiagram (whDouble (braidLongDiagram (torusPairKnot r s h))) :=
  ⟨morseFits_of_morseReach_whd (morseReach_pairWhiteheadKnot_whDouble h)
      (morseFits_braidLongDiagram _).1,
    by rw [orientWrithes_whDouble_torusPairKnot h]; rfl⟩

end AJConjecture
