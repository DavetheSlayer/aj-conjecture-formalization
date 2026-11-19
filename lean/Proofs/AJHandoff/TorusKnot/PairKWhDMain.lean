import Mathlib
import AJHandoff.TorusKnot.PairKWhDWellDef
import AJHandoff.TorusKnot.PairKWhDIdent
import AJHandoff.TorusKnot.PairKWhDClasp

/-!
# T-KNOT in diagram form: the braid closures are `Wh⁻₀(T(r, s))`

`pairWhiteheadKnot_whDouble`: for every admissible pair `(r, s)`, with `C` the cut-open diagram of
the closed braid `(σ_0 ⋯ σ_(r-2))^s` (the right-handed `T(r, s)`),

1. the closed braid `pairWhiteheadKnot r s h` (the knot of Theorem T), cut open, reaches
   `whDouble C` by the moves of the checker;
2. `C` is a long-knot diagram of blackboard framing `(r - 1)s`;
3. `whDouble C` is a long-knot diagram (one component) of oriented writhe `2(r - 1)s - 2`;
4. the clasp is negative: in the orientation induced by the knot, its two crossings have oriented
   sign `-1`.

The band of `whDouble C` is untwisted by construction (`-morseWrithe C` full twists); the
crossing-sign statements of untwistedness are `zero_mem_bandLinkings_whBand` (`PairKWhDBand`) and
`bandLinkings_whBand_braidLongDiagram` (`PairKWhDBandTorus`).

`whDouble` is a generic operation on long-knot diagrams that respects the moves
(`morseReach_whDouble`), defined without reference to torus knots (`PairKWhDDefs`). What remains
interpretation (moves = framed isotopy of long knots, long closure = closed braid, conventions
of sign, orientation and mirror against MARK) is listed in `formalization/WHITEHEAD_BRIDGE.md` of the audit repository.
-/

namespace AJConjecture

/-- **T-KNOT, diagram form.** The closed braid `pairWhiteheadKnot r s h` is, up to the moves,
the untwisted negative-clasp Whitehead double of the right-handed torus knot `T(r, s)`. -/
theorem pairWhiteheadKnot_whDouble {r s : ℕ} (h : IsTorusPair r s) :
    MorseReach 1 (braidLongDiagram (pairWhiteheadKnot r s h))
        (whDouble (braidLongDiagram (torusPairKnot r s h))) ∧
      IsLongKnotDiagram (braidLongDiagram (torusPairKnot r s h)) ∧
      morseWrithe (braidLongDiagram (torusPairKnot r s h)) = (((r - 1) * s : ℕ) : ℤ) ∧
      orientWrithes (whDouble (braidLongDiagram (torusPairKnot r s h))) =
        [2 * (((r - 1) * s : ℕ) : ℤ) - 2] ∧
      orientStates (claspWord ++ [(.cap, 1)]) [([true, false, true], 0)] = [([true], -2)] :=
  ⟨morseReach_pairWhiteheadKnot_whDouble h, isLongKnotDiagram_braidLongDiagram _,
    morseWrithe_torusPairKnot h, orientWrithes_whDouble_torusPairKnot h,
    orientStates_clasp_negative⟩

/-- The library's family `whiteheadTorusKnot k` (Theorem F) is, up to the moves, the untwisted
negative-clasp Whitehead double of `T(2, 2k + 1)`. -/
theorem whiteheadTorusKnot_whDouble (k : ℕ) (hk : 1 ≤ k) (h : IsTorusPair 2 (2 * k + 1)) :
    MorseReach 1 (braidLongDiagram (whiteheadTorusKnot k hk))
        (whDouble (braidLongDiagram (torusPairKnot 2 (2 * k + 1) h))) ∧
      (pairWhiteheadKnot 2 (2 * k + 1) h).word = (whiteheadTorusKnot k hk).word ∧
      (pairWhiteheadKnot 2 (2 * k + 1) h).strands = (whiteheadTorusKnot k hk).strands :=
  ⟨morseReach_whiteheadTorusKnot_whDouble k hk h, pairWhiteheadWord_two k hk, pairStrands_two k⟩

end AJConjecture
