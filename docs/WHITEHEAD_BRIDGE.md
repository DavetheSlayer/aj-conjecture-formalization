# How the braid of `pairWhiteheadKnot r s h` is identified with Z(T(r,s))

17 November 2026. Package `AJHandoff/TorusKnot/PairKWhD*.lean` (in `lean/Proofs/`, like every
library file cited below).

This document is about which knot the braid represents. That the formal coloured Jones function
and A-polynomial are the conventional invariants of that knot, with matching chirality and
peripheral conventions, is treated in [`MARK_BRIDGE.md`](MARK_BRIDGE.md).

## Short answer

The knot of Theorem T is a closed braid `K_{r,s} = pairWhiteheadKnot r s h` on `2(r−1)s+1`
strands. Lean now proves, without reference to how that braid was found, that its diagram is
equivalent under elementary diagram moves to `whDouble(C)`. Here `C` is the diagram of the
right-handed torus knot `T(r,s)`, and `whDouble` is a general construction on knot diagrams. The
construction produces a band along the diagram, removes the band's framing, and adds a clasp;
Lean proves that the band is untwisted (linking number 0) and that the clasp is negative.

These Lean statements are proved with no `sorry` and standard axioms only, including the
refinement that, for braid companions, the labelling used to compute the band's linking number is
the only one (step (F)). The rest of the chain consists of
definitions and standard facts about diagrams; they are listed below and are not formalized,
because Mathlib has no 3-dimensional topology.

The coloured Jones sequence and the A-polynomial / eigenvalue set in `theoremT` are computed from
the same BraidKnot `pairWhiteheadKnot r s h` (section 4).

## 1. Objects

* **Diagrams.** A *Morse word* is a diagram sliced into horizontal levels and read from the
  bottom up. Each level is a cup (a minimum), a cap (a maximum), or a crossing of two adjacent
  strands with a sign. A *long-knot diagram* is a word that starts and ends on one strand.
  Joining its top end to its bottom end on the right gives a knot diagram.
* **The companion.** `C = braidLongDiagram (torusPairKnot r s h)` is the closed braid
  `(σ₀σ₁⋯σ_{r−2})^s`, cut open in its first column. Its closure is `T(r,s)`; it is right-handed
  because `(cross true)` is the positive crossing (section 3).
* **The Whitehead double of a diagram** (`whDouble`, file `PairKWhDDefs`). For any long-knot
  diagram `D`, `whDouble D` is built from four pieces:
  1. a cup that opens the band and the closing strand;
  2. the *blackboard double* of `D`, in which every strand becomes two parallel strands. These
     are the two edges of a thin band along `D`, and the band carries the blackboard framing
     `w(D)`;
  3. `w(D)` negative full twists of the two edges (`bandUntwist`), where `w(D)` is the oriented
     writhe of `D`;
  4. the clasp `claspWord` and a final cap.

  This definition does not use torus knots, braids, or the word `pairTargetWord`. The oriented
  writhe is defined from all consistent orientations of the diagram (`orientWrithes`). A diagram
  is a *long-knot diagram* (`IsLongKnotDiagram`) if it has exactly one orientation with both ends
  pointing up; equivalently, it has no closed components.

## 2. The chain of identifications

Each step below is marked [Lean] (proved),
[definition] (a modelling choice), or [external] (a published or standard fact that is not
formalized).

**(A) [Lean] The braid closure reaches the band-and-clasp diagram.**
`morseReach_pair_source_target`: the braid of `K_{r,s}`, cut open, is transformed into
`pairTargetWord r s` by a checked list of moves. This was already proved.

**(B) [definition + external] The moves are isotopies.** The moves are those of
`AJConjecture.MorseRule`. Each is an ambient isotopy of long knots with fixed ends, and each
preserves the blackboard framing:
* `zig`: a cup followed by a cap on a shared strand is a straight strand (planar isotopy);
* `r2`, `r3`: the Reidemeister II and III moves;
* `cupSlide`, `capSlide`: a strand that passes entirely over, or entirely under, both legs of a
  minimum or maximum is slid past it (an isotopy);
* `kink`: a positive and a negative curl on the same side cancel (the framed Reidemeister I
  move);
* `exch`: two levels with disjoint supports change heights (planar isotopy).

So "reachable" implies "isotopic as framed long knots", and isotopic long knots have isotopic
closures. Lean proves that the oriented writhe, which is the blackboard framing, is unchanged by
every move (`morseWrithe_eq_of_morseReach`). Lean also already proves that every move preserves
the coloured-Jones state sum (`morseOp_eq_of_morseApplyAll`). That "moves are isotopies" is not
formal: it is the elementary direction of Reidemeister's theorem.

**(C) [Lean] The companion's framing.**
`orientWrithes_braidLongDiagram`: a closed braid with one component, cut open, has exactly one
orientation (all braid strands point upward), and its writhe is the braid writhe. Consequently
`C` is a long-knot diagram and its framing is `(r−1)s` (`morseWrithe_torusPairKnot`).

**(D) [Lean] The band-and-clasp diagram is the generic double of `T(r,s)`.**
`whDouble_torusPairKnot`: `whDouble C = pairTargetWord r s`, as an equality of words. The
`2(r−1)s` negative crossings of the target word are exactly the framing correction
`bandUntwist((r−1)s)`. Combining this with (A) gives
`morseReach_pairWhiteheadKnot_whDouble`: the braid of `K_{r,s}`, cut open, reaches
`whDouble C`. The theorem `morseReach_whiteheadTorusKnot_whDouble` gives the same statement for
the library's family `whiteheadTorusKnot k`, that is `r = 2`, `s = 2k+1`; Theorem F is about
these knots, and `pairWhiteheadWord_two` shows they are the same braids.

**(E) [Lean] `whDouble` is an operation on knot types.** `morseReach_whDouble`: if `D` reaches
`D'`, then `whDouble D` reaches `whDouble D'`. The proof combines two facts: the doubled move
list is a move list, and both diagrams receive the same number of correcting twists because the
writhe is invariant. So the double depends only on the framed isotopy class of the companion
diagram, not on the particular diagram `C`. This is fully proved; `#print axioms` lists only
`propext`, `Classical.choice`, `Quot.sound`.

**(F) [Lean] Untwisted and negative clasp.** Both properties are stated in terms of
the word itself:
* *Untwisted.* Linking numbers are defined from crossing signs (`bandLinkings`).
  - `zero_mem_bandLinkings_whBand` [Lean]: for every long-knot diagram `D`, the two edges of the
    band, oriented in parallel along `D`, have linking number 0.
  - `bandLinkings_whBand_braidLongDiagram` [Lean]: for a connected closed braid cut open, this
    labelling is the only one, so the linking number `0` involves no choice.
* *Negative clasp.* `orientStates_clasp_negative` is proved by `decide`. When the band arrives
  with its left edge pointing up, its right edge pointing down, and the closing strand pointing
  up (the orientation of the knot), the clasp has exactly one orientation and its two crossings
  contribute −2, so both are negative. The two crossings are self-crossings of a single
  component, so their sign does not depend on the orientation (`_rev`).
* *One component.* `orientWrithes_whDouble_torusPairKnot` [Lean]: `whDouble C` has
  exactly one orientation, so it is a knot, and its writhe is `2(r−1)s−2`. This equals the
  writhe of the braid.

**(G) [definition + external] The closure of `whDouble D` is the satellite `Wh⁻₀(closure D)`.**
In the closure of `whDouble D`, the closing strand and the clasp arc form the hook that clasps
the end of the band, and the band runs along `closure(D)`. This is the standard picture of a
Whitehead double. For a Whitehead-pattern satellite, two numbers fix the pattern up to isotopy
in the solid torus: the framing of the band and the sign of the clasp. Both are proved in (F):
framing 0, negative clasp. Reading the picture as this satellite is the only remaining
geometric interpretation. It is not formal topology.

**(H) [external] Z(T(r,s)) is Wh⁻₀(T(r,s)) (MARK).** MARK states that Zheng's `Z(K,0)` is the
mirror of Schilder's `D₀(mirror K)`, with preferred framings. Schilder's `D₀` has a positive
clasp, so its mirror has a negative clasp, and the companion is mirrored twice, giving `K`
itself. The source audit G4 (§2) independently reads two negative clasp crossings and
zero-linking framing in Zheng's diagram `WL(0)`. Hence `Z(T(r,s)) = Wh⁻₀(T(r,s))`, the
negative-clasp, untwisted Whitehead double of the right-handed `T(r,s)`, which is the object of
(G). This is a reading of the published pictures, not a formal statement.

**Summary theorem.** `pairWhiteheadKnot_whDouble` [Lean, axiom-clean] collects (A), (C), (D)
and (F) for every admissible pair: reachability to `whDouble C`, `C` a long-knot diagram of
framing `(r−1)s`, `whDouble C` one component of writhe `2(r−1)s−2`, negative clasp.
`whiteheadTorusKnot_whDouble` does the same for Theorem F's family.

## 3. Conventions that are choices

* **Crossing sign.** `(cross true, i)` and the braid letter `(i, true)` are the right-handed
  crossing when both strands point up. This is the library's convention: its bracket gives the
  closure of `σ₀³` the Jones polynomial `t + t³ − t⁴` (right-handed trefoil). So `T(r,s)` is
  right-handed, as T-KNOT requires.
* **Zero framing.** The band's framing is cancelled by `−w(D)` full twists, where `w(D)` is the
  oriented writhe. The resulting linking number 0 is a theorem in (F), not part of the
  definition.
* **Clasp sign.** The clasp is the library's `claspWord`. Its sign, negative, is the theorem in
  (F).
* **Orientation.** The knot is oriented by its input strand pointing up, and the companion `C`
  by its braid strands pointing up. Reversing the orientation of the knot does not change the
  coloured Jones polynomials, because sl₂ colours are self-dual. It sends the eigenvalue pair
  `(M, L)` to `(M⁻¹, L⁻¹)`, which only changes which common eigenline is read. MARK's preferred
  eigenvalue convention `(M, L) = (u⁻¹, v)` is a statement about the marking of the pattern
  exterior and belongs to the geometry package; the formal Theorem T does not use it.
* **Mirror.** No mirror occurs on the formal side. The companion in `whDouble C` is the
  right-handed `T(r,s)`. MARK's double mirror is used only in (H) to read Zheng's picture.

## 4. Jones sequence and eigenvalue set are computed from the same knot

In `AJHandoff/TorusKnot/PairKTheoremT.lean`, `PairTClauses K m` refers to `coloredJones K`,
`eigenvalueSet K` and `AJSquareFree K` for a single argument `K`. `theoremT` instantiates it with
`K = pairWhiteheadKnot r s h`. In `pairTClauses_of_input`:
* the Jones sequence comes from `pairQ_knot_package r s h hT (pairWhiteheadKnot r s h) …`. Its
  first conjunct is `∀ n, laurentToField (coloredJones (pairWhiteheadKnot r s h) n) = pairQFormula …`,
  and its hypotheses are `longKnotOp_pairWhiteheadKnot h`, which uses step (A), and
  `writhe_pairWhiteheadKnot h`;
* the A-polynomial clauses come from `exists_aPolynomial_pair h`, `toComparison_dvd_famBound_pair h`
  and `isCoprime_extraFactor_pair h`. All three are stated for
  `eigenvalueSet (pairWhiteheadKnot r s h)`;
* `coloredJones K` is computed from `K.strands` and `K.word` (Chebyshev-cabled bracket and the
  writhe). `eigenvalueSet K` is computed from `KnotGroup K = PresentedGroup (artinRels K)` with
  `meridian K` and `longitude K`. Both are read off the same structure, so there is one braid
  word and one knot.

The peripheral structure of that knot group is the Whitehead satellite structure over `T(r,s)`
(`isWhSatellite_pairWhiteheadKnot`, already proved).

## 5. Independent numerical evidence (not proofs)

* For `(2,3), (2,5), (2,7), (3,4), (3,5)`, the Jones polynomial of `whDouble C` equals the skein
  prediction for `Wh⁻₀(T(r,s))`:
  `V = t⁻² + (t^{−3/2} − t^{−1/2})·V(C₀)`, where `V(C₀) = (J_{T(r,s)}(3) + 1)/(−t^{1/2} − t^{−1/2})`
  is the Jones polynomial of the 0-framed 2-cable. This prediction would fail for a positive
  clasp, or for any nonzero twisting.
* For `(2,3), (2,5)`, the Jones polynomial of the braid closure of `K_{r,s}` equals that of
  `whDouble C`.
* Regina checks recorded in `PairKBlocks`: for 8 pairs, one component, annulus framing 0,
  companion `T(r,s)`.

Added 18 November 2026 (`scripts/whitehead_double/check_whd_manuscript.py`, input
`lean_words.txt` produced by `lean/tools/WhdWords.lean`; output `check_whd_manuscript.out`, 69
checks, all pass). The braid words are evaluated from the library, not transcribed.

* **Zheng's own formula.** The closed formula `[N] F_N` that Lean proves for the coloured Jones
  function of `K_{r,s}` equals Zheng's printed formula for `WD(T(p,q), 0)` (math/0508138v4,
  (2.7), (2.9) with `r = 0`, and (4.1)), with `t_Zheng = q = T⁴`: exactly at three rational
  points for `N ≤ 6` and the pairs `(2,3), (2,5), (2,7), (3,4), (3,5), (4,5)`, and as an identity
  of rational functions for `N ≤ 4` (`(2,3)`), `N ≤ 3` (`(2,5)`, `(3,4)`), `N ≤ 2` (`(3,5)`).
  Under the same substitution Zheng's (4.1) is the library's formula for the companion (a Lean
  theorem, `pairQ_torusInput`). The comparison fails already at `N = 2` if Zheng's formula is
  taken with one twist `r = ±1`, with the clasp alone mirrored, with the companion alone
  mirrored, or with everything mirrored. So, at the level of the coloured Jones function, the
  formal knot is Zheng's zero-twist double of the same companion with the same clasp, and this
  does not depend on reading his figure. It is a finite check, not a proof for all colours, and
  the coloured Jones function is not known to determine the knot.
* **Untwisted.** The Alexander polynomial of the braid closure, computed from the Burau matrices
  of the braid word, is trivial for the same six pairs (the minor is `t^k` at 40 rational
  points). A Whitehead double with `τ ≠ 0` twists has Alexander polynomial
  `τt² − (2τ+1)t + τ`. This test uses only the braid word and is insensitive to mirror images.
* **The braid printed in the source manuscript.** The 7-strand, 24-crossing braid of the source
  manuscript (`whiteheadTrefoilWord` of the earlier library) is not the word
  `pairWhiteheadWord 2 3` of the current library. They present the same knot for this reason:
  the earlier library (the version accepted by the comparator) proved that the source braid
  reaches the 28-letter word `witnessTargetWord`, and `tools/WhdWords.lean` checks by `decide`
  that `pairTargetWord 2 3 = torusTargetWord 1 = witnessTargetWord`, the diagram
  `whDouble (trefoil)` reached by the current braid. No single library contains both move
  lists. Consistently, the two braids have the same colour-2 polynomial, the value `F_2` printed
  in the source manuscript, and trivial Alexander polynomial.
