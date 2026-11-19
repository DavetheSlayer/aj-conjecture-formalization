# v1 scope: what is proved, what is conditional, what is external

*Note on paths (20 November 2026).* This document was written in the audit repository
(`DavetheSlayer/aj-conjecture-audit`), whose folder `formalization/` is the root of the present
repository: read `formalization/lean` as `lean`, and `V1_SCOPE.md`, `MARK_BRIDGE.md` and the other
notes as files of `docs/`. The paths `handoffs/…` and `formalization/manuscript/…`, and the commits
`78e3873` and `a5005af`, are those of the audit repository. The text below is otherwise unchanged.

17 November 2026. This document reconciles the formal development in `formalization/lean`
(libraries `AJConjecture`, `AJFamily`, `AJHandoff` in the folder `Proofs/`, and the pair
`Solution.lean` / `Challenge.lean`) with the handoff contracts
(`handoffs/2026-11-15-ti-g-mahler/package/THEOREM_CONTRACTS.md`), the follow-up
(`handoffs/2026-11-16-manuscript-lean-interface`) and the manuscript
(`formalization/manuscript/AJ_Whitehead_formal_proof.tex`). It was first committed as `78e3873` (branch
`formalization-family`; the additions of `MARK_BRIDGE.md` as `a5005af`). Scope is
the untwisted family only; twisted Whitehead doubles are not considered anywhere.

File names are those after the cleanup of 18 November 2026, which changed no declaration and no
module name of the libraries: the three libraries moved from `formalization/lean/` into
`formalization/lean/Proofs/` (library files are cited below by their path in that folder, e.g.
`AJFamily/MarkovEquiv.lean`); the release pair `AJRelease.lean` / `AJReleaseChallenge.lean` became
`Solution.lean` / `Challenge.lean` (with `AJRelease/AJReleaseDefs.lean` as `Proofs/SolutionDefs.lean`
and `comparator-release.json` as `comparator.json`); the axiom listings moved to `checks/`; and the
earlier two-theorem challenge `AJChallenge.lean` was removed, both of its theorems being among the
47 of the present challenge.

*Addendum, 20 November 2026.* The twisted Whitehead doubles (every integer twist, both clasp signs,
both companion chiralities; handoff of 18 November) are treated in a fourth library,
`Proofs/AJTwist/`, and in a separate note, [`FOUR_FAMILIES.md`](FOUR_FAMILIES.md). The solution and
the challenge gained two theorems for them, so `comparator.json` now names 49 theorems and the
challenge has 98 modules. Nothing below was changed: this document remains the scope statement of
v1 (the untwisted family), and its counts (47 theorems, 89 challenge modules, 20,034 build jobs,
46,804 reachable constants) are those of 18 November. The 47 statements, the declarations they use
and the three libraries are unchanged since then; of the earlier challenge modules, `C_QAlgSymbolPoly`
gained one declaration (`moebiusSubst`, used only by the new statements) and `C_PairKTheoremT` has a
different import line.

## 0. Outcome

1. **The core AJ discrepancy is kernel-checked, with no hypothesis beyond the pair being
   admissible.** For every coprime `2 ≤ r < s`, the closed braid `β_{r,s}` (explicit word
   `pairWhiteheadWord r s` on `pairStrands r s` strands) violates the weak AJ conjecture as the
   library defines it: in `ℚ(M)[L^{±1}]` (the ring `toComparison` maps to), the extra factor
   `E = L² − (M⁴ − 4M² + 1)L + M⁴` divides the classical limit of every primitive recurrence of its
   coloured Jones function, while every A-polynomial of its knot group is associated to
   `(L − 1)B_{rs}` and is coprime to `E`. The proofs use only `propext`, `Classical.choice` and
   `Quot.sound`. "As the library defines it": that the library's coloured Jones function, knot
   group, eigenvalue set and A-polynomial predicate are the conventional ones is a definition-level
   identification (Section 5, item 2a).
2. **Independence of the conditional material is checked mechanically** (Section 2): following
   every constant in the statements and proofs of the core theorems (85,835 constants) reaches
   none of Zheng's estimates, the JSJ premise, the triangulation data, Bloch–Wigner, the
   hyperbolic measure or Theorem G. Control runs on the conditional theorems do detect their
   premises.
3. **Both invariants concern the same explicit closed braid** (Section 1.1), and the braid closure
   is carried by a kernel-checked sequence of diagram moves to `whDouble C`, a generic untwisted
   negative-clasp Whitehead double of the right-handed `T(r, s)` diagram `C` (Section 1.2). That
   `whDouble C` is the knot `Z(T(r, s))` of the sources is a reading of definitions and figures,
   listed in Section 1.3. That the two formal invariants are the conventional invariants of that
   one knot, with matching chirality and peripheral conventions, is the subject of
   [`MARK_BRIDGE.md`](MARK_BRIDGE.md): it rests on four standard external facts, the conventions
   are calibrated in Lean and against the worked example in Lê's paper, and the refutation is also
   proved in a form that does not depend on the chirality pairing of the two sides
   (`not_ajSquareFree_mirror_pair`).
4. **Zheng's estimates.** Of the two estimates affected by the sign correction, (5.16) is now a
   Lean theorem with no hypothesis, and (5.19) a Lean theorem from Zheng's printed (5.12), which
   does not involve the corrected quantity. The physical diagonal (G-PHYS) is conditional only on
   Zheng's printed estimates that do not involve it (Section 3.1).
5. **Release verification is not yet complete.** The release challenge and solution pass the
   local checks of Section 6, but `lake comparator` needs a Linux sandbox and has not been run on
   them. Full release verification is therefore **not** claimed.

## 1. Core semantic identification

### 1.1 One braid, both invariants

In `theoremT` every clause about the pair `(r, s)` is a clause of `PairTClauses K (r * s)` for the
single record `K = pairWhiteheadKnot r s h`:

* the Jones side uses `coloredJones K : ℤ → ℤ[t^{±1}]` (all integer colours; `Annihilates`
  quantifies over every `n ∈ ℤ`);
* the classical side uses `eigenvalueSet K`, the pairs `(ρ(μ)₀₀, ρ(λ)₀₀)` for representations
  `ρ : KnotGroup K → SL₂(ℂ)` with `ρ(μ)`, `ρ(λ)` upper triangular, where `μ = meridian K`,
  `λ = longitude K`;
* the conclusion `¬ AJSquareFree K` combines the two for the same `K`.

`coloredJones`, `KnotGroup`, `meridian` and `longitude` are functions of the record's strand count
and braid word only (the other fields are proofs). The release statements make this explicit: they
quantify over every `K` with `K.strands = pairStrands r s` and `K.word = pairWhiteheadWord r s`,
and prove existence of such a `K`. For `r = 2` the word is the library's family word
(`release_pairWord_two`: `pairWhiteheadWord 2 (2k+1) = whiteheadTorusWord k` on `4k + 3`
strands), so Theorem T at `r = 2`, Theorem F, the minimal-order theorem and
`not_ajSquareFreeConjecture` (the case `k = 1`) all concern the same braids.

### 1.2 The bridge from the braid to `Z(T(r, s))`

A diagram in the library is a *Morse word*: a knot diagram sliced into levels, each a cup, a cap or
a signed crossing of adjacent strands. A *long-knot diagram* starts and ends on one strand; closing
it on the right gives a knot diagram. The library's diagram moves (`MorseRule`) are: `zig` (a cup
and a cap cancel), `r2`, `r3` (Reidemeister II and III), `cupSlide`, `capSlide` (a strand passes
over or under both legs of an extremum), `kink` (a positive and a negative curl cancel: the framed
Reidemeister I move), `exch` (two levels with disjoint supports change height). `MorseReach 1 D D'`
says that `D'` is obtained from `D` by a finite list of these moves.

The Whitehead double is defined for an arbitrary long-knot diagram `D`, with no reference to torus
knots or braids (`PairKWhDDefs`):

  `whDouble D` = a cup, then the blackboard double of `D` (each strand replaced by two parallel
  strands: a band along `D` carrying the blackboard framing `w(D)`), then `w(D)` negative full
  twists of the two band edges (`bandUntwist`), then the clasp `claspWord`, then a cap,

where `w(D)` is the oriented writhe, computed from the orientations of `D` (`morseWrithe`). The
chain, all steps proved in Lean with standard axioms only:

| Step | Statement | Lean |
|---|---|---|
| A | The closed braid `β_{r,s}`, cut open, reaches the band-and-clasp word `pairTargetWord r s` by diagram moves | `morseReach_pair_source_target` |
| B | The companion diagram `C` = closed braid `(σ_0 ⋯ σ_{r−2})^s` cut open (right-handed `T(r, s)`) is a long-knot diagram with framing `(r − 1)s` | `orientWrithes_braidLongDiagram`, `morseWrithe_torusPairKnot` |
| C | `whDouble C = pairTargetWord r s`, as words | `whDouble_torusPairKnot` |
| D | `whDouble` is an operation on diagram classes: for `D` fitting on one strand (`morseFits 1 D`), `D` reaches `D'` ⇒ `whDouble D` reaches `whDouble D'` (every move, including the framed R1, preserves the oriented writhe) | `morseReach_whDouble`, `morseWrithe_eq_of_morseReach` |
| E | The band is untwisted: its two edges, oriented in parallel, have linking number `0` (linking number defined from crossing signs); for braid companions this is the only labelling | `zero_mem_bandLinkings_whBand`, `bandLinkings_whBand_braidLongDiagram` |
| F | The clasp is negative: entered with the states (up, down, up) of the left band edge, the right band edge and the closing strand, the clasp and final cap have a single orientation with oriented writhe `−2`, so both clasp crossings are negative. That (up, down, up) is the orientation the knot induces there follows from G (one component, input strand upward); it is not stated as a separate lemma | `orientStates_clasp_negative` |
| G | `whDouble C` has one component, of writhe `2(r − 1)s − 2` (the writhe of the braid) | `orientWrithes_whDouble_torusPairKnot` |
| Σ | A, B, C, F, G together for every admissible pair (`pairWhiteheadKnot_whDouble`); for the `r = 2` family `whiteheadTorusKnot k`, the move sequence and the equality of braid records (`whiteheadTorusKnot_whDouble`), the other facts being the case `r = 2` of the former | `pairWhiteheadKnot_whDouble`, `whiteheadTorusKnot_whDouble` |

So: the closed braid on which both invariants are computed is, up to the library's diagram moves,
the generic untwisted negative-clasp double of the right-handed `T(r, s)` diagram. On the group
side, there is a homomorphism from the knot group of `T(r, s)` to the knot group of `β_{r,s}` under
which the meridian and longitude of `β_{r,s}` satisfy the Whitehead pattern relations with the
images of the companion's peripheral words (`isWhSatellite_pairWhiteheadKnot`; the statement does
not assert injectivity or a splitting of the group), and every `SL₂(ℂ)` representation of the
companion group together with matrices satisfying the pattern relations lifts to a representation
of the knot group of `β_{r,s}` (`pairRealizesSatellite`). The coloured bracket identity used by the
Jones side is a consequence of step A (`longKnotOp_pairWhiteheadKnot`), so the Jones computation
passes through the same diagram moves.

For braid companions the untwisting statement is also choice-free: the band over a connected closed
braid has exactly one labelling with both edges running upward, and its linking number is `0`
(`bandLinkings_whBand_braidLongDiagram`).

### 1.3 What the bridge leaves to the reader of the definitions

These are definitions and standard facts, not formalized because Mathlib has no
three-dimensional topology:

1. **The moves are isotopies.** Each `MorseRule` move is an ambient isotopy of framed long knots
   with fixed ends (the elementary direction of Reidemeister's theorem); hence reachable diagrams
   have isotopic closures. Class (E).
2. **The closure of `whDouble D` is the satellite `Wh⁻₀(closure D)`.** In the closure, the
   closing strand and the clasp form the hook around the end of the band, and the band runs along
   the closure of `D`: the standard picture of a Whitehead double. A Whitehead-pattern satellite is
   fixed up to isotopy in the solid torus by the band framing and the clasp sign, and both are the
   Lean theorems E and F. Class (N).
3. **`Z(T(r, s))` of the sources is `Wh⁻₀(T(r, s))`.** MARK: Zheng's `Z(K, 0)` is the mirror of
   Schilder's `D₀(mirror K)` with preferred framings; Schilder's clasp is positive, so the mirror's
   is negative and the companion is mirrored twice. The G4 audit reads two negative clasp crossings
   and zero framing directly in Zheng's figure `WL(0)`. A reading of published figures. Class (N).
4. **Conventions.** `(cross true)` is the right-handed crossing (computed, not a Lean lemma: the
   library's bracket gives the closure of `σ_0³` the Jones polynomial `t + t³ − t⁴`, checked
   independently twice), so `T(r, s)` is right-handed; the knot is
   oriented by its input strand. Reversing the orientation leaves the coloured Jones polynomials
   unchanged and sends `(M, L)` to `(M^{−1}, L^{−1})`. No mirror occurs on the formal side.
5. **The library's invariants are the conventional ones** (Section 5, items 2a and 2b; the bridge,
   its calibration and the chirality-robust form of the refutation are in `MARK_BRIDGE.md`).

Numerical cross-checks (not proofs): for `(2,3), (2,5), (2,7), (3,4), (3,5)` the Jones polynomial
of `whDouble C`, computed by an independent state sum, equals the skein prediction for
`Wh⁻₀(T(r, s))` from the 3-coloured Jones polynomial of `T(r, s)` (a positive clasp or a nonzero
twist breaks the match); Regina checks recorded in `PairKBlocks` give one component, annulus
framing 0 and companion `T(r, s)` for eight pairs.

## 2. Hypothesis audit

The exact statements are in Appendix A. The audit follows every constant occurring in the type or
the proof term of the listed theorems (theorem bodies included), with the tool
`formalization/lean/tools/AuditReach.lean` (run time about 20 seconds). The method
over-approximates dependence; independence also follows directly from the core statements, which
carry no premise among their hypotheses, together with their axiom lists.

| Roots | Constants reached | Watched premises reached |
|---|---|---|
| Core: `theoremT`, `theoremF`, `minimalRecurrence_whiteheadTorusKnot`, `isRecurrencePolynomial_whiteheadTorusKnot_one`, `aPolynomial_pair_associated_famBound`, `not_ajSquareFreeConjecture`, `release_theoremT`, `release_classicalEquality`, `release_minimalRecurrence`, `release_pairWord_two` | 85,835 | `MarkovEquiv` only |
| Bridge: `pairWhiteheadKnot_whDouble`, `whiteheadTorusKnot_whDouble`, `morseReach_whDouble`, `bandLinkings_whBand_braidLongDiagram`, `coloredJones_two_pairWhiteheadKnot_ne` | 53,924 | none |
| MARK: `not_ajSquareFree_mirror_pair`, `isCoprime_extraFactorMirror_pair`, `commute_meridian_longitude`, `map_longitude_eq_one_of_commGroup`, `coloredJones_two_trefoil`, `eigenvalueSet_trefoil_subset`, `mem_eigenvalueSet_trefoil`, `longitude_mul_meridian_pow_torusPairKnot` | 82,201 | `MarkovEquiv` only (through `theoremT`) |
| Control: `geo_phys_of_zhengVerbatim` | 49,965 | `ZhengEstimates`, `ZhengVerbatim`, `ZhengEq512` |
| Control: `pairWhiteheadKnot_not_markovEquiv_of_jsj` | 9,318 | `WhiteheadJSJProp`, `MarkovEquiv` |
| Control: `geo_theoremG` | 72,148 | `ZhengEstimates`, `WhiteheadGluing`, `WhiteheadComplete`, `whiteheadPeripheral`, `blochWigner`, `geoHypMeasure`, `GeoTillmannGroup`, `geoShapeRep` |

Watched: `ZhengEstimates`, `ZhengVerbatim`, `ZhengEq512`, `WhiteheadJSJProp`, `WhiteheadGluing`,
`WhiteheadComplete`, `whiteheadPeripheral`, `blochWigner`, `geoHypMeasure`, `GeoTillmannGroup`,
`geoShapeRep`, `geo_theoremG`, `MarkovEquiv`, `sorryAx`.

`MarkovEquiv` occurs in the core only as the relation named in the distinctness conclusion
(`¬ MarkovEquiv K K'`); it is a definition, not an assumption. No core theorem has a hypothesis
beyond `IsTorusPair r s` (resp. `1 ≤ k`) and the record equalities. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for every core and release theorem.

Hence the AJ discrepancy does not depend on Zheng's estimates, on Markov's theorem, on JSJ theory,
or on the identification of the hyperbolic triangulation. Those enter only the statements that
interpret the result (distinct knot types) or that concern the geometry of `E` (Theorem G).

## 3. Conditional geometry and external identifications

### 3.1 Zheng's estimates (G-PHYS)

Zheng's printed (5.4) has a sign error in `b_{n,i}`; the library uses the corrected sign, proved
right by `geo_reduced_value_eq_zhengDiagonal`. The six conjuncts of `ZhengEstimates a`:

| Conjunct | Involves `b`? | Zheng (math/0508138v4) | Status |
|---|---|---|---|
| Lemma 3.2 (localization) | no | Lemma 3.2, (3.25), p. 9 | cited verbatim |
| Lemma 3.3, `β = −(8a+1)` and `β = 0` | no | Lemma 3.3, (3.29), p. 9; constant (3.34), p. 10 | cited verbatim |
| (5.16) `‖b Ĥ + q∂_qĤ‖ = O(N⁴)` | yes | (5.16), p. 16 | **Lean theorem** `zhengEq516_holds` (no hypothesis) |
| (5.19) `‖b Ĥ‖ = O(N²)` on the window | yes | (5.18)–(5.19), p. 16 | **Lean theorem** `zhengEq519_of_zhengEq512`, from Zheng's `b`-free (5.12) |
| (5.20) `q∂_qĤ = C_{a,N} a_n^{−8a} + O(N²)` | no | (5.20), p. 16, via Lemma 5.2 and Lemma 5.1 | cited verbatim |
| Proposition 4.1 (`A⁺_{a,2}(N,1) ≠ 0`) | no | Prop. 4.1, pp. 11–14 | cited verbatim |

`geo_phys_of_zhengVerbatim` states the two analytic conclusions of G-PHYS (the leading term never
vanishes, and the diagonal divided by the leading term tends to `1`) conditional only on
`ZhengVerbatim a` (Lemma 3.2, Lemma 3.3, (5.12) at odd colours, (5.20), Prop. 4.1, all as printed;
`(5.12)` at odd colours is weaker than what Zheng proves). The remaining clauses of G-PHYS (the
exact chain from the coloured Jones polynomial to Zheng's diagonal) are unconditional clauses of
`geo_theoremG`. The corrected-sign estimates need no new idea: Zheng bounds every summand of `b` in
absolute value, so its sign never enters.

Two slips in Zheng's proofs, neither affecting his statements as used:

* (5.18) "`b = O(N²)` on `0 < n, i, n + i < αN`" is false near `i = 0` (for `i = 1`, `n = N/2`,
  `|b|/N²` grows like `(log N)/2π`); it holds on the window `|n − N/2| + |i − N/4| < N/(8a)`, which
  is all that is used. The window bound `|b| ≤ 4N²` is proved in Lean.
* Lemma 5.2 is stated on the colour window `|2n + 1 − N| < N/(4a)`, while the `(n, i)` window only
  gives `< N/(4a) + 1`. A one-step identity in `n` closes the gap; it is proved in Lean for `Ĥ`
  (used by (5.19)) and written out for `q∂_qĤ` (used by (5.20)) in `ZHENG_CORRECTED_PROOFS.md`,
  Section 7.

Classification: G-PHYS is **conditional in Lean on premises proved externally** (Zheng's printed
lemmas). Numerical checks of all six conjuncts are in the same document (Section 9).

### 3.2 Distinct knot types (Markov, Jones, JSJ)

Proved in Lean: for distinct admissible pairs the closed braids are not Markov equivalent
(`theoremT`, second clause), and their colour-2 coloured Jones polynomials differ
(`coloredJones_two_pairWhiteheadKnot_ne`, no hypothesis beyond admissibility). `MarkovEquiv` is the
equivalence relation on (strand count, word) pairs generated by the braid relations (cancellation,
far commutation, `σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}`), cyclic rotation of the word
(conjugation) and stabilization by `σ_m^{±1}` (`AJFamily/MarkovEquiv.lean`); reading it as Markov
equivalence is a definition-level identification (Section 5, item 2b). Two external routes turn this into distinct knot types:

* **Markov's theorem** (hard direction: closed braids with isotopic closures are Markov
  equivalent; Markov 1936, Birman, *Braids, Links, and Mapping Class Groups*, Thm. 2.3; Traczyk
  1998). Distinct Markov classes then give distinct oriented knot types.
* **Invariance of the coloured Jones polynomial** under isotopy of the closure, together with the
  identification of the library's `coloredJones` with the standard one (the definition interface
  of Section 1.3). This route needs no braid theory.

The JSJ route of the handoff (`pairWhiteheadKnot_not_markovEquiv_of_jsj`,
`pairWhiteheadKnot_knotGroup_not_equiv_of_jsj`) is conditional on `WhiteheadJSJProp`, which bundles
Whitten / Gordon–Luecke, JSJ uniqueness (Jaco–Shalen, Johannson), `KnotGroup` = π₁ of the exterior,
and the satellite identification; its algebraic core (centre and quotient `C_r * C_s` of the torus
knot group, recovery of `(r, s)`) is proved. It is not needed for distinctness given either route
above.

### 3.3 The triangulation

Lean proves: Tillmann's four-tetrahedron gluing and completeness equations have exactly the
positively oriented complete solution `(i, i, i, i)`; the Bloch–Wigner sum is `4G`; the ideal
tetrahedron of shape `i` has hyperbolic volume `G` (for the hyperbolic density); the slice with the
first cusp complete maps onto `E` at `(M, L) = (u, v^{−1})`; the pattern group of the library's
satellite relations maps isomorphically onto Tillmann's `W⁺` group, and the shape representation is
given by explicit `SL₂(ℂ)` matrices.

External (not formalized): that the glued complex is the Whitehead link exterior with its complete
hyperbolic structure, and that its volume is the sum of the tetrahedron volumes (Thurston's notes,
Ch. 4; Tillmann's thesis, Ch. 5; Neumann–Zagier 1985). An independent check on 17 November compared
every formula of `WhiteheadGluing`, `WhiteheadComplete`, `whiteheadPeripheral`, the `W⁺`
presentation and the slice term by term with Tillmann's thesis (pp. 137–149, 161) and found them
correct, with two deliberate choices: completeness is stated with `t² = 1` (the case `t = 1` forces
degenerate shapes), and the slice uses the inverted longitude `v^{−1}`, justified by the G4 marking
notes rather than by Tillmann.

## 4. Scope reconciliation of four claims

| Claim | Where claimed | Lean type (Appendix A) | Source | Verdict |
|---|---|---|---|---|
| Classical equality `A ≐ (L − 1)B_{rs}` for every admissible pair | `HANDOFF_ACCEPTANCE.md` | `aPolynomial_pair_associated_famBound`: for every `A` with `IsAPolynomialOf (eigenvalueSet K) A`, `toComparison A` is associated to `toComparison ((L − 1) B_{rs})` in `ℚ(M)[L^{±1}]`; existence of such `A` is a clause of `PairTClauses` | T-CLASS asks only `A_K ∣ (L − 1)B_m` and coprimality; the follow-up asks for the reverse inclusion | **Matches the claim; stronger than the source.** Equality holds after inverting all nonzero polynomials in `M`, so factors in `M` alone and powers of `L` are not determined. The comparison with the CCGLS A-polynomial is a definition interface (Section 5, item 2a). |
| Exact recurrence order | `HANDOFF_ACCEPTANCE.md` ("the exact minimal recurrence of the family") | `minimalRecurrence_whiteheadTorusKnot`: for the doubles of `T(2, 2k+1)` only, every recurrence polynomial (all integer colours, localized, primitive, minimal `L`-degree) has degree `8k + 8` and classical limit associated to `(L − 1)² E B_{2(2k+1)}`; `k = 1`: `16` and `(L − 1)² E B_6` | Follow-up: general exact orders undetermined in the source; trefoil order 16 and the full factorization had only written proofs | **Correct but must be scoped to `r = 2`.** For `r ≥ 3` nothing beyond existence and `E`-survival is proved or claimed. The wording "of the family" is corrected (Section 7). |
| Gauge and reparametrization laws (I-GAUGE) | `HANDOFF_ACCEPTANCE.md` (outcome list: "gauge, ramification and reparametrization laws") | `det_gauge`; `hasNormalizedIndex_mul_coboundary` (index `+ ord_{z₀} g₀`) and `…_mul_inv_coboundary` (opposite convention, `−`); `hasNormalizedIndex_gauge_of_isJointRegular`; `hasNormalizedIndex_rescale` (`h ↦ a h`, first jet and `c` rescaled together); `hasNormalizedIndex_powerSubst` (`x = a z^k`, `z₀ ≠ 0`); `hasSimpleResidue_ramify` (`z ↦ z₀ + w^e` multiplies the residue by `e`) | I-GAUGE: regular gauges and unramified parameter transports preserve the index, rational gauges preserve it mod `ℤ`, ramification multiplies by `e` | **Narrower than the source.** General unramified meridian coordinates (including `z ↦ 1/z`), regular `h`-dependent coordinate changes, `h ↦ a h + O(h²)` and the constant extension `h = s^e` are not formalized (Section 5, item 10). No downstream theorem uses them. The outcome list is corrected (Section 7). |
| Normalization (G-NORM) | `HANDOFF_ACCEPTANCE.md` ("curve and normalization") | `geo_theoremG`: explicit field isomorphism `ℚ(E) ≅ ℚ(Y² = X³ − X)`, `j = 1728`; the integral closure of the Laurent coordinate ring of `E` is the coordinate ring of the elliptic curve minus four points; the projective model is compact; the `r`-cover has fibres of size 1 exactly over `0, 1, −1, ∞` and 2 elsewhere | G-NORM: the smooth projective normalization is the elliptic curve, a double cover of `ℙ¹_r` branched exactly at `0, ±1, ∞`; acceptance asks for a normalization or the model-uniqueness theorem | **The affine normalization is proved; the projective statement uses an external theorem.** That a one-variable function field has a unique smooth projective model (Hartshorne I.6; Stacks 0BY1) is not in Mathlib. |

The manuscript (`AJ_Whitehead_formal_proof.tex`, draft of 16 November) predates the handoff
library. It covers `r = 2` only and states that "the proof does not compute the recurrence
polynomial or the A-polynomial of `W_k`". That is now an understatement, not an overclaim; the
manuscript must be updated before release to state the order `8k + 8`, the factorization and the
classical equality, and to add Theorem T for all coprime pairs.

## 5. Classification of every outstanding interface

Classes: **(E)** mathematically proved externally (standard or published), not formalized;
**(C)** a Lean statement is conditional on a named premise; **(N)** not yet formally connected
(the Lean objects and the conventional objects are related by a definition-level identification
that is argued in prose, not proved); **(G)** genuine formalization gap (a claimed statement whose
Lean version is missing or narrower).

| # | Interface | Class | What is proved in Lean | What is external, and where |
|---|---|---|---|---|
| 1 | Braid closure `β_{r,s}` = untwisted negative-clasp Whitehead double `Z(T(r, s))` | N (the moves being isotopies: E) | Diagram-move equivalence of the braid closure with the generic `whDouble` of the right-handed `T(r, s)` diagram; `whDouble` well defined on diagram classes; band linking number `0`; negative clasp; one component; a homomorphism from the companion group satisfying the Whitehead peripheral relations, and lifting of companion-and-pattern `SL₂(ℂ)` representations (Section 1.2) | That the moves are isotopies (elementary Reidemeister); that the closure of `whDouble D` is `Wh⁻₀(closure D)` (reading of the diagram; its two determining invariants are proved); that the sources' `Z(T(r, s))` is `Wh⁻₀(T(r, s))` (MARK, G4) |
| 2a | Library definitions of the conjecture = conventional invariants of one knot (`coloredJones` = Lê's coloured Jones function at every integer colour; `KnotGroup`, `meridian`, `longitude` = π₁ of the exterior with meridian and preferred longitude; `eigenvalueSet` and `IsAPolynomialOf` = the boundary eigenvalue set and `(L − 1) A_K`; `AJSquareFree` = implied by Lê's weak AJ conjecture), with the same chirality on both sides | N, reduced to four standard facts (`MARK_BRIDGE.md`, §7) | For every braid knot the longitude commutes with the meridian and is null-homologous (`commute_meridian_longitude`, `map_longitude_eq_one_of_commGroup`); unknot normalisation (`coloredJones_unknot`); calibration on the closure of `σ₀³`: colour-2 value of the right-handed trefoil (`coloredJones_two_trefoil`), eigenvalue set exactly `(L − 1)(L M⁶ + 1) = 0` (`eigenvalueSet_trefoil_subset`, `mem_eigenvalueSet_trefoil`), and `λ μ^{rs}` central for every companion (`longitude_mul_meridian_pow_torusPairKnot`); **the refutation in a form independent of the chirality pairing** (`not_ajSquareFree_mirror_pair`). The seven baseline definition files are those whose verbatim copies the accepted comparator run (8dd21cf) compared, for `not_ajSquareFreeConjecture` only. | X1 Kauffman's state sum of a closed braid is the Temperley–Lieb trace; X2 Artin's presentation of the group of a closed braid with its meridians and parallels (Birman, Thm. 2.2); X3 the definition of the A-polynomial (CCGLS; Lê §3.2) with a three-line lemma; X4 the statement of the conjecture (Lê 2006). The agreement of the chirality of the two sides is established three ways, including Lê's own trefoil example reproduced from the Lean definitions, and is not needed for the refutation. Specialist reading of the seven files is still pending. |
| 2b | Further definitions read as conventional objects: `MarkovEquiv` = Markov equivalence; `geoHypMeasure` = hyperbolic volume (for G-VOL); `GeoMilnorK2` = Milnor K₂ (for G-K2); `blochWigner`, `logMahlerMeasure₂` = the Bloch–Wigner function and the logarithmic Mahler measure; `PairTClauses`, `famB`/`famBound`, `pairWhiteheadWord`, `whiteheadTorusWord` | N | All of them are now in the release challenge (Section 6), which has not yet been run through `lake comparator`; none of them has been comparator-checked yet. | Standard definitions; each is a short explicit formula or generated relation in the files named in Appendix A |
| 3 | Distinct knot types | E | Pairwise non-Markov-equivalence (`theoremT`) and pairwise distinct colour-2 Jones polynomials (`coloredJones_two_pairWhiteheadKnot_ne`) | Markov's theorem (Birman Thm. 2.3) plus item 2b, or isotopy invariance of the coloured Jones polynomial plus item 2a |
| 4 | JSJ distinctness route | C | Conditional theorems on `WhiteheadJSJProp`; algebraic core unconditional | JSJ uniqueness, Whitten / Gordon–Luecke; superseded for distinctness by item 3 |
| 5 | Triangulation = Whitehead link exterior; volume = Σ tetrahedron volumes | E | Gluing/completeness solutions, Bloch–Wigner sum `4G`, ideal tetrahedron volume `G`, slice onto `E`, `W⁺` group isomorphism, shape representation | Thurston's notes Ch. 4; Tillmann Ch. 5; Neumann–Zagier; transcription checked against Tillmann |
| 6 | Marking `(M, L) = (u, v^{−1})` on the slice | N | Pattern group of the library's satellite relations ≅ Tillmann's `W⁺`; slice onto `E` with inverted longitude | G4 peripheral dictionary (handoff `inputs/marking_addenda`) |
| 7 | G-PHYS asymptotics | C | Corrected (5.16), (5.19); exact chain from `coloredJones` of `W_k` to Zheng's diagonal; G-PHYS from `ZhengVerbatim a` | Zheng's printed Lemma 3.2, Lemma 3.3, (5.12), (5.20), Prop. 4.1 (E); one window step for (5.20) written in `ZHENG_CORRECTED_PROOFS.md` |
| 8 | Classical A-polynomial beyond the horizontal localization (vertical factors, powers of `L`) | not claimed | Equality in `ℚ(M)[L^{±1}]` | — |
| 9 | Exact recurrence orders for `r ≥ 3` | not claimed (open) | Existence and `E`-survival only | Undetermined in the source as well |
| 10 | I-GAUGE laws beyond those formalized: general unramified meridian coordinates `w = φ(z)` (including `z ↦ 1/z`), regular `h`-dependent coordinate changes, parameter changes `h ↦ a h + O(h²)`, and the constant extension `h = s^e` (source: `lattice_obstruction.md` §6, items 1, 2 and 5) | G | Integer shift law in both conventions, determinant formula, jointly regular gauges, `h ↦ a h`, `x = a z^k`, ramification `z ↦ z₀ + w^e` | Elementary (the residue of a one-form is invariant under regular changes of coordinate); unused downstream |
| 11 | G-NORM: smooth projective model | E (uniqueness) | Affine normalization, field isomorphism, compact model, branching | Uniqueness of the smooth projective model (Hartshorne I.6; Stacks 0BY1) |
| 12 | T-JETS "jointly invertible companion" | G | Allowed-node conditions (including endpoint units) and both indices `−1/2` at both mixed nodes; the Lean Theorem I needs only these | The joint-invertibility conclusion itself is not stated; nothing in Lean uses it |
| 13 | Release verification by `lake comparator` | pending | Local checks (Section 6) | Requires a Linux sandbox run |

Units with no outstanding interface (formalized as contracted; recorded in `HANDOFF_ACCEPTANCE.md`
with their theorem names): I-INT (`exists_hasNormalizedIndex_int_of_quotient`), I-PART
(`locResidual_partition`), I-NODE (`hasSimpleResidue_locLogJet_of_allowedNode`,
`hasNormalizedIndex_locNodeIndex`), I-SEQ (`seq_theoremS` and the forcing lemmas), I-CTRL (the four
controls, `not_weakLatticeLemma`), I (`oreIrreducible_of_connected`), and every other Theorem T
and Theorem G unit apart from the items in the table (T-KNOT: item 1; T-CLASS, T-AEX, T-AJ:
item 2a; T-DIST: items 2b and 3; T-JETS: item 12; G-NORM: item 11; G-K2, G-MAHLER, G-VOL: items 2b
and 5; G-SHAPE, MARK: item 6; G-PHYS: item 7).

## 6. Release verification status

**The release challenge.** `comparator.json` names 47 theorems; the challenge
(`Challenge.lean` with `Challenge/C_*.lean`) states them with `sorry`, and the
solution `Solution.lean` proves them from the library (`Proofs/`). The 47 theorems (exact statements in
Appendix A.6):

| Group | Theorems |
|---|---|
| Counterexample family (Theorems T and F) | `not_ajSquareFreeConjecture`, `release_theoremT`, `release_classicalEquality`, `release_minimalRecurrence`, `release_pairWord_two` |
| Distinct knot types | `release_coloredJones_two_ne` (with `release_theoremT`'s non-Markov-equivalence clause) |
| Satellite bridge | `release_whDouble` (steps A–G of Section 1.2 for every admissible pair), `morseReach_whDouble`, `morseWrithe_eq_of_morseReach`, `zero_mem_bandLinkings_whBand` |
| Mahler measure, volume, slice | `ajFamily_main` |
| Zheng's estimates and G-PHYS | `zhengEq516_holds`, `zhengEq519_of_zhengEq512`, `zhengEstimates_of_verbatim`, `geo_phys_of_zhengVerbatim` |
| Theorem G | `release_theoremG` (31 clauses of `geo_theoremG`, with G-KERNEL and G-PHYS stated for the braid records), `release_theoremG_supplement` (the other 5: function-field isomorphism, `finrank = 2`, G-K2, two MARK clauses) |
| Theorems I and S | `exists_hasNormalizedIndex_int_of_quotient`, `exists_int_hasNormalizedIndex_locLogJet`, `locResidual_partition`, `hasSimpleResidue_locLogJet_of_allowedNode`, `hasNormalizedIndex_locNodeIndex`, `locBlockDvd_iff_of_forbiddenEdge`, `oreIrreducible_of_connected`, `det_gauge`, `hasNormalizedIndex_mul_coboundary`, `hasNormalizedIndex_mul_inv_coboundary`, `hasNormalizedIndex_gauge_of_isJointRegular`, `hasNormalizedIndex_rescale`, `release_hasNormalizedIndex_powerSubst`, `release_hasSimpleResidue_ramify`, `release_seq_theoremS`, `exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational`, `exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous`, `toComparison_specialize_dvd_of_tail_annihilator_gauge`, the controls `toyRecOp_pseudoIrreducible`, `toyRecOp_primitive_specialize`, `exists_C_mul_eq_oreMul_toyRecOp`, `locFactored_nodeIndex`, `constSeq_minimum`, `constSeq_oversized`, `constSeq_not_selected`, `not_weakLatticeLemma`, and the application `toy_theoremI` |
| T-JETS, T-IRR | `pairQJets_abNode`, `pairQJets_ebNode`, `pairQ_transferOp_oreIrreducible` |

How the challenge is built (`tools/make_challenge.py`; its docstring has the details):

* Statements mention only data definitions and predicates. Where a library statement mentions a
  knot record with embedded proofs (`pairWhiteheadKnot`, `whiteheadTorusKnot`, `torusPairKnot`),
  the release version quantifies over every `K : BraidKnot` with the given strand count and braid
  word, and proves that such a `K` exists.
* Every declaration the statements depend on is copied verbatim from its source file into one
  challenge module per source file (88 modules, 3,487 lines with the root), importing only Mathlib
  and one another along the library's own imports. One module per source file is needed because
  Lean shares auxiliary declarations (nested-proof lemmas, identical `match` definitions) within a
  module; with the library's module boundaries the challenge gets the library's auxiliary
  declarations. The challenge contains declarations only (no metaprogramming); the only option set
  is a linter option, copied with three statements.
* Library definitions whose bodies use `private` lemmas cannot be copied (a private name contains
  its module). `Proofs/SolutionDefs.lean` has public copies of those lemmas and replacement
  definitions (`ratRamifyR`, `ratPowerSubstR`, `seqEvalR`, `geoRfunR`, `geoShapeRepR`,
  `geoPatToTilR`, `geoPatternShapeRepR`, and two `IsDomain` instances) whose statements and bodies
  are those of the library definitions except for the proof terms; they are definitionally equal to
  the library's (proof irrelevance), and the four release theorems that use them
  (`release_hasSimpleResidue_ramify`, `release_hasNormalizedIndex_powerSubst`,
  `release_seq_theoremS`, `release_theoremG_supplement`) are proved by the library theorems
  directly. The replacement definitions are part of the challenge, so a reviewer reads them there.
* The declaration list inside the generator was computed from the built library by a closure
  script (not shipped); its correctness is what `--check` and the identity check below verify.

The checks were run again on 18 November 2026 in the present layout, on a build from scratch:

| Check | Result |
|---|---|
| `lake build Proofs Solution Challenge` | passes (20,034 jobs: Mathlib, the 808 modules of `Proofs/` and `Solution.lean`, the 89 of the challenge); the only warnings are Lake's advisory about importing `Mathlib` as a whole and the challenge's 47 intended `sorry` |
| `#print axioms` (`checks/PrintAxiomsV1.lean`: the 47 release theorems and 29 further theorems cited here and in `MARK_BRIDGE.md`) | `[propext, Classical.choice, Quot.sound]` or a subset (`orientStates_clasp_negative`: `[propext]`) |
| `tools/make_challenge.py --check` (every challenge module regenerated and compared byte for byte: verbatim declarations, imports following the library's, statements equal to the solution's, config naming exactly the statements) | passes: "89 challenge modules match the source declarations and statements; comparator.json names the 47 theorems" |
| `tools/compare_reach.py` (identity, in the built challenge and solution, of every constant reachable from the statements, and of the statement types) | identical: 46,804 constants as the tool counts them (another traversal convention gives slightly different counts); theorem types identical |
| Kernel replay (Lean's `leanchecker`, without `--fresh`: each module's declarations re-checked by the kernel against its imports), `tools/replay_modules.sh` | all 808 modules of `Proofs/` (`AJConjecture`, `AJFamily`, `AJHandoff`, `SolutionDefs`) and `Solution` accepted, exit code 0 for each: the non-root modules each in its own `leanchecker` process, the four roots (`AJConjecture`, `AJFamily`, `AJHandoff`, `Solution`: 1, 1, 0 and 14 declarations) by `tools/ReplayExact.lean`, leanchecker's per-module routine applied to exactly that module. (`leanchecker` on a root name replays every module with that prefix in one process, which dies of a segmentation fault on this machine; this is why the roots are replayed separately.) |
| `lake comparator` (it reads `comparator.json`) | **not run**: it needs a Linux sandbox (bubblewrap); the last accepted run (8dd21cf, 15 November) was on a Linux cluster |

Until `lake comparator` accepts the release configuration, the release is "locally verified", not
"release verified". To run it: in `formalization/lean` on Linux, with the pinned toolchain, the
Mathlib cache and bubblewrap,
`PATH="$PATH:$(lean --print-prefix)/bin" lake comparator`
(the `PATH` addition puts `nanoda_bin` in reach; see `reports/comparator-2026-11-15.md`,
"Deviations").

## 7. Corrections to earlier documents

* `HANDOFF_ACCEPTANCE.md`, outcome list: "the exact minimal recurrence of the family" now reads
  "of the doubles of `T(2, 2k+1)`"; "gauge, ramification and reparametrization laws" now names the
  formalized reparametrizations (`h ↦ a h`, `x = a z^k`).
* `HANDOFF_ACCEPTANCE.md`, conditional statements: G-PHYS is conditional on `ZhengVerbatim a`
  (Zheng as printed); for the corrected `b`, (5.16) is a Lean theorem and (5.19) a Lean theorem
  from Zheng's `b`-free (5.12). The interpretation paragraph now points to the satellite bridge
  (Section 1.2).
* Earlier statements that the library's definitions are "comparator-accepted" apply only to the
  seven baseline files and the theorem `not_ajSquareFreeConjecture` (Section 5, items 2a and 2b).
* `MARK_BRIDGE.md` (17 November) replaces the earlier one-line description of the definition
  interface (item 2a) by an explicit bridge, and adds two Lean files (`PairKMirrorRobust.lean`,
  `PairKMarkCalib.lean`); they are not yet part of the release challenge.
* Manuscript: to be updated as in Section 4 before release.

## Appendix A. Exact Lean statements

Generated, not transcribed: this is the output of `lake env lean tools/V1Appendix.lean` (run from `formalization/lean`, with `pp.fieldNotation false` and `pp.proofs false`). It prints, in order: (A.1) the conjecture and the predicates it uses; (A.2) the core and release theorems; (A.3) the satellite bridge, definitions then theorems; (A.4) the conditional statements; (A.5) `#print axioms` for the main theorems; (A.6) the statement of every theorem checked by the release challenge, in the order of `comparator.json`; (A.7) the chirality-robust refutation and the calibration theorems of `MARK_BRIDGE.md`.

```lean
def AJConjecture.AJSquareFree : BraidKnot → Prop :=
fun K =>
  ∀ (α : RecOp),
    IsRecurrencePolynomial (coloredJones K) α →
      ∀ (A : Polynomial (Polynomial ℤ)),
        IsAPolynomialOf (eigenvalueSet K) A →
          Ideal.radical (Ideal.span {toComparison (specialize α)}) = Ideal.span {toComparison A}
def AJConjecture.AJSquareFreeConjecture : Prop :=
∀ (K : BraidKnot), AJSquareFree K
def AJConjecture.IsRecurrencePolynomial : (ℤ → LaurentPolynomial ℤ) → RecOp → Prop :=
fun f α =>
  α ≠ 0 ∧
    InLocalizedAnnihilator f α ∧
      (∀ (Q : RecOp), Q ≠ 0 → InLocalizedAnnihilator f Q → Polynomial.natDegree α ≤ Polynomial.natDegree Q) ∧
        Polynomial.IsPrimitive α
def AJConjecture.InLocalizedAnnihilator : (ℤ → LaurentPolynomial ℤ) → RecOp → Prop :=
fun f Q => ∃ c, c ≠ 0 ∧ Annihilates (Polynomial.C c * Q) f
def AJConjecture.Annihilates : RecOp → (ℤ → LaurentPolynomial ℤ) → Prop :=
fun P f => ∀ (n : ℤ), opApply P f n = 0
def AJConjecture.opApply : RecOp → (ℤ → LaurentPolynomial ℤ) → ℤ → LaurentPolynomial ℤ :=
fun P f n => Polynomial.sum P fun i D => (evalAt n) D * f (n + ↑i)
def AJConjecture.specialize : RecOp →+* Polynomial (Polynomial ℤ) :=
Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom (-1)))
def AJConjecture.toComparison : Polynomial (Polynomial ℤ) →+* ComparisonRing :=
RingHom.comp Polynomial.toLaurent
  (Polynomial.mapRingHom
    (RingHom.comp (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.mapRingHom (Int.castRingHom ℚ))))
def AJConjecture.IsAPolynomialOf : Set (ℂ × ℂ) → Polynomial (Polynomial ℤ) → Prop :=
fun S A =>
  Squarefree (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) A) ∧
    ∀ (g : Polynomial (Polynomial ℂ)),
      Irreducible g →
        (g ∣ Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) A ↔
          ∀ (p : ℂ × ℂ), evalPoint g p = 0 → p ∈ zariskiClosure S)
def AJConjecture.eigenvalueSet : BraidKnot → Set (ℂ × ℂ) :=
fun K =>
  {p |
    ∃ ρ,
      ↑(ρ (meridian K)) 1 0 = 0 ∧
        ↑(ρ (longitude K)) 1 0 = 0 ∧ ↑(ρ (meridian K)) 0 0 = Prod.fst p ∧ ↑(ρ (longitude K)) 0 0 = Prod.snd p}
def AJConjecture.extraFactor : Polynomial (Polynomial ℤ) :=
Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ 4 - 4 * Polynomial.X ^ 2 + 1) * Polynomial.X +
  Polynomial.C (Polynomial.X ^ 4)
def AJConjecture.famBound : ℕ → Polynomial (Polynomial ℤ) :=
fun m => (Polynomial.X - 1) * famB m
def AJConjecture.IsTorusPair : ℕ → ℕ → Prop :=
fun r s => 2 ≤ r ∧ r < s ∧ Nat.Coprime r s
def AJConjecture.MarkovEquiv : BraidKnot → BraidKnot → Prop :=
fun K K' => Relation.EqvGen MarkovStep (BraidKnot.strands K, BraidKnot.word K) (BraidKnot.strands K', BraidKnot.word K')
def AJConjecture.PairTClauses : BraidKnot → ℕ → Prop :=
fun K m =>
  (∃ Q, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
    (∃ α, IsRecurrencePolynomial (coloredJones K) α) ∧
      (∀ (Q : RecOp),
          Q ≠ 0 →
            Polynomial.IsPrimitive Q →
              InLocalizedAnnihilator (coloredJones K) Q →
                specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
        (∃ A, IsAPolynomialOf (eigenvalueSet K) A) ∧
          (∀ (A : Polynomial (Polynomial ℤ)),
              IsAPolynomialOf (eigenvalueSet K) A →
                toComparison A ∣ toComparison (famBound m) ∧ IsCoprime (toComparison extraFactor) (toComparison A)) ∧
            ¬AJSquareFree K
not_ajSquareFreeConjecture : ¬AJSquareFreeConjecture
theoremT : (∀ (r s : ℕ) (h : IsTorusPair r s), PairTClauses (pairWhiteheadKnot r s h) (r * s)) ∧
  (∀ (r s r' s' : ℕ) (h : IsTorusPair r s) (h' : IsTorusPair r' s'),
      (r, s) ≠ (r', s') → ¬MarkovEquiv (pairWhiteheadKnot r s h) (pairWhiteheadKnot r' s' h')) ∧
    ∀ (j : ℕ), 1 ≤ j → IsTorusPair 3 (3 * j + 1)
theoremF : (∀ (k : ℕ) (hk : 1 ≤ k),
    PairTClauses (pairWhiteheadKnot 2 (2 * k + 1) ⋯) (2 * (2 * k + 1)) ∧
      BraidKnot.word (pairWhiteheadKnot 2 (2 * k + 1) ⋯) = whiteheadTorusWord k ∧
        BraidKnot.strands (pairWhiteheadKnot 2 (2 * k + 1) ⋯) = 4 * k + 3) ∧
  ∀ (k k' : ℕ) (hk : 1 ≤ k) (hk' : 1 ≤ k'),
    k ≠ k' → ¬MarkovEquiv (pairWhiteheadKnot 2 (2 * k + 1) ⋯) (pairWhiteheadKnot 2 (2 * k' + 1) ⋯)
@aPolynomial_pair_associated_famBound : ∀ {r s : ℕ} (h : IsTorusPair r s) {A : Polynomial (Polynomial ℤ)},
  IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A →
    Associated (toComparison A) (toComparison (famBound (r * s)))
minimalRecurrence_whiteheadTorusKnot : ∀ (k : ℕ) (hk : 1 ≤ k),
  (∃ α, IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α) ∧
    ∀ (α : RecOp),
      IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α →
        Polynomial.natDegree α = 8 * k + 8 ∧
          Associated (toComparison (specialize α))
            (toComparison ((Polynomial.X - 1) ^ 2 * extraFactor * twistPoly (2 * (2 * k + 1))))
isRecurrencePolynomial_whiteheadTorusKnot_one : (∃ α,
    IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot 1 ⋯)) α) ∧
  ∀ (α : RecOp),
    IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot 1 ⋯)) α →
      Polynomial.natDegree α = 16 ∧
        Associated (toComparison (specialize α)) (toComparison ((Polynomial.X - 1) ^ 2 * extraFactor * twistPoly 6))
release_theoremT : (∀ (r s : ℕ),
    IsTorusPair r s → ∃ K, BraidKnot.strands K = pairStrands r s ∧ BraidKnot.word K = pairWhiteheadWord r s) ∧
  (∀ (r s : ℕ),
      IsTorusPair r s →
        ∀ (K : BraidKnot),
          BraidKnot.strands K = pairStrands r s → BraidKnot.word K = pairWhiteheadWord r s → PairTClauses K (r * s)) ∧
    (∀ (r s r' s' : ℕ),
        IsTorusPair r s →
          IsTorusPair r' s' →
            (r, s) ≠ (r', s') →
              ∀ (K K' : BraidKnot),
                BraidKnot.strands K = pairStrands r s →
                  BraidKnot.word K = pairWhiteheadWord r s →
                    BraidKnot.strands K' = pairStrands r' s' →
                      BraidKnot.word K' = pairWhiteheadWord r' s' → ¬MarkovEquiv K K') ∧
      ∀ (j : ℕ), 1 ≤ j → IsTorusPair 3 (3 * j + 1)
release_classicalEquality : ∀ (r s : ℕ),
  IsTorusPair r s →
    ∀ (K : BraidKnot),
      BraidKnot.strands K = pairStrands r s →
        BraidKnot.word K = pairWhiteheadWord r s →
          ∀ (A : Polynomial (Polynomial ℤ)),
            IsAPolynomialOf (eigenvalueSet K) A → Associated (toComparison A) (toComparison (famBound (r * s)))
release_minimalRecurrence : ∀ (k : ℕ),
  1 ≤ k →
    (∃ K, BraidKnot.strands K = 4 * k + 3 ∧ BraidKnot.word K = whiteheadTorusWord k) ∧
      ∀ (K : BraidKnot),
        BraidKnot.strands K = 4 * k + 3 →
          BraidKnot.word K = whiteheadTorusWord k →
            (∃ α, IsRecurrencePolynomial (coloredJones K) α) ∧
              ∀ (α : RecOp),
                IsRecurrencePolynomial (coloredJones K) α →
                  Polynomial.natDegree α = 8 * k + 8 ∧
                    Associated (toComparison (specialize α))
                      (toComparison ((Polynomial.X - 1) ^ 2 * extraFactor * famB (2 * (2 * k + 1))))
release_pairWord_two : ∀ (k : ℕ),
  1 ≤ k → pairStrands 2 (2 * k + 1) = 4 * k + 3 ∧ pairWhiteheadWord 2 (2 * k + 1) = whiteheadTorusWord k
@morseReach_pair_source_target : ∀ {r s : ℕ},
  IsTorusPair r s → MorseReach 1 (morseLongClosure (pairStrands r s) (pairWhiteheadWord r s)) (pairTargetWord r s)
def AJConjecture.pairTargetWord : ℕ → ℕ → MorseWord :=
fun r s =>
  [(MorseKind.cup, 1)] ++ morseDouble (morseLongClosure r (torusPairWord r s)) ++
        List.replicate (2 * ((r - 1) * s)) (MorseKind.cross false, 0) ++
      claspWord ++
    [(MorseKind.cap, 1)]
@longKnotOp_pairWhiteheadKnot : ∀ {r s : ℕ} (h : IsTorusPair r s) (c : ℕ),
  longKnotOp (pairWhiteheadKnot r s h) c =
    ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) * (halfTwist c false ^ (2 * ((r - 1) * s)) * claspOp c))
@writhe_pairWhiteheadKnot : ∀ {r s : ℕ} (h : IsTorusPair r s),
  writhe (BraidKnot.word (pairWhiteheadKnot r s h)) = 2 * ↑((r - 1) * s) - 2
@isWhSatellite_pairWhiteheadKnot : ∀ {r s : ℕ} (h : IsTorusPair r s),
  IsWhSatellite (torusPairKnot r s h) (pairWhiteheadKnot r s h)
def AJConjecture.IsWhSatellite : BraidKnot → BraidKnot → Prop :=
fun C K =>
  ∃ φ μ₁,
    φ (meridian C) = compMer (meridian K) μ₁ ∧
      μ₁ = (φ (longitude C))⁻¹ * meridian K * φ (longitude C) ∧
        longitude K =
          meridian K ^ 2 * φ (longitude C) * (meridian K)⁻¹ * (φ (longitude C))⁻¹ * meridian K * μ₁⁻¹ * (meridian K)⁻¹
@pairRealizesSatellite : ∀ {r s : ℕ} (h : IsTorusPair r s),
  PairRealizesSatellite (torusPairKnot r s h) (pairWhiteheadKnot r s h)
def AJConjecture.PairRealizesSatellite : BraidKnot → BraidKnot → Prop :=
fun C K =>
  ∀ (ψ : KnotGroup C →* Matrix.SpecialLinearGroup (Fin 2) ℂ) (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ),
    ψ (meridian C) = compMer a a₁ →
      a₁ = (ψ (longitude C))⁻¹ * a * ψ (longitude C) →
        ∃ ρ, ρ (meridian K) = a ∧ ρ (longitude K) = a ^ 2 * ψ (longitude C) * a⁻¹ * (ψ (longitude C))⁻¹ * a * a₁⁻¹ * a⁻¹
def AJConjecture.whDouble : MorseWord → MorseWord :=
fun D => [(MorseKind.cup, 1)] ++ whBand D ++ claspWord ++ [(MorseKind.cap, 1)]
def AJConjecture.whBand : MorseWord → MorseWord :=
fun D => morseDouble D ++ bandUntwist (morseWrithe D)
def AJConjecture.bandUntwist : ℤ → MorseWord :=
fun w =>
  if 0 ≤ w then List.replicate (2 * Int.toNat w) (MorseKind.cross false, 0)
  else List.replicate (2 * Int.toNat (-w)) (MorseKind.cross true, 0)
def AJConjecture.morseWrithe : MorseWord → ℤ :=
fun D => List.sum (orientWrithes D)
def AJConjecture.IsLongKnotDiagram : MorseWord → Prop :=
fun D => morseFits 1 D = true ∧ List.length (orientWrithes D) = 1
def AJConjecture.braidLongDiagram : BraidKnot → MorseWord :=
fun K => morseLongClosure (BraidKnot.strands K) (BraidKnot.word K)
@whDouble_torusPairKnot : ∀ {r s : ℕ} (h : IsTorusPair r s),
  whDouble (braidLongDiagram (torusPairKnot r s h)) = pairTargetWord r s
@morseReach_whDouble : ∀ {D D' : MorseWord},
  morseFits 1 D = true → MorseReach 1 D D' → MorseReach 1 (whDouble D) (whDouble D')
@morseWrithe_eq_of_morseReach : ∀ {D D' : MorseWord},
  morseFits 1 D = true → MorseReach 1 D D' → morseWrithe D = morseWrithe D'
orientWrithes_braidLongDiagram : ∀ (K : BraidKnot), orientWrithes (braidLongDiagram K) = [writhe (BraidKnot.word K)]
@zero_mem_bandLinkings_whBand : ∀ {D : MorseWord}, IsLongKnotDiagram D → 0 ∈ bandLinkings (whBand D)
bandLinkings_whBand_braidLongDiagram : ∀ (K : BraidKnot), bandLinkings (whBand (braidLongDiagram K)) = [0]
orientStates_clasp_negative : orientStates (claspWord ++ [(MorseKind.cap, 1)]) [([true, false, true], 0)] =
  [([true], -2)]
@orientWrithes_whDouble_torusPairKnot : ∀ {r s : ℕ} (h : IsTorusPair r s),
  orientWrithes (whDouble (braidLongDiagram (torusPairKnot r s h))) = [2 * ↑((r - 1) * s) - 2]
@pairWhiteheadKnot_whDouble : ∀ {r s : ℕ} (h : IsTorusPair r s),
  MorseReach 1 (braidLongDiagram (pairWhiteheadKnot r s h)) (whDouble (braidLongDiagram (torusPairKnot r s h))) ∧
    IsLongKnotDiagram (braidLongDiagram (torusPairKnot r s h)) ∧
      morseWrithe (braidLongDiagram (torusPairKnot r s h)) = ↑((r - 1) * s) ∧
        orientWrithes (whDouble (braidLongDiagram (torusPairKnot r s h))) = [2 * ↑((r - 1) * s) - 2] ∧
          orientStates (claspWord ++ [(MorseKind.cap, 1)]) [([true, false, true], 0)] = [([true], -2)]
whiteheadTorusKnot_whDouble : ∀ (k : ℕ) (hk : 1 ≤ k) (h : IsTorusPair 2 (2 * k + 1)),
  MorseReach 1 (braidLongDiagram (whiteheadTorusKnot k hk))
      (whDouble (braidLongDiagram (torusPairKnot 2 (2 * k + 1) h))) ∧
    BraidKnot.word (pairWhiteheadKnot 2 (2 * k + 1) h) = BraidKnot.word (whiteheadTorusKnot k hk) ∧
      BraidKnot.strands (pairWhiteheadKnot 2 (2 * k + 1) h) = BraidKnot.strands (whiteheadTorusKnot k hk)
@coloredJones_two_pairWhiteheadKnot_ne : ∀ {r s r' s' : ℕ} (h : IsTorusPair r s) (h' : IsTorusPair r' s'),
  (r, s) ≠ (r', s') → coloredJones (pairWhiteheadKnot r s h) 2 ≠ coloredJones (pairWhiteheadKnot r' s' h') 2
def AJConjecture.ZhengVerbatim : ℕ → Prop :=
fun a =>
  ZhengLemma32 ∧
    (∀ (δ : ℝ), 1 / 2 < δ → δ < 2 / 3 → ZhengLemma33 (-(8 * ↑a + 1)) δ ∧ ZhengLemma33 0 δ) ∧
      ZhengEq512 a ∧ ZhengEq520 a ∧ ZhengProp41 a
def AJConjecture.ZhengEstimates : ℕ → Prop :=
fun a =>
  ZhengLemma32 ∧
    (∀ (δ : ℝ), 1 / 2 < δ → δ < 2 / 3 → ZhengLemma33 (-(8 * ↑a + 1)) δ ∧ ZhengLemma33 0 δ) ∧
      ZhengEq516 a ∧ ZhengEq519 a ∧ ZhengEq520 a ∧ ZhengProp41 a
zhengEq516_holds : ∀ (a : ℕ), ZhengEq516 a
zhengEq519_of_zhengEq512 : ∀ (a : ℕ), 1 ≤ a → ZhengEq512 a → ZhengEq519 a
zhengEstimates_of_verbatim : ∀ (a : ℕ), 1 ≤ a → ZhengVerbatim a → ZhengEstimates a
geo_phys_of_zhengVerbatim : ∀ (a : ℕ),
  3 ≤ a →
    Odd a →
      ZhengVerbatim a →
        (∀ (N : ℕ), 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
          Filter.Tendsto (fun N => geoZhengDiagonal a N / geoZhengLeading a N) Filter.atTop (nhds 1)
def AJConjecture.WhiteheadJSJProp : Prop :=
∀ (r s r' s' : ℕ) (h : IsTorusPair r s) (h' : IsTorusPair r' s'),
  Nonempty (KnotGroup (pairWhiteheadKnot r s h) ≃* KnotGroup (pairWhiteheadKnot r' s' h')) →
    Nonempty (KnotGroup (torusPairKnot r s h) ≃* KnotGroup (torusPairKnot r' s' h'))
pairWhiteheadKnot_not_markovEquiv_of_jsj : WhiteheadJSJProp →
  ∀ {r s r' s' : ℕ} (h : IsTorusPair r s) (h' : IsTorusPair r' s'),
    (r, s) ≠ (r', s') → ¬MarkovEquiv (pairWhiteheadKnot r s h) (pairWhiteheadKnot r' s' h')
pairWhiteheadKnot_knotGroup_not_equiv_of_jsj : WhiteheadJSJProp →
  ∀ {r s r' s' : ℕ} (h : IsTorusPair r s) (h' : IsTorusPair r' s'),
    (r, s) ≠ (r', s') → ¬Nonempty (KnotGroup (pairWhiteheadKnot r s h) ≃* KnotGroup (pairWhiteheadKnot r' s' h'))
'AJConjecture.not_ajSquareFreeConjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.theoremT' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.theoremF' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.aPolynomial_pair_associated_famBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.minimalRecurrence_whiteheadTorusKnot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.isRecurrencePolynomial_whiteheadTorusKnot_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.release_theoremT' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.release_classicalEquality' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.release_minimalRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.release_pairWord_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.morseReach_pair_source_target' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.geo_phys_of_zhengVerbatim' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.zhengEq516_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.pairWhiteheadKnot_whDouble' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.whiteheadTorusKnot_whDouble' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.morseReach_whDouble' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.bandLinkings_whBand_braidLongDiagram' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.zero_mem_bandLinkings_whBand' depends on axioms: [propext, Classical.choice, Quot.sound]
'AJConjecture.coloredJones_two_pairWhiteheadKnot_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
not_ajSquareFreeConjecture : ¬AJSquareFreeConjecture
release_theoremT : (∀ (r s : ℕ),
    IsTorusPair r s → ∃ K, BraidKnot.strands K = pairStrands r s ∧ BraidKnot.word K = pairWhiteheadWord r s) ∧
  (∀ (r s : ℕ),
      IsTorusPair r s →
        ∀ (K : BraidKnot),
          BraidKnot.strands K = pairStrands r s → BraidKnot.word K = pairWhiteheadWord r s → PairTClauses K (r * s)) ∧
    (∀ (r s r' s' : ℕ),
        IsTorusPair r s →
          IsTorusPair r' s' →
            (r, s) ≠ (r', s') →
              ∀ (K K' : BraidKnot),
                BraidKnot.strands K = pairStrands r s →
                  BraidKnot.word K = pairWhiteheadWord r s →
                    BraidKnot.strands K' = pairStrands r' s' →
                      BraidKnot.word K' = pairWhiteheadWord r' s' → ¬MarkovEquiv K K') ∧
      ∀ (j : ℕ), 1 ≤ j → IsTorusPair 3 (3 * j + 1)
release_classicalEquality : ∀ (r s : ℕ),
  IsTorusPair r s →
    ∀ (K : BraidKnot),
      BraidKnot.strands K = pairStrands r s →
        BraidKnot.word K = pairWhiteheadWord r s →
          ∀ (A : Polynomial (Polynomial ℤ)),
            IsAPolynomialOf (eigenvalueSet K) A → Associated (toComparison A) (toComparison (famBound (r * s)))
release_minimalRecurrence : ∀ (k : ℕ),
  1 ≤ k →
    (∃ K, BraidKnot.strands K = 4 * k + 3 ∧ BraidKnot.word K = whiteheadTorusWord k) ∧
      ∀ (K : BraidKnot),
        BraidKnot.strands K = 4 * k + 3 →
          BraidKnot.word K = whiteheadTorusWord k →
            (∃ α, IsRecurrencePolynomial (coloredJones K) α) ∧
              ∀ (α : RecOp),
                IsRecurrencePolynomial (coloredJones K) α →
                  Polynomial.natDegree α = 8 * k + 8 ∧
                    Associated (toComparison (specialize α))
                      (toComparison ((Polynomial.X - 1) ^ 2 * extraFactor * famB (2 * (2 * k + 1))))
release_pairWord_two : ∀ (k : ℕ),
  1 ≤ k → pairStrands 2 (2 * k + 1) = 4 * k + 3 ∧ pairWhiteheadWord 2 (2 * k + 1) = whiteheadTorusWord k
release_coloredJones_two_ne : ∀ (r s r' s' : ℕ),
  IsTorusPair r s →
    IsTorusPair r' s' →
      (r, s) ≠ (r', s') →
        ∀ (K K' : BraidKnot),
          BraidKnot.strands K = pairStrands r s →
            BraidKnot.word K = pairWhiteheadWord r s →
              BraidKnot.strands K' = pairStrands r' s' →
                BraidKnot.word K' = pairWhiteheadWord r' s' → coloredJones K 2 ≠ coloredJones K' 2
release_whDouble : (∀ (r s : ℕ),
    IsTorusPair r s →
      MorseReach 1 (morseLongClosure (pairStrands r s) (pairWhiteheadWord r s))
          (whDouble (morseLongClosure r (torusPairWord r s))) ∧
        IsLongKnotDiagram (morseLongClosure r (torusPairWord r s)) ∧
          morseWrithe (morseLongClosure r (torusPairWord r s)) = ↑((r - 1) * s) ∧
            orientWrithes (whDouble (morseLongClosure r (torusPairWord r s))) = [2 * ↑((r - 1) * s) - 2] ∧
              bandLinkings (whBand (morseLongClosure r (torusPairWord r s))) = [0]) ∧
  orientStates (claspWord ++ [(MorseKind.cap, 1)]) [([true, false, true], 0)] = [([true], -2)]
@morseReach_whDouble : ∀ {D D' : MorseWord},
  morseFits 1 D = true → MorseReach 1 D D' → MorseReach 1 (whDouble D) (whDouble D')
@morseWrithe_eq_of_morseReach : ∀ {D D' : MorseWord},
  morseFits 1 D = true → MorseReach 1 D D' → morseWrithe D = morseWrithe D'
@zero_mem_bandLinkings_whBand : ∀ {D : MorseWord}, IsLongKnotDiagram D → 0 ∈ bandLinkings (whBand D)
ajFamily_main : (∃ K,
    (Pairwise fun i j => ¬MarkovEquiv (K i) (K j)) ∧
      ∀ (n : ℕ),
        ¬AJSquareFree (K n) ∧
          (∀ (Q : RecOp),
              Q ≠ 0 →
                Polynomial.IsPrimitive Q →
                  InLocalizedAnnihilator (coloredJones (K n)) Q →
                    specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
            ∀ (A : Polynomial (Polynomial ℤ)),
              IsAPolynomialOf (eigenvalueSet (K n)) A → IsCoprime (toComparison extraFactor) (toComparison A)) ∧
  (MeasureTheory.IntegrableOn (torusLogAbs extraFactorℂ) torusBox MeasureTheory.volume ∧
      logMahlerMeasure₂ extraFactorℂ = 4 * catalanConstant / Real.pi) ∧
    (∃! z, WhiteheadGluing z ∧ WhiteheadComplete z ∧ ∀ (j : Fin 4), 0 < Complex.im (z j)) ∧
      (∀ (z : Fin 4 → ℂ),
          WhiteheadGluing z →
            WhiteheadComplete z →
              (∀ (j : Fin 4), 0 < Complex.im (z j)) → ∑ j, blochWigner (z j) = 4 * catalanConstant) ∧
        (∀ (z : Fin 4 → ℂ),
            WhiteheadGluing z →
              Prod.fst (whiteheadPeripheral z) = 1 →
                Prod.fst (Prod.snd (whiteheadPeripheral z)) = -1 →
                  ∀ (u : ℂ),
                    u ^ 2 = Prod.fst (Prod.snd (Prod.snd (whiteheadPeripheral z))) →
                      evalPoint extraFactorℂ (u, (Prod.snd (Prod.snd (Prod.snd (whiteheadPeripheral z))))⁻¹) = 0) ∧
          ∀ (p : ℂ × ℂ),
            evalPoint extraFactorℂ p = 0 →
              Prod.fst p ≠ 0 →
                ∃ z,
                  WhiteheadGluing z ∧
                    Prod.fst (whiteheadPeripheral z) = 1 ∧
                      Prod.fst (Prod.snd (whiteheadPeripheral z)) = -1 ∧
                        Prod.fst (Prod.snd (Prod.snd (whiteheadPeripheral z))) = Prod.fst p ^ 2 ∧
                          Prod.snd (Prod.snd (Prod.snd (whiteheadPeripheral z))) = (Prod.snd p)⁻¹
zhengEq516_holds : ∀ (a : ℕ), ZhengEq516 a
zhengEq519_of_zhengEq512 : ∀ (a : ℕ), 1 ≤ a → ZhengEq512 a → ZhengEq519 a
zhengEstimates_of_verbatim : ∀ (a : ℕ), 1 ≤ a → ZhengVerbatim a → ZhengEstimates a
geo_phys_of_zhengVerbatim : ∀ (a : ℕ),
  3 ≤ a →
    Odd a →
      ZhengVerbatim a →
        (∀ (N : ℕ), 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
          Filter.Tendsto (fun N => geoZhengDiagonal a N / geoZhengLeading a N) Filter.atTop (nhds 1)
release_theoremG : (∀ (k : ℕ),
    1 ≤ k →
      ∀ (K : BraidKnot),
        BraidKnot.strands K = 4 * k + 3 →
          BraidKnot.word K = whiteheadTorusWord k →
            ∀ (N B : ℕ),
              1 ≤ N →
                N ≤ B →
                  laurentToField (coloredJones K ↑N) =
                    RatFunc.X ^ (4 * ↑N ^ 2 - 2 * ↑N - 2) *
                      (PowerSeries.coeff (N - 1))
                        (∑ n ∈ Finset.range B, PowerSeries.C (torusOddColor (2 * k + 1) n) * geoClaspGen N n)) ∧
  (∀ (x : ℂ),
      x ≠ 0 →
        x ^ 2 ≠ 1 →
          Set.BijOn (geoChannelL x) {y | geoChannelT x y = 0} {L | L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0}) ∧
    (∀ (a : ℕ) {x y : ℂ},
        x ≠ 0 →
          x ^ 2 ≠ 1 →
            y ≠ 0 ∧ y ≠ 1 ∧ y ≠ x ∧ y ≠ -x ∧ y ≠ -1 →
              (geoRatioQ a 1 x (-1) (-y) = 1 ∧ geoRatioZ 1 x (-1) (-y) = 1 ↔ geoChannelT x y = 0) ∧
                geoRatioX 1 x (-1) (-y) = geoChannelL x y) ∧
      Set.BijOn geoToWeierstrass GeoSmoothTorusLocus GeoWeierstrassOpen ∧
        WeierstrassCurve.j geoWeierstrass = 1728 ∧
          (∃ e,
              ↑(e ((algebraMap GeoCoordE GeoLaurentE) geoMer)) = geoNuM ∧
                ↑(e ((algebraMap GeoCoordE GeoLaurentE) geoLong)) = geoNuL) ∧
            Subalgebra.restrictScalars ℚ (integralClosure (↥geoLaurentImage) GeoKW) = geoPuncturedImage ∧
              CompactSpace GeoEllipticPoints ∧
                (∀ (r : OnePoint ℂ),
                    Set.ncard (geoCoverR ⁻¹' {r}) = if r = ↑0 ∨ r = ↑1 ∨ r = ↑(-1) ∨ r = OnePoint.infty then 1 else 2) ∧
                  (∀ {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ},
                      HasDerivAt γ γ' t →
                        (∀ᶠ (s : ℝ) in nhds t, γ s ∈ GeoSmoothTorusLocus) →
                          HasDerivAt (fun s => geoRegPrimitive (geoCurveR (γ s)))
                            (geoEta (Prod.fst (γ t)) (Prod.snd (γ t)) (Prod.fst γ') (Prod.snd γ')) t) ∧
                    (geoRegPrimitive 0 = 0 ∧
                        geoRegPrimitive 1 = 0 ∧
                          geoRegPrimitive (-1) = 0 ∧
                            geoRegPrimitive Complex.I = 2 * catalanConstant ∧
                              geoRegPrimitive (-Complex.I) = -(2 * catalanConstant)) ∧
                      (Continuous (geoRegPrimitiveP1 ∘ geoCoverR) ∧
                          (∀ q ∈ GeoPuncturedModel,
                              Prod.fst q ^ 2 ≠ -1 →
                                geoNormMap q ∈ GeoSmoothTorusLocus ∧
                                  geoRegPrimitive (geoCurveR (geoNormMap q)) = geoRegPrimitiveP1 ↑(-Prod.fst q)) ∧
                            (∀ (P : GeoEllipticPoints),
                                geoCoverR P = ↑0 ∨
                                    geoCoverR P = ↑1 ∨ geoCoverR P = ↑(-1) ∨ geoCoverR P = OnePoint.infty →
                                  geoRegPrimitiveP1 (geoCoverR P) = 0) ∧
                              (∀ (P : GeoEllipticPoints),
                                  geoCoverR P = ↑Complex.I → geoRegPrimitiveP1 (geoCoverR P) = 2 * catalanConstant) ∧
                                ∀ (P : GeoEllipticPoints),
                                  geoCoverR P = ↑(-Complex.I) →
                                    geoRegPrimitiveP1 (geoCoverR P) = -(2 * catalanConstant)) ∧
                        (∀ (ε : ℂ),
                            ε = 1 ∨ ε = -1 →
                              ¬∃ c,
                                  Filter.Tendsto (fun p => geoRegPrimitive (geoCurveR p))
                                    (nhdsWithin (ε, -1) GeoSmoothTorusLocus) (nhds c)) ∧
                          (∀ (a : ℕ), GeoChannelActionBranch (geoChannelAction a) geoChannelActionDomain) ∧
                            (∀ (a : ℕ),
                                ∃ ε > 0,
                                  ∀ r ∈ Metric.ball 2 ε,
                                    (Complex.log (-geoX r) + ↑Real.pi * Complex.I,
                                          Complex.log (1 / r) + ↑Real.pi * Complex.I) ∈
                                        geoChannelActionDomain ∧
                                      (fderiv ℂ (geoChannelAction a)
                                            (Complex.log (-geoX r) + ↑Real.pi * Complex.I,
                                              Complex.log (1 / r) + ↑Real.pi * Complex.I))
                                          (0, 1) =
                                        0) ∧
                              (∀ {S : ℂ × ℂ → ℂ} {Ω : Set (ℂ × ℂ)},
                                  GeoChannelActionBranch S Ω →
                                    ∀ {ℓ : ℂ → ℂ × ℂ} {r : ℂ},
                                      r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧ r ^ 2 ≠ -1 →
                                        DifferentiableAt ℂ ℓ r →
                                          ℓ r ∈ Ω →
                                            Complex.exp (Prod.fst (ℓ r)) = geoX r ∧
                                                Complex.exp (Prod.snd (ℓ r)) = -1 / r →
                                              (fderiv ℂ S (ℓ r)) (0, 1) = 0 →
                                                HasDerivAt (fun ρ => S (ℓ ρ))
                                                    ((fderiv ℂ S (ℓ r)) (1, 0) * deriv (fun ρ => Prod.fst (ℓ ρ)) r) r ∧
                                                  Complex.exp ((fderiv ℂ S (ℓ r)) (1, 0)) = geoL r) ∧
                                (∀ {Ω : Set ℂ},
                                    IsOpen Ω →
                                      IsPreconnected Ω →
                                        (∀ r ∈ Ω, r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1) →
                                          ∀ {lx lL s : ℂ → ℂ},
                                            DifferentiableOn ℂ lx Ω →
                                              DifferentiableOn ℂ lL Ω →
                                                (∀ r ∈ Ω, Complex.exp (lx r) = geoX r) →
                                                  (∀ r ∈ Ω, Complex.exp (lL r) = geoL r) →
                                                    (∀ r ∈ Ω, HasDerivAt s (lL r * deriv lx r) r) →
                                                      (∀ {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ},
                                                          HasDerivAt γ γ' t →
                                                            (∀ᶠ (τ : ℝ) in nhds t,
                                                                γ τ ∈ GeoSmoothTorusLocus ∧ geoCurveR (γ τ) ∈ Ω) →
                                                              HasDerivAt
                                                                (fun τ =>
                                                                  Complex.im (s (geoCurveR (γ τ))) -
                                                                    Complex.im (lL (geoCurveR (γ τ))) *
                                                                      Complex.re (lx (geoCurveR (γ τ))))
                                                                (-2 *
                                                                  geoEta (Prod.fst (γ t)) (Prod.snd (γ t)) (Prod.fst γ')
                                                                    (Prod.snd γ'))
                                                                t) ∧
                                                        (∃ c,
                                                            ∀ r ∈ Ω,
                                                              Complex.im (s r) - Complex.im (lL r) * Complex.re (lx r) +
                                                                  2 * geoRegPrimitive r =
                                                                c) ∧
                                                          (1 / 2 ∈ Ω →
                                                            Complex.im (s (1 / 2)) -
                                                                  Complex.im (lL (1 / 2)) * Complex.re (lx (1 / 2)) =
                                                                0 →
                                                              ∀ r ∈ Ω,
                                                                Complex.im (s r) -
                                                                    Complex.im (lL r) * Complex.re (lx r) =
                                                                  -2 * geoRegPrimitive r)) ∧
                                  logMahlerMeasure₂ extraFactorℂ = 4 * catalanConstant / Real.pi ∧
                                    (∀ (z : Fin 4 → ℂ),
                                        WhiteheadGluing z →
                                          Prod.fst (whiteheadPeripheral z) = 1 →
                                            Prod.fst (Prod.snd (whiteheadPeripheral z)) = -1 →
                                              ∃ w, w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 ∧ z = geoSliceShapes w) ∧
                                      (∀ (r : ℂ),
                                          r ≠ -1 →
                                            r ≠ 1 →
                                              ∑ j, blochWigner (geoSliceShapes ((1 - r) / (1 + r)) j) =
                                                -2 * geoRegPrimitive r) ∧
                                        ∑ j, blochWigner (geoSliceShapes Complex.I j) = 4 * catalanConstant ∧
                                          ∑ j, blochWigner (geoSliceShapes Complex.I j)⁻¹ = -(4 * catalanConstant) ∧
                                            (∀ (z : Fin 4 → ℂ),
                                                WhiteheadGluing z →
                                                  WhiteheadComplete z →
                                                    |∑ j, blochWigner (z j)| = 4 * catalanConstant) ∧
                                              geoHypMeasure geoIdealTetI = ENNReal.ofReal catalanConstant ∧
                                                (∀ (k : ℕ),
                                                    1 ≤ k →
                                                      ∀ (K : BraidKnot),
                                                        BraidKnot.strands K = 4 * k + 3 →
                                                          BraidKnot.word K = whiteheadTorusWord k →
                                                            ∀ (N : ℕ),
                                                              1 ≤ N →
                                                                laurentToField (coloredJones K ↑N) =
                                                                  quantumInt ↑N * torusReducedFormula (2 * k + 1) N) ∧
                                                  (∀ (k N : ℕ),
                                                      1 ≤ k →
                                                        1 ≤ N →
                                                          ∃ P, laurentToField P = torusReducedFormula (2 * k + 1) N) ∧
                                                    (∀ (a N : ℕ) (P : LaurentPolynomial ℤ),
                                                        1 ≤ N →
                                                          laurentToField P = torusReducedFormula a N →
                                                            (LaurentPolynomial.eval₂ (Int.castRingHom ℂ)
                                                                  (Units.mk0
                                                                    (Complex.exp (↑Real.pi * Complex.I / (2 * ↑N))) ⋯))
                                                                P =
                                                              geoZhengDiagonal a N) ∧
                                                      (∀ (a N n : ℕ),
                                                          1 ≤ N →
                                                            geoPhasePow N n (-(8 * ↑a)) =
                                                              geoRootQ N ^ (-(2 * ↑a * ↑n * (↑n + 1)))) ∧
                                                        (∀ (δ : ℝ),
                                                            1 / 2 < δ →
                                                              δ < 1 →
                                                                ∃ C N₀,
                                                                  ∀ (N n i : ℕ),
                                                                    N₀ ≤ N →
                                                                      n + i < N →
                                                                        GeoInWindow N (↑N ^ δ) n i →
                                                                          have q := geoRootQ N;
                                                                          have zi :=
                                                                            (1 - q ^ (i + 1)) / (1 - q ^ (n + i + 1));
                                                                          have zj :=
                                                                            (1 - q ^ (N - n - i)) / (1 - q ^ (N - i));
                                                                          ‖q ^ n + 1‖ ≤ C * ↑N ^ (δ - 1) ∧
                                                                            ‖q ^ i - Complex.I‖ ≤ C * ↑N ^ (δ - 1) ∧
                                                                              ‖q ^ (N - 1 - n - i) - Complex.I‖ ≤
                                                                                  C * ↑N ^ (δ - 1) ∧
                                                                                ‖zi + Complex.I‖ ≤ C * ↑N ^ (δ - 1) ∧
                                                                                  ‖zj + Complex.I‖ ≤ C * ↑N ^ (δ - 1) ∧
                                                                                    ‖q ^ n * zi - Complex.I‖ ≤
                                                                                        C * ↑N ^ (δ - 1) ∧
                                                                                      ‖q ^ n * zj - Complex.I‖ ≤
                                                                                        C * ↑N ^ (δ - 1)) ∧
                                                          (∀ (a : ℕ),
                                                              geoRatioQ a 1 1 (-1) (-Complex.I) = 1 ∧
                                                                geoRatioZ 1 1 (-1) (-Complex.I) = 1 ∧
                                                                  geoRatioX 1 1 (-1) (-Complex.I) = -1 ∧
                                                                    geoChannelT 1 Complex.I = 0 ∧
                                                                      -2 * geoRegPrimitive (-Complex.I) =
                                                                        4 * catalanConstant) ∧
                                                            ∀ (a : ℕ),
                                                              3 ≤ a →
                                                                Odd a →
                                                                  ZhengEstimates a →
                                                                    (∀ (N : ℕ), 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
                                                                      Filter.Tendsto
                                                                        (fun N =>
                                                                          geoZhengDiagonal a N / geoZhengLeading a N)
                                                                        Filter.atTop (nhds 1)
release_theoremG_supplement : (∃ e,
    e ((algebraMap GeoCoordE GeoFunFieldE) geoMer) *
          -((algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine geoWeierstrass))
                  (WeierstrassCurve.Affine.FunctionField (WeierstrassCurve.toAffine geoWeierstrass)))
                geoWX *
              (1 +
                (algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine geoWeierstrass))
                    (WeierstrassCurve.Affine.FunctionField (WeierstrassCurve.toAffine geoWeierstrass)))
                  geoWX)) =
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine geoWeierstrass))
            (WeierstrassCurve.Affine.FunctionField (WeierstrassCurve.toAffine geoWeierstrass)))
          geoWY ∧
      e ((algebraMap GeoCoordE GeoFunFieldE) geoLong) *
            (1 +
                (algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine geoWeierstrass))
                    (WeierstrassCurve.Affine.FunctionField (WeierstrassCurve.toAffine geoWeierstrass)))
                  geoWX) ^
              2 =
          (1 -
              (algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine geoWeierstrass))
                  (WeierstrassCurve.Affine.FunctionField (WeierstrassCurve.toAffine geoWeierstrass)))
                geoWX) ^
            2 ∧
        (RingEquiv.symm e)
            ((algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine geoWeierstrass))
                (WeierstrassCurve.Affine.FunctionField (WeierstrassCurve.toAffine geoWeierstrass)))
              geoWX) =
          -(((algebraMap GeoCoordE GeoFunFieldE) geoMer ^ 2 + (algebraMap GeoCoordE GeoFunFieldE) geoLong) /
              ((algebraMap GeoCoordE GeoFunFieldE) geoMer ^ 2 *
                ((algebraMap GeoCoordE GeoFunFieldE) geoMer ^ 2 - 1)))) ∧
  Module.finrank (↥ℚ⟮geoRfunR⟯) GeoFunFieldE = 2 ∧
    geoSymbol (Units.mk0 geoMerBar geoMerBar_ne_zeroR) (Units.mk0 geoLongBar geoLongBar_ne_zeroR) ⊗ₜ[ℤ] 1 = 0 ∧
      (∀ (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1) (hu : u ^ 2 = (1 + w) / (w * (1 - w))),
          GeoAxisCompleted (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) ∧
            GeoPatternEigenPair (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) (u, (w ^ 2)⁻¹) ∧
              GeoPatternEigenPair (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) (u⁻¹, w ^ 2)) ∧
        {p |
            ∃ w u,
              ∃ (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1) (hu : u ^ 2 = (1 + w) / (w * (1 - w))),
                GeoPatternEigenPair (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) p} =
          {p | evalPoint extraFactorℂ p = 0 ∧ Prod.fst p ≠ 0}
exists_hasNormalizedIndex_int_of_quotient : ∀ (δ : LocDilation) {z₀ : ℂ},
  z₀ ≠ 0 →
    ∀ {d r : ℕ} {A : Matrix (Fin d) (Fin d) LocField},
      IsJointRegular z₀ A →
        ∀ {Q : Matrix (Fin r) (Fin d) LocField},
          Function.Surjective ⇑(Matrix.mulVecLin Q) →
            ∀ {B : Matrix (Fin r) (Fin r) LocField},
              B * Matrix.map Q ⇑(LocDilation.fieldShift δ) = Q * A →
                ∃ D₀ D₁,
                  HasHJet (Matrix.det B) D₀ D₁ ∧ IsUnitAt z₀ D₀ ∧ ∃ n, HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁ ↑n
exists_int_hasNormalizedIndex_locLogJet : ∀ (δ : LocDilation) {P S R : LocOp} {β : LocPoly},
  locJet0 β ≠ 0 →
    Polynomial.C β * P = oreMul (LocDilation.shiftHom δ) S R →
      ∀ {z₀ : ℂ},
        z₀ ≠ 0 →
          Polynomial.natDegree (opJet0 P) = Polynomial.natDegree P →
            Polynomial.eval z₀ (Polynomial.leadingCoeff (opJet0 P)) ≠ 0 →
              Polynomial.eval z₀ ((AddMonoidAlgebra.coeff (opJet0 P)) 0) ≠ 0 →
                ∃ n,
                  HasNormalizedIndex (LocDilation.c δ) z₀ ((algebraMap (Polynomial ℂ) (RatFunc ℂ)) (locLogJetDen R))
                    ((algebraMap (Polynomial ℂ) (RatFunc ℂ)) (locLogJetNum R)) ↑n
locResidual_partition : ∀ (δ : LocDilation) {P S R : LocOp} {β : LocPoly},
  locJet0 β ≠ 0 →
    Polynomial.C β * P = oreMul (LocDilation.shiftHom δ) S R →
      Polynomial.natDegree (opJet0 P) = Polynomial.natDegree P →
        (AddMonoidAlgebra.coeff (opJet0 P)) 0 ≠ 0 →
          Squarefree (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (opJet0 P)) →
            opJet0 S * opJet0 R = Polynomial.C (locJet0 β) * opJet0 P ∧
              Polynomial.natDegree (opJet0 R) = Polynomial.natDegree R ∧
                Polynomial.natDegree (opJet0 S) = Polynomial.natDegree S ∧
                  (AddMonoidAlgebra.coeff (opJet0 R)) 0 ≠ 0 ∧
                    (AddMonoidAlgebra.coeff (opJet0 S)) 0 ≠ 0 ∧
                      IsCoprime (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (opJet0 S))
                        (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (opJet0 R))
hasSimpleResidue_locLogJet_of_allowedNode : ∀ (δ : LocDilation) {P S R : LocOp} {β : LocPoly},
  locJet0 β ≠ 0 →
    Polynomial.C β * P = oreMul (LocDilation.shiftHom δ) S R →
      ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] {B : ι → Polynomial (Polynomial ℂ)},
        LocResidualBlocks P B →
          ∀ {κ₁ κ₂ : Polynomial ℂ} {g h : ι} {z₀ lam : ℂ},
            LocAllowedNode P B κ₁ κ₂ g h z₀ lam →
              LocBlockDvd (B g) (opJet0 R) →
                LocBlockDvd (B h) (opJet0 S) →
                  HasSimpleResidue
                    ((algebraMap (Polynomial ℂ) (RatFunc ℂ)) (locLogJetNum R) /
                      (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (locLogJetDen R))
                    z₀
                    (LocDilation.c δ * z₀ *
                      locNodeIndex (LocDilation.c δ) z₀ lam (opJet1 P) (B g) (B h) (locCofactor B g h) κ₁ κ₂)
hasNormalizedIndex_locNodeIndex : ∀ (δ : LocDilation) {P S R : LocOp} {β : LocPoly},
  locJet0 β ≠ 0 →
    Polynomial.C β * P = oreMul (LocDilation.shiftHom δ) S R →
      ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] {B : ι → Polynomial (Polynomial ℂ)},
        LocResidualBlocks P B →
          ∀ {κ₁ κ₂ : Polynomial ℂ} {g h : ι} {z₀ lam : ℂ},
            LocAllowedNode P B κ₁ κ₂ g h z₀ lam →
              LocBlockDvd (B g) (opJet0 R) →
                LocBlockDvd (B h) (opJet0 S) →
                  HasNormalizedIndex (LocDilation.c δ) z₀ ((algebraMap (Polynomial ℂ) (RatFunc ℂ)) (locLogJetDen R))
                    ((algebraMap (Polynomial ℂ) (RatFunc ℂ)) (locLogJetNum R))
                    (locNodeIndex (LocDilation.c δ) z₀ lam (opJet1 P) (B g) (B h) (locCofactor B g h) κ₁ κ₂)
locBlockDvd_iff_of_forbiddenEdge : ∀ (δ : LocDilation) {P S R : LocOp} {β : LocPoly},
  locJet0 β ≠ 0 →
    Polynomial.C β * P = oreMul (LocDilation.shiftHom δ) S R →
      ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] {B : ι → Polynomial (Polynomial ℂ)},
        LocResidualBlocks P B →
          ∀ {κ₁ κ₂ : Polynomial ℂ} {i j : ι} {z₀ lam : ℂ},
            LocAllowedNode P B κ₁ κ₂ i j z₀ lam →
              (∀ (n : ℤ), locNodeIndex (LocDilation.c δ) z₀ lam (opJet1 P) (B i) (B j) (locCofactor B i j) κ₁ κ₂ ≠ ↑n) →
                (LocBlockDvd (B i) (opJet0 R) ↔ LocBlockDvd (B j) (opJet0 R))
oreIrreducible_of_connected : ∀ (δ : LocDilation) {P : LocOp},
  0 < Polynomial.natDegree P →
    Polynomial.natDegree (opJet0 P) = Polynomial.natDegree P →
      (AddMonoidAlgebra.coeff (opJet0 P)) 0 ≠ 0 →
        ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] {B : ι → Polynomial (Polynomial ℂ)},
          LocResidualBlocks P B →
            ∀ (Γ : SimpleGraph ι),
              SimpleGraph.Connected Γ →
                (∀ (i j : ι),
                    SimpleGraph.Adj Γ i j →
                      ∃ κ₁ κ₂ z₀ lam,
                        LocAllowedNode P B κ₁ κ₂ i j z₀ lam ∧
                          ∀ (n : ℤ),
                            locNodeIndex (LocDilation.c δ) z₀ lam (opJet1 P) (B i) (B j) (locCofactor B i j) κ₁ κ₂ ≠
                              ↑n) →
                  OreIrreducible (LocDilation.fieldShiftHom δ) (Polynomial.map (algebraMap LocPoly LocField) P)
det_gauge : ∀ (δ : LocDilation) {r : ℕ} (B G : Matrix (Fin r) (Fin r) LocField),
  Matrix.det G ≠ 0 →
    Matrix.det (G⁻¹ * B * Matrix.map G ⇑(LocDilation.fieldShift δ)) =
      Matrix.det B * (LocDilation.fieldShift δ) (Matrix.det G) / Matrix.det G
hasNormalizedIndex_mul_coboundary : ∀ (δ : LocDilation) {z₀ : ℂ},
  z₀ ≠ 0 →
    ∀ {D g : LocField} {D₀ D₁ : RatFunc ℂ},
      HasHJet D D₀ D₁ →
        D₀ ≠ 0 →
          ∀ {ι : ℂ},
            HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁ ι →
              ∀ {k : ℤ} {g₀ g₁ : RatFunc ℂ},
                HasHJet ((algebraMap LocPoly LocField) locH ^ (-k) * g) g₀ g₁ →
                  g₀ ≠ 0 →
                    ∀ {m : ℤ},
                      HasOrderAt g₀ z₀ m →
                        ∃ D₁',
                          HasHJet (D * (LocDilation.fieldShift δ) g / g) D₀ D₁' ∧
                            HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁' (ι + ↑m)
hasNormalizedIndex_mul_inv_coboundary : ∀ (δ : LocDilation) {z₀ : ℂ},
  z₀ ≠ 0 →
    ∀ {D g : LocField} {D₀ D₁ : RatFunc ℂ},
      HasHJet D D₀ D₁ →
        D₀ ≠ 0 →
          ∀ {ι : ℂ},
            HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁ ι →
              ∀ {k : ℤ} {g₀ g₁ : RatFunc ℂ},
                HasHJet ((algebraMap LocPoly LocField) locH ^ (-k) * g) g₀ g₁ →
                  g₀ ≠ 0 →
                    ∀ {m : ℤ},
                      HasOrderAt g₀ z₀ m →
                        ∃ D₁',
                          HasHJet (D * g / (LocDilation.fieldShift δ) g) D₀ D₁' ∧
                            HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁' (ι - ↑m)
hasNormalizedIndex_gauge_of_isJointRegular : ∀ (δ : LocDilation) {z₀ : ℂ},
  z₀ ≠ 0 →
    ∀ {r : ℕ} {B G : Matrix (Fin r) (Fin r) LocField},
      IsJointRegular z₀ G →
        ∀ {D₀ D₁ : RatFunc ℂ},
          HasHJet (Matrix.det B) D₀ D₁ →
            D₀ ≠ 0 →
              ∀ {ι : ℂ},
                HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁ ι →
                  ∃ D₁',
                    HasHJet (Matrix.det (G⁻¹ * B * Matrix.map G ⇑(LocDilation.fieldShift δ))) D₀ D₁' ∧
                      HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁' ι
hasNormalizedIndex_rescale : ∀ (δ : LocDilation) {a : ℂ} (ha : a ≠ 0) {A B : LocPoly},
  locJet0 B ≠ 0 →
    ∀ {D₀ D₁ : RatFunc ℂ},
      HasHJet ((algebraMap LocPoly LocField) A / (algebraMap LocPoly LocField) B) D₀ D₁ →
        ∀ {z₀ ι : ℂ},
          HasHJet ((algebraMap LocPoly LocField) ((locRescale a) A) / (algebraMap LocPoly LocField) ((locRescale a) B))
              D₀ (RatFunc.C a * D₁) ∧
            (HasNormalizedIndex (LocDilation.c (locDilationRescale δ a ha)) z₀ D₀ (RatFunc.C a * D₁) ι ↔
              HasNormalizedIndex (LocDilation.c δ) z₀ D₀ D₁ ι)
@release_hasSimpleResidue_ramify : ∀ {f : RatFunc ℂ} {z₀ ι : ℂ},
  HasSimpleResidue f z₀ ι →
    ∀ {e : ℕ} (he : 0 < e), HasSimpleResidue ((ratRamifyR z₀ e he) f * ↑e * RatFunc.X ^ (e - 1)) 0 (↑e * ι)
release_hasNormalizedIndex_powerSubst : ∀ (δ : LocDilation) {a : ℂ} (ha : a ≠ 0) {k : ℕ} (hk : 0 < k) {z₀ : ℂ},
  z₀ ≠ 0 →
    ∀ {A B : LocPoly},
      locJet0 B ≠ 0 →
        ∀ {D₀ D₁ : RatFunc ℂ},
          HasHJet ((algebraMap LocPoly LocField) A / (algebraMap LocPoly LocField) B) D₀ D₁ →
            ∀ {ι : ℂ},
              HasNormalizedIndex (LocDilation.c (locDilationPow δ k hk)) (a * z₀ ^ k) D₀ D₁ ι →
                HasHJet
                    ((algebraMap LocPoly LocField) ((locPowerSubst a k) A) /
                      (algebraMap LocPoly LocField) ((locPowerSubst a k) B))
                    ((ratPowerSubstR a k ha hk) D₀) ((ratPowerSubstR a k ha hk) D₁) ∧
                  HasNormalizedIndex (LocDilation.c δ) z₀ ((ratPowerSubstR a k ha hk) D₀)
                    ((ratPowerSubstR a k ha hk) D₁) ι
@exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational : ∀ {P : RecOp},
  0 < Polynomial.natDegree P →
    (∀ {β : Coeff},
        β ≠ 0 →
          ∀ {S R : RecOp},
            Polynomial.C β * P = oreMul coeffShift S R →
              Polynomial.natDegree R = 0 ∨ Polynomial.natDegree R = Polynomial.natDegree P) →
      ∀ {f : ℤ → RatFunc ℚ},
        ¬EventuallyRational f →
          (EventuallyRational fun n => opApplyField P f n) →
            ∀ {Q : RecOp} {n₁ : ℤ},
              (∀ (n : ℤ), n₁ ≤ n → opApplyField Q f n = 0) →
                ∃ β, β ≠ 0 ∧ ∃ T, Polynomial.C β * Q = oreMul coeffShift T P
@exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous : ∀ {P : RecOp},
  0 < Polynomial.natDegree P →
    (∀ {β : Coeff},
        β ≠ 0 →
          ∀ {S R : RecOp},
            Polynomial.C β * P = oreMul coeffShift S R →
              Polynomial.natDegree R = 0 ∨ Polynomial.natDegree R = Polynomial.natDegree P) →
      ∀ {f : ℤ → RatFunc ℚ},
        (¬∃ n₀, ∀ (n : ℤ), n₀ ≤ n → f n = 0) →
          ∀ {n₀ : ℤ},
            (∀ (n : ℤ), n₀ ≤ n → opApplyField P f n = 0) →
              ∀ {Q : RecOp} {n₁ : ℤ},
                (∀ (n : ℤ), n₁ ≤ n → opApplyField Q f n = 0) →
                  ∃ β, β ≠ 0 ∧ ∃ T, Polynomial.C β * Q = oreMul coeffShift T P
@toComparison_specialize_dvd_of_tail_annihilator_gauge : ∀ {P : RecOp},
  0 < Polynomial.natDegree P →
    specialize P ≠ 0 →
      (∀ {β : Coeff},
          β ≠ 0 →
            ∀ {S R : RecOp},
              Polynomial.C β * P = oreMul coeffShift S R →
                Polynomial.natDegree R = 0 ∨ Polynomial.natDegree R = Polynomial.natDegree P) →
        ∀ {F : ℤ → RatFunc ℚ},
          ¬EventuallyRational F →
            (EventuallyRational fun n => opApplyField P F n) →
              ∀ {J : ℤ → RatFunc ℚ},
                (∀ (n : ℤ), 1 ≤ n → J n = quantumInt n * F n) →
                  ∀ {Q : RecOp},
                    Polynomial.IsPrimitive Q →
                      (∃ c, c ≠ 0 ∧ ∃ n₀, ∀ (n : ℤ), n₀ ≤ n → opApplyField (Polynomial.C c * Q) J n = 0) →
                        toComparison (specialize P) ∣ toComparison (specialize Q)
@release_seq_theoremS : ∀ {P : Polynomial SeqField},
  OreIrreducible seqShift P →
    ∀ {F : SeqGerm},
      F ∉ RingHom.range seqEvalR →
        diffAct seqEvalR seqGermShift P F ∈ RingHom.range seqEvalR →
          ∀ {G : Polynomial SeqField}, diffAct seqEvalR seqGermShift G F = 0 → ∃ H, G = oreMul seqShift H P
@toyRecOp_pseudoIrreducible : ∀ {β : Coeff},
  β ≠ 0 →
    ∀ {S R : RecOp},
      Polynomial.C β * toyRecOp = oreMul coeffShift S R →
        Polynomial.natDegree R = 0 ∨ Polynomial.natDegree R = Polynomial.natDegree toyRecOp
@exists_C_mul_eq_oreMul_toyRecOp : ∀ {Q : RecOp} {n₁ : ℤ},
  (∀ (n : ℤ), n₁ ≤ n → opApplyField Q toySeq n = 0) →
    ∃ β, β ≠ 0 ∧ ∃ T, Polynomial.C β * Q = oreMul coeffShift T toyRecOp
toyRecOp_primitive_specialize : Polynomial.IsPrimitive toyRecOp ∧
  Polynomial.natDegree toyRecOp = 2 ∧
    specialize toyRecOp = (Polynomial.X - Polynomial.C Polynomial.X) * (Polynomial.X + Polynomial.C (Polynomial.X - 2))
locFactored_nodeIndex : locNodeIndex 1 1 1 (opJet1 locFactoredOp) (locToyBlock 0) (locToyBlock 1)
      (locCofactor locToyBlock 0 1) 1 1 =
    -1 ∧
  locNodeIndex 1 1 1 (opJet1 locFactoredOp) (locToyBlock 1) (locToyBlock 0) (locCofactor locToyBlock 1 0) 1 1 = 0
constSeq_minimum : (∀ (n : ℤ), opApplyField (Polynomial.X - 1) constSeq n = 0) ∧
  ∀ {Q : RecOp} {n₁ : ℤ},
    (∀ (n : ℤ), n₁ ≤ n → opApplyField Q constSeq n = 0) →
      ∃ β, β ≠ 0 ∧ ∃ T, Polynomial.C β * Q = oreMul coeffShift T (Polynomial.X - 1)
constSeq_oversized : (∀ (n : ℤ), opApplyField (oreMul coeffShift toyRecOp (Polynomial.X - 1)) constSeq n = 0) ∧
  specialize (oreMul coeffShift toyRecOp (Polynomial.X - 1)) =
      (Polynomial.X - Polynomial.C Polynomial.X) * (Polynomial.X + Polynomial.C (Polynomial.X - 2)) *
        (Polynomial.X - 1) ∧
    ¬toComparison (Polynomial.X - Polynomial.C Polynomial.X) ∣ toComparison (specialize (Polynomial.X - 1)) ∧
      ¬toComparison (Polynomial.X + Polynomial.C (Polynomial.X - 2)) ∣ toComparison (specialize (Polynomial.X - 1))
constSeq_not_selected : EventuallyRational constSeq ∧ ∀ (n : ℤ), n ≠ 0 → opApplyField toyRecOp constSeq n ≠ 0
not_weakLatticeLemma : ¬WeakLatticeLemma
toy_theoremI : OreIrreducible (LocDilation.fieldShiftHom toyDilation)
    (Polynomial.map (algebraMap LocPoly LocField) locToyOp) ∧
  (∀ (n : ℤ), opApplyField toyRecOp toySeq n = 0) ∧
    (∀ {Q : RecOp} {n₁ : ℤ},
        (∀ (n : ℤ), n₁ ≤ n → opApplyField Q toySeq n = 0) →
          ∃ β, β ≠ 0 ∧ ∃ T, Polynomial.C β * Q = oreMul coeffShift T toyRecOp) ∧
      Polynomial.IsPrimitive toyRecOp ∧
        specialize toyRecOp =
          (Polynomial.X - Polynomial.C Polynomial.X) * (Polynomial.X + Polynomial.C (Polynomial.X - 2))
pairQJets_abNode : ∀ (m : ℕ),
  2 ≤ m →
    ∀ {m₀ : ℂ},
      ↑m * (m₀ ^ 2) ^ 2 - (2 * ↑m + 1) * m₀ ^ 2 + ↑m = 0 →
        LocAllowedNode (pairQJetRow (famTransferOp m)) (pairQJetBlocks m) (pairQJetKappa₁ m) (pairQJetKappa₂ m) 0 2 m₀
            1 ∧
          locNodeIndex (LocDilation.c pairQJetDilation) m₀ 1 (opJet1 (pairQJetRow (famTransferOp m)))
                (pairQJetBlocks m 0) (pairQJetBlocks m 2) (locCofactor (pairQJetBlocks m) 0 2) (pairQJetKappa₁ m)
                (pairQJetKappa₂ m) =
              -1 / 2 ∧
            locNodeIndex (LocDilation.c pairQJetDilation) m₀ 1 (opJet1 (pairQJetRow (famTransferOp m)))
                (pairQJetBlocks m 2) (pairQJetBlocks m 0) (locCofactor (pairQJetBlocks m) 2 0) (pairQJetKappa₁ m)
                (pairQJetKappa₂ m) =
              -1 / 2
pairQJets_ebNode : ∀ (m : ℕ),
  2 ≤ m →
    ∀ {m₀ : ℂ},
      ↑m * (2 * ↑m + 1) * (m₀ ^ 2) ^ 2 + (4 * ↑m ^ 2 + 2 * ↑m + 1) * m₀ ^ 2 + ↑m * (2 * ↑m + 1) = 0 →
        LocAllowedNode (pairQJetRow (famTransferOp m)) (pairQJetBlocks m) (pairQJetKappa₁ m) (pairQJetKappa₂ m) 1 2 m₀
            (ebNodeL m m₀)⁻¹ ∧
          locNodeIndex (LocDilation.c pairQJetDilation) m₀ (ebNodeL m m₀)⁻¹ (opJet1 (pairQJetRow (famTransferOp m)))
                (pairQJetBlocks m 1) (pairQJetBlocks m 2) (locCofactor (pairQJetBlocks m) 1 2) (pairQJetKappa₁ m)
                (pairQJetKappa₂ m) =
              -1 / 2 ∧
            locNodeIndex (LocDilation.c pairQJetDilation) m₀ (ebNodeL m m₀)⁻¹ (opJet1 (pairQJetRow (famTransferOp m)))
                (pairQJetBlocks m 2) (pairQJetBlocks m 1) (locCofactor (pairQJetBlocks m) 2 1) (pairQJetKappa₁ m)
                (pairQJetKappa₂ m) =
              -1 / 2
pairQ_transferOp_oreIrreducible : ∀ (r s : ℕ),
  IsTorusPair r s →
    OreIrreducible coeffShiftField (Polynomial.map (algebraMap Coeff (FractionRing Coeff)) (famTransferOp (r * s)))
def AJConjecture.extraFactorMirror : Polynomial (Polynomial ℤ) :=
Polynomial.C (Polynomial.X ^ 4) * Polynomial.X ^ 2 -
    Polynomial.C (Polynomial.X ^ 4 - 4 * Polynomial.X ^ 2 + 1) * Polynomial.X +
  1
toComparison_extraFactorMirror : toComparison extraFactorMirror =
  LaurentPolynomial.T 2 * LaurentPolynomial.invert (toComparison extraFactor)
@exists_extraFactorMirror_zero_not_famBound_zero : ∀ {m : ℕ},
  0 < m → ∃ p, evalPoint (mapC extraFactorMirror) p = 0 ∧ evalPoint (mapC (famBound m)) p ≠ 0
@isCoprime_extraFactorMirror_famBound : ∀ {m : ℕ},
  0 < m → IsCoprime (toComparison extraFactorMirror) (toComparison (famBound m))
@isCoprime_extraFactorMirror_pair : ∀ {r s : ℕ} (h : IsTorusPair r s) {A : Polynomial (Polynomial ℤ)},
  IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A →
    IsCoprime (toComparison extraFactorMirror) (toComparison A)
@not_ajSquareFree_mirror_pair : ∀ {r s : ℕ} (h : IsTorusPair r s) (α : RecOp),
  IsRecurrencePolynomial (coloredJones (pairWhiteheadKnot r s h)) α →
    ∀ (A : Polynomial (Polynomial ℤ)),
      IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A →
        Ideal.radical (Ideal.span {toComparison (specialize α)}) ≠
          Ideal.span {LaurentPolynomial.invert (toComparison A)}
commute_meridian_longitude : ∀ (K : BraidKnot), Commute (meridian K) (longitude K)
map_longitude_eq_one_of_commGroup : ∀ (K : BraidKnot) {A : Type u_1} [inst : CommGroup A] (f : KnotGroup K →* A),
  f (longitude K) = 1
exists_hom_meridian_ofAdd_one : ∀ (K : BraidKnot), ∃ f, f (meridian K) = Multiplicative.ofAdd 1
@longitude_mul_meridian_pow_torusPairKnot : ∀ {r s : ℕ} (h : IsTorusPair r s),
  longitude (torusPairKnot r s h) * meridian (torusPairKnot r s h) ^ (r * s) = torusFullProd h ^ s
@torusFullProd_pow_mem_center : ∀ {r s : ℕ} (h : IsTorusPair r s),
  torusFullProd h ^ s ∈ Subgroup.center (KnotGroup (torusPairKnot r s h))
coloredJones_two_trefoil : coloredJones (torusPairKnot 2 3 isTorusPair_two_three) 2 =
  (LaurentPolynomial.T 2 + LaurentPolynomial.T (-2)) *
    (LaurentPolynomial.T (-4) + LaurentPolynomial.T (-12) - LaurentPolynomial.T (-16))
@eigenvalueSet_trefoil_subset : ∀ {p : ℂ × ℂ},
  p ∈ eigenvalueSet (torusPairKnot 2 3 isTorusPair_two_three) → Prod.snd p = 1 ∨ Prod.snd p * Prod.fst p ^ 6 = -1
@mem_eigenvalueSet_trefoil : ∀ {M : ℂ},
  M ≠ 0 → (M, -(M ^ 6)⁻¹) ∈ eigenvalueSet (torusPairKnot 2 3 isTorusPair_two_three)
```
