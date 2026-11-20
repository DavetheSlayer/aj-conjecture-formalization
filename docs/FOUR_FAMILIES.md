# The four families of twisted Whitehead doubles

**Status (2026-11-20).** Theorem 1.1 of *Whitehead doubles and the failure of the AJ conjecture* ([arXiv:2611.24826v1](https://arxiv.org/abs/2611.24826v1)) is proved in Lean without `sorry`, without `native_decide` and without new axioms, as `AJConjecture.theoremFourFamilies` in the library [`lean/Proofs/AJTwist/`](../lean/Proofs/AJTwist/) (223 files, about 40,400 lines, on top of the three earlier libraries, which are unchanged). It has no hypothesis from the literature. The solution and the challenge for `lake comparator` contain it in braid-word form, together with the formula for the coloured Jones functions. The local checks pass; **`lake comparator` has not been run**, so release verification is not claimed.

This note says what is proved, how the Lean proof relates to the manuscript, and what a reader has to accept from outside Lean. It extends the v1 scope ([`V1_SCOPE.md`](V1_SCOPE.md)), which was limited to the untwisted negative-clasp doubles.

The formalization was made from revision 5 of the manuscript ([handoff of 18 November 2026](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/e4a4786b01dec67c542924d82a4c1a2378e6a05d/handoffs/2026-11-18-whitehead-four-family)), under the title *Whitehead doubles and the failure of the square-free AJ conjecture*; the arXiv version is a later revision. Theorem 1.1 is the same statement in both, and Sections 2 to 8.2 carry the same numbers, so the section numbers below and in the comments of the Lean files apply to the arXiv version as well. Sections 1.3, 7.6, 8.4 and 8.5 of the arXiv version are new and are not formalized. Appendix E of arXiv v1 describes the formalization before this library existed.

## 1. The theorem

For coprime `2 ≤ r < s`, a twist `ℓ ∈ ℤ`, a clasp sign and a companion `T(r, ±s)`, the manuscript writes `W_{ε,ℓ}(T_η)` for the `ℓ`-twisted Whitehead double with clasp sign `ε` of the torus knot `T_η`. In Lean these four families are `twFamilyKnot r s h σ η ℓ` (`σ = true`: negative clasp; `η = true`: companion `T(r, s)`, `η = false`: companion `T(r, -s)`), explicit closed braids (Section 2).

```lean
theorem theoremFourFamilies :
    (∀ (r s : ℕ) (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ),
      TwFamilyClauses (twFamilyKnot r s h true η ℓ) extraFactor
          (twBound (-ℓ) (twIndex η r s ℓ)) ∧
        TwFamilyClauses (twFamilyKnot r s h false η ℓ) extraFactorMirror
          (twBound ℓ (-(twIndex η r s ℓ))).reverse) ∧
    Irreducible (toComparison extraFactor) ∧ Irreducible (toComparison extraFactorMirror) ∧
    ∀ (r s : ℕ) (h : IsTorusPair r s),
      twFamilyKnot r s h true true 0 = pairWhiteheadKnot r s h ∧
        twBound (-0) (twIndex true r s 0) = famBound (r * s)
```

`TwFamilyClauses K G P` (file `Main/TwMClauses.lean`) is the list of clauses of Theorem T with the factor `G` and the classical bound `P` as parameters:

1. the localized annihilator of the coloured Jones function of `K` contains a nonzero operator;
2. a recurrence polynomial of `K` exists;
3. for every nonzero primitive operator `Q` of the localized annihilator, the classical limit `Q(-1, M, L)` is nonzero and divisible by `G` in `ℚ(M)[L, L⁻¹]`;
4. an A-polynomial of `K` exists;
5. every A-polynomial of `K` divides `P` and is coprime to `G` in `ℚ(M)[L, L⁻¹]`;
6. the localized square-free `SL₂` AJ statement `AJSquareFree K` fails.

The parameters are those of the manuscript:

| | negative clasp | positive clasp |
|---|---|---|
| factor `G` | `E = L² - (M⁴ - 4M² + 1)L + M⁴` (`extraFactor`) | `E^∨ = M⁴E(M⁻¹, L) = M⁴L² - (M⁴ - 4M² + 1)L + 1` (`extraFactorMirror`) |
| bound `P` | `(L - 1)·𝒫_(-ℓ)·𝒫_a`, `a = η·rs - ℓ` (`twBound (-ℓ) (twIndex η r s ℓ)`) | the bound of the mirror knot `W_{-,-ℓ}(T_{-η})`, reversed in `L` |

Here `𝒫_k` (`twP k`) is `B_k` for `k ≥ 1` (`twistPoly k`), `1` for `k = 0` and `C_(-k)` for `k < 0` (`twistPolyNeg`). For the positive clasp the manuscript transports the bound by `M ↦ M⁻¹`; the Lean statement reverses it in `L`. The two forms differ by a unit `±M^j` of `ℚ(M)[L, L⁻¹]`, because every eigenvalue set is invariant under `(M, L) ↦ (M⁻¹, L⁻¹)` (`eigenvalueSet_symm`). The last clause of the theorem says that for `ℓ = 0`, the negative clasp and the companion `T(r, s)` the knot and the bound are those of `theoremT`; that instance of the theorem is the first clause of `theoremT` verbatim (`pairTClauses_of_twFamilyClauses`).

As in v1, the classical clause is the inclusion of the boundary eigenvalues in the bound together with coprimality; it does not determine the A-polynomial. The exact recurrence polynomial is not determined either: what is proved is that the factor divides the classical limit of every recurrence polynomial. Both sides are sharpened in [`FURTHER_CLAIMS.md`](FURTHER_CLAIMS.md): the whole symbol `(L - 1)·E·𝒫_a` divides the classical limit for every twist, and the A-polynomial is the companion-abelian factor `(L - 1)·𝒫_(-ℓ)` or the full bound.

## 2. The knots

`twWhiteheadKnot r s h ℓ σ` is the closure of the braid word `twWhiteheadWord r s ℓ σ` on `twStrands r s ℓ` strands (`Knot/TwKBlocks.lean`, `Knot/TwKKnot.lean`). The word is that of Theorem T (`pairBlocks r s`, a braided-surface presentation with `2c + 1` discs, `c = (r - 1)s`) with two changes: the first band is rerouted through a chain of bands over `2|ℓ|` new discs for `ℓ < 0` and `2ℓ + 4` new discs for `ℓ > 0`, which gives the band `ℓ` full twists and changes the writhe by `-2ℓ`; and for the positive clasp the two negative clasp letters become positive ones. A run of `|1 - 2ℓ|` letters on one level would **not** be a band with `1 - 2ℓ` half twists (it is the twisted double only for `ℓ ∈ {0, 1}`): `σ_i^k` is `k` parallel bands.

The two families over `T(r, -s)` are defined as mirror images: `twFamilyKnot r s h σ false ℓ` is the closure of the inverse of the braid of `twWhiteheadKnot r s h (-ℓ) (!σ)` (`BraidKnot.inv`). The mirror identity `(W_{ε,ℓ}(T_η))^* = W_{-ε,-ℓ}(T_{-η})` of the manuscript is therefore a definition in Lean, not a theorem. For the closure of an inverse braid the library proves that the coloured Jones function is conjugated by `t ↦ t⁻¹` (`coloredJones_inv`) and that the knot group is the same with the same meridian and the inverse longitude (`exists_knotGroup_inv_equiv`, `eigenvalueSet_inv'`).

What Lean proves about these closed braids, for every `ℓ` and both clasp signs:

- `isBandClasp_twWhiteheadKnot`: at every cabling thickness the Kauffman-bracket operator of the cut-open closed braid equals the operator of the band-and-clasp diagram over `T(r, s)`: the doubled companion, `2ℓ - 2(r - 1)s` half twists of the band (the blackboard framing `(r - 1)s` of the companion braid corrected to `ℓ` full twists), the clasp of sign `σ`. The writhe is `2(r - 1)s - 2ℓ ∓ 2` (`writhe_twWhiteheadKnot`). For `ℓ ≤ 0` it is proved through checked diagram moves (the move checker of the earlier libraries) together with an operator identity for the order of the twist beads; the twists `ℓ > 0` follow by a Cayley–Hamilton argument on the full-twist operator. The result is an identity of Kauffman-bracket operators; a diagram isotopy to the band-and-clasp diagram is not stated in Lean, in contrast to the untwisted case (`release_whDouble`).
- `release_fourFamilies_coloredJones` (in the challenge): the coloured Jones function is the cyclotomic formula of the manuscript with the input twisted by `q^(-a n(n+1))`.
- `isTwWhSatellite_twWhiteheadKnot`: the knot group has the satellite structure used on the classical side.

That these closed braids present the marked satellites `W_{ε,ℓ}(T_η)` of the manuscript is **not** a Lean theorem (Section 5). The evidence outside Lean is in [`scripts/four_families/`](../scripts/four_families/): the Alexander polynomial of 56 of the braids is `d·t² + (1 - 2d)·t + d` with `d = ℓ` for the negative and `d = -ℓ` for the positive clasp; the colour-2 value of the Lean coloured Jones function, recomputed from the definition, equals the manuscript's formula in 36 instances, each matching exactly one of 36 candidate triples (clasp, companion, twist); and `twistPoly k`, `twistPolyNeg k` equal the manuscript's `B_k`, `C_k` for `k ≤ 6`.

## 3. The proof and the manuscript

| Package (`lean/Proofs/AJTwist/`) | Files, lines | Manuscript | Content and main theorems |
|---|---|---|---|
| `TwDefs.lean` | 1, 146 | §2 | the index `a` (`twIndex`), signed half twists and clasps, the band-and-clasp interface `IsBandClasp`, mirror and inverse braids |
| `Knot/` | 32, 10,460 | §2 | the braids, their closures, the band-and-clasp identity for both clasp signs and all twists (`isBandClasp_twWhiteheadKnot`), the mirror (`coloredJones_inv`, `exists_knotGroup_inv_equiv`), the data definitions `twFamilyStrands`, `twFamilyWord` |
| `Quantum/` | 42, 4,958 | §3 | the coloured Jones function from the band-and-clasp identity (`twQ_coloredJones_negClasp`, `twQ_coloredJones_posClasp`); the transfer operators `P_a` for every integer `a` (`twTransferOp`, equal to the v1 operator for `a ≥ 1`), with special symbol divisible by `E` (`extraFactor_dvd_specialize_twTransferOp`); the transfer identity with its forcing in the span of the Gaussian periods (`twQ_transfer_mem_periodSpan`) |
| `Exist/` | 24, 2,176 | §8.1 | a nonzero annihilator of the formula exists for every `ℓ` (`twH_exists_annihilator`, `twH_knot`), by a finite-rank count on the inner Gaussian periods |
| `Factor/` | 54, 9,299 | §4, §5 | `P_a` has no proper right factor for `a ≠ 0` (`twf_irreducible`: two simple crossings with indices `-1/2` for `a ≥ 2` and `a < 0`, rank-one tests for `a = 1`) and no right factor of order one for `a = 0` (`twf_no_linear`) |
| `Select/` | 34, 6,484 | §6, §8.1 | the actual sequence selects the factor (`tws_selects`) and the factor survives in every nonzero primitive element of the localized annihilator (`tws_survival`) |
| `Classical/` | 28, 5,999 | §7 | the satellite structure of the knot group, the inclusion of the boundary eigenvalues in the bound, coprimality with the factor, existence of an A-polynomial (`twClassClauses_twFamilyKnot_neg`, `twClassClauses_twFamilyKnot_pos`) |
| `Main/` | 8, 925 | §8.2 | the mirror transport of the quantum clauses to the positive clasp (`twm_mirror_exists`, `twm_mirror_survival`) and the assembly (`theoremFourFamilies`) |

The exact types of these theorems are in [`lean/checks/FOUR_FAMILIES_THEOREMS.txt`](../lean/checks/FOUR_FAMILIES_THEOREMS.txt), their axioms in [`lean/checks/PrintAxiomsFourFamilies.expected.txt`](../lean/checks/PrintAxiomsFourFamilies.expected.txt).

No formula or constant of the manuscript was found to be wrong. Where the Lean proof differs from the written one:

| Manuscript | Lean |
|---|---|
| §8.1: a nonzero annihilator exists for `ℓ ≠ 0` by q-holonomicity (cited) | proved (`Exist/`): contiguity relations of the inner Gaussian periods give finitely many generators, hence a relation; no citation |
| Lemma 7.1 gives the inclusion `A_S ∣ (L - 1)𝒫_(-ℓ)𝒫_a`; the existence of the A-polynomial is taken for granted | existence proved from the inclusion by the Galois-descent lemma of the earlier library (`exists_isAPolynomialOf_of_isAutStable`); the inclusion holds at every point of the eigenvalue set, without an extra meridian factor |
| the two finite-sum forms of the clasp coefficients are identified by a citation | proved |
| §5.5: one sentence on the dual quotient | replaced by integrality of the right factor and multiplicativity of the end coefficients |
| §5.6: a second descent (`t ↦ it`) | not needed |
| §6.4: closure under rational coefficients (sketch) | bypassed: saturation and formal division |
| §8.2: the mirror transport preserves primitivity | holds when the denominators are cleared with the exact degrees, which the Lean proof tracks |
| coprimality of `G` and the bound by resultants | by a common-zero argument: a zero of `E` at `M = 2` at which the bound does not vanish |
| the mirror identity for the families over `T(r, -s)` | a definition (Section 2) |

The coloured Jones function is Lê's, in the variable `t` with `q = t⁴`, and the operator ring is `ℤ[t][M][L]` with the localized annihilator of the earlier libraries, as in v1.

## 4. Solution and challenge

[`lean/Solution.lean`](../lean/Solution.lean) states two theorems for the four families, with every knot given by its data, as for the v1 theorems: a claim is made for **every** `K : BraidKnot` with `K.strands = twFamilyStrands r s η ℓ` and `K.word = twFamilyWord r s σ η ℓ`, and a separate clause says that such a `K` exists.

- `release_theoremFourFamilies`: such a closed braid exists for all parameters; each one satisfies `TwFamilyClauses` with the factor and the bound of Section 1; `E` and `E^∨` are irreducible in `ℚ(M)[L, L⁻¹]`; for `ℓ = 0`, the negative clasp and `T(r, s)` the strands, the word and the bound are those of Theorem T.
- `release_fourFamilies_coloredJones`: for the negative clasp the coloured Jones function of the closed braid is `twFormula η r s ℓ` at every integer colour; for the positive clasp its image under `t ↦ t⁻¹` is `twFormula (!η) r s (-ℓ)`, the formula of the mirror knot.

[`lean/Challenge.lean`](../lean/Challenge.lean) has the same two statements with `sorry`, after the 47 of v1. They add nine modules `Challenge/C_<name>.lean` with verbatim copies of 23 further declarations, and one declaration (`moebiusSubst`) to an existing module: the block lists and words (`twHeadTop`, `twChain`, `twExtra`, `twClaspBlock`, `twBlocks`, `twStrands`, `twWhiteheadWord`, `twFamilyStrands`, `twFamilyWord`, `mirrorWord`, `invWord`), the index and the polynomials (`twIndex`, `symbolTwistNeg`, `twistPolyNeg`, `twP`, `twBound`, `extraFactorMirror`), the clause list `TwFamilyClauses` and the formula (`twInput`, `twFormula`, `pairQCycloCoeff`, `pairQReducedFormula`, `pairQFormula`). `comparator.json` names the 49 theorems.

## 5. What a reader has to trust

The statement files of v1 (see [`README.md`](../README.md)) and the declarations listed in Section 4, nothing else. Outside Lean remain:

- that the closed braids `twFamilyKnot r s h σ η ℓ` present the satellites `W_{ε,ℓ}(T_η)` of the manuscript, with its marking. Lean proves the band-and-clasp operator identity, the writhe, the coloured Jones formula and the satellite structure of the knot group for the explicit braids; the reading of these as the twisted Whitehead doubles rests on the same facts as in v1 ([`V1_SCOPE.md`](V1_SCOPE.md), [`MARK_BRIDGE.md`](MARK_BRIDGE.md)) and on the computations of Section 2. No topology is formalized;
- that the closure of the inverse braid is the mirror image with the opposite orientation, and that the mirror image of `W_{ε,ℓ}(T_η)` is `W_{-ε,-ℓ}(T_{-η})`;
- the conventions of v1 for the two invariants (Kauffman state sum, Artin presentation with parallels, the definition of the A-polynomial, Lê's statement of the conjecture).

The theorem makes no claim that the knots are pairwise distinct.

## 6. What was checked

At the first upload (2026-11-20, 49 statements in the challenge), in the folder `lean`; the record is [`reports/local-checks-2026-11-20.md`](../reports/local-checks-2026-11-20.md). The counts of the present version, with the further claims of the paper, are in [`FURTHER_CLAIMS.md`](FURTHER_CLAIMS.md), Section 4.

| Check | Result |
|---|---|
| `lake build` (library and solution), `lake build Challenge` | no errors; no `sorry` outside the 49 statements of the challenge |
| `checks/PrintAxiomsFourFamilies.lean` (the two release theorems, `theoremFourFamilies` and 35 further results) | only `propext`, `Classical.choice`, `Quot.sound`; output recorded in `checks/PrintAxiomsFourFamilies.expected.txt` |
| the three earlier axiom listings | outputs equal to the recorded ones |
| `tools/make_challenge.py --check` | 98 challenge modules match the sources; `comparator.json` names the 49 theorems |
| `tools/closure_decls.py` | the declarations copied into the challenge are the computed closure of the 49 statements (97 source files, 376 declarations); for the 47 v1 statements it reproduces the earlier list |
| `tools/compare_reach.py` | the 46,846 constants reachable from the 49 statements are identical in challenge and solution (563 from this development); the 49 theorem types are identical |
| `tools/AuditReach.lean`, group `FOUR_FAMILIES` | none of the watched premises is reached (no estimate of Zheng, no JSJ input, no triangulation, no Markov equivalence, no `sorryAx`) |
| kernel replay (`leanchecker`, one process per module) of the 224 modules of `AJTwist`, of `SolutionDefs` and of `Solution` | all accepted |
| the scripts of `scripts/four_families/` (Section 2) | no mismatch; outputs recorded there |
| independent audit of the statement against the manuscript (2026-11-19) | faithful, with the deviations listed in Sections 1–3 |
| `lake comparator`, `nanoda` | not run |
