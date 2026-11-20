# The further claims of the paper: Sections 7.6, 8.4, 8.5, 9 and Theorem B.1 (4)

**Status (2026-11-20).** The claims of *Whitehead doubles and the failure of the AJ conjecture* ([arXiv:2611.24826v1](https://arxiv.org/abs/2611.24826v1)) beyond Theorem 1.1 that need no topology or hyperbolic geometry are proved in Lean, without `sorry`, without `native_decide` and without new axioms, in the library [`lean/Proofs/AJPaper/`](../lean/Proofs/AJPaper/) (133 files, about 18,800 lines, on top of the four earlier libraries, which are unchanged). Eleven of the theorems are in the solution and the challenge for `lake comparator`. The local checks pass; **`lake comparator` has not been run**.

This note says what is proved, where the Lean statements differ from the paper, and what remains outside Lean. For Theorem 1.1 itself see [`FOUR_FAMILIES.md`](FOUR_FAMILIES.md); for the untwisted family, [`V1_SCOPE.md`](V1_SCOPE.md).

## 1. What is proved

`f_S` ranges over the classical limits `Q(-1, M, L)` of the nonzero primitive elements `Q` of the localized annihilator of the coloured Jones function (the recurrence polynomial among them), `A_S` over all A-polynomials, divisibility and association are in `R = ℚ(M)[L, L⁻¹]`, `a = η·rs - ℓ`, and `𝒫_k` is `twP k`. The knots are the closed braids `twFamilyKnot r s h σ η ℓ` of the four families. "Challenge" is the name in `lean/comparator.json`.

| Paper | Statement proved | Lean | Challenge |
|---|---|---|---|
| **Corollary 8.3** | for `ℓ = 0`, all four families: `A_S ∣ f_S` | `corollary_untwisted_reverse` | `release_corollaryUntwisted` |
| **§8.4**, after Cor. 8.3 | for every twist and both clasps: `(L - 1)·E·𝒫_a ∣ f_S` (positive clasp: `(L - 1)·E^∨·𝒫_(-a)` reversed in `L`); in particular `L - 1 ∣ f_S` | `ppl_symbol_dvd_negClasp`, `ppl_symbol_dvd_posClasp`, `ppl_sub_one_dvd` | `release_wholeSymbolAllTwists`, `release_subOneDvd` |
| §5 and §6.7 at `a = 0` (stronger than the paper, see Section 2) | the transfer operator `P_a` is irreducible for every integer `a` | `ppl_no_quadratic`, `ppl_irreducible` | `ppl_irreducible` |
| **§8.5** | every raw annihilator, complex coefficients included, specializes to a function vanishing on `G = 0`; a point of `G = 0` lies outside the closure of the classical eigenvalue set; the ideal formulations of Tran (Conjecture 2) and of Sikora (Conjecture 9, `sl₂`) fail | `theoremIdealFormulations` | `release_idealFormulations` |
| **Definition 9.1, Corollary 9.2** | the torus-companion fingerprints of the two Whitehead patterns are exactly the associates of `E`, respectively `E^∨` | `isTorusFingerprint_extraFactor`, `isTorusFingerprint_extraFactorMirror` | `corollary_whitehead_fingerprint` |
| **§7.6**, satellites | `(L - 1)·𝒫_(-ℓ) ∣ A_S` (positive clasp: `(L - 1)·𝒫_ℓ` reversed in `L`) | `ppa_fillingFactor_dvd_neg`, `ppa_fillingFactor_dvd_pos` | `release_fillingFactor` |
| §7.6 with the bound (41) (not stated in the paper in this form) | `A_S` is associated to `(L - 1)·𝒫_(-ℓ)` or to the full bound `(L - 1)·𝒫_(-ℓ)·𝒫_a`, and to `(L - 1)·𝒫_(-ℓ)` when `a = 0` | `ppa_aPolynomial_cases_neg`, `…_pos`, `ppa_aPolynomial_of_index_zero_neg`, `…_pos` | `release_fillingDichotomy` |
| **§7.6**, twist knots | `A_(Z_(-k)) ≐ (L - 1)·𝒫_k` for every `k ∈ ℤ` | `ppa_aPolynomial_twistKnot`, `ppa_aPolynomial_pureClosure` | `release_twistKnots` |
| **Theorem B.1 (4)**, Appendix B.5 | Zheng's estimates hold for the companions `T(a, 2)`, `a ≥ 3` odd; the diagonal sum is asymptotic to its nonzero leading term, without hypothesis | `zhengVerbatim_holds`, `zhengEstimates_holds`, `geo_phys_holds` | `zhengEstimates_holds`, `geo_phys_holds` |

Exact types: [`lean/checks/PAPER_THEOREMS.txt`](../lean/checks/PAPER_THEOREMS.txt); axioms: [`lean/checks/PrintAxiomsPaper.expected.txt`](../lean/checks/PrintAxiomsPaper.expected.txt).

| Package (`lean/Proofs/AJPaper/`) | Files, lines | Content |
|---|---|---|
| `Sharp/` | 11, 1,065 | §8.4: the whole symbol in the specialized minimum for `a ≠ 0`, Corollary 8.3, the symmetry `𝒫_k(M⁻¹, L⁻¹) ≐ 𝒫_k` |
| `Divisor/` | 16, 2,436 | the index `a = 0`: the adjoint of `P_0` has no right factor of order one, hence `P_0` has no right factor of order two and is irreducible; the whole symbol for every twist |
| `Ideal/` | 15, 1,587 | §8.5: operators with complex coefficients, the reduction to integer coefficients, the explicit point, the two conjectures and their failure |
| `Finger/` | 11, 1,081 | §9: the extra support `Δ_K`, fingerprints, the trefoil test and its mirror image |
| `Filling/` | 29, 4,759 | §7.6: representations with abelian companion for the twisted braids, the filling factor, the dichotomy, the twist knots |
| `Zheng/` | 51, 7,877 | Zheng's Lemma 3.2, Lemma 3.3, (5.12), (5.20) and Proposition 4.1, and the unconditional diagonal theorem |

## 2. Where Lean and the paper differ

Nothing in these sections of the paper was found false. The differences:

**The index `a = 0` (Sections 1, 5.6, 6.7, 8.4).** The paper excludes only first-order right divisors of `P_0`, says that the degree of the selected divisor `R_0` is "two or three", and in §8.4 obtains `L - 1 ∣ f_S` at `a = 0` from Lê's general divisibility, "even if the selected divisor specializes to the quadratic alone". Lean proves more: `P_0` is irreducible (`ppl_irreducible`), so the selected divisor is `P_0`, and `(L - 1)·E ∣ f_S` at `a = 0` (`release_indexZero`). Lê's proposition is not used and is not formalized; for a general knot it needs the Melvin–Morton expansion. The caveat of §8.4 and the phrase "two or three" can be dropped.

**The positive clasp.** The paper transports statements to the positive clasp by `M ↦ M⁻¹`; the library's classical bound is the bound of the mirror knot reversed in `L`. The two agree up to a unit of `R` because `𝒫_k(M⁻¹, L⁻¹) ≐ 𝒫_k` for every `k` (`pps_twistPoly_inv`, `pps_twistPolyNeg_inv`), a symmetry the paper uses without stating it.

**§8.5.** The two cited conjectures are formal predicates on a closed braid, `PpiTranConjecture` and `PpiSikoraConjecture` (`Ideal/PpIConjectures.lean`), written from the sources (Tran, arXiv:1111.5065, Conjecture 2; Sikora, arXiv:0807.0943v2, Conjecture 9). The header of that file lists the four points where the predicate interprets the source: the A-ideal is the ideal of functions vanishing on the library's eigenvalue set; the specialized invariant ideal is taken as the ideal it generates; Sikora's coefficient ring is `ℂ[t^{±2}]` through `q^{1/2} = t²`, with `G = SL₂(ℂ)`; his equivalent statement about zero sets is not formalized separately. The "generic point" of the paper is the explicit point `(2, L₀)` with `L₀² - L₀ + 16 = 0`, and its mirror analogue.

**§9.** `Δ_K` and the fingerprint are defined up to association, with no representative chosen (`Finger/PpFDefs.lean`). The family of "all nontrivial torus companions of both chiralities" is `T(r, ±s)` for coprime `2 ≤ r < s`. The positive-clasp half needs two general facts that the paper leaves implicit: the recurrence polynomial of the mirror image is the mirror of the recurrence polynomial, and the A-polynomial of the mirror image is the A-polynomial with `L` inverted, as an equality up to units (`ppf_recurrencePolynomial_bar`, `ppf_aPolynomial_inv`). The statements of §9 about general patterns (`F_tor(P^*)`, reindexing of twists), Conjecture 9.3 and the discussion paragraphs are not formalized: the library has no notion of a pattern.

**§7.6.** The paper extends a representation of the pattern over the companion by its abelianization. The library has the satellite structure only in the forward direction (a homomorphism from the companion group), so the representations are built directly as fixed tuples of the explicit twisted braids. "Generic" is `M ≠ 0`, `M⁴ ≠ 1`, `L ≠ -M²`. The paper states the divisibility for an arbitrary companion; Lean proves it for the four families. The dichotomy for `A_S` is a consequence that the paper does not state; whether the factor `𝒫_a` occurs for `ℓ ≠ 0` (the paper's question after Corollary 8.3) is left open here as there.

**Twist knots.** The library had no braids for them. `ppaTwistKnot ℓ` is the closure of `ppaTwistWord ℓ` on `3 + twExtra ℓ` strands (`Filling/PpATwistBlocks.lean`): the twist chain of the twisted doubles on three base strands, followed by `σ₁⁻¹ σ₀⁻¹ σ₁⁻¹`. That these closures are the twist knots `Z_ℓ` with the paper's sign of `ℓ` is, as for all knots here, outside Lean. Evidence from the independent audit of 20 November: for `-4 ≤ ℓ ≤ 4` the closures have one component, Alexander polynomial `ℓ·t² + (1 - 2ℓ)·t + ℓ` up to units, and the Jones polynomials of `10_1, 8_1, 6_1, 4_1`, the unknot, the left-handed trefoil, `5_2, 7_2, 9_2`; SnapPy identifies the complements; `twP 1` is the Cooper–Long A-polynomial of the figure-eight knot and `twP (-1) = L + M⁶` that of the left-handed trefoil.

**Theorem B.1 (4).** `geo_phys_holds` states that the leading term is nonzero and that the quotient of the diagonal sum by it tends to 1; the statements on the window and on the limits of the coordinates were already unconditional (`geo_phys_coordinates`, `geo_phys_endpoint` in `AJHandoff/Geometry/`). `zhengEstimates_holds` discharges the hypothesis `ZhengEstimates a` of the full diagonal statement `geo_phys_diagonal` and of the G-PHYS clause of `geo_theoremG` (`release_theoremG` in the challenge), which keep their conditional form in the earlier library. The range is `a ≥ 3` odd and cannot be enlarged: `ZhengProp41 1` and `ZhengEq512 2` are false. Zheng's arguments were found correct but incomplete in three places, none affecting a statement: Lemma 3.2 needs the bound also on the boundary of the triangle; his (5.5) is cited and the residue count (5.10) only asserted (both re-derived as exact identities); the window of (5.20) exceeds that of his Lemma 5.2 by one step. The printed sign error in his coefficient `b` was documented earlier ([`ZHENG_CORRECTED_PROOFS.md`](ZHENG_CORRECTED_PROOFS.md)). The contour shift across the poles of the kernel is built from the rectangle theorem, since Mathlib has no residue theorem.

## 3. What remains outside Lean

Of the paper's claims, after this library:

- Section 2 and Proposition 2.1 (the two published diagrams are the same marked pattern), and with it the reading of every closed braid as the knot the paper names;
- that distinct pairs `(r, s)` give distinct knot types (§7.5: the JSJ decomposition; Lean has non-Markov-equivalence and different colour-2 Jones polynomials);
- that Tillmann's triangulation is the Whitehead link exterior and that its volume is hyperbolic volume (§B.4; Lean has `m(E) = 4G/π` and the sum of the Bloch–Wigner values);
- Lê's divisibility for a general knot (not needed for the knots of the paper);
- the general-pattern statements and the discussion of Section 9, and Section 1.3, which are not theorems about the knots of the library.

## 4. What was checked

In the folder `lean`, on the tree that contains this note (record: [`reports/local-checks-2026-11-20b.md`](../reports/local-checks-2026-11-20b.md)):

| Check | Result |
|---|---|
| `lake build`, `lake build Challenge` | no errors; no `sorry` outside the 60 statements of the challenge |
| `checks/PrintAxiomsPaper.lean` (the eleven challenge theorems and 36 further results) | only `propext`, `Classical.choice`, `Quot.sound`; output recorded |
| `tools/make_challenge.py --check`, `tools/closure_decls.py` | 107 challenge modules match the sources; the copied declarations are the computed closure of the 60 statements (106 source files, 414 declarations) |
| `tools/compare_reach.py` | the 46,912 constants reachable from the 60 statements are identical in challenge and solution; the 60 theorem types are identical |
| `tools/check_autoimplicit.sh` | the challenge, the solution and every file of `Proofs/AJPaper/` elaborate with `autoImplicit` off |
| `tools/AuditReach.lean` | the group of Sections 7.6, 8.4, 8.5, 9 reaches no watched premise; the diagonal theorem reaches only Zheng's estimates, which are proved |
| two independent audits of the statements against the paper and the cited sources (2026-11-20) | faithful; the deviations are those of Section 2 |
| `lake comparator` | not run |
