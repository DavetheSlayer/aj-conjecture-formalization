# AJ conjecture: Lean formalization and comparator records

Lean 4 sources, comparator inputs and verification records for

> Jinzheng Li, Yuqi Li, Hao-Yu Sun, *Whitehead doubles and the failure of the AJ conjecture*, [arXiv:2611.24826v1](https://arxiv.org/abs/2611.24826v1).

**Status (2026-11-20).** The main theorem of the paper (Theorem 1.1: the AJ radical equality fails for the twisted Whitehead doubles of the torus knots `T(r, ±s)`, for every integer twist, both clasp signs and both companion chiralities) the results on the untwisted family, and the further claims of Sections 7.6, 8.4, 8.5 and 9 and of Theorem B.1 (4) are proved in Lean 4 with Mathlib, without `sorry`, without `native_decide` and without axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The project builds and passes the local checks recorded in [`reports/local-checks-2026-11-20b.md`](reports/local-checks-2026-11-20b.md) (for the first upload: [`reports/local-checks-2026-11-20.md`](reports/local-checks-2026-11-20.md)). What remains outside Lean is topology and hyperbolic geometry: that the closed braids are the knots the paper names (Section 2), distinctness as knot types, and the identification of the triangulation and of hyperbolic volume. **`lake comparator` has not yet been run on this version**; the inputs for that run are in [`lean/`](lean/) and the instructions in [`COMPARATOR.md`](COMPARATOR.md). Until its report is added to [`reports/`](reports/), no comparator verification of this version is claimed. The only comparator acceptance on record is that of 15 November 2026 for the single-braid theorem at an earlier commit ([report](reports/comparator-2026-11-15.md)).

## The paper and the Lean theorems

All declarations are in the namespace `AJConjecture`. The column "Challenge" gives the names under which the result is among the 60 theorems of [`lean/comparator.json`](lean/comparator.json). The challenge states a result for every closed braid with the given number of strands and braid word, so that its statement mentions only data.

| Paper (arXiv v1) | Lean | Challenge |
|---|---|---|
| **Theorem 1.1**: for coprime `2 ≤ r < s`, every `ℓ ∈ ℤ`, both clasp signs and both companions, the annihilator is nonzero, `0 ≠ f_S`, `G ∣ f_S`, `gcd(G, A_S) = 1` with `G = E` (negative clasp) or `E^∨` (positive clasp) irreducible, and the radical equality fails | `theoremFourFamilies` (`lean/Proofs/AJTwist/Main/TwMTheorem.lean`) | `release_theoremFourFamilies`; the coloured Jones functions of the knots: `release_fourFamilies_coloredJones` |
| **Theorem 8.1**: the untwisted negative-clasp doubles `Z(T(r, s))`; `A ∣ (L - 1)B_rs` | `theoremT` (`lean/Proofs/AJHandoff/TorusKnot/PairKTheoremT.lean`) | `release_theoremT`; sharper, `A ≐ (L - 1)B_rs`: `release_classicalEquality` |
| distinct knots in Theorem 8.1 and Corollary 8.2 | proved as: the closed braids are pairwise not Markov equivalent, and their colour-2 coloured Jones polynomials differ | in `release_theoremT`; `release_coloredJones_two_ne` |
| **Corollary 8.2**: odd two-strand companions `T(2, 2k+1)` | `theoremF`, `ajFamily_main` | `ajFamily_main`, `release_pairWord_two` |
| **Theorem A.1**: the trefoil double has order 16, `f ≐ (L - 1)²B₆E`, `A ≐ (L - 1)B₆` | `minimalRecurrence_whiteheadTorusKnot` (every `k ≥ 1`: order `8k + 8`, `f ≐ (L - 1)²·E·B_{2(2k+1)}`), `aPolynomial_pair_associated_famBound`; the counterexample itself: `not_ajSquareFreeConjecture` | `release_minimalRecurrence`, `release_classicalEquality`, `not_ajSquareFreeConjecture` |
| **Section 4**: the crossing criterion (Theorem 4.2) and the selected sequence (Lemma 4.3) | the local Theorem I (`oreIrreducible_of_connected`, `locBlockDvd_iff_of_forbiddenEdge`, …) and the sequence theorem S of `lean/Proofs/AJHandoff/LocalTheory/` | 27 units, listed in [`docs/V1_SCOPE.md`](docs/V1_SCOPE.md) |
| **Section 5**: the nodes, the first jets and the factors of the satellite operators | for the untwisted family in `AJHandoff/TorusQuantum/`; for every index `a` in `AJTwist/Factor/` (`twf_irreducible`, `twf_no_linear`) | `pairQJets_abNode`, `pairQJets_ebNode`, `pairQ_transferOp_oreIrreducible` (untwisted family) |
| **Theorem B.1** (1)–(3) and `π·m(E) = Vol = 4G`: the curve `E`, its normalization, the completed-axis slice, the Mahler measure | `geo_theoremG`, `mahlerMeasure_extraFactor`, `whitehead_volume` | `release_theoremG`, `release_theoremG_supplement`, `ajFamily_main` |
| **Theorem B.1** (4): the actual diagonal | `geo_phys_holds`, without hypothesis: Zheng's estimates are proved for the companions `T(a, 2)`, `a ≥ 3` odd (`zhengVerbatim_holds`), with (5.16) and (5.19) for the corrected sign | `geo_phys_holds`, `zhengEstimates_holds`; the conditional forms `geo_phys_of_zhengVerbatim`, `zhengEstimates_of_verbatim` and `zhengEq516_holds`, `zhengEq519_of_zhengEq512` remain |
| Section 2 and Proposition 2.1: the diagrams are the named marked satellites | **not formalized.** For the untwisted family the closed braid reaches the band-and-clasp diagram by checked diagram moves; for all twists the Kauffman-bracket operators agree (`isBandClasp_twWhiteheadKnot`) | `release_whDouble`, `morseReach_whDouble`, `morseWrithe_eq_of_morseReach`, `zero_mem_bandLinkings_whBand` |
| **Corollary 8.3** and §8.4: `A_S ∣ f_S` for the untwisted doubles; the classical factors in `f_S` | `corollary_untwisted_reverse`; for every twist `(L - 1)·E·𝒫_a ∣ f_S`, also at `a = 0`, where the paper cites Lê (`ppl_symbol_dvd_negClasp`, `ppl_sub_one_dvd`); the transfer operator is irreducible for every `a` (`ppl_irreducible`) | `release_corollaryUntwisted`, `release_wholeSymbolAllTwists`, `release_subOneDvd`, `ppl_irreducible` |
| **§8.5**: the ideal formulations of Tran and of Sikora | `theoremIdealFormulations` | `release_idealFormulations` |
| **Definition 9.1, Corollary 9.2**: the torus-companion fingerprints | `isTorusFingerprint_extraFactor`, `isTorusFingerprint_extraFactorMirror` | `corollary_whitehead_fingerprint` |
| **§7.6**: `(L - 1)·𝒫_(-ℓ) ∣ A_S`; `A ≐ (L - 1)·𝒫_k` for the twist knots | `ppa_fillingFactor_dvd_neg`, `ppa_fillingFactor_dvd_pos`, `ppa_aPolynomial_twistKnot` | `release_fillingFactor`, `release_fillingDichotomy`, `release_twistKnots` |
| §7.5 (distinct knot types by the JSJ decomposition), §B.4 (the triangulation, hyperbolic volume), §1.3 and the discussion of §9 | **not formalized** (topology and geometry; discussion) | — |

Notes on the correspondence.

- *Theorem 1.1 was formalized after the paper was posted.* Appendix E of arXiv v1 ("What has been formally checked") describes the formalization at commit `78e38735` of the audit repository and says that it treats the untwisted negative-clasp doubles of right-handed torus knots only. That is the state of the three libraries `AJConjecture`, `AJFamily` and `AJHandoff` here, which are unchanged since (see [Provenance](#provenance)). The fourth library, `AJTwist`, proves Theorem 1.1 in full. It was written from revision 5 of the manuscript, which has the same Theorem 1.1 and the same section numbers 2 to 8.2 as arXiv v1. [`docs/FOUR_FAMILIES.md`](docs/FOUR_FAMILIES.md) gives the statement, the relation to the written proof, and what remains outside Lean.
- *The further claims.* [`docs/FURTHER_CLAIMS.md`](docs/FURTHER_CLAIMS.md) covers Sections 7.6, 8.4, 8.5, 9 and Theorem B.1 (4): the statements, where Lean proves more than the paper (the transfer operator is irreducible also at `a = 0`, so Lê's divisibility is not needed there), the four points where the formal versions of the two cited conjectures interpret their sources, and the evidence that the new braids for the twist knots are those knots.
- *Fewer inputs than the written proof.* The Lean proof of Theorem 1.1 does not cite q-holonomicity for the existence of a recurrence (it is proved for these sequences), and it proves the existence of the A-polynomial in the library's sense. No hypothesis from the literature remains in `theoremFourFamilies`.
- *What the classical clause says.* As in the paper, the classical side is the inclusion of the boundary eigenvalues in a bound, together with coprimality with `G`. For the positive clasp the Lean bound is the bound of the mirror knot reversed in `L`, where the paper inverts `M`; the two differ by a unit of `ℚ(M)[L, L⁻¹]`.
- *The knots are explicit closed braids.* Every theorem is about the closure of a braid word given in the statement. That these closures are the marked satellites of the paper is outside Lean; the evidence is described in [`docs/FOUR_FAMILIES.md`](docs/FOUR_FAMILIES.md), Section 2, [`docs/WHITEHEAD_BRIDGE.md`](docs/WHITEHEAD_BRIDGE.md) and [`docs/MARK_BRIDGE.md`](docs/MARK_BRIDGE.md), with the computations in [`scripts/`](scripts/). The families over `T(r, -s)` are defined as closures of inverse braids, so the paper's mirror identity is a definition here.

## Layout

| Path | Content |
|---|---|
| [`lean/`](lean/) | The Lake project (Lean `v4.36.0-rc2`, Mathlib pinned to `26573066084e6e2aa8526ea358bc43b66d96f970`; `lake-manifest.json` pins the transitive dependencies). |
| `lean/Proofs/` | All proofs: 1,165 files, about 170,000 lines, in five libraries. `AJConjecture/` (266 files: the definitions of the statement, the skein-theoretic and q-algebraic machinery, the unknot sanity check); `AJFamily/` (188 files: the family `T(2, 2k+1)`, the Mahler measure and the volume); `AJHandoff/` (349 files: Theorem T for all `T(r, s)`, Theorems I and S, the minimal recurrence, Theorem G, the satellite bridge, Zheng's corrected estimates, the marked-knot bridge); `AJTwist/` (223 files: the four families of Theorem 1.1); `AJPaper/` (133 files: Sections 7.6, 8.4, 8.5, 9 and Zheng's estimates); the five root files and `SolutionDefs.lean`. Module names do not contain the folder: `Proofs/AJFamily/MarkovEquiv.lean` is the module `AJFamily.MarkovEquiv`. |
| `lean/Solution.lean` | The solution: the 60 release theorems, proved from `Proofs/`. |
| `lean/Challenge.lean`, `lean/Challenge/` | The challenge: the same 60 statements with `sorry` in place of the proofs, on top of 106 modules `Challenge/C_<name>.lean` with verbatim copies (without comments) of the declarations the statements use. It imports only Mathlib and is generated by `tools/make_challenge.py`. |
| `lean/comparator.json` | The configuration for `lake comparator`: challenge module `Challenge`, solution module `Solution`, the 60 theorem names, the permitted axioms, `nanoda` as an additional kernel. |
| `lean/checks/` | Axiom listings with their recorded outputs (`PrintAxioms*.lean`, `*.expected.txt`) and the exact types of the recorded theorems (`HANDOFF_THEOREMS.txt`, `FOUR_FAMILIES_THEOREMS.txt`, `PAPER_THEOREMS.txt`). |
| `lean/tools/` | `make_challenge.py` (generates and checks the challenge), `closure_decls.py` (computes the list of declarations the challenge copies), `compare_reach.py` (the comparator's identity rule applied to the built modules, without the sandbox), `check_imports.py` (file names against imports, for case-sensitive file systems), `check_autoimplicit.sh` (no statement relies on an auto-bound variable), `run_comparator.sh` (the comparator run with its record), `replay_modules.sh` with `ReplayExact.lean` (kernel replay), `AuditReach.lean` (which premises a theorem depends on), `V1Appendix.lean`, `WhdWords.lean`, `TwWords.lean` (printed statements and braid words for the notes and scripts). |
| [`docs/`](docs/) | The scope notes: [`FOUR_FAMILIES.md`](docs/FOUR_FAMILIES.md) (Theorem 1.1), [`FURTHER_CLAIMS.md`](docs/FURTHER_CLAIMS.md) (Sections 7.6, 8.4, 8.5, 9, Theorem B.1 (4)), [`V1_SCOPE.md`](docs/V1_SCOPE.md) (the untwisted family: what is proved, what is conditional, what is external; cited in Appendix E of the paper), [`WHITEHEAD_BRIDGE.md`](docs/WHITEHEAD_BRIDGE.md), [`MARK_BRIDGE.md`](docs/MARK_BRIDGE.md), [`ZHENG_CORRECTED_PROOFS.md`](docs/ZHENG_CORRECTED_PROOFS.md), [`HANDOFF_ACCEPTANCE.md`](docs/HANDOFF_ACCEPTANCE.md). |
| [`scripts/`](scripts/) | Computations outside Lean that the notes cite: the comparison of the braids with the manuscript's formulas and with Zheng's, the Alexander polynomials, the calibration against Lê's conventions. |
| [`reports/`](reports/) | Verification records: local builds and comparator runs, kept apart ([index](reports/README.md)). |
| [`COMPARATOR.md`](COMPARATOR.md) | How to run `lake comparator` on this repository and what to record. |

## What is stated

The conjecture is the radical form of the AJ conjecture (`lean/Proofs/AJConjecture/AJStatement.lean`):

```lean
def AJSquareFree (K : BraidKnot) : Prop :=
  ∀ α : RecOp, IsRecurrencePolynomial (coloredJones K) α →
    ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      Ideal.radical (Ideal.span {toComparison (specialize α)}) = Ideal.span {toComparison A}

def AJSquareFreeConjecture : Prop := ∀ K : BraidKnot, AJSquareFree K
```

In words: for every knot, the radical of the ideal generated by the classical limit `α(-1, M, L)` of the recurrence polynomial equals the ideal generated by the A-polynomial, in `ℚ(M)[L, L⁻¹]`; this is equation (1) of the paper. The main theorem, for the knots `twFamilyKnot r s h σ η ℓ` (`σ = true`: negative clasp; `η = true`: companion `T(r, s)`):

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

`TwFamilyClauses K G P` says: the localized annihilator of the coloured Jones function of `K` contains a nonzero operator; a recurrence polynomial exists; for every nonzero primitive operator of the localized annihilator the classical limit is nonzero and divisible by `G`; an A-polynomial exists; every A-polynomial divides `P` and is coprime to `G`; and `AJSquareFree K` fails. Here `extraFactor` is `E = L² - (M⁴ - 4M² + 1)L + M⁴` and `extraFactorMirror` is `E^∨ = M⁴L² - (M⁴ - 4M² + 1)L + 1`.

## What a reader has to trust

A kernel check shows that a proof has no gaps. It does not show that the statement says what was intended. The statements rest on ten definition files (526 lines, no theorems):

| File (in `lean/Proofs/`) | Lines | Defines |
|---|---|---|
| `AJConjecture/BraidKnot.lean` | 44 | braid words, their permutations, closures that are knots |
| `AJConjecture/KauffmanBracket.lean` | 52 | the Kauffman bracket of a braid closure |
| `AJConjecture/ColoredJones.lean` | 54 | the coloured Jones function at all integer colours |
| `AJConjecture/RecurrenceIdeal.lean` | 61 | recurrence operators, the localized annihilator, recurrence polynomials, specialization |
| `AJConjecture/KnotGroup.lean` | 66 | the knot group of a braid closure, meridian and preferred longitude |
| `AJConjecture/APolynomial.lean` | 44 | boundary eigenvalues and the A-polynomial |
| `AJConjecture/AJStatement.lean` | 31 | the conjecture |
| `AJConjecture/WitnessPolynomials.lean` | 20 | the factor `E` |
| `AJFamily/MarkovEquiv.lean` | 53 | Markov moves on closed braids and Markov equivalence |
| `AJFamily/VolumeDefs.lean` | 101 | Catalan's constant, the Mahler measure, the Bloch–Wigner function, the Whitehead link triangulation |

and on the further data definitions that the 60 statements use (braid words, polynomials, the predicates of Theorems I, S and G, the two ideal conjectures, the fingerprint), all copied verbatim into `lean/Challenge/`; for Theorem 1.1 these are listed in [`docs/FOUR_FAMILIES.md`](docs/FOUR_FAMILIES.md), Section 4, and for the further claims they are the files `Ideal/PpIDefs.lean`, `Ideal/PpIConjectures.lean`, `Finger/PpFDefs.lean` and the twist-knot words of `Filling/PpATwistBlocks.lean`. As a test against errors of convention, the conjecture is proved for the unknot (`ajSquareFree_unknot`), and the definitions are calibrated on the trefoil braid against Lê's paper ([`docs/MARK_BRIDGE.md`](docs/MARK_BRIDGE.md)).

Outside Lean, and to be accepted from the paper or the literature:

- that the explicit closed braids present the marked satellites `W_{ε,ℓ}(T_η)` (no topology is formalized), and that the closure of the inverse braid is the mirror image;
- that the Kauffman state sum and the Artin presentation with parallels used in the definitions give the conventional coloured Jones function and the knot group with its preferred peripheral pair;
- that closed braids which are not Markov equivalent present different knot types (Markov's theorem; the formal statement is the non-equivalence);
- that Tillmann's triangulation is the Whitehead link complement and that its volume is the sum of the Bloch–Wigner values (hyperbolic volume is not defined in Lean);

## Building

Requirements: [elan](https://github.com/leanprover/elan) (it installs the toolchain named in `lean/lean-toolchain`), git, and network access for the first command.

```sh
cd lean
lake exe cache get                     # download the pre-built Mathlib
lake build                             # the 1,165 files of Proofs/ and Solution.lean
lake build Challenge                   # the challenge: 107 modules, 60 intended `sorry`
lake env lean checks/PrintAxiomsPaper.lean          # compare with checks/PrintAxiomsPaper.expected.txt
python3 tools/make_challenge.py --check
python3 tools/compare_reach.py
```

`lake build` must end with `Build completed successfully` and no error. The only warnings are Lake's advisory about importing `Mathlib` as a whole, and the 60 `sorry`s of the challenge. The times of the builds on the development machine are in the records of [`reports/`](reports/README.md).

## Checking with the comparator

`lake comparator` builds the challenge and the solution inside a sandbox, exports them, and establishes that each of the 60 named theorems of the solution proves the same statement as in the challenge from identical declarations, uses no axiom outside the permitted list, and is accepted by Lean's kernel and by `nanoda`. It needs Linux with `bubblewrap`. [`COMPARATOR.md`](COMPARATOR.md) has the steps, the pitfalls met in the run of 15 November, and the list of what the report has to record; `lean/tools/run_comparator.sh` runs it and collects that record.

## Provenance

The Lean development was moved here from the audit repository [`DavetheSlayer/aj-conjecture-audit`](https://github.com/DavetheSlayer/aj-conjecture-audit), folder `formalization/`, which is the root of this repository.

| Here | Origin |
|---|---|
| `lean/Proofs/AJConjecture/`, `AJFamily/`, `AJHandoff/` | byte-identical to audit commit [`a5005af`](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/a5005af977767984ca8ecb7a9e4e8c29714600f7/formalization/lean) (branch `formalization-family`), there directly in `formalization/lean/`. Relative to [`78e38735`](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/78e38735b592fd0632cf4ef4bfdd3cba2b7779e5/formalization/lean), the commit cited in Appendix E of the paper (merged into `main` as [`c5f40ea`](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/c5f40ea6ce55931bb19645e40a30528b2e32f5fb/formalization)), two files were added (`AJHandoff/TorusKnot/PairKMirrorRobust.lean`, `PairKMarkCalib.lean`) and none changed. |
| `lean/Solution.lean`, `lean/Challenge*`, `lean/comparator.json`, `lean/Proofs/SolutionDefs.lean` | `AJRelease.lean`, `AJReleaseChallenge*`, `comparator-release.json`, `AJRelease/AJReleaseDefs.lean` of the same commits, renamed on 18 November and extended on 20 November by the two four-family theorems and by the eleven theorems on the further claims. The 47 earlier statements are unchanged. |
| `lean/Proofs/AJTwist/`, `lean/Proofs/AJPaper/` | new (19–20 November 2026); not in the audit repository. |
| `docs/`, `scripts/` | `formalization/*.md` and `formalization/scripts/` of the audit repository at `a5005af`, with notes on paths at the heads of the documents; `docs/FOUR_FAMILIES.md`, `docs/FURTHER_CLAIMS.md` and `scripts/four_families/` are new. |
| `reports/comparator-2026-11-15.md` | the report of the accepted run on the single-braid theorem, archived at audit commit [`418b3ed`](https://github.com/DavetheSlayer/aj-conjecture-audit/blob/418b3ed892825dd595011ef5d35e62fd54eeeb22/formalization/reports/comparator-2026-11-15.md); the checked solution is audit commit `8dd21cf` (reference [1] of the paper). Imported unchanged. |

Not moved: the 173-page formal manuscript and the comparison report of the audit repository (`formalization/manuscript/`, `formalization/comparison/`), which describe the libraries before 17 November, and the review packets and handoffs: the [handoff of 15 November](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/c5f40ea6ce55931bb19645e40a30528b2e32f5fb/handoffs/2026-11-15-ti-g-mahler), the [interface addendum of 16 November](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/c5f40ea6ce55931bb19645e40a30528b2e32f5fb/handoffs/2026-11-16-manuscript-lean-interface) and the [four-family handoff of 18 November](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/e4a4786b01dec67c542924d82a4c1a2378e6a05d/handoffs/2026-11-18-whitehead-four-family).

## Adding a formalization or comparator result

For Lean changes, record the theorem names and their scope, the Lean toolchain, and dependency pins. For comparator runs, record the exact tested commit and config, the command, the kernel or sandbox versions, the outcome, and the log or a stable reference to it. Label local builds and comparator runs separately so readers can tell exactly what was checked. If a result is imported from the audit repository, retain its original commit and report references. The template and the index of records are in [`reports/`](reports/README.md).

## How the formalization was produced

The Lean code was written by AI agents (Claude, Anthropic) under the direction of the authors, with the MerLean framework (see Appendix E and the acknowledgments of the paper): the single counterexample on 13 November 2026, the family and the volume on 15–16 November, the remaining contracts of the untwisted family on 17 November, the four families on 19 November and the further claims on 20 November 2026, each from the written material of the project at that date. No human has yet read the proofs line by line; the kernel has. The statement files were audited against the written sources by independent agents. Readers should treat the kernel check as establishing the theorems as formally stated, and the correspondence of those statements with the intended mathematics as the part that deserves human review.

## 中文说明

本库是论文 [arXiv:2611.24826v1](https://arxiv.org/abs/2611.24826v1) 的 Lean 源码、comparator 输入和验证记录。

- **已上传**：全部 Lean 源码（`lean/`）、comparator 配置（`lean/comparator.json`，60 条定理）、本地构建与检查记录（`reports/local-checks-2026-11-20.md`、`reports/local-checks-2026-11-20b.md`）、范围说明（`docs/`）。
- **待完成**：在 Linux 服务器上运行 `lake comparator`。步骤和需要记录的内容见 [`COMPARATOR.md`](COMPARATOR.md)；运行后按 `reports/comparator-TEMPLATE.md` 写报告并提交到 `reports/`。在此之前，不声称本版本通过了 comparator 验证。
- **与论文附录 E 的关系**：附录 E 描述的是 11 月 17 日的状态，只覆盖无扭转、负扣环、右手伴随的情形。本库在其基础上增加了 `AJTwist` 库（定理 1.1 的全部四族情形）和 `AJPaper` 库（第 7.6、8.4、8.5、9 节以及定理 B.1 (4) 所需的 Zheng 估计）；原有三个库逐字未变。仍在 Lean 之外的只有拓扑与双曲几何部分：第 2 节的图式识别、纽结类型的区分、三角剖分与双曲体积的认定。
- 原始材料与交接说明保存在 audit 仓库，链接见上文 Provenance 一节（[中文交接指南](https://github.com/DavetheSlayer/aj-conjecture-audit/blob/e4a4786b01dec67c542924d82a4c1a2378e6a05d/handoffs/2026-11-18-whitehead-four-family/FOR_JINZHENG_%E4%B8%AD%E6%96%87.md)）。
