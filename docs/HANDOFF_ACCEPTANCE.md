# Acceptance record: the 15 November handoff and the 16 November follow-up

*Note on paths (20 November 2026).* This record was written in the audit repository
(`DavetheSlayer/aj-conjecture-audit`), whose folder `formalization/` is the root of the present
repository: read `formalization/lean` as `lean`. The paths `handoffs/…` and the commit `78e3873`
are those of the audit repository. The text below is otherwise unchanged.

This records, as the handoff note (`handoffs/2026-11-15-ti-g-mahler/package/FOR_JINZHENG_中文.md`)
asks, the exact type, dependencies, axioms and check log of every new theorem. The Lean code is in
`formalization/lean/Proofs/AJHandoff/` (≈ 330 files), indexed by
`formalization/lean/Proofs/AJHandoff.lean`, on top of the unchanged `AJConjecture/` and `AJFamily/`
libraries in the same folder. (Paths are those after the cleanup of 18 November 2026, which moved
the libraries from `formalization/lean/` into `formalization/lean/Proofs/` without changing a
module name; files are cited below by their path in that folder.)

**Superseded in part by [`V1_SCOPE.md`](V1_SCOPE.md) (17 November)**, which reconciles this record
with the Lean types, classifies every outstanding interface (proved externally, conditional, not
formally connected, formalization gap), adds the satellite bridge and the corrected Zheng estimates,
and describes the release check. Where the two differ, `V1_SCOPE.md` is authoritative.

## Outcome

Every unit of `THEOREM_CONTRACTS.md` and every priority of the follow-up is formalized, with the
narrowings and external inputs listed in the next section and classified in `V1_SCOPE.md`, §5; every
theorem below is checked by Lean with axioms `propext`, `Classical.choice`, `Quot.sound` only: no
`sorry`, no new axiom, no `native_decide`.

* **Theorem T** for the Whitehead doubles of all torus knots `T(r, s)`, coprime `2 ≤ r < s`, with
  all clauses (`theoremT`), and Theorem F as its instance `r = 2` on the library's family
  (`theoremF`). Its inputs include the coloured Jones polynomial of `T(r, s)` at odd colours (the
  Rosso–Jones / Zheng (4.1) formula), proved from the library's definition (`pairQ_torusInput`), the
  isotopy of each braid to the satellite diagram, the satellite structure of its knot group, and the
  classical equality `A ≐ (L - 1) B_rs` in `ℚ(M)[L, L⁻¹]`.
* **Theorem I and Theorem S** in general (integrality, partition, node residue formula (4), the
  gauge law in both conventions, ramification, the reparametrizations `h ↦ a h` and `x = a z^k`,
  the connected-graph theorem, Theorem S with forcing in `K` including `0`), the four controls and a
  non-family application. Other reparametrizations of I-GAUGE are not formalized (`V1_SCOPE.md`,
  §5, item 10).
* **The exact minimal recurrence** of the doubles of `T(2, 2k+1)` (the case `r = 2` only; for
  `r ≥ 3` existence and `E`-survival are proved, no order): order `8k + 8` and special symbol
  `(L - 1)² E B_m` for every recurrence polynomial; for `k = 1` order `16` and `(L - 1)² E B_6`.
* **Theorem G** (`geo_theoremG`): kernel formula and channel bijection, curve and normalization,
  regulator and its compact extension, `{M, L} = 0` in `K₂ᴹ ⊗ ℚ`, critical action, Mahler measure,
  shapes and marking, signed, oriented and metric volumes (the ideal tetrahedron of shape `i` has
  hyperbolic volume `G`), and the physical diagonal.

## Conditional statements and interpretation

* **G-PHYS asymptotics** are conditional on Zheng's printed estimates that do not involve `b`
  (`geo_phys_of_zhengVerbatim`, premise `ZhengVerbatim a`: Lemmas 3.2–3.3, (5.12), (5.20),
  Proposition 4.1). Zheng's printed (5.4) has a sign error; for the corrected `b`, (5.16) is a Lean
  theorem (`zhengEq516_holds`) and (5.19) a Lean theorem from (5.12) (`zhengEq519_of_zhengEq512`);
  proofs and two slips in Zheng's arguments: `ZHENG_CORRECTED_PROOFS.md`. The earlier form, on the
  premise `ZhengEstimates a`, remains in `geo_theoremG`. The
  chain from the actual coloured Jones polynomial of `W_k` to Zheng's diagonal is unconditional
  (`exists_laurent_torusReducedFormula`, `geo_reduced_value_eq_zhengDiagonal`, which also confirms
  the corrected sign).
* **Distinct knot types.** Proved: different admissible pairs give closed braids that are not Markov
  equivalent (`theoremT`) and have different colour-2 coloured Jones polynomials
  (`coloredJones_two_pairWhiteheadKnot_ne`). Reading this as distinct knot types needs the hard
  direction of Markov's theorem, or the isotopy invariance of the coloured Jones polynomial. The JSJ route of the handoff is formalized conditional on the named proposition
  `WhiteheadJSJProp` (which bundles Gordon–Luecke/Whitten, JSJ uniqueness, `KnotGroup` = π₁ of the
  exterior and the identification below), with its algebraic core proved (centre of the torus knot
  group, quotient `C_r * C_s`, torsion orders, recovery of `(r, s)`).
* **Interpretation, not formalized:** that the closed braid `pairWhiteheadKnot r s h` is the
  geometric satellite `Z(T(r, s))` with its preferred framing and marking. The formal content is
  now a diagram-move equivalence of the braid closure with `whDouble C`, a generic untwisted
  negative-clasp Whitehead double of the right-handed `T(r, s)` diagram, with zero band framing,
  negative clasp and one component proved (`pairWhiteheadKnot_whDouble`; `WHITEHEAD_BRIDGE.md`),
  plus the Whitehead peripheral relations in its knot group; what remains is that the moves are
  isotopies and the reading of `whDouble` and of the sources' figures (`V1_SCOPE.md`, §1.3); that the four-tetrahedron triangulation is the Whitehead link exterior with its
  complete hyperbolic metric (the formal content is the gluing equations, the holonomy
  representation derived from the library's peripheral words, and the metric volume of the ideal
  tetrahedra).
* **Narrower than the source, documented in the files:** I-GAUGE reparametrizations are formalized
  for `h ↦ a h` and `x = a z^k`, not general unramified ones, and the inversion `z ↦ 1/z` is
  omitted; G-NORM is stated through the integral closure and a compact model (uniqueness of the
  smooth projective model is not in Mathlib); T-JETS's "jointly invertible companion" is expressed
  by the endpoint conditions of the local theory.

## Findings about the sources

* Zheng (math/0508138) (5.4): the sign of the summed terms is wrong; the corrected sign is proved
  correct (`geo_reduced_value_eq_zhengDiagonal`).
* `B_m(±i, 1) = 0` for every `m`: `C = L - 1` and `B_m` also meet on the fibre `M² = -1`. This is
  outside the allowed nodes and does not affect the theorems.
* No contract was found false. Several scaffolded internal helper lemmas were found false during
  the work (a fence lemma for unattached discs, an action lift crossing a branch cut, an even-turn
  count in the isotopy design); each was replaced by a corrected statement, with the
  counterexample recorded.

## Check log

* Lean 4.36.0-rc2, Mathlib `2657306`. From `formalization/lean`: `lake build AJHandoff` (the
  library was then a Lake library of its own; now `lake build`) — `Build completed successfully
  (19772 jobs)`, no error, no warning from these files.
* `lake env lean checks/PrintAxiomsHandoff.lean` reproduces
  `checks/PrintAxiomsHandoff.expected.txt`: 73
  theorems, every one `[propext, Classical.choice, Quot.sound]`.
* Exact types: `formalization/lean/checks/HANDOFF_THEOREMS.txt` (`#check` output).
* Statement audits: two independent audits of all statements against the contracts and a third of
  the statements added last; every reported discrepancy was resolved (strengthened clauses, added
  existence clauses, documentation of the corrected `b`).
* Commit: `78e3873` (branch `formalization-family`).
* Dependencies: each theorem's module is listed below; its full dependency set is the Lean import
  graph of that module (within `AJHandoff/`, `AJFamily/`, `AJConjecture/` and Mathlib).

## Theorems, unit by unit
### Line 1 — knot family and quantum side (T-KNOT, T-JONES, T-TRANSFER, T-BLOCK, T-JETS, T-IRR, T-MIN)

| Theorem | Module | Axioms |
|---|---|---|
| `theoremT` | `AJHandoff.TorusKnot.PairKTheoremT` | propext, Classical.choice, Quot.sound |
| `theoremT_of_input` | `AJHandoff.TorusKnot.PairKTheoremT` | propext, Classical.choice, Quot.sound |
| `theoremF` | `AJHandoff.TorusKnot.PairKTheoremT` | propext, Classical.choice, Quot.sound |
| `pairQ_torusInput` | `AJHandoff.TorusQuantum.PairQTorusInputProof` | propext, Classical.choice, Quot.sound |
| `pairQ_formula_package` | `AJHandoff.TorusQuantum.PairQPackage` | propext, Classical.choice, Quot.sound |
| `pairQ_knot_package` | `AJHandoff.TorusQuantum.PairQPackage` | propext, Classical.choice, Quot.sound |
| `pairQ_opApplyField_famTransferOp` | `AJHandoff.TorusQuantum.PairQTransferApply` | propext, Classical.choice, Quot.sound |
| `pairQ_tOrder_reducedFormula` | `AJHandoff.TorusQuantum.PairQTOrderFormula` | propext, Classical.choice, Quot.sound |
| `pairQ_symbol` | `AJHandoff.TorusQuantum.PairQSymbolPackage` | propext, Classical.choice, Quot.sound |
| `pairQ_block` | `AJHandoff.TorusQuantum.PairQSymbolPackage` | propext, Classical.choice, Quot.sound |
| `pairQ_abNode` | `AJHandoff.TorusQuantum.PairQSymbolPackage` | propext, Classical.choice, Quot.sound |
| `pairQ_ebNode` | `AJHandoff.TorusQuantum.PairQSymbolPackage` | propext, Classical.choice, Quot.sound |
| `pairQJets_abNode` | `AJHandoff.TorusQuantum.PairQJetsIndex` | propext, Classical.choice, Quot.sound |
| `pairQJets_ebNode` | `AJHandoff.TorusQuantum.PairQJetsIndex` | propext, Classical.choice, Quot.sound |
| `pairQ_transferOp_irreducible` | `AJHandoff.TorusQuantum.PairQSymbolPackage` | propext, Classical.choice, Quot.sound |
| `pairQ_transferOp_oreIrreducible` | `AJHandoff.TorusQuantum.PairQIrrField` | propext, Classical.choice, Quot.sound |
| `longKnotOp_pairWhiteheadKnot` | `AJHandoff.TorusKnot.PairKLongKnot` | propext, Classical.choice, Quot.sound |
| `writhe_pairWhiteheadKnot` | `AJHandoff.TorusKnot.PairKLongKnot` | propext, Classical.choice, Quot.sound |

### Line 2 — local Theorem I and sequence theorem S (I-INT, I-PART, I-NODE, I-GAUGE, I-SEQ, I-CTRL, I)

| Theorem | Module | Axioms |
|---|---|---|
| `exists_hasNormalizedIndex_int_of_quotient` | `AJHandoff.LocalTheory.LocQuotientIndex` | propext, Classical.choice, Quot.sound |
| `exists_int_hasNormalizedIndex_locLogJet` | `AJHandoff.LocalTheory.LocFactorIndexInt` | propext, Classical.choice, Quot.sound |
| `locResidual_partition` | `AJHandoff.LocalTheory.LocPartition` | propext, Classical.choice, Quot.sound |
| `hasSimpleResidue_locLogJet_of_allowedNode` | `AJHandoff.LocalTheory.LocNodeResidue` | propext, Classical.choice, Quot.sound |
| `hasNormalizedIndex_locNodeIndex` | `AJHandoff.LocalTheory.LocNodeResidue` | propext, Classical.choice, Quot.sound |
| `locBlockDvd_iff_of_forbiddenEdge` | `AJHandoff.LocalTheory.LocGraphTheorem` | propext, Classical.choice, Quot.sound |
| `oreIrreducible_of_connected` | `AJHandoff.LocalTheory.LocGraphTheorem` | propext, Classical.choice, Quot.sound |
| `det_gauge` | `AJHandoff.LocalTheory.LocGaugeIndex` | propext, Classical.choice, Quot.sound |
| `hasNormalizedIndex_mul_coboundary` | `AJHandoff.LocalTheory.LocGaugeIndex` | propext, Classical.choice, Quot.sound |
| `hasNormalizedIndex_mul_inv_coboundary` | `AJHandoff.LocalTheory.LocGaugeIndex` | propext, Classical.choice, Quot.sound |
| `hasNormalizedIndex_gauge_of_isJointRegular` | `AJHandoff.LocalTheory.LocGaugeIndex` | propext, Classical.choice, Quot.sound |
| `hasSimpleResidue_ramify` | `AJHandoff.LocalTheory.LocRamification` | propext, Classical.choice, Quot.sound |
| `hasNormalizedIndex_rescale` | `AJHandoff.LocalTheory.LocRescale` | propext, Classical.choice, Quot.sound |
| `hasNormalizedIndex_powerSubst` | `AJHandoff.LocalTheory.LocPowerPullback` | propext, Classical.choice, Quot.sound |
| `seq_theoremS` | `AJHandoff.LocalTheory.LocTheoremS` | propext, Classical.choice, Quot.sound |
| `exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational` | `AJHandoff.LocalTheory.LocTheoremSRecOp` | propext, Classical.choice, Quot.sound |
| `exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous` | `AJHandoff.LocalTheory.LocTheoremSRecOp` | propext, Classical.choice, Quot.sound |
| `toComparison_specialize_dvd_of_tail_annihilator_gauge` | `AJHandoff.LocalTheory.LocSeqSpecialize` | propext, Classical.choice, Quot.sound |
| `toyRecOp_pseudoIrreducible` | `AJHandoff.LocalTheory.LocToyMinimum` | propext, Classical.choice, Quot.sound |
| `exists_C_mul_eq_oreMul_toyRecOp` | `AJHandoff.LocalTheory.LocToyMinimum` | propext, Classical.choice, Quot.sound |
| `toyRecOp_primitive_specialize` | `AJHandoff.LocalTheory.LocToyMinimum` | propext, Classical.choice, Quot.sound |
| `locFactored_nodeIndex` | `AJHandoff.LocalTheory.LocFactoredControl` | propext, Classical.choice, Quot.sound |
| `constSeq_minimum` | `AJHandoff.LocalTheory.LocConstantControl` | propext, Classical.choice, Quot.sound |
| `constSeq_oversized` | `AJHandoff.LocalTheory.LocConstantControl` | propext, Classical.choice, Quot.sound |
| `constSeq_not_selected` | `AJHandoff.LocalTheory.LocConstantControl` | propext, Classical.choice, Quot.sound |
| `not_weakLatticeLemma` | `AJHandoff.LocalTheory.LocWeakControl` | propext, Classical.choice, Quot.sound |
| `toy_theoremI` | `AJHandoff.LocalTheory.LocTheoremI` | propext, Classical.choice, Quot.sound |

### Line 3 — classical side, A-polynomial witness, distinctness (T-CLASS, T-AEX, T-AJ, T-DIST, T, F)

| Theorem | Module | Axioms |
|---|---|---|
| `isWhSatellite_pairWhiteheadKnot` | `AJHandoff.TorusKnot.PairKPeripheral` | propext, Classical.choice, Quot.sound |
| `toComparison_dvd_famBound_pair` | `AJHandoff.TorusKnot.PairKAPolyHorizontal` | propext, Classical.choice, Quot.sound |
| `isCoprime_extraFactor_pair` | `AJHandoff.TorusKnot.PairKAPolyHorizontal` | propext, Classical.choice, Quot.sound |
| `sub_one_dvd_aPolynomial` | `AJHandoff.TorusKnot.PairKAPolyHorizontal` | propext, Classical.choice, Quot.sound |
| `aPolynomial_pair_associated` | `AJHandoff.TorusKnot.PairKAPolyHorizontal` | propext, Classical.choice, Quot.sound |
| `famB_eq_twistPoly` | `AJHandoff.TorusKnot.PairKBmIdentity` | propext, Classical.choice, Quot.sound |
| `pairRealizesSatellite` | `AJHandoff.TorusKnot.PairKReverse` | propext, Classical.choice, Quot.sound |
| `exists_pairFixedTuple` | `AJHandoff.TorusKnot.PairKRevTuple` | propext, Classical.choice, Quot.sound |
| `pair_reverse_inclusion` | `AJHandoff.TorusKnot.PairKReverse` | propext, Classical.choice, Quot.sound |
| `aPolynomial_pair_factors` | `AJHandoff.TorusKnot.PairKReverse` | propext, Classical.choice, Quot.sound |
| `aPolynomial_pair_associated_famBound` | `AJHandoff.TorusKnot.PairKReverse` | propext, Classical.choice, Quot.sound |
| `center_torusKnotGroup` | `AJHandoff.TorusKnot.PairKCoprodTorsion` | propext, Classical.choice, Quot.sound |
| `torusKnotGroup_quot_center` | `AJHandoff.TorusKnot.PairKCoprodTorsion` | propext, Classical.choice, Quot.sound |
| `orderOf_dvd_of_isOfFinOrder_cycCoprod` | `AJHandoff.TorusKnot.PairKCoprodTorsion` | propext, Classical.choice, Quot.sound |
| `eq_of_mulEquiv_cycCoprod` | `AJHandoff.TorusKnot.PairKCoprodTorsion` | propext, Classical.choice, Quot.sound |
| `knotGroup_torusPairKnot_equiv` | `AJHandoff.TorusKnot.PairKCoprodTorsion` | propext, Classical.choice, Quot.sound |
| `pairWhiteheadKnot_not_markovEquiv_of_jsj` | `AJHandoff.TorusKnot.PairKJSJ` | propext, Classical.choice, Quot.sound |
| `pairWhiteheadKnot_knotGroup_not_equiv_of_jsj` | `AJHandoff.TorusKnot.PairKJSJ` | propext, Classical.choice, Quot.sound |

### Lines 4 and 5 — Theorem G (G-KERNEL, G-CURVE, G-NORM, G-REG, G-REG-COMPACT, G-K2, G-ACTION, G-MAHLER, G-SHAPE, MARK, G-VOL, G-PHYS)

| Theorem | Module | Axioms |
|---|---|---|
| `geo_theoremG` | `AJHandoff.Geometry.GeoTheoremG` | propext, Classical.choice, Quot.sound |
| `geo_hypVolume_idealTetI` | `AJHandoff.Geometry.GeoVolumeHyperbolic` | propext, Classical.choice, Quot.sound |
| `longKnotOp_mul_jwAt_eq_smul` | `AJHandoff.Geometry.GeoLongKnotScalar` | propext, Classical.choice, Quot.sound |
| `exists_laurent_torusReducedFormula` | `AJHandoff.Geometry.GeoReducedIntegral` | propext, Classical.choice, Quot.sound |
| `geo_reduced_value_eq_zhengDiagonal` | `AJHandoff.Geometry.GeoPhysReduced` | propext, Classical.choice, Quot.sound |

### Follow-up priority 3 — B0 scope and the exact minimal recurrence

| Theorem | Module | Axioms |
|---|---|---|
| `tailOrder_whiteheadTorusKnot` | `AJHandoff.LocalTheory.LocFamilyMinimalOrder` | propext, Classical.choice, Quot.sound |
| `minimalRecurrence_whiteheadTorusKnot` | `AJHandoff.LocalTheory.LocFamilyMinimalOrder` | propext, Classical.choice, Quot.sound |
| `natDegree_isRecurrencePolynomial_whiteheadTorusKnot` | `AJHandoff.LocalTheory.LocFamilyMinimalOrder` | propext, Classical.choice, Quot.sound |
| `specialize_isRecurrencePolynomial_whiteheadTorusKnot` | `AJHandoff.LocalTheory.LocFamilyMinimalOrder` | propext, Classical.choice, Quot.sound |
| `isRecurrencePolynomial_whiteheadTorusKnot_one` | `AJHandoff.LocalTheory.LocFamilyMinimalOrder` | propext, Classical.choice, Quot.sound |
