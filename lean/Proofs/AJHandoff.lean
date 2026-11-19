import Mathlib
import AJHandoff.TorusKnot.PairKTheoremT
import AJHandoff.TorusKnot.PairKJSJ
import AJHandoff.TorusKnot.PairKReverse
import AJHandoff.TorusKnot.PairKAPolyHorizontal
import AJHandoff.TorusQuantum.PairQPackage
import AJHandoff.TorusQuantum.PairQSymbolPackage
import AJHandoff.TorusQuantum.PairQTOrderFormula
import AJHandoff.TorusQuantum.PairQIrrField
import AJHandoff.TorusKnot.PairKBmIdentity
import AJHandoff.LocalTheory.LocQuotientIndex
import AJHandoff.LocalTheory.LocFactorIndexInt
import AJHandoff.LocalTheory.LocPartition
import AJHandoff.LocalTheory.LocNodeResidue
import AJHandoff.LocalTheory.LocGraphTheorem
import AJHandoff.LocalTheory.LocGaugeIndex
import AJHandoff.LocalTheory.LocRamification
import AJHandoff.LocalTheory.LocRescale
import AJHandoff.LocalTheory.LocPowerPullback
import AJHandoff.LocalTheory.LocTheoremS
import AJHandoff.LocalTheory.LocTheoremSRecOp
import AJHandoff.LocalTheory.LocSeqSpecialize
import AJHandoff.LocalTheory.LocTheoremI
import AJHandoff.LocalTheory.LocToyMinimum
import AJHandoff.LocalTheory.LocFactoredControl
import AJHandoff.LocalTheory.LocConstantControl
import AJHandoff.LocalTheory.LocWeakControl
import AJHandoff.LocalTheory.LocFamilyMinimalOrder
import AJHandoff.Geometry.GeoTheoremG
import AJHandoff.TorusQuantum.PairQTorusInputProof
import AJHandoff.TorusQuantum.PairQTransferApply
import AJHandoff.TorusQuantum.PairQJetsIndex
import AJHandoff.Geometry.GeoLongKnotScalar
import AJHandoff.Geometry.GeoVolumeOriented
import AJHandoff.LocalTheory.LocFieldIso
import AJHandoff.TorusQuantum.PairQJetsIndexIrr
import AJHandoff.TorusQuantum.PairQJetsIndexRow

/-!
# The remaining contracts of the 15 November handoff

Theorem T for the Whitehead doubles of all torus knots `T(r, s)` with coprime `2 ≤ r < s`, the
local Theorem I and the sequence theorem S, the exact minimal recurrence of the family, and the
structural Theorem G around the curve `E`. Units are those of `THEOREM_CONTRACTS.md` of the
handoff (`handoffs/2026-11-15-ti-g-mahler/package`); the follow-up is
`handoffs/2026-11-16-manuscript-lean-interface`.

## Where each unit is proved

* **Theorem T** (T-KNOT, T-JONES, T-TRANSFER, T-BLOCK, T-JETS, T-IRR, T-MIN, T-CLASS, T-AEX, T-AJ,
  T-DIST, T, F): `theoremT`, `theoremF` (the instance `r = 2`, the library's family),
  `theoremT_of_input` (the same, conditional only on the companion input). Units: `pairQ_torusInput`
  (the coloured Jones polynomial of `T(r, s)` at odd colours, Zheng (4.1) / Rosso–Jones, from the
  library's definition), `pairQ_formula_package`, `pairQ_knot_package`,
  `pairQ_opApplyField_famTransferOp` (T-TRANSFER: `P_rs F = ρ` on `N > d`, forcing from `j < r + s +
  1`), `pairQ_tOrder_reducedFormula` (its valuation clause `ord_t F_N = -4(N-1)(rsN-1)`),
  `pairQ_symbol`, `pairQ_block` (T-BLOCK), `pairQ_abNode`, `pairQ_ebNode`, `pairQJets_abNode`,
  `pairQJets_ebNode` (T-JETS: both allocation indices `-1/2` at both mixed nodes, in the local
  theory with `t = -exp(h/4)`, `c = -1/2`), `pairQ_transferOp_irreducible`,
  `pairQ_transferOp_oreIrreducible` (T-IRR over `ℤ[t][M]` and over `Frac ℤ[t][M]`),
  `longKnotOp_pairWhiteheadKnot`, `writhe_pairWhiteheadKnot` (T-KNOT: the isotopy to the satellite
  diagram), `isWhSatellite_pairWhiteheadKnot` (the satellite structure of the knot group),
  `aPolynomial_pair_associated`, `toComparison_dvd_famBound_pair`, `isCoprime_extraFactor_pair`,
  `sub_one_dvd_aPolynomial`, `famB_eq_twistPoly` (the classical and the quantum `B_m` agree),
  `pairRealizesSatellite`, `pair_reverse_inclusion`, `aPolynomial_pair_factors`,
  `aPolynomial_pair_associated_famBound` (T-AEX and the follow-up's classical equality `A ≐ (L - 1)
  B_rs` in `ℚ(M)[L, L⁻¹]`). Distinctness is proved as pairwise non-Markov-equivalence (`theoremT`,
  second clause); reading it as distinct knot types needs the hard direction of Markov's theorem.
  The JSJ route is `pairWhiteheadKnot_not_markovEquiv_of_jsj` and
  `pairWhiteheadKnot_knotGroup_not_equiv_of_jsj` (non-isomorphic knot groups), conditional on the
  named proposition `WhiteheadJSJProp` (which bundles Gordon–Luecke/Whitten, JSJ uniqueness,
  `KnotGroup` = π₁ of the exterior and the identification of the braid closure with `Wh(T(r, s))`),
  with its algebraic core proved unconditionally (`center_torusKnotGroup`,
  `torusKnotGroup_quot_center`, `orderOf_dvd_of_isOfFinOrder_cycCoprod`, `eq_of_mulEquiv_cycCoprod`,
  `knotGroup_torusPairKnot_equiv`). Interpretation: that the closed braid `pairWhiteheadKnot r s h`
  is the geometric satellite `Z(T(r, s))` with its preferred framing; the formal statement is an
  isotopy, in the library's skein model, to the satellite diagram, and the satellite structure of
  its knot group.
* **Theorem I** (I-INT, I-PART, I-NODE, I-GAUGE, I-SEQ, I-CTRL, I):
  `exists_hasNormalizedIndex_int_of_quotient` (I-INT), `exists_int_hasNormalizedIndex_locLogJet`,
  `locResidual_partition` (I-PART), `hasSimpleResidue_locLogJet_of_allowedNode`,
  `hasNormalizedIndex_locNodeIndex` (I-NODE), `locBlockDvd_iff_of_forbiddenEdge`,
  `oreIrreducible_of_connected` (the graph theorem), `det_gauge`,
  `hasNormalizedIndex_mul_coboundary`, `hasNormalizedIndex_mul_inv_coboundary`,
  `hasNormalizedIndex_gauge_of_isJointRegular`, `hasSimpleResidue_ramify`,
  `hasNormalizedIndex_rescale`, `hasNormalizedIndex_powerSubst` (I-GAUGE; reparametrizations are
  formalized for `h ↦ a h` and `x = a z^k`, the inversion `z ↦ 1/z` is not), `seq_theoremS`,
  `exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational`,
  `exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous`,
  `toComparison_specialize_dvd_of_tail_annihilator_gauge` (I-SEQ, forcing in `K` including `0`),
  `toyRecOp_pseudoIrreducible`, `exists_C_mul_eq_oreMul_toyRecOp`, `toyRecOp_primitive_specialize`,
  `locFactored_nodeIndex`, `constSeq_minimum`, `constSeq_oversized`, `constSeq_not_selected`,
  `not_weakLatticeLemma` (I-CTRL), `toy_theoremI` (a non-family application).
* **Minimal recurrence and the B0 scope** (follow-up, priority 3): `tailOrder_whiteheadTorusKnot`
  (reduced and unreduced tails), `minimalRecurrence_whiteheadTorusKnot` (existence; order `8k + 8`;
  special symbol `(L - 1)² E B_m`), `isRecurrencePolynomial_whiteheadTorusKnot_one` (order 16 and
  `(L - 1)² E B_6` for `k = 1`); the classical equality is `aPolynomial_pair_associated_famBound`
  (for `(2, 3)`: `A ≐ (L - 1) B_6`).
* **Theorem G** (G-KERNEL, G-CURVE, G-NORM, G-REG, G-REG-COMPACT, G-K2, G-ACTION, G-MAHLER, G-SHAPE,
  MARK, G-VOL, G-PHYS): `geo_theoremG`, with the units it assembles, among them
  `geo_hypVolume_idealTetI` (hyperbolic volume of the ideal tetrahedron of shape `i` is `G`, for the
  density `t⁻³`), `longKnotOp_mul_jwAt_eq_smul` and `exists_laurent_torusReducedFormula` (the
  reduced invariant is integral) and `geo_reduced_value_eq_zhengDiagonal` (its value at `q_N` is
  Zheng's diagonal). G-PHYS: the chain from the actual coloured Jones polynomial of `W_k` to Zheng's
  diagonal is unconditional; the asymptotics are conditional on the named proposition
  `ZhengEstimates a` (Zheng's analytic estimates, with (5.16) and (5.19) for the corrected `b`, see
  `GeoPhysDefs`). Interpretation: that the four-tetrahedron triangulation is the Whitehead link
  exterior with its complete hyperbolic metric.
-/
