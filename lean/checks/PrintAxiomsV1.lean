import AJFamily
import AJHandoff
import Solution
import AJHandoff.TorusKnot.PairKWhDMain
import AJHandoff.TorusKnot.PairKWhDBandTorus
import AJHandoff.TorusKnot.PairKJonesTwoNe
import AJHandoff.TorusKnot.PairKMirrorRobust
import AJHandoff.TorusKnot.PairKMarkCalib
import AJHandoff.Geometry.GeoZhVerbatim

/-!
# Axiom report for the v1 release theorems

Run from the folder `lean`, after `lake build`:

    lake env lean checks/PrintAxiomsV1.lean

Every line must read `depends on axioms: [propext, Classical.choice, Quot.sound]` (or a subset);
compare with `PrintAxiomsV1.expected.txt`. First the 47 v1 theorems of `comparator.json` (the
challenge `Challenge.lean`; its two four-family theorems are listed in
`PrintAxiomsFourFamilies.lean`), then the further theorems cited in `docs/V1_SCOPE.md` (core, satellite
bridge, Zheng), then those of `docs/MARK_BRIDGE.md`.
-/

-- the challenge (comparator.json)
#print axioms AJConjecture.not_ajSquareFreeConjecture
#print axioms AJConjecture.release_theoremT
#print axioms AJConjecture.release_classicalEquality
#print axioms AJConjecture.release_minimalRecurrence
#print axioms AJConjecture.release_pairWord_two
#print axioms AJConjecture.release_coloredJones_two_ne
#print axioms AJConjecture.release_whDouble
#print axioms AJConjecture.morseReach_whDouble
#print axioms AJConjecture.morseWrithe_eq_of_morseReach
#print axioms AJConjecture.zero_mem_bandLinkings_whBand
#print axioms AJConjecture.ajFamily_main
#print axioms AJConjecture.zhengEq516_holds
#print axioms AJConjecture.zhengEq519_of_zhengEq512
#print axioms AJConjecture.zhengEstimates_of_verbatim
#print axioms AJConjecture.geo_phys_of_zhengVerbatim
#print axioms AJConjecture.release_theoremG
#print axioms AJConjecture.release_theoremG_supplement
#print axioms AJConjecture.exists_hasNormalizedIndex_int_of_quotient
#print axioms AJConjecture.exists_int_hasNormalizedIndex_locLogJet
#print axioms AJConjecture.locResidual_partition
#print axioms AJConjecture.hasSimpleResidue_locLogJet_of_allowedNode
#print axioms AJConjecture.hasNormalizedIndex_locNodeIndex
#print axioms AJConjecture.locBlockDvd_iff_of_forbiddenEdge
#print axioms AJConjecture.oreIrreducible_of_connected
#print axioms AJConjecture.det_gauge
#print axioms AJConjecture.hasNormalizedIndex_mul_coboundary
#print axioms AJConjecture.hasNormalizedIndex_mul_inv_coboundary
#print axioms AJConjecture.hasNormalizedIndex_gauge_of_isJointRegular
#print axioms AJConjecture.hasNormalizedIndex_rescale
#print axioms AJConjecture.release_hasSimpleResidue_ramify
#print axioms AJConjecture.release_hasNormalizedIndex_powerSubst
#print axioms AJConjecture.exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational
#print axioms AJConjecture.exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous
#print axioms AJConjecture.toComparison_specialize_dvd_of_tail_annihilator_gauge
#print axioms AJConjecture.release_seq_theoremS
#print axioms AJConjecture.toyRecOp_pseudoIrreducible
#print axioms AJConjecture.exists_C_mul_eq_oreMul_toyRecOp
#print axioms AJConjecture.toyRecOp_primitive_specialize
#print axioms AJConjecture.locFactored_nodeIndex
#print axioms AJConjecture.constSeq_minimum
#print axioms AJConjecture.constSeq_oversized
#print axioms AJConjecture.constSeq_not_selected
#print axioms AJConjecture.not_weakLatticeLemma
#print axioms AJConjecture.toy_theoremI
#print axioms AJConjecture.pairQJets_abNode
#print axioms AJConjecture.pairQJets_ebNode
#print axioms AJConjecture.pairQ_transferOp_oreIrreducible
-- further theorems cited in V1_SCOPE.md
#print axioms AJConjecture.theoremT
#print axioms AJConjecture.theoremF
#print axioms AJConjecture.aPolynomial_pair_associated_famBound
#print axioms AJConjecture.minimalRecurrence_whiteheadTorusKnot
#print axioms AJConjecture.isRecurrencePolynomial_whiteheadTorusKnot_one
#print axioms AJConjecture.morseReach_pair_source_target
#print axioms AJConjecture.whDouble_torusPairKnot
#print axioms AJConjecture.orientWrithes_braidLongDiagram
#print axioms AJConjecture.bandLinkings_whBand_braidLongDiagram
#print axioms AJConjecture.orientStates_clasp_negative
#print axioms AJConjecture.orientWrithes_whDouble_torusPairKnot
#print axioms AJConjecture.pairWhiteheadKnot_whDouble
#print axioms AJConjecture.whiteheadTorusKnot_whDouble
#print axioms AJConjecture.isWhSatellite_pairWhiteheadKnot
#print axioms AJConjecture.pairRealizesSatellite
#print axioms AJConjecture.coloredJones_two_pairWhiteheadKnot_ne
-- the marked-knot bridge (MARK_BRIDGE.md): chirality-robust refutation and calibration
#print axioms AJConjecture.toComparison_extraFactorMirror
#print axioms AJConjecture.exists_extraFactorMirror_zero_not_famBound_zero
#print axioms AJConjecture.isCoprime_extraFactorMirror_famBound
#print axioms AJConjecture.isCoprime_extraFactorMirror_pair
#print axioms AJConjecture.not_ajSquareFree_mirror_pair
#print axioms AJConjecture.commute_meridian_longitude
#print axioms AJConjecture.map_longitude_eq_one_of_commGroup
#print axioms AJConjecture.exists_hom_meridian_ofAdd_one
#print axioms AJConjecture.longitude_mul_meridian_pow_torusPairKnot
#print axioms AJConjecture.torusFullProd_pow_mem_center
#print axioms AJConjecture.coloredJones_two_trefoil
#print axioms AJConjecture.eigenvalueSet_trefoil_subset
#print axioms AJConjecture.mem_eigenvalueSet_trefoil
