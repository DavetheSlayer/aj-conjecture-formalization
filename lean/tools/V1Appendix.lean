import AJFamily
import AJHandoff
import Solution
import AJHandoff.Geometry.GeoZhVerbatim
import AJHandoff.TorusKnot.PairKWhDMain
import AJHandoff.TorusKnot.PairKWhDBandTorus
import AJHandoff.TorusKnot.PairKJonesTwoNe
import AJHandoff.TorusKnot.PairKMirrorRobust
import AJHandoff.TorusKnot.PairKMarkCalib
/-!
# Appendix A of `docs/V1_SCOPE.md`

Run from the folder `lean`, after `lake build`:

    lake env lean tools/V1Appendix.lean

Prints the exact statements of the v1 release: the predicates, the core and release theorems, the
satellite bridge, the conditional statements, the axioms of the main theorems, (A.6) every
theorem checked by the challenge (`comparator.json`), in its order, and (A.7) the
chirality-robust refutation and the calibration theorems of `MARK_BRIDGE.md`.
-/

set_option pp.fieldNotation false
set_option pp.proofs false
open AJConjecture
-- A.1 the conjecture and the predicates
#print AJSquareFree
#print AJSquareFreeConjecture
#print IsRecurrencePolynomial
#print InLocalizedAnnihilator
#print Annihilates
#print opApply
#print specialize
#print toComparison
#print IsAPolynomialOf
#print eigenvalueSet
#print extraFactor
#print famBound
#print IsTorusPair
#print MarkovEquiv
#print PairTClauses
-- A.2 core theorems
#check @not_ajSquareFreeConjecture
#check @theoremT
#check @theoremF
#check @aPolynomial_pair_associated_famBound
#check @minimalRecurrence_whiteheadTorusKnot
#check @isRecurrencePolynomial_whiteheadTorusKnot_one
#check @release_theoremT
#check @release_classicalEquality
#check @release_minimalRecurrence
#check @release_pairWord_two
-- A.3 the satellite bridge
#check @morseReach_pair_source_target
#print pairTargetWord
#check @longKnotOp_pairWhiteheadKnot
#check @writhe_pairWhiteheadKnot
#check @isWhSatellite_pairWhiteheadKnot
#print IsWhSatellite
#check @pairRealizesSatellite
#print PairRealizesSatellite
#print whDouble
#print whBand
#print bandUntwist
#print morseWrithe
#print IsLongKnotDiagram
#print braidLongDiagram
#check @whDouble_torusPairKnot
#check @morseReach_whDouble
#check @morseWrithe_eq_of_morseReach
#check @orientWrithes_braidLongDiagram
#check @zero_mem_bandLinkings_whBand
#check @bandLinkings_whBand_braidLongDiagram
#check @orientStates_clasp_negative
#check @orientWrithes_whDouble_torusPairKnot
#check @pairWhiteheadKnot_whDouble
#check @whiteheadTorusKnot_whDouble
#check @coloredJones_two_pairWhiteheadKnot_ne
-- A.4 conditional statements
#print ZhengVerbatim
#print ZhengEstimates
#check @zhengEq516_holds
#check @zhengEq519_of_zhengEq512
#check @zhengEstimates_of_verbatim
#check @geo_phys_of_zhengVerbatim
#print WhiteheadJSJProp
#check @pairWhiteheadKnot_not_markovEquiv_of_jsj
#check @pairWhiteheadKnot_knotGroup_not_equiv_of_jsj
-- A.5 axioms
#print axioms not_ajSquareFreeConjecture
#print axioms theoremT
#print axioms theoremF
#print axioms aPolynomial_pair_associated_famBound
#print axioms minimalRecurrence_whiteheadTorusKnot
#print axioms isRecurrencePolynomial_whiteheadTorusKnot_one
#print axioms release_theoremT
#print axioms release_classicalEquality
#print axioms release_minimalRecurrence
#print axioms release_pairWord_two
#print axioms morseReach_pair_source_target
#print axioms geo_phys_of_zhengVerbatim
#print axioms zhengEq516_holds
#print axioms pairWhiteheadKnot_whDouble
#print axioms whiteheadTorusKnot_whDouble
#print axioms morseReach_whDouble
#print axioms bandLinkings_whBand_braidLongDiagram
#print axioms zero_mem_bandLinkings_whBand
#print axioms coloredJones_two_pairWhiteheadKnot_ne
-- A.6 the release challenge
#check @not_ajSquareFreeConjecture
#check @release_theoremT
#check @release_classicalEquality
#check @release_minimalRecurrence
#check @release_pairWord_two
#check @release_coloredJones_two_ne
#check @release_whDouble
#check @morseReach_whDouble
#check @morseWrithe_eq_of_morseReach
#check @zero_mem_bandLinkings_whBand
#check @ajFamily_main
#check @zhengEq516_holds
#check @zhengEq519_of_zhengEq512
#check @zhengEstimates_of_verbatim
#check @geo_phys_of_zhengVerbatim
#check @release_theoremG
#check @release_theoremG_supplement
#check @exists_hasNormalizedIndex_int_of_quotient
#check @exists_int_hasNormalizedIndex_locLogJet
#check @locResidual_partition
#check @hasSimpleResidue_locLogJet_of_allowedNode
#check @hasNormalizedIndex_locNodeIndex
#check @locBlockDvd_iff_of_forbiddenEdge
#check @oreIrreducible_of_connected
#check @det_gauge
#check @hasNormalizedIndex_mul_coboundary
#check @hasNormalizedIndex_mul_inv_coboundary
#check @hasNormalizedIndex_gauge_of_isJointRegular
#check @hasNormalizedIndex_rescale
#check @release_hasSimpleResidue_ramify
#check @release_hasNormalizedIndex_powerSubst
#check @exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational
#check @exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous
#check @toComparison_specialize_dvd_of_tail_annihilator_gauge
#check @release_seq_theoremS
#check @toyRecOp_pseudoIrreducible
#check @exists_C_mul_eq_oreMul_toyRecOp
#check @toyRecOp_primitive_specialize
#check @locFactored_nodeIndex
#check @constSeq_minimum
#check @constSeq_oversized
#check @constSeq_not_selected
#check @not_weakLatticeLemma
#check @toy_theoremI
#check @pairQJets_abNode
#check @pairQJets_ebNode
#check @pairQ_transferOp_oreIrreducible
-- A.7 the marked-knot bridge (MARK_BRIDGE.md)
#print extraFactorMirror
#check @toComparison_extraFactorMirror
#check @exists_extraFactorMirror_zero_not_famBound_zero
#check @isCoprime_extraFactorMirror_famBound
#check @isCoprime_extraFactorMirror_pair
#check @not_ajSquareFree_mirror_pair
#check @commute_meridian_longitude
#check @map_longitude_eq_one_of_commGroup
#check @exists_hom_meridian_ofAdd_one
#check @longitude_mul_meridian_pow_torusPairKnot
#check @torusFullProd_pow_mem_center
#check @coloredJones_two_trefoil
#check @eigenvalueSet_trefoil_subset
#check @mem_eigenvalueSet_trefoil
