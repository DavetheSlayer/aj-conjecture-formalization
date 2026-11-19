import AJHandoff

/-!
# Axiom report for the handoff theorems

Run from the folder `lean`, after `lake build`:

    lake env lean checks/PrintAxiomsHandoff.lean

Every line must read `depends on axioms: [propext, Classical.choice, Quot.sound]` (or a subset);
compare with `PrintAxiomsHandoff.expected.txt`. The theorems are those listed in the index
`Proofs/AJHandoff.lean`, unit by unit.
-/

#print axioms AJConjecture.aPolynomial_pair_associated
#print axioms AJConjecture.aPolynomial_pair_factors
#print axioms AJConjecture.center_torusKnotGroup
#print axioms AJConjecture.constSeq_minimum
#print axioms AJConjecture.constSeq_not_selected
#print axioms AJConjecture.constSeq_oversized
#print axioms AJConjecture.det_gauge
#print axioms AJConjecture.eq_of_mulEquiv_cycCoprod
#print axioms AJConjecture.exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous
#print axioms AJConjecture.exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational
#print axioms AJConjecture.exists_C_mul_eq_oreMul_toyRecOp
#print axioms AJConjecture.exists_hasNormalizedIndex_int_of_quotient
#print axioms AJConjecture.exists_int_hasNormalizedIndex_locLogJet
#print axioms AJConjecture.famB_eq_twistPoly
#print axioms AJConjecture.geo_theoremG
#print axioms AJConjecture.hasNormalizedIndex_gauge_of_isJointRegular
#print axioms AJConjecture.hasNormalizedIndex_locNodeIndex
#print axioms AJConjecture.hasNormalizedIndex_mul_coboundary
#print axioms AJConjecture.hasNormalizedIndex_mul_inv_coboundary
#print axioms AJConjecture.hasNormalizedIndex_powerSubst
#print axioms AJConjecture.hasNormalizedIndex_rescale
#print axioms AJConjecture.hasSimpleResidue_locLogJet_of_allowedNode
#print axioms AJConjecture.hasSimpleResidue_ramify
#print axioms AJConjecture.isCoprime_extraFactor_pair
#print axioms AJConjecture.isRecurrencePolynomial_whiteheadTorusKnot_one
#print axioms AJConjecture.knotGroup_torusPairKnot_equiv
#print axioms AJConjecture.locBlockDvd_iff_of_forbiddenEdge
#print axioms AJConjecture.locFactored_nodeIndex
#print axioms AJConjecture.locResidual_partition
#print axioms AJConjecture.longKnotOp_pairWhiteheadKnot
#print axioms AJConjecture.minimalRecurrence_whiteheadTorusKnot
#print axioms AJConjecture.not_weakLatticeLemma
#print axioms AJConjecture.orderOf_dvd_of_isOfFinOrder_cycCoprod
#print axioms AJConjecture.oreIrreducible_of_connected
#print axioms AJConjecture.pairQ_abNode
#print axioms AJConjecture.pairQ_block
#print axioms AJConjecture.pairQ_ebNode
#print axioms AJConjecture.pairQ_formula_package
#print axioms AJConjecture.pairQ_knot_package
#print axioms AJConjecture.pairQ_symbol
#print axioms AJConjecture.pairQ_tOrder_reducedFormula
#print axioms AJConjecture.pairQ_transferOp_irreducible
#print axioms AJConjecture.pairQ_transferOp_oreIrreducible
#print axioms AJConjecture.pairWhiteheadKnot_knotGroup_not_equiv_of_jsj
#print axioms AJConjecture.pairWhiteheadKnot_not_markovEquiv_of_jsj
#print axioms AJConjecture.pair_reverse_inclusion
#print axioms AJConjecture.seq_theoremS
#print axioms AJConjecture.sub_one_dvd_aPolynomial
#print axioms AJConjecture.tailOrder_whiteheadTorusKnot
#print axioms AJConjecture.theoremF
#print axioms AJConjecture.theoremT
#print axioms AJConjecture.theoremT_of_input
#print axioms AJConjecture.toComparison_dvd_famBound_pair
#print axioms AJConjecture.toComparison_specialize_dvd_of_tail_annihilator_gauge
#print axioms AJConjecture.torusKnotGroup_quot_center
#print axioms AJConjecture.toyRecOp_primitive_specialize
#print axioms AJConjecture.toyRecOp_pseudoIrreducible
#print axioms AJConjecture.toy_theoremI
#print axioms AJConjecture.writhe_pairWhiteheadKnot
#print axioms AJConjecture.pairQ_torusInput
#print axioms AJConjecture.pairQ_opApplyField_famTransferOp
#print axioms AJConjecture.aPolynomial_pair_associated_famBound
#print axioms AJConjecture.longKnotOp_mul_jwAt_eq_smul
#print axioms AJConjecture.exists_laurent_torusReducedFormula
#print axioms AJConjecture.geo_hypVolume_idealTetI
#print axioms AJConjecture.geo_reduced_value_eq_zhengDiagonal
#print axioms AJConjecture.natDegree_isRecurrencePolynomial_whiteheadTorusKnot
#print axioms AJConjecture.specialize_isRecurrencePolynomial_whiteheadTorusKnot
#print axioms AJConjecture.pairRealizesSatellite
#print axioms AJConjecture.isWhSatellite_pairWhiteheadKnot
#print axioms AJConjecture.pairQJets_abNode
#print axioms AJConjecture.pairQJets_ebNode
#print axioms AJConjecture.exists_pairFixedTuple
