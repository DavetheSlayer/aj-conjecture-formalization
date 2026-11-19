import AJTwist
import Solution

/-!
# Axiom report for the four-family theorem (handoff of 18 November 2026)

Run from the folder `lean`, after `lake build`:

    lake env lean checks/PrintAxiomsFourFamilies.lean

Every line must read `depends on axioms: [propext, Classical.choice, Quot.sound]` (or a subset);
compare with `PrintAxiomsFourFamilies.expected.txt`. First the two four-family theorems of
`comparator.json` (the challenge `Challenge.lean`), then the main theorem of the library
`Proofs/AJTwist/`, then the results it is assembled from, package by package (see
`docs/FOUR_FAMILIES.md`).
-/

-- the challenge (comparator.json)
#print axioms AJConjecture.release_theoremFourFamilies
#print axioms AJConjecture.release_fourFamilies_coloredJones

-- the main theorem (Main)
#print axioms AJConjecture.theoremFourFamilies
#print axioms AJConjecture.twFamilyClauses_twFamilyKnot
#print axioms AJConjecture.twFamilyClauses_negClasp
#print axioms AJConjecture.twFamilyClauses_posClasp
#print axioms AJConjecture.twFamilyKnot_untwisted
#print axioms AJConjecture.pairTClauses_of_twFamilyClauses
#print axioms AJConjecture.prime_toComparison_extraFactorMirror
#print axioms AJConjecture.twm_coloredJones_negClasp
#print axioms AJConjecture.twm_coloredJones_posClasp
#print axioms AJConjecture.twm_coloredJones_mirror
#print axioms AJConjecture.twm_mirror_exists
#print axioms AJConjecture.twm_mirror_survival

-- the knots (Knot)
#print axioms AJConjecture.isBandClasp_twWhiteheadKnot
#print axioms AJConjecture.writhe_twWhiteheadKnot
#print axioms AJConjecture.twWhiteheadKnot_zero_true
#print axioms AJConjecture.eq_twFamilyKnot_of_word
#print axioms AJConjecture.coloredJones_inv
#print axioms AJConjecture.exists_knotGroup_inv_equiv
#print axioms AJConjecture.eigenvalueSet_inv'
#print axioms AJConjecture.eigenvalueSet_symm

-- the coloured Jones function and the transfer (Quantum)
#print axioms AJConjecture.twQ_coloredJones_negClasp
#print axioms AJConjecture.twQ_coloredJones_posClasp
#print axioms AJConjecture.twQ_transfer_mem_periodSpan
#print axioms AJConjecture.twTransferOp_natCast
#print axioms AJConjecture.specialize_twTransferOp_ne_zero
#print axioms AJConjecture.extraFactor_dvd_specialize_twTransferOp

-- existence of an annihilator (Exist)
#print axioms AJConjecture.twH_exists_annihilator
#print axioms AJConjecture.twH_knot
#print axioms AJConjecture.twH_knot_bar

-- the factor theory of the transfer operators (Factor)
#print axioms AJConjecture.twf_irreducible
#print axioms AJConjecture.twf_no_linear

-- selection by the actual sequence (Select)
#print axioms AJConjecture.tws_selects
#print axioms AJConjecture.tws_survival

-- the classical side (Classical)
#print axioms AJConjecture.twClassClauses_twFamilyKnot_neg
#print axioms AJConjecture.twClassClauses_twFamilyKnot_pos
#print axioms AJConjecture.isTwWhSatellite_twWhiteheadKnot
