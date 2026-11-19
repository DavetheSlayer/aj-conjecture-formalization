import AJFamily
import AJConjecture.UnknotAJ

/-!
# Axiom report

Run from the folder `lean`, after `lake build`:

    lake env lean checks/PrintAxioms.lean

Every line must read `depends on axioms: [propext, Classical.choice, Quot.sound]` (or a subset).
In particular `sorryAx` must not occur, and no axiom introduced by this development.
-/

open AJConjecture

-- The two main theorems.
#check (not_ajSquareFreeConjecture : ¬ AJSquareFreeConjecture)
#print axioms not_ajSquareFreeConjecture
#print axioms ajFamily_main

-- The family of counterexamples `whiteheadTorusKnot k` (braided Seifert-surface presentations of
-- the Whitehead doubles of `T(2, 2k+1)`), and their pairwise distinctness.
#print axioms whiteheadTorusKnot_counterexample
#print axioms whiteheadTorusKnot_pairwise_not_markovEquiv

-- The three inputs for each family knot.
-- (1) Sequence identity: the coloured Jones function equals the closed formula at every colour.
#print axioms laurentToField_coloredJones_whiteheadTorusKnot
-- (2) Quantum side: `E` divides the classical limit of every operator annihilating the formula.
#print axioms extraFactor_dvd_specialize_of_annihilates_torusWhiteheadFormula
-- (3) Classical side: the satellite structure of the knot group over `T(2, 2k+1)`, the bound it
-- gives on the boundary eigenvalues, and an A-polynomial not divisible by `E`.
#print axioms satellitePeripheral_whiteheadTorusKnot
#print axioms evalPoint_famBound_of_mem_eigenvalueSet
#print axioms exists_aPolynomial_not_extraFactor_dvd

-- Intermediate results: the isotopy from the closed braid to the satellite diagram, the
-- annihilator, irreducibility of the transfer operator, Jones distinctness.
#print axioms longKnotOp_whiteheadTorusKnot
#print axioms exists_annihilator_torusWhiteheadFormula
#print axioms natDegree_eq_zero_or_of_oreMul_eq_famTransferOp
#print axioms coloredJones_two_whiteheadTorusKnot_injective
#print axioms morseOp_eq_of_morseApplyAll

-- The analytic and geometric statements.
#print axioms mahlerMeasure_extraFactor
#print axioms whitehead_volume
#print axioms whitehead_slice_mem_extraFactor
#print axioms exists_whitehead_slice_of_extraFactor

-- Sanity check of the definitions, not used by the main theorems: the conjecture holds for the
-- unknot.
#print axioms ajSquareFree_unknot
