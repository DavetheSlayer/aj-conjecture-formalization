import AJPaper
import Solution

/-!
# Axiom report for the further claims of the paper (library `Proofs/AJPaper/`)

Run from the folder `lean`, after `lake build`:

    lake env lean checks/PrintAxiomsPaper.lean

Every line must read `depends on axioms: [propext, Classical.choice, Quot.sound]` (or a subset);
compare with `PrintAxiomsPaper.expected.txt`. First the eleven theorems of `comparator.json` that
concern Sections 7.6, 8.4, 8.5 and 9 and Theorem B.1 (4) of arXiv:2611.24826v1, then the results
they are assembled from, package by package (see `docs/FURTHER_CLAIMS.md`).
-/

-- the challenge (comparator.json)
#print axioms AJConjecture.release_corollaryUntwisted
#print axioms AJConjecture.release_wholeSymbolAllTwists
#print axioms AJConjecture.release_subOneDvd
#print axioms AJConjecture.ppl_irreducible
#print axioms AJConjecture.release_idealFormulations
#print axioms AJConjecture.corollary_whitehead_fingerprint
#print axioms AJConjecture.release_fillingFactor
#print axioms AJConjecture.release_fillingDichotomy
#print axioms AJConjecture.release_twistKnots
#print axioms AJConjecture.zhengEstimates_holds
#print axioms AJConjecture.geo_phys_holds

-- Section 8.4 (Sharp)
#print axioms AJConjecture.corollary_untwisted_reverse
#print axioms AJConjecture.pps_symbol_dvd_negClasp
#print axioms AJConjecture.pps_symbol_dvd_posClasp
#print axioms AJConjecture.release_wholeSymbol

-- Section 8.4, the index a = 0 (Divisor)
#print axioms AJConjecture.ppl_no_quadratic
#print axioms AJConjecture.ppl_irreducible_zero
#print axioms AJConjecture.ppl_symbol_dvd_negClasp
#print axioms AJConjecture.ppl_symbol_dvd_posClasp
#print axioms AJConjecture.ppl_zero_dvd_negClasp
#print axioms AJConjecture.ppl_zero_dvd_posClasp
#print axioms AJConjecture.ppl_sub_one_dvd
#print axioms AJConjecture.release_indexZero

-- Section 8.5 (Ideal)
#print axioms AJConjecture.theoremIdealFormulations
#print axioms AJConjecture.ppi_eval_eps_eq_zero
#print axioms AJConjecture.ppi_exists_point
#print axioms AJConjecture.not_ppiTranConjecture_of_point
#print axioms AJConjecture.not_ppiSikoraConjecture_of_point

-- Section 9 (Finger)
#print axioms AJConjecture.isTorusFingerprint_extraFactor
#print axioms AJConjecture.isTorusFingerprint_extraFactorMirror
#print axioms AJConjecture.ppf_recurrencePolynomial_bar
#print axioms AJConjecture.ppf_aPolynomial_inv

-- Section 7.6 (Filling)
#print axioms AJConjecture.ppa_fillingFactor_dvd_neg
#print axioms AJConjecture.ppa_fillingFactor_dvd_pos
#print axioms AJConjecture.ppa_aPolynomial_cases_neg
#print axioms AJConjecture.ppa_aPolynomial_cases_pos
#print axioms AJConjecture.ppa_aPolynomial_of_index_zero_neg
#print axioms AJConjecture.ppa_aPolynomial_of_index_zero_pos
#print axioms AJConjecture.ppa_aPolynomial_twistKnot
#print axioms AJConjecture.ppa_aPolynomial_pureClosure

-- Theorem B.1 (4): Zheng's estimates (Zheng)
#print axioms AJConjecture.zhengLemma32_holds
#print axioms AJConjecture.zhengLemma33_holds
#print axioms AJConjecture.zhengEq512_holds
#print axioms AJConjecture.zhengEq520_holds
#print axioms AJConjecture.zhengProp41_holds
#print axioms AJConjecture.zhengVerbatim_holds
#print axioms AJConjecture.ppZ_strip_shift_simple_pole
