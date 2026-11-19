import Mathlib
import AJPaper.Sharp.PpSRelease
import AJPaper.Divisor.PpLRelease
import AJPaper.Ideal.PpIMain
import AJPaper.Finger.PpFMain
import AJPaper.Filling.PpADichotomy
import AJPaper.Filling.PpATwistMain
import AJPaper.Zheng.PpZVerbatim

/-!
# The remaining claims of the paper

Formalization of the claims of *Whitehead doubles and the failure of the AJ conjecture*
(arXiv:2611.24826v1) beyond Theorem 1.1 that need no topology or hyperbolic geometry:
Section 8.4 (the classical factors in the specialized minimum, Corollary 8.3), Section 8.5 (the
ideal formulations), Section 9 (the torus-companion fingerprint, Corollary 9.2), Section 7.6
(the companion-abelian filling factor) and Zheng's estimates for Appendix B.5. The packages are
the subfolders of `AJPaper/`:

* `Sharp/` (Section 8.4): `corollary_untwisted_reverse` (Corollary 8.3), the whole symbol
  `(L - 1) E 𝒫_a` in the specialized minimum for `a ≠ 0`;
* `Divisor/` (Section 8.4, the index `a = 0`): `ppl_irreducible` (the transfer operator is
  irreducible for every index), `ppl_symbol_dvd_negClasp`, `ppl_sub_one_dvd`;
* `Ideal/` (Section 8.5): `theoremIdealFormulations` (the ideal formulations of Tran and of Sikora
  fail for the four families);
* `Finger/` (Section 9): `corollary_whitehead_fingerprint` (Corollary 9.2);
* `Filling/` (Section 7.6): `ppa_fillingFactor_dvd_neg`, `ppa_fillingFactor_dvd_pos`, the
  dichotomy for the A-polynomial, and `ppa_aPolynomial_twistKnot` for the twist knots;
* `Zheng/` (Appendix B.5): `zhengVerbatim_holds` (Zheng's estimates) and `geo_phys_holds`
  (Theorem B.1 (4) without hypothesis).
-/
