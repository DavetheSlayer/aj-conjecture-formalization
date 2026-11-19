import Mathlib
import AJHandoff.LocalTheory.LocToyMinimum

/-!
# Theorem I and its genuine non-family application

Theorem I of the source consists of the following checked statements of this package:

* Lemma 1 (I-INT): `exists_hasNormalizedIndex_int_of_quotient` — every rational quotient of a
  (JL) difference module has a determinant with `v_h = 0`, unit reduction and integral normalized
  index, with moving and coalescing poles allowed;
* Lemma 2 (I-PART): `locResidual_partition`;
* Lemma 3 (I-NODE): `hasNormalizedIndex_locNodeIndex` (formula (4)) and `locNodeIndex_swap`
  (formula (5), `I_H = -1 - I_G`);
* Theorem 4: `locBlockDvd_iff_of_forbiddenEdge`, `oreIrreducible_of_connected`;
* I-GAUGE: `hasNormalizedIndex_mul_coboundary`, `hasNormalizedIndex_mul_inv_coboundary`,
  `hasNormalizedIndex_gauge_of_isJointRegular`, `hasNormalizedIndex_powerSubst`,
  `hasNormalizedIndex_rescale`, `hasSimpleResidue_ramify`;
* I-SEQ: `seq_theoremS` (over `ℚ(t, M)`), `exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational`,
  `exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous`,
  `toComparison_specialize_dvd_of_tail_annihilator_gauge`;
* I-CTRL: this file, `LocFactoredControl`, `LocConstantControl`, `LocWeakControl`.

The application below lies outside the Whitehead finite-sum family: the degree-two operator
`u² - 2u + z(2 - z)` is irreducible over `ℂ((h))(z)` by the connected obstruction graph, hence has
no right pseudo-factor over `ℤ[t][M]`; the explicitly selected two-sided sequence `f₀ = f₁ = 1`
has it as actual minimum (in the tail ideal and in the saturated all-integer ideal), and both
residual blocks `u - z`, `u + z - 2` survive in its primitive `q = 1` specialization.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Theorem I, toy application.** -/
theorem toy_theoremI :
    OreIrreducible toyDilation.fieldShiftHom (locToyOp.map (algebraMap LocPoly LocField)) ∧
      (∀ n : ℤ, opApplyField toyRecOp toySeq n = 0) ∧
      (∀ {Q : RecOp} {n₁ : ℤ}, (∀ n : ℤ, n₁ ≤ n → opApplyField Q toySeq n = 0) →
        ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T toyRecOp) ∧
      toyRecOp.IsPrimitive ∧ specialize toyRecOp = (X - C X) * (X + C (X - 2)) :=
  ⟨locToy_oreIrreducible, opApplyField_toyRecOp_toySeq, exists_C_mul_eq_oreMul_toyRecOp,
    toyRecOp_primitive_specialize.1, toyRecOp_primitive_specialize.2.2⟩

end AJConjecture
