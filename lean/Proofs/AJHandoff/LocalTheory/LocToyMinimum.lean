import Mathlib
import AJConjecture.QAlgPrimitiveScaling
import AJHandoff.LocalTheory.LocToyDescent
import AJHandoff.LocalTheory.LocToySequence
import AJHandoff.LocalTheory.LocTheoremSRecOp

/-!
# I-CTRL / I: the toy sequence has actual minimum `u² - 2u + z(2 - z)`

The toy recurrence operator has no right pseudo-factor of order `1` over `ℤ[t][M]` (from its
irreducibility over `ℂ((h))(z)`, `locToy_oreIrreducible`, by `oreIrreducible_map_iff` and the
descent `pseudoIrreducible_of_map` along `toyEmbed`). It annihilates the selected sequence at every
integer, and the sequence is not eventually zero, so by Theorem S (homogeneous form) every
annihilator of a tail is a left multiple of it up to a nonzero scalar: it is the minimum of both
the tail ideal and the rationally saturated all-integer ideal. It is primitive, and its special
symbol at `t = -1` (`q = 1`) is `(L - M)(L + M - 2)`: both residual blocks survive in the
minimum.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The toy recurrence operator maps to the toy operator over `ℂ[[h]][z]`. -/
private theorem toyRecOp_map_toyEmbed : toyRecOp.map toyEmbed = locToyOp := by
  simp [toyRecOp, locToyOp, toyEmbed]

/-- The toy recurrence operator is monic. -/
private theorem toyRecOp_monic : toyRecOp.Monic := by
  unfold toyRecOp
  monicity!

/-- The toy recurrence operator has order two. -/
private theorem toyRecOp_natDegree : toyRecOp.natDegree = 2 := by
  unfold toyRecOp
  compute_degree!

/-- The toy operator has no right pseudo-factor of intermediate order over `ℤ[t][M]`. -/
theorem toyRecOp_pseudoIrreducible {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * toyRecOp = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = toyRecOp.natDegree := by
  have hpos : 0 < locToyOp.natDegree := by
    have h0 := locToy_oreIrreducible.1
    rwa [natDegree_map_eq_of_injective (IsFractionRing.injective LocPoly LocField)] at h0
  refine pseudoIrreducible_of_map toyEmbed toyEmbed_injective coeffShift toyDilation.shiftHom
    toyEmbed_coeffShift (fun hβ' S' R' h' ↦ ?_) hβ h
  rw [toyRecOp_map_toyEmbed] at h' ⊢
  exact (oreIrreducible_map_iff toyDilation.shiftHom toyDilation.fieldShiftHom
    (fun a ↦ toyDilation.fieldShift_algebraMap a) hpos).1 locToy_oreIrreducible hβ' h'

/-- Every annihilator of a tail of the toy sequence is a left multiple of the toy operator. -/
theorem exists_C_mul_eq_oreMul_toyRecOp {Q : RecOp} {n₁ : ℤ}
    (hQ : ∀ n : ℤ, n₁ ≤ n → opApplyField Q toySeq n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T toyRecOp :=
  exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous (by rw [toyRecOp_natDegree]; norm_num)
    toyRecOp_pseudoIrreducible toySeq_not_eventually_zero (n₀ := 0)
    (fun n _ ↦ opApplyField_toyRecOp_toySeq n) hQ

/-- The toy operator is primitive, of order `2`, and both residual blocks survive at `t = -1`. -/
theorem toyRecOp_primitive_specialize :
    toyRecOp.IsPrimitive ∧ toyRecOp.natDegree = 2 ∧
      specialize toyRecOp = (X - C X) * (X + C (X - 2)) := by
  refine ⟨toyRecOp_monic.isPrimitive, toyRecOp_natDegree, ?_⟩
  simp [specialize, toyRecOp]
  ring

end AJConjecture
