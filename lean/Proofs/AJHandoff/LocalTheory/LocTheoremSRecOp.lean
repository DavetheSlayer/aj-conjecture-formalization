import Mathlib
import AJConjecture.QAlgEventuallyRationalClosure
import AJConjecture.QAlgOrePseudoDivision
import AJConjecture.QAlgEvalAtFieldZeros
import AJConjecture.QAlgOpApplyFieldOreMul
import AJHandoff.LocalTheory.LocSeqGerm

/-!
# I-SEQ: Theorem S for recurrence operators, zero forcing included

The form of Theorem S used by the applications, for operators with coefficients in `ℤ[t][M]`
(the library's `RecOp`) and pseudo-factorizations (equivalent to the form over `ℚ(t, M)` by
`oreIrreducible_map_iff` and `exists_C_mul_eq_oreMul_of_map_eq`).

* Inhomogeneous: if `P` has no right pseudo-factor of intermediate degree, `f` is not eventually
  rational and `P f` is eventually rational (possibly eventually zero), every annihilator of a
  tail of `f` is, up to a nonzero scalar, a left multiple of `P`. The library's
  `exists_C_mul_eq_oreMul_of_tail_annihilator_of_irreducible` also assumed `P f` eventually
  nonzero.
* Homogeneous: if `f` is not eventually zero and `P f` vanishes on a tail, the same conclusion
  (the Bézout argument of the source's toy application).

Proof: the minimal-degree argument of the library's `TailMinimalDegreeGeneric` for the left
ideal `{Q : Q f eventually rational}` (resp. `{Q : Q f eventually zero}`), followed by right
pseudo-division of the annihilator by its minimal element.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The germ of a sequence vanishing on a tail is zero. -/
private theorem seqGerm_eq_zero_of_tail {g : ℤ → RatFunc ℚ} {n₁ : ℤ} (hg : ∀ n : ℤ, n₁ ≤ n → g n = 0) :
    seqGerm g = 0 := by
  rw [seqGerm, ← map_zero (Filter.Germ.coeRingHom Filter.atTop)]
  exact Filter.Germ.coe_eq.mpr <| Filter.eventually_atTop.mpr ⟨n₁, hg⟩

/-- Theorem S for recurrence operators, for any `L`- and `ev(K)`-stable subgroup `W` of germs:
a pseudo-irreducible `P` with `P f ∈ W` and `f ∉ W` right-divides every tail annihilator of `f`
up to a nonzero scalar. -/
private theorem exists_C_mul_eq_oreMul_of_tail_annihilator_of_mem {P : RecOp} (hP : 0 < P.natDegree)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (W : AddSubgroup SeqGerm) (hWK : ∀ (a : SeqField) (w : SeqGerm), w ∈ W → seqEval a * w ∈ W)
    (hWL : ∀ w ∈ W, seqGermShift w ∈ W) {f : ℤ → RatFunc ℚ} (hF : seqGerm f ∉ W)
    (hPF : (seqGerm fun n ↦ opApplyField P f n) ∈ W)
    {Q : RecOp} {n₁ : ℤ} (hQ : ∀ n : ℤ, n₁ ≤ n → opApplyField Q f n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T P := by
  have hirrK := (oreIrreducible_map_iff coeffShift seqShift seqShift_algebraMap hP).mpr hirr
  have hG : diffAct seqEval seqGermShift (Q.map (algebraMap Coeff SeqField)) (seqGerm f) = 0 := by
    rw [diffAct_seqEval_map]
    exact seqGerm_eq_zero_of_tail hQ
  obtain ⟨H, hH⟩ := exists_eq_oreMul_of_diffAct_eq_zero seqShift seqEval seqGermShift
    seqGermShift_seqEval W hWK hWL hirrK hF (by rwa [diffAct_seqEval_map]) hG
  exact exists_C_mul_eq_oreMul_of_map_eq coeffShift seqShift seqShift_algebraMap hH

/-- **Theorem S**, inhomogeneous form, forcing eventually rational (including zero). -/
theorem exists_C_mul_eq_oreMul_of_tail_annihilator_of_rational {P : RecOp}
    (hP : 0 < P.natDegree)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    {f : ℤ → RatFunc ℚ} (hnr : ¬ EventuallyRational f)
    (hrat : EventuallyRational fun n ↦ opApplyField P f n)
    {Q : RecOp} {n₁ : ℤ} (hQ : ∀ n : ℤ, n₁ ≤ n → opApplyField Q f n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T P :=
  exists_C_mul_eq_oreMul_of_tail_annihilator_of_mem hP hirr seqEval.range.toAddSubgroup
    (fun a _ ⟨x, hx⟩ ↦ ⟨a * x, by rw [map_mul, hx]⟩)
    (fun _ ⟨x, hx⟩ ↦ ⟨seqShift x, by rw [← seqGermShift_seqEval, hx]⟩)
    (fun h ↦ hnr ((eventuallyRational_iff_mem_range f).mpr h))
    ((eventuallyRational_iff_mem_range _).mp hrat) hQ

/-- **Theorem S**, homogeneous form. -/
theorem exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous {P : RecOp}
    (hP : 0 < P.natDegree)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    {f : ℤ → RatFunc ℚ} (hnz : ¬ ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → f n = 0) {n₀ : ℤ}
    (hPf : ∀ n : ℤ, n₀ ≤ n → opApplyField P f n = 0)
    {Q : RecOp} {n₁ : ℤ} (hQ : ∀ n : ℤ, n₁ ≤ n → opApplyField Q f n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T P := by
  refine exists_C_mul_eq_oreMul_of_tail_annihilator_of_mem hP hirr ⊥
    (fun a w hw ↦ by rw [AddSubgroup.mem_bot] at hw ⊢; rw [hw, mul_zero])
    (fun w hw ↦ by rw [AddSubgroup.mem_bot] at hw ⊢; rw [hw, map_zero]) ?_
    (AddSubgroup.mem_bot.mpr (seqGerm_eq_zero_of_tail hPf)) hQ
  rw [AddSubgroup.mem_bot, seqGerm, ← map_zero (Filter.Germ.coeRingHom Filter.atTop)]
  intro h
  exact hnz (Filter.eventually_atTop.mp (Filter.Germ.coe_eq.mp h))

end AJConjecture
