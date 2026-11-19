import Mathlib
import AJConjecture.QAlgEventuallyRational
import AJConjecture.QAlgEvalAtFieldZeros
import AJConjecture.QAlgOpApplyFieldBasic
import AJHandoff.LocalTheory.LocSeqField
import AJHandoff.LocalTheory.LocTheoremSAbstract

/-!
# The sequence module: germs of sequences at `+∞`

`S` is the ring of sequences `ℤ → ℚ(t)` modulo eventual equality (`Filter.Germ atTop`). The shift
`L` sends `f` to `n ↦ f(n+1)`. Every `a ∈ K = ℚ(t, M)` defines the tail sequence
`n ↦ a(t, t^(2n))`: a nonzero element of `ℤ[t][M]` vanishes at only finitely many colours
(`exists_forall_ge_evalAtField_ne_zero`), so it is a unit of `S` and evaluation extends to a ring
homomorphism `ev : K → S` with `L ∘ ev = ev ∘ τ`. Statements about tail classes never cancel a
rational coefficient at one of its exceptional colours.

The bridge to the library: an operator with coefficients in `ℤ[t][M]` acts on the germ of `f` as
`opApplyField` does on `f`; `f` is eventually rational (`EventuallyRational`) exactly when its
germ lies in `ev(K)`.
-/

open Polynomial Filter

noncomputable section

namespace AJConjecture

/-- Sequences in `ℚ(t)` modulo eventual equality. -/
abbrev SeqGerm : Type := Germ (atTop : Filter ℤ) (RatFunc ℚ)

/-- The germ of a sequence. -/
def seqGerm (f : ℤ → RatFunc ℚ) : SeqGerm := Germ.coeRingHom atTop f

/-- The shift `L f = (n ↦ f(n + 1))` of germs. -/
def seqGermShift : SeqGerm →+* SeqGerm where
  toFun f := f.compTendsto (· + 1) (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  map_one' := rfl
  map_mul' f g := Germ.inductionOn₂ f g fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' f g := Germ.inductionOn₂ f g fun _ _ ↦ rfl

theorem isUnit_seqGerm_evalAtField {c : Coeff} (hc : c ∈ nonZeroDivisors Coeff) :
    IsUnit (seqGerm fun n ↦ evalAtField n c) := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero (nonZeroDivisors.ne_zero hc)
  refine IsUnit.of_mul_eq_one (seqGerm fun n ↦ (evalAtField n c)⁻¹) ?_
  rw [seqGerm, seqGerm, ← map_mul, ← map_one (Germ.coeRingHom atTop)]
  exact Germ.coe_eq.mpr <| Filter.eventually_atTop.mpr ⟨n₀, fun n hn ↦
    mul_inv_cancel₀ (hn₀ n hn)⟩

/-- Evaluation `ev : K → S`, `a ↦ (n ↦ a(t, t^(2n)))` on a tail. -/
def seqEval : SeqField →+* SeqGerm :=
  IsLocalization.lift (M := nonZeroDivisors Coeff) (S := SeqField)
    (g := (Germ.coeRingHom atTop).comp (RingHom.pi fun n ↦ evalAtField n))
    (fun c ↦ isUnit_seqGerm_evalAtField c.2)

/-- Evaluation of an element of `ℤ[t][M]`. -/
private theorem seqEval_algebraMap (c : Coeff) :
    seqEval (algebraMap Coeff SeqField c) = seqGerm fun n ↦ evalAtField n c := by
  exact IsLocalization.lift_eq (M := nonZeroDivisors Coeff) (S := SeqField) _ c

/-- The shift of the germ of a sequence. -/
private theorem seqGermShift_seqGerm (f : ℤ → RatFunc ℚ) :
    seqGermShift (seqGerm f) = seqGerm fun n ↦ f (n + 1) :=
  rfl

/-- Iterated shifts of the germ of a sequence. -/
private theorem iterate_seqGermShift_seqGerm (i : ℕ) (f : ℤ → RatFunc ℚ) :
    seqGermShift^[i] (seqGerm f) = seqGerm fun n ↦ f (n + i) := by
  induction i generalizing f with
  | zero => simp only [Function.iterate_zero, id, Nat.cast_zero, add_zero]
  | succ i ih =>
    rw [Function.iterate_succ_apply, seqGermShift_seqGerm, ih]
    congr 1
    funext n
    congr 1
    push_cast
    ring

theorem seqGermShift_seqEval (a : SeqField) : seqGermShift (seqEval a) = seqEval (seqShift a) := by
  have h : seqGermShift.comp seqEval = seqEval.comp seqShift := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors Coeff) (RingHom.ext fun c ↦ ?_)
    simp only [RingHom.comp_apply, seqShift_algebraMap, seqEval_algebraMap,
      seqGermShift_seqGerm, evalAtField_coeffShift]
  exact congrArg (fun φ : SeqField →+* SeqGerm ↦ φ a) h

/-- Operators with coefficients in `ℤ[t][M]` act on germs as `opApplyField` acts on sequences. -/
theorem diffAct_seqEval_map (P : RecOp) (f : ℤ → RatFunc ℚ) :
    diffAct seqEval seqGermShift (P.map (algebraMap Coeff SeqField)) (seqGerm f) =
      seqGerm fun n ↦ opApplyField P f n := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, diffAct_add_left, hp, hq, seqGerm, seqGerm, seqGerm, ← map_add]
    congr 1
    funext n
    rw [Pi.add_apply, opApplyField_add_left]
  | monomial i a =>
    rw [Polynomial.map_monomial, diffAct_monomial, seqEval_algebraMap,
      iterate_seqGermShift_seqGerm, seqGerm, seqGerm, seqGerm, ← map_mul]
    congr 1
    funext n
    rw [Pi.mul_apply, opApplyField_monomial]

/-- `f` is eventually rational exactly when its germ lies in `ev(K)`. -/
theorem eventuallyRational_iff_mem_range (f : ℤ → RatFunc ℚ) :
    EventuallyRational f ↔ seqGerm f ∈ seqEval.range := by
  constructor
  · rintro ⟨a, b, hb, n₀, h⟩
    have hbK : algebraMap Coeff SeqField b ≠ 0 := by
      rwa [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    refine ⟨algebraMap Coeff SeqField a / algebraMap Coeff SeqField b, ?_⟩
    have hu : IsUnit (seqEval (algebraMap Coeff SeqField b)) := hbK.isUnit.map seqEval
    refine hu.mul_left_cancel ?_
    rw [← map_mul, mul_div_cancel₀ _ hbK, seqEval_algebraMap, seqEval_algebraMap, seqGerm,
      seqGerm, seqGerm, ← map_mul]
    exact (Germ.coe_eq.mpr <| Filter.eventually_atTop.mpr ⟨n₀, fun n hn ↦ h n hn⟩).symm
  · rintro ⟨x, hx⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Coeff) x
    have hbK : algebraMap Coeff SeqField b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h := congrArg (· * seqEval (algebraMap Coeff SeqField b)) hx
    rw [← map_mul, div_mul_cancel₀ _ hbK, seqEval_algebraMap, seqEval_algebraMap, seqGerm,
      seqGerm, seqGerm, ← map_mul] at h
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (Germ.coe_eq.mp h)
    refine ⟨a, b, nonZeroDivisors.ne_zero hb, n₀, fun n hn ↦ ?_⟩
    rw [hn₀ n hn, Pi.mul_apply, mul_comm]

end AJConjecture
