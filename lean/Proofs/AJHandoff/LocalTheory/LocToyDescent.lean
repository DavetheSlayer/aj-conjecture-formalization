import Mathlib
import AJConjecture.QAlgCoeffShift
import AJHandoff.LocalTheory.LocToyOperator

/-!
# From `ℂ((h))(z)` back to `ℚ(t, M)`: the embedding `t ↦ exp(h/2)`, `M ↦ z`

The library's sequence world uses `ℤ[t][M]` with `τ(M) = t² M` and `M` acting by `t^(2n)`; the
toy's `q = t²`. The embedding `t ↦ exp(h/2)`, `M ↦ z` of `ℤ[t][M]` into `ℂ[[h]][z]` is injective
(`exp(h/2) - α ≠ 0` in the domain `ℂ[[h]]` for every `α ∈ ℂ`, and a nonzero integer polynomial
splits over `ℂ`) and carries `τ` to the shift `σ(z) = exp(h) z` of `toyDilation`. A right
pseudo-factor over `ℤ[t][M]` maps to one over `ℂ[[h]][z]` (`pseudoIrreducible_of_map`), so
irreducibility over `ℂ((h))(z)` implies irreducibility over `ℚ(t, M)`. The same mechanism, with
`t ↦ -exp(h/4)` and the backward shift, is the source's full-field passage for the knot
operators.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The embedding `ℤ[t][M] → ℂ[[h]][z]`, `t ↦ exp(h/2)`, `M ↦ z`. -/
def toyEmbed : Coeff →+* LocPoly :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Int.castRingHom LocPoly)
      (C (PowerSeries.rescale (1 / 2 : ℂ) (PowerSeries.exp ℂ)))) X

/-- The half-exponential `exp(h/2)`. -/
private def toyHalfExp : PowerSeries ℂ := PowerSeries.rescale (1 / 2 : ℂ) (PowerSeries.exp ℂ)

/-- The inner evaluation `ℤ[t] → ℂ[[h]]`, `t ↦ exp(h/2)`. -/
private def toyInnerEval : ℤ[X] →+* PowerSeries ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries ℂ)) toyHalfExp

/-- The embedding is coefficientwise evaluation at `exp(h/2)`. -/
private theorem toyEmbed_eq_map (c : Coeff) : toyEmbed c = c.map toyInnerEval := by
  have hf : Polynomial.eval₂RingHom (Int.castRingHom LocPoly)
      (C (PowerSeries.rescale (1 / 2 : ℂ) (PowerSeries.exp ℂ))) =
      (C : PowerSeries ℂ →+* LocPoly).comp toyInnerEval := by
    refine Polynomial.ringHom_ext (fun n ↦ ?_) ?_
    · simp [toyInnerEval]
    · simp [toyInnerEval, toyHalfExp]
  simp only [toyEmbed, coe_eval₂RingHom, hf]
  rfl

/-- `exp(h/2) - α ≠ 0` for every constant `α`. -/
private theorem toyHalfExp_sub_ne_zero (α : ℂ) :
    toyHalfExp - algebraMap ℂ (PowerSeries ℂ) α ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  simp [toyHalfExp, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1

/-- `exp(h/2)` is not a root of a nonzero integer polynomial. -/
private theorem toyInnerEval_injective : Function.Injective toyInnerEval := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra hq0
  set qC : ℂ[X] := q.map (Int.castRingHom ℂ) with hqC
  have hqC0 : qC ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).2 hq0
  have heval : aeval toyHalfExp qC = 0 := by
    have hcomp : (algebraMap ℂ (PowerSeries ℂ)).comp (Int.castRingHom ℂ) =
        Int.castRingHom (PowerSeries ℂ) := RingHom.ext_int _ _
    rw [hqC, aeval_def, eval₂_map, hcomp]
    exact hq
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.splits qC).natDegree_eq_card_roots.symm] at heval
  simp only [map_mul, aeval_C, map_multiset_prod, Multiset.map_map, Function.comp_apply,
    map_sub, aeval_X] at heval
  rcases mul_eq_zero.mp heval with h | h
  · exact leadingCoeff_ne_zero.2 hqC0
      ((map_eq_zero_iff _ (algebraMap ℂ (PowerSeries ℂ)).injective).1 h)
  · obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h)
    exact toyHalfExp_sub_ne_zero a ha

theorem toyEmbed_injective : Function.Injective toyEmbed := by
  intro a b hab
  rw [toyEmbed_eq_map, toyEmbed_eq_map] at hab
  exact Polynomial.map_injective _ toyInnerEval_injective hab

theorem toyEmbed_coeffShift (c : Coeff) :
    toyEmbed (coeffShift c) = toyDilation.shift (toyEmbed c) := by
  have hQ : toyInnerEval (X ^ 2) = (toyDilation.Q : PowerSeries ℂ) := by
    rw [map_pow]
    simp only [toyInnerEval, coe_eval₂RingHom, eval₂_X, toyHalfExp, toyDilation, LocDilation.exp,
      IsUnit.unit_spec, sq]
    rw [PowerSeries.exp_mul_exp_eq_exp_add]
    norm_num
  change toyEmbed (c.comp (C (X ^ 2) * X)) = (toyEmbed c).comp (C _ * X)
  rw [toyEmbed_eq_map, toyEmbed_eq_map, Polynomial.map_comp, Polynomial.map_mul, map_C, map_X,
    hQ]

/-- A right pseudo-factor of intermediate degree descends along an injective intertwining map. -/
theorem pseudoIrreducible_of_map {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) (σ : A →+* A) (τ : B →+* B)
    (hfσ : ∀ a, f (σ a) = τ (f a)) {P : A[X]}
    (h : ∀ {β : B}, β ≠ 0 → ∀ {S R : B[X]}, C β * P.map f = oreMul τ S R →
      R.natDegree = 0 ∨ R.natDegree = (P.map f).natDegree) :
    ∀ {β : A}, β ≠ 0 → ∀ {S R : A[X]}, C β * P = oreMul σ S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree := by
  intro β hβ S R hSR
  have hmap := congrArg (Polynomial.map f) hSR
  rw [Polynomial.map_mul, map_C, map_oreMul f σ τ hfσ] at hmap
  have hβ' : f β ≠ 0 := (map_ne_zero_iff f hf).2 hβ
  rw [← natDegree_map_eq_of_injective hf R, ← natDegree_map_eq_of_injective hf P]
  exact h hβ' hmap

end AJConjecture
