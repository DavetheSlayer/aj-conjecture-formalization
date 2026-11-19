import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJHandoff.PairDefs
import AJConjecture.SkeinKnotTraceJwCols
import AJConjecture.SkeinBraidMatrixBasic

/-!
# The knot trace of `T(r, s)` as a trace of a power of the cyclic braid (node RA6.1)

`knotTrace (T(r,s)) b f_b = qtr(c^s f_b^{⊗ r})`, `c` the `b`-cable of `σ_0 ⋯ σ_(r-2)`.

Route. `knotTrace_jwAt_eq_qtr_cols` with the columns `1, …, r - 1` (`List.range' 1 (r - 1)`),
so that the projectors are those of all columns (`rjColsProj`, `List.range_succ_eq_map`); and
`cable b (torusPairWord r s)` is the concatenation of `s` copies of `cable b (rjCycleWord r)`
(`cable` is a `flatMap`, `List.flatMap_flatten`-type lemmas), whose matrix is `c^s`
(`braidMatrix_append`, induction on `s`). Estimate 50–90 lines.
-/

noncomputable section

namespace AJConjecture

/-- The cable of the `s`-th power of the cyclic word has the matrix `c^s`. -/
private theorem braidMatrix_cable_torusPairWord_knotTraceCycle (b r s : ℕ) :
    braidMatrix (b * r) (cable b (torusPairWord r s)) = rjCycleMat b r ^ s := by
  induction s with
  | zero => exact braidMatrix_nil _
  | succ s ih =>
    rw [torusPairWord, List.replicate_succ, List.flatten_cons, cable, List.flatMap_append,
      braidMatrix_append, ← cable, ← cable, ← torusPairWord, ih, pow_succ', rjCycleMat,
      rjCycleWord]

/-- The knot trace of the torus knot with the projector is a trace of `c^s`. -/
theorem rj_knotTrace_torusPairKnot (r s : ℕ) (h : IsTorusPair r s) (b : ℕ) :
    knotTrace (torusPairKnot r s h) b (jwAt b 0 b) =
      qtr (b * r) (rjCycleMat b r ^ s * rjColsProj b r) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by obtain ⟨hr, -⟩ := h; omega⟩
  rw [knotTrace_jwAt_eq_qtr_cols (torusPairKnot (r' + 1) s h) b (List.range' 1 r')
    (fun p hp ↦ by
      rw [List.mem_range'] at hp
      change p < r' + 1
      omega)]
  change qtr (b * (r' + 1)) (braidMatrix (b * (r' + 1)) (cable b (torusPairWord (r' + 1) s)) *
    _) = _
  rw [braidMatrix_cable_torusPairWord_knotTraceCycle, rjColsProj, List.range_eq_range',
    List.range'_succ, List.map_cons, List.prod_cons, mul_zero, zero_add]
  rfl

end AJConjecture
