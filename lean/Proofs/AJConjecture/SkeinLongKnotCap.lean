import Mathlib
import AJConjecture.SkeinKnotTraceBasic
import AJConjecture.SkeinLapTraceStep
import AJConjecture.SkeinTracePairing

/-!
# The long knot is natural with respect to caps

`Tr_{K,k+2}(capAt * G) = Tr_{K,k}(G * capAt)` for every matrix `G`: a cap on two adjacent strands
of the cable can be pushed once around the knot. With `m` the number of strands, the lap trace
`lapTrace K k j G ℓ ((k + 2) m - 2 (ℓ + 1))` is the left-hand side for `ℓ = 0`
(`AJConjecture.lapTrace_zero`), does not change from `ℓ` to `ℓ + 1 < m`
(`AJConjecture.lapTrace_succ`, induction on `ℓ`), and is the right-hand side for `ℓ = m - 1`
(`AJConjecture.lapTrace_last`).

The operator form `capAt * Λ_K(k) = Λ_K(k+2) * capAt` follows: by
`AJConjecture.knotTrace_eq_qtr_longKnotOp` and the cyclicity of the trace
(`AJConjecture.qtr_mul_comm_of_weight` with `AJConjecture.skWeight_mul_capAt`) the two sides have
the same trace pairing with every `G`, and the pairing is non-degenerate
(`AJConjecture.eq_of_forall_qtr_mul_eq`).
-/

namespace AJConjecture

/-- As long as the cap has not come back to the column `0`, the lap trace is the knot trace of
`capAt k j * G` on the `(k + 2)`-cable. -/
private theorem lapTrace_eq_knotTrace_capAt_mul (K : BraidKnot) (k j : ℕ) (hj : j ≤ k)
    (G : SkMat k (k + 2)) (ℓ : ℕ) :
    ∀ M : ℕ, ℓ < K.strands → M + 2 * (ℓ + 1) = (k + 2) * K.strands →
      lapTrace K k j G ℓ M = knotTrace K (k + 2) (capAt k j * G) := by
  induction ℓ with
  | zero => exact fun M _ hM ↦ lapTrace_zero K k j G M hj (by omega)
  | succ ℓ ih =>
    intro M hℓ hM
    rw [← lapTrace_succ K k j G ℓ M hj hℓ hM]
    exact ih (M + 2) (by omega) (by omega)

/-- The knot trace is a trace on the Temperley–Lieb category: a cap moves around the knot. -/
theorem knotTrace_capAt_mul (K : BraidKnot) (k j : ℕ) (hj : j ≤ k) (G : SkMat k (k + 2)) :
    knotTrace K (k + 2) (capAt k j * G) = knotTrace K k (G * capAt k j) := by
  obtain ⟨r, hr⟩ : ∃ r, r + 1 = K.strands := ⟨K.strands - 1, by have := K.strands_pos; omega⟩
  rw [← lapTrace_eq_knotTrace_capAt_mul K k j hj G r (k * K.strands) (by omega)
    (by rw [hr]; ring)]
  exact lapTrace_last K k j G r (k * K.strands) hj hr rfl

/-- The long knot is natural with respect to caps. -/
theorem capAt_mul_longKnotOp (K : BraidKnot) (k j : ℕ) (hj : j ≤ k) :
    capAt k j * longKnotOp K k = longKnotOp K (k + 2) * capAt k j := by
  refine eq_of_forall_qtr_mul_eq (k + 2) k _ _ fun G ↦ ?_
  rw [Matrix.mul_assoc, qtr_mul_comm_of_weight (k + 2) k (capAt k j) (longKnotOp K k * G)
    (skWeight_mul_capAt k j), Matrix.mul_assoc, ← knotTrace_eq_qtr_longKnotOp,
    Matrix.mul_assoc, ← knotTrace_eq_qtr_longKnotOp, knotTrace_capAt_mul K k j hj G]

end AJConjecture
