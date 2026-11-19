import Mathlib
import AJHandoff.TorusKnot.PairKAnnArith
import AJHandoff.TorusKnot.PairKAnnHurwitz
import AJHandoff.TorusKnot.PairKAnnForm

/-!
# The Hurwitz elements in the frame of a top level

`pairAnnHur_eq_top`: `R'_p = Π^w y_0 Π^(-w)` with `w = W(T_t) - W_0` whenever `p ≡ t - 1 (mod s)`
(`pairAnn_congr`, `pairAnnW_zero`, `pairAnnHur_eq_conj`). This is the form in which the transition
lemmas of `AJHandoff.TorusKnot.PairKAnnClosedLow`, `…ClosedTop` and `…Ends` use the torus
relation.
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- `R'_p` in the frame of the top level `T_t`, for `p ≡ t - 1 (mod s)`. -/
theorem pairAnnHur_eq_top (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (t p : ℕ) (hp : (p : ℤ) ≡ (t : ℤ) - 1 [ZMOD s]) :
    pairAnnHur r y p = pairAnnPi r y ^ (pairAnnTopW r s t - pairAnnW r s 0) * y 0 *
      (pairAnnPi r y ^ (pairAnnTopW r s t - pairAnnW r s 0))⁻¹ := by
  refine pairAnnHur_eq_conj h y hy _ p ?_
  rw [pairAnnW_zero h]
  exact (pairAnn_congr h t).trans hp.symm

end AJConjecture
