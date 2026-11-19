import Mathlib
import AJConjecture.SkeinMat

/-!
# The partial quantum trace

`ptrTail k n A` closes the tensor factors at the positions `≥ k` of an operator on `V^{⊗ n}`
with the weight of the quantum trace; the result is an operator on `V^{⊗ k}`. Only this right
closure is used: the left closure of a factor carries the inverse weight and is avoided by
conjugating with braids.
-/

noncomputable section

namespace AJConjecture

/-- The partial quantum trace over the tensor factors at the positions `≥ k`:
`(ptrTail k n A) a b = ∑_s μ(s) A (a, s) (b, s)`. -/
def ptrTail (k n : ℕ) (A : SkMat n n) : SkMat k k :=
  Matrix.of fun a b ↦ ∑ s : Fin (n - k) → Bool, (∏ x, skWeightEntry (s x)) *
    A (fun j ↦ if h : (j : ℕ) < k then a ⟨j, h⟩ else s ⟨j - k, by omega⟩)
      (fun j ↦ if h : (j : ℕ) < k then b ⟨j, h⟩ else s ⟨j - k, by omega⟩)

end AJConjecture
