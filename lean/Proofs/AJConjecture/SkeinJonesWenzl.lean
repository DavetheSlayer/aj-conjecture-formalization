import Mathlib
import AJConjecture.SkeinMat

/-!
# The Jones–Wenzl projector

`jwAt n i k` is the Jones–Wenzl projector `f_k` on the tensor factors `i, …, i + k - 1` of
`V^{⊗ n}`, defined by Wenzl's recursion inside the ring of operators on `V^{⊗ n}`:
`f_{k+2} = f_{k+1} + ([k+1]/[k+2]) f_{k+1} e_{i+k} f_{k+1}` (this is
`f_{k+1} ⊗ 1 - (Δ_k/Δ_{k+1}) (f_{k+1} ⊗ 1) e (f_{k+1} ⊗ 1)`). Because `e_j = 0` when it does not
fit, the recursion stops by itself at the border of the ambient space.
-/

noncomputable section

namespace AJConjecture

/-- The Jones–Wenzl projector `f_k` on the factors `i, …, i + k - 1` of `V^{⊗ n}`. -/
def jwAt (n i : ℕ) : ℕ → SkMat n n
  | 0 => 1
  | 1 => 1
  | (k + 2) => jwAt n i (k + 1) + (quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2)) •
      (jwAt n i (k + 1) * tlGenF n (i + k) * jwAt n i (k + 1))

end AJConjecture
