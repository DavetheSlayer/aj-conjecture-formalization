import Mathlib
import AJConjecture.KauffmanBracket
import AJConjecture.WhiteheadFormula

/-!
# Field-valued matrices on `V^{⊗ m}`

The skein layer works with matrices over `ℚ(t)` indexed by the states `Fin m → Bool` of
`V^{⊗ m}`, exactly as `AJConjecture.bracket` does over `ℤ[t, t⁻¹]`. A matrix `A : SkMat m n` is
read as a morphism from `m` strands to `n` strands, and `A * B` is "first `A`, then `B`" (the
row index is the input state), which is the order of the letters of a braid word in
`AJConjecture.bracket`. All sizes are free natural-number parameters: an operator that does not
fit into its ambient space is `0`, as `AJConjecture.tlGen` already is, so that no cast between
`Fin` types ever appears in a statement.
-/

noncomputable section

namespace AJConjecture

/-- Matrices from `V^{⊗ m}` to `V^{⊗ n}` over `ℚ(t)`: morphisms from `m` strands to `n`
strands. -/
abbrev SkMat (m n : ℕ) : Type := Matrix (Fin m → Bool) (Fin n → Bool) (RatFunc ℚ)

/-- The weight of one tensor factor in the quantum trace: `-t²` on `e_false`, `-t⁻²` on
`e_true`. -/
def skWeightEntry (b : Bool) : RatFunc ℚ :=
  if b then -(RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)

/-- The weight `μ^{⊗ m}` of the quantum trace on `V^{⊗ m}`. -/
def skWeight (m : ℕ) : SkMat m m :=
  Matrix.diagonal fun a ↦ ∏ k, skWeightEntry (a k)

/-- The quantum trace `qtr_m(A) = tr(μ^{⊗ m} A)`: the closure of all `m` strands. -/
def qtr (m : ℕ) (A : SkMat m m) : RatFunc ℚ :=
  Matrix.trace (skWeight m * A)

/-- The Temperley–Lieb generator `e_i` on `V^{⊗ m}` over `ℚ(t)` (zero unless `i + 1 < m`). -/
def tlGenF (m i : ℕ) : SkMat m m :=
  (tlGen m i).map laurentToField

/-- The matrix of a braid generator over `ℚ(t)`. -/
def crossingF (m : ℕ) (g : ℕ × Bool) : SkMat m m :=
  (crossingMatrix m g).map laurentToField

/-- The matrix `ρ_m(w)` of a braid word on `V^{⊗ m}`: the product of the matrices of its letters,
in the order of the word. -/
def braidMatrix (m : ℕ) (w : BraidWord) : SkMat m m :=
  (w.map (crossingF m)).prod

end AJConjecture
