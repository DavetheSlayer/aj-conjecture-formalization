import Mathlib
import AJConjecture.BraidKnot

/-!
# The Kauffman bracket of a closed braid

The bracket is computed in the tensor representation of the Temperley–Lieb algebra on
`V^{⊗ m}`, `V = ⟨e_false, e_true⟩`: a positive crossing acts by `t • 1 + t⁻¹ • e_i`, and the
closure is the quantum trace with weight `diag(-t², -t⁻²)` on each factor. The normalisation is
`⟨∅⟩ = 1`, `⟨unknot⟩ = -t² - t⁻²`.
-/

open LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- Entries of the Temperley–Lieb generator ("cup followed by cap") on `V ⊗ V`, where `V` has
the basis `e_false`, `e_true`: it is supported on `e_false ⊗ e_true`, `e_true ⊗ e_false`. -/
def cupCapEntry (a₀ a₁ b₀ b₁ : Bool) : ℤ[T;T⁻¹] :=
  match a₀, a₁, b₀, b₁ with
  | false, true, false, true => -T 2
  | false, true, true, false => 1
  | true, false, false, true => 1
  | true, false, true, false => -T (-2)
  | _, _, _, _ => 0

/-- The Temperley–Lieb generator `e_i` acting on the tensor factors `i`, `i + 1` of `V^{⊗ m}`. -/
def tlGen (m i : ℕ) : Matrix (Fin m → Bool) (Fin m → Bool) ℤ[T;T⁻¹] :=
  Matrix.of fun a b ↦
    if h : i + 1 < m then
      if ∀ k : Fin m, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → a k = b k then
        cupCapEntry (a ⟨i, Nat.lt_of_succ_lt h⟩) (a ⟨i + 1, h⟩)
          (b ⟨i, Nat.lt_of_succ_lt h⟩) (b ⟨i + 1, h⟩)
      else 0
    else 0

/-- Kauffman's skein relation for a braid generator: a positive crossing is `t • 1 + t⁻¹ • e_i`,
a negative crossing is `t⁻¹ • 1 + t • e_i`. -/
def crossingMatrix (m : ℕ) (g : ℕ × Bool) : Matrix (Fin m → Bool) (Fin m → Bool) ℤ[T;T⁻¹] :=
  if g.2 then (T 1 : ℤ[T;T⁻¹]) • 1 + (T (-1) : ℤ[T;T⁻¹]) • tlGen m g.1
  else (T (-1) : ℤ[T;T⁻¹]) • 1 + (T 1 : ℤ[T;T⁻¹]) • tlGen m g.1

/-- The Kauffman bracket of the closure of a braid word on `m` strands, normalised by
`⟨∅⟩ = 1` and `⟨unknot⟩ = -t² - t⁻²`, computed as a quantum trace on `V^{⊗ m}`. -/
def bracket (m : ℕ) (w : BraidWord) : ℤ[T;T⁻¹] :=
  Matrix.trace
    (Matrix.diagonal (fun a : Fin m → Bool ↦ ∏ k, if a k then -T (-2) else -T 2) *
      (w.map (crossingMatrix m)).prod)

end AJConjecture
