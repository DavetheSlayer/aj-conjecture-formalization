import Mathlib
import AJConjecture.KauffmanBracket

/-!
# The coloured Jones function

The unreduced coloured Jones polynomial in the convention of Lê–Tran: for a zero-framed knot
`K` and a colour (dimension) `n ≥ 1`, `J_K(n) = (-1)^(n-1) ⟨K(S_{n-1})⟩`, the Kauffman bracket
of `K` cabled by the Chebyshev polynomial `S_{n-1}`. Then `J_unknot(n) = [n]` and `J_K(1) = 1`.
The function is extended to all integers by `J_K(0) = 0` and `J_K(-n) = -J_K(n)`.
-/

open LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The blackboard `c`-parallel of a braid generator: the `c` strands replacing strand `i`
cross the `c` strands replacing strand `i + 1`, all with the sign of the original crossing. -/
def cableGen (c : ℕ) (g : ℕ × Bool) : BraidWord :=
  if g.2 then
    (List.range c).reverse.flatMap fun a ↦ (List.range c).map fun b ↦ (c * g.1 + a + b, true)
  else
    (List.range c).flatMap fun a ↦ (List.range c).reverse.map fun b ↦ (c * g.1 + a + b, false)

/-- The blackboard `c`-parallel of a braid word (a braid word on `c * m` strands). -/
def cable (c : ℕ) (w : BraidWord) : BraidWord :=
  w.flatMap (cableGen c)

/-- The writhe of the closed braid diagram: the sum of the signs of its crossings. -/
def writhe (w : BraidWord) : ℤ :=
  (w.map fun g ↦ if g.2 then (1 : ℤ) else -1).sum

/-- The bracket of the closed braid cabled (with the blackboard framing) by the Chebyshev
polynomial `S_k(z) = ∑_j (-1)^j (k-j choose j) z^(k-2j)`. -/
def chebyshevBracket (m : ℕ) (w : BraidWord) (k : ℕ) : ℤ[T;T⁻¹] :=
  ∑ j ∈ Finset.range (k / 2 + 1),
    ((-1 : ℤ) ^ j * ((k - j).choose j : ℤ)) • bracket ((k - 2 * j) * m) (cable (k - 2 * j) w)

/-- The unreduced coloured Jones polynomial of the zero-framed knot at the positive colour
(dimension) `k + 1`: `(-1)^k ⟨K(S_k)⟩`. The zero-framed cabling is obtained from the blackboard
one through the twist factor `((-1)^k t^((k+1)²-1))^(-writhe)`. -/
def coloredJonesPos (K : BraidKnot) (k : ℕ) : ℤ[T;T⁻¹] :=
  ((-1 : ℤ) ^ (k * (1 + (writhe K.word).natAbs))) •
    (T (-(writhe K.word) * (((k : ℤ) + 1) ^ 2 - 1)) * chebyshevBracket K.strands K.word k)

/-- The coloured Jones function on all integers: `J(0) = 0` and `J(-n) = -J(n)`. -/
def coloredJones (K : BraidKnot) (n : ℤ) : ℤ[T;T⁻¹] :=
  if 0 < n then coloredJonesPos K (n.toNat - 1)
  else if n < 0 then -coloredJonesPos K ((-n).toNat - 1)
  else 0

end AJConjecture
