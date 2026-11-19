import Mathlib
import AJConjecture.QAlgSymbolCompact
import AJConjecture.QAlgSymbolPoly

/-!
# The twist polynomial

The twist polynomial `B_k = twistPoly k` in `ℤ[M][L]` and its `J`-form `symbolTwist k`, defined by
Chebyshev-type recursions. The `t = -1` symbol of `famTransferOp m` is `(L - 1) · E · B_m` up to
polynomials in `M`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `T̂_k = x^k T_k(Z, e)` in `ℤ[x][J]`: `T̂_0 = 1`, `T̂_1 = ζ + xJ - x² - 1`,
`T̂_(k+2) = ζ T̂_(k+1) - x² T̂_k`. -/
def symbolTwist : ℕ → ℤ[X][X]
  | 0 => 1
  | 1 => symbolZeta + C X * X - C (X ^ 2 + 1)
  | k + 2 => symbolZeta * symbolTwist (k + 1) - C (X ^ 2) * symbolTwist k

/-- `Ẑ = (L + x)² ζ(J)` written in `ℤ[M][L]` (`x = M²`). -/
def zetaMoebiusM : ℤ[X][X] :=
  symbolZetaMoebius.map (Polynomial.compRingHom (X ^ 2))

/-- The twist polynomial `B_k(M, L) = x^k (L + x)^(2k) T_k(Z, e)`, `x = M²`, by the recursion
`B_(k+2) = Ẑ B_(k+1) - x² (L + x)⁴ B_k`. -/
def twistPoly : ℕ → ℤ[X][X]
  | 0 => 1
  | 1 => zetaMoebiusM + C (X ^ 2) * (C (X ^ 2) * X + 1) * (C (X ^ 2) + X) -
      C (X ^ 4 + 1) * (C (X ^ 2) + X) ^ 2
  | k + 2 => zetaMoebiusM * twistPoly (k + 1) - C (X ^ 4) * (C (X ^ 2) + X) ^ 4 * twistPoly k

end AJConjecture
