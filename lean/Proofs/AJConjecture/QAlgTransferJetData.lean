import Mathlib

/-!
# Lucas sequences and their derivatives

Over a commutative ring: the Lucas sequence `S_0 = 2`, `S_1 = z`, `S_(d+2) = z S_(d+1) - s S_d`
(`transferLucas`), its derivative `∂_z S_d` (`transferLucasDeriv`) and half its second derivative
`½ ∂_z² S_d` (`transferLucasHasse`), defined by the differentiated recursions, and the polynomial
`transferJetZetaDeriv`.
-/

noncomputable section

namespace AJConjecture

/-- `q^15 x - q^16 - q x (1 + x) + 2 q² x j`, the derivative in `j` of
`x² + q^15 (1 + x) + (q^15 x - q^16 - q x (1 + x)) j + q² x j²`. -/
def transferJetZetaDeriv {R : Type*} [CommRing R] (q x j : R) : R :=
  q ^ 15 * x - q ^ 16 - q * x * (1 + x) + 2 * (q ^ 2 * x * j)

/-- The Lucas sequence `S_0 = 2`, `S_1 = z`, `S_(d+2) = z S_(d+1) - s S_d`. -/
def transferLucas {R : Type*} [CommRing R] (z s : R) : ℕ → R
  | 0 => 2
  | 1 => z
  | d + 2 => z * transferLucas z s (d + 1) - s * transferLucas z s d

/-- The derivative in `z` of the Lucas sequence: `S_0' = 0`, `S_1' = 1`,
`S_(d+2)' = S_(d+1) + z S_(d+1)' - s S_d'`. -/
def transferLucasDeriv {R : Type*} [CommRing R] (z s : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | d + 2 => transferLucas z s (d + 1) + z * transferLucasDeriv z s (d + 1) -
      s * transferLucasDeriv z s d

/-- Half the second derivative in `z` of the Lucas sequence: `H_0 = H_1 = 0`,
`H_(d+2) = S_(d+1)' + z H_(d+1) - s H_d`. -/
def transferLucasHasse {R : Type*} [CommRing R] (z s : R) : ℕ → R
  | 0 => 0
  | 1 => 0
  | d + 2 => transferLucasDeriv z s (d + 1) + z * transferLucasHasse z s (d + 1) -
      s * transferLucasHasse z s d

end AJConjecture
