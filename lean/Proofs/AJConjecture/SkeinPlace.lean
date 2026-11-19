import Mathlib
import AJConjecture.SkeinMat

/-!
# Local operators, cups and caps

`skPlace n n' i A` is the matrix `1_i ⊗ A ⊗ 1_r` from `V^{⊗ n}` to `V^{⊗ n'}`, for a matrix `A`
from `k` to `l` factors placed at the position `i`; it is meaningful when `n = i + k + r` and
`n' = i + l + r`, and it is `0` otherwise. The ambient sizes `n`, `n'` are free parameters and the
index maps are written with `<`, so that compositions never need a cast.

Cups and caps are the rectangular matrices with `e = cap * cup` entrywise:
`cap(F,T) = 1`, `cap(T,F) = -t⁻²`, `cup(F,T) = -t²`, `cup(T,F) = 1`. The thick cup `cupThick c`
is `c` nested cups (the factor `x` is paired with the factor `2c - 1 - x`); it turns a bundle of
`c` strands around.
-/

noncomputable section

namespace AJConjecture

/-- Entries of the cap `V ⊗ V → ℚ(t)`: `cap(F,T) = 1`, `cap(T,F) = -t⁻²`. -/
def capEntry (a b : Bool) : RatFunc ℚ :=
  match a, b with
  | false, true => 1
  | true, false => -(RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ)
  | _, _ => 0

/-- Entries of the cup `ℚ(t) → V ⊗ V`: `cup(F,T) = -t²`, `cup(T,F) = 1`. -/
def cupEntry (a b : Bool) : RatFunc ℚ :=
  match a, b with
  | false, true => -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)
  | true, false => 1
  | _, _ => 0

/-- The matrix `1_i ⊗ A ⊗ 1_r` from `V^{⊗ n}` to `V^{⊗ n'}`: the states agree on the first `i`
factors and on the last `r` factors, and `A` acts on the `k` factors in between. It is `0`
unless `i + k ≤ n` and `n + l = n' + k`. -/
def skPlace (n n' i : ℕ) {k l : ℕ} (A : SkMat k l) : SkMat n n' :=
  Matrix.of fun a b ↦
    if h : i + k ≤ n ∧ n + l = n' + k then
      if (∀ x : Fin n, (hx : (x : ℕ) < i) → a x = b ⟨x, by omega⟩) ∧
          (∀ x : Fin n, (hx : i + k ≤ (x : ℕ)) → a x = b ⟨x + l - k, by omega⟩) then
        A (fun x ↦ a ⟨i + x, by omega⟩) (fun y ↦ b ⟨i + y, by omega⟩)
      else 0
    else 0

/-- The cup, from `0` to `2` strands. -/
def skCup : SkMat 0 2 :=
  Matrix.of fun _ b ↦ cupEntry (b 0) (b 1)

/-- The cap, from `2` to `0` strands. -/
def skCap : SkMat 2 0 :=
  Matrix.of fun a _ ↦ capEntry (a 0) (a 1)

/-- A cup inserted at the position `i` of `n` strands. -/
def cupAt (n i : ℕ) : SkMat n (n + 2) :=
  skPlace n (n + 2) i skCup

/-- A cap on the strands `i`, `i + 1` of `n + 2` strands. -/
def capAt (n i : ℕ) : SkMat (n + 2) n :=
  skPlace (n + 2) n i skCap

/-- The thick cup: `c` nested cups, pairing the factor `x` with the factor `2c - 1 - x`. -/
def cupThick (c : ℕ) : SkMat 0 (2 * c) :=
  Matrix.of fun _ b ↦ ∏ x : Fin c, cupEntry (b ⟨x, by omega⟩) (b ⟨2 * c - 1 - x, by omega⟩)

/-- The thick cap: `c` nested caps, pairing the factor `x` with the factor `2c - 1 - x`. -/
def capThick (c : ℕ) : SkMat (2 * c) 0 :=
  Matrix.of fun a _ ↦ ∏ x : Fin c, capEntry (a ⟨x, by omega⟩) (a ⟨2 * c - 1 - x, by omega⟩)

end AJConjecture
