import Mathlib
import AJConjecture.QAlgIntFibre
import AJConjecture.QAlgWeylSymbol

/-!
# Basic properties of the fibre

Evaluation at `(m, l)` is evaluation of the fibre at `l`; the coefficients of the fibre are the
values at `m` of the coefficients; the fibre is multiplicative and commutes with `∂/∂L`; the
fibre of `∂p/∂M` has the values of the derivatives of the coefficients as coefficients.
-/

open Polynomial

namespace AJConjecture

/-- The value at a complex point is the value of the fibre. -/
theorem evalIntPoint_eq_eval_intFibre (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l = (intFibre p m).eval l := by
  unfold evalIntPoint evalPoint intFibre
  rw [eval₂_map, eval_map]
  congr 1
  ext c
  · simp
  · simp

/-- The fibre commutes with the derivative in `L`. -/
theorem intFibre_derivative (p : ℤ[X][X]) (m : ℂ) :
    intFibre (derivative p) m = derivative (intFibre p m) := by
  rw [intFibre, intFibre, derivative_map]

end AJConjecture
