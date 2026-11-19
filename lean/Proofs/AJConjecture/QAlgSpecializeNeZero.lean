import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# Operators with vanishing specialisation

`specialize P = 0` exactly when `t + 1` divides `P`; in particular a primitive operator has a
nonzero specialisation.
-/

open Polynomial

namespace AJConjecture

/-- The specialisation at `t = -1` vanishes exactly on the multiples of `t + 1`. -/
theorem specialize_eq_zero_iff_dvd (P : RecOp) :
    specialize P = 0 ↔ C (C (X + 1 : ℤ[X])) ∣ P := by
  have hX : (X + 1 : ℤ[X]) = X - C (-1) := by
    rw [map_neg, sub_neg_eq_add, map_one]
  simp only [Polynomial.C_dvd_iff_dvd_coeff, hX, Polynomial.dvd_iff_isRoot, IsRoot.def]
  constructor
  · intro h i j
    have h1 := congrArg (fun p : ℤ[X][X] ↦ (p.coeff i).coeff j) h
    simpa [specialize] using h1
  · intro h
    ext i j
    simpa [specialize] using h i j

/-- A primitive operator has a nonzero specialisation at `t = -1`. -/
theorem specialize_ne_zero_of_isPrimitive {Q : RecOp} (hQ : Q.IsPrimitive) :
    specialize Q ≠ 0 := by
  intro h
  have hu : IsUnit (C (X + 1 : ℤ[X])) := hQ _ ((specialize_eq_zero_iff_dvd Q).mp h)
  rw [Polynomial.isUnit_C] at hu
  have hX : (X + 1 : ℤ[X]) = X - C (-1) := by
    rw [map_neg, sub_neg_eq_add, map_one]
  rw [hX] at hu
  exact Polynomial.not_isUnit_X_sub_C _ hu

end AJConjecture
