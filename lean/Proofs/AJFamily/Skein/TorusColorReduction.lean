import Mathlib
import AJConjecture.ColoredJones
import AJFamily.Quantum.TorusFormula

/-!
# Reduction to positive colours

If the coloured Jones function of `K` agrees with `torusWhiteheadFormula a` at every positive
colour, it agrees at every integer colour: both sides are odd in the colour.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem laurentToField_coloredJones_of_pos_torus (K : BraidKnot) (a : ℕ)
    (h : ∀ k : ℕ, laurentToField (coloredJonesPos K k) = torusWhiteheadFormula a ((k : ℤ) + 1))
    (n : ℤ) : laurentToField (coloredJones K n) = torusWhiteheadFormula a n := by
  unfold coloredJones
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have h1 : ((n.toNat - 1 : ℕ) : ℤ) + 1 = n := by omega
    simp only [hn, ite_true]
    rw [h, h1]
  · subst hn
    simp [torusWhiteheadFormula]
  · have hn' : ¬ (0 : ℤ) < n := by omega
    have hpos : (0 : ℤ) < -n := by omega
    have h1 : (((-n).toNat - 1 : ℕ) : ℤ) + 1 = -n := by omega
    simp only [hn', hn, ite_false, ite_true]
    rw [map_neg, h, h1]
    simp only [torusWhiteheadFormula, hpos, hn', hn, ite_true, ite_false, neg_neg]

end AJConjecture
