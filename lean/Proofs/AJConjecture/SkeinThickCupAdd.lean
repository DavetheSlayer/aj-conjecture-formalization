import Mathlib
import AJConjecture.SkeinThickCupInner

/-!
# Nests of caps and cups compose

The thick cap on one strand is the cap, and a nest of `a + b` caps is the nest of the `b` inner
caps followed by the nest of the `a` outer caps; symmetrically for cups. Induction on `b` with
`AJConjecture.capThick_succ_inner` (innermost cap first), `AJConjecture.skPlace_mul` and
`AJConjecture.skPlace_skPlace`; or entrywise, splitting the product of `a + b` cap entries.
-/

namespace AJConjecture

/-- The thick cap on one strand is the cap. -/
theorem capThick_one : capThick 1 = skCap := by
  ext a b
  simp only [capThick, skCap, Matrix.of_apply, Fin.prod_univ_succ, Fin.val_zero,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rfl

/-- A nest of `a + b` caps: the `b` inner caps, then the `a` outer caps. -/
theorem capThick_add (a b : ℕ) :
    capThick (a + b) = skPlace (2 * (a + b)) (2 * a) a (capThick b) * capThick a := by
  induction b with
  | zero =>
    have h : skPlace (2 * (a + 0)) (2 * a) a (capThick 0) = 1 := by
      rw [capThick_zero]
      exact skPlace_one (2 * a) a 0 (by omega)
    rw [h]
    exact (Matrix.one_mul (capThick a)).symm
  | succ b ih =>
    have h1 : capThick (a + (b + 1)) =
        skPlace (2 * (a + (b + 1))) (2 * (a + b)) (a + b) skCap * capThick (a + b) :=
      capThick_succ_inner (a + b)
    rw [h1, ih, capThick_succ_inner b,
      skPlace_mul (2 * (a + (b + 1))) (2 * (a + b)) (2 * a) a _ (capThick b) (by omega) (by omega)
        (by omega),
      skPlace_skPlace (2 * (a + (b + 1))) (2 * (a + b)) a b skCap (by omega) (by omega) (by omega)
        (by omega), Matrix.mul_assoc]

/-- A nest of `a + b` cups: the `a` outer cups, then the `b` inner cups. -/
theorem cupThick_add (a b : ℕ) :
    cupThick (a + b) = cupThick a * skPlace (2 * a) (2 * (a + b)) a (cupThick b) := by
  induction b with
  | zero =>
    have h : skPlace (2 * a) (2 * (a + 0)) a (cupThick 0) = 1 := by
      rw [cupThick_zero]
      exact skPlace_one (2 * a) a 0 (by omega)
    rw [h]
    exact (Matrix.mul_one (cupThick a)).symm
  | succ b ih =>
    have h1 : cupThick (a + (b + 1)) =
        cupThick (a + b) * skPlace (2 * (a + b)) (2 * (a + (b + 1))) (a + b) skCup :=
      cupThick_succ_inner (a + b)
    rw [h1, ih, cupThick_succ_inner b,
      skPlace_mul (2 * a) (2 * (a + b)) (2 * (a + (b + 1))) a (cupThick b) _ (by omega) (by omega)
        (by omega),
      skPlace_skPlace (2 * (a + b)) (2 * (a + (b + 1))) a b skCup (by omega) (by omega) (by omega)
        (by omega), Matrix.mul_assoc]

end AJConjecture
