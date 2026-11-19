import Mathlib
import AJConjecture.SkeinThickCup

/-!
# Thick cups and caps, innermost strand first

The thick cap on `k + 1` strands is the innermost cap (on the two middle strands) followed by
the thick cap on `k` strands, and the thick cup on `k + 1` strands is the thick cup on `k`
strands followed by the innermost cup. Entrywise: the product of the `k + 1` cap entries is split
at the index `x = k`, and the sum over the intermediate states has one non-zero term
(`AJConjecture.skPlace_append_apply`). `AJConjecture.capThick_succ` is the decomposition with the
outermost cap last.
-/

namespace AJConjecture

/-- A placed thick cup on `c + 1` strands: the thick cup on `c` strands, then the innermost
cup. -/
private theorem skPlace_cupThick_succ_inner_thickCupInner (c : ℕ) :
    ∀ m n' i : ℕ, i ≤ n' → n' + 2 * c = m →
      skPlace n' (m + 2) i (cupThick (c + 1)) = skPlace n' m i (cupThick c) * cupAt m (i + c) := by
  induction c with
  | zero =>
    intro m n' i h h'
    obtain rfl : n' = m := by omega
    rw [skPlace_cupThick_succ n' (n' + 2) i 0 (by omega) (by omega),
      cupThick_zero, skPlace_one (n' + 2) (i + 1) 0 (by omega),
      skPlace_one n' i 0 (by omega), Matrix.one_mul, Matrix.mul_one]
    rfl
  | succ c ih =>
    intro m n' i h h'
    rw [skPlace_cupThick_succ n' (m + 2) i (c + 1) (by omega) (by omega),
      ih m (n' + 2) (i + 1) (by omega) (by omega), ← Matrix.mul_assoc,
      ← skPlace_cupThick_succ n' m i c (by omega) (by omega),
      Nat.add_right_comm i 1 c, Nat.add_assoc i c 1]

/-- The thick cap on `k + 1` strands: the innermost cap, then the thick cap on `k` strands. -/
theorem capThick_succ_inner (k : ℕ) :
    capThick (k + 1) = skPlace (2 * (k + 1)) (2 * k) k skCap * capThick k := by
  have h := skPlace_capThick_succ_inner k (2 * k) 0 0 (by omega) (by omega)
  rw [skPlace_self, skPlace_self, Nat.zero_add] at h
  exact h

/-- The thick cup on `k + 1` strands: the thick cup on `k` strands, then the innermost cup. -/
theorem cupThick_succ_inner (k : ℕ) :
    cupThick (k + 1) = cupThick k * skPlace (2 * k) (2 * (k + 1)) k skCup := by
  have h := skPlace_cupThick_succ_inner_thickCupInner k (2 * k) 0 0 (by omega) (by omega)
  rw [skPlace_self, skPlace_self, Nat.zero_add] at h
  exact h

end AJConjecture
