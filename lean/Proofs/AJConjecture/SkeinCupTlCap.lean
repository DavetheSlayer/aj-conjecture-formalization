import Mathlib
import AJConjecture.SkeinCupAtComm
import AJConjecture.SkeinZigzag

/-!
# A generator between a cup and a cap

Three planar isotopies used in the bubble lemma. With `e = capAt * cupAt`
(`AJConjecture.capAt_mul_cupAt`): a generator that shares one strand with a cup below it and a
cap above it is two zig-zags (`AJConjecture.cupAt_mul_capAt_succ`,
`AJConjecture.cupAt_succ_mul_capAt`), hence the identity; two generators, one on each side, give
after the far commutations of `AJConjecture.capAt_mul_tlGenF_of_lt` and its companions a cap
followed by a cup on the strands next to each other after the removal of the two middle
strands, that is the generator `e_i` on two strands fewer. The third statement needs no
hypothesis: both sides vanish when the generators do not fit.
-/

namespace AJConjecture

/-- A cup that does not fit is zero. -/
theorem cupAt_eq_zero (n i : ℕ) (h : n < i) : cupAt n i = 0 := by
  ext a b
  simp only [cupAt, skPlace, Matrix.of_apply, Matrix.zero_apply]
  split_ifs with h1
  · omega
  · rfl
  · rfl

/-- A generator on the right strand of a cup and of the cap above it is a straight strand. -/
theorem cupAt_mul_tlGenF_succ_mul_capAt (n i : ℕ) (h : i < n) :
    cupAt n i * tlGenF (n + 2) (i + 1) * capAt n i = 1 := by
  rw [← capAt_mul_cupAt n (i + 1) (Nat.succ_le_of_lt h), ← Matrix.mul_assoc,
    cupAt_mul_capAt_succ n i h, Matrix.one_mul, cupAt_succ_mul_capAt n i h]

/-- A generator on the left strand of a cup and of the cap above it is a straight strand. -/
theorem cupAt_succ_mul_tlGenF_mul_capAt_succ (n i : ℕ) (h : i < n) :
    cupAt n (i + 1) * tlGenF (n + 2) i * capAt n (i + 1) = 1 := by
  rw [← capAt_mul_cupAt n i h.le, ← Matrix.mul_assoc, cupAt_succ_mul_capAt n i h, Matrix.one_mul,
    cupAt_mul_capAt_succ n i h]

/-- Generators on both sides of a cup and of the cap above it: the generator on the two
neighbouring strands. -/
theorem cupAt_succ_mul_tlGenF_mul_tlGenF_mul_capAt_succ (n i : ℕ) :
    cupAt n (i + 1) * tlGenF (n + 2) i * tlGenF (n + 2) (i + 2) * capAt n (i + 1) = tlGenF n i := by
  rcases Nat.lt_or_ge i n with h | h
  · rw [← capAt_mul_cupAt n i h.le, ← Matrix.mul_assoc, cupAt_succ_mul_capAt n i h, Matrix.one_mul,
      ← tlGenF_mul_cupAt_of_le n i i le_rfl, Matrix.mul_assoc, cupAt_mul_capAt_succ n i h,
      Matrix.mul_one]
  · rw [cupAt_eq_zero n (i + 1) (by omega), tlGenF_eq_zero n i (by omega),
      Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]

end AJConjecture
