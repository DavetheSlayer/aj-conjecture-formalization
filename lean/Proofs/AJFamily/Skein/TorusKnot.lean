import Mathlib
import AJConjecture.BraidKnot

/-!
# The torus knots `T(2, 2k+1)`

`torusWord k = σ_0^(2k+1)` and its closure `torusKnot k` on two strands, the companions of the
family.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The braid word `σ_0^(2k+1)` of the right-handed torus knot `T(2, 2k+1)`. -/
def torusWord (k : ℕ) : BraidWord :=
  List.replicate (2 * k + 1) (0, true)

theorem isOnStrands_torusWord (k : ℕ) : IsOnStrands 2 (torusWord k) := by
  intro g hg
  rw [torusWord, List.mem_replicate] at hg
  rw [hg.2]
  norm_num

theorem connected_torusWord (k : ℕ) (i j : Fin 2) :
    ∃ n : ℕ, (strandPerm 2 (torusWord k) ^ n) i = j := by
  have hswap : strandSwap 2 0 = Equiv.swap (0 : Fin 2) 1 := by
    simp [strandSwap]
  have hperm : strandPerm 2 (torusWord k) = Equiv.swap (0 : Fin 2) 1 := by
    rw [strandPerm, torusWord, List.map_replicate, List.prod_replicate, hswap, pow_succ,
      pow_mul, sq, Equiv.swap_mul_self, one_pow, one_mul]
  by_cases hij : i = j
  · exact ⟨0, by rw [pow_zero, hij]; rfl⟩
  · refine ⟨1, ?_⟩
    rw [pow_one, hperm]
    fin_cases i <;> fin_cases j <;> simp_all

/-- The right-handed torus knot `T(2, 2k+1)`, the closure of `σ_0^(2k+1)` on two strands. -/
def torusKnot (k : ℕ) : BraidKnot where
  strands := 2
  word := torusWord k
  strands_pos := by norm_num
  isOnStrands := isOnStrands_torusWord k
  connected := connected_torusWord k

end AJConjecture
