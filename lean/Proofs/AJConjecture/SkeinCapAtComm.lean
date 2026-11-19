import Mathlib
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinPlaceComm
import AJConjecture.SkeinTlGenPlace

/-!
# A cap commutes with generators and braids on other strands

The interchange law for a cap and a Temperley–Lieb generator, or a braid word, whose strands
are all on the left of the cap (same indices before and after the cap) or all on its right
(indices shifted by `2`). The statements for generators are instances of
`AJConjecture.skPlace_mul_skPlace_comm` with `AJConjecture.tlGenF_eq_skPlace`; the statements for
words follow letter by letter with `σ_i^{±1} = t^{±1} + t^{∓1} e_i`. No hypothesis on the ambient
size is needed: both sides vanish when the cap does not fit, and the generators on both sides
vanish together.
-/

namespace AJConjecture

/-- A cap that does not fit is zero. -/
private theorem capAt_eq_zero_capAtComm (n i : ℕ) (h : n < i) : capAt n i = 0 := by
  ext a b
  simp only [capAt, skPlace, Matrix.of_apply, Matrix.zero_apply]
  split_ifs with h1
  · omega
  · rfl
  · rfl

/-- The matrix of a braid word with a first letter. -/
private theorem braidMatrix_cons_capAtComm (m : ℕ) (g : ℕ × Bool) (w : BraidWord) :
    braidMatrix m (g :: w) = crossingF m g * braidMatrix m w := by
  rw [braidMatrix, braidMatrix, List.map_cons, List.prod_cons]

/-- A generator on the left of a cap commutes with it. -/
theorem capAt_mul_tlGenF_of_lt (n i j : ℕ) (h : j + 1 < i) :
    capAt n i * tlGenF n j = tlGenF (n + 2) j * capAt n i := by
  rcases Nat.lt_or_ge n i with hi | hi
  · rw [capAt_eq_zero_capAtComm n i hi, Matrix.zero_mul, Matrix.mul_zero]
  · have key := skPlace_mul_skPlace_comm (n + 2) (n + 2) n n j i (tlGenF 2 0) skCap
      (by omega) (by omega) rfl rfl rfl
    rw [show i + 2 - 2 = i from by omega] at key
    rw [capAt, tlGenF_eq_skPlace n j, tlGenF_eq_skPlace (n + 2) j, key]

/-- A generator on the right of a cap commutes with it; its index is shifted by `2`. -/
theorem capAt_mul_tlGenF_of_le (n i j : ℕ) (h : i ≤ j) :
    capAt n i * tlGenF n j = tlGenF (n + 2) (j + 2) * capAt n i := by
  rcases Nat.lt_or_ge n (j + 2) with hj | hj
  · rw [tlGenF_eq_zero n j (by omega), tlGenF_eq_zero (n + 2) (j + 2) (by omega),
      Matrix.zero_mul, Matrix.mul_zero]
  · have key := skPlace_mul_skPlace_comm (n + 2) n (n + 2) n i (j + 2) skCap (tlGenF 2 0)
      (by omega) (by omega) rfl rfl rfl
    rw [show j + 2 + 0 - 2 = j from by omega] at key
    rw [capAt, tlGenF_eq_skPlace n j, tlGenF_eq_skPlace (n + 2) (j + 2), key]

/-- A crossing on the left of a cap commutes with it. -/
private theorem capAt_mul_crossingF_of_lt_capAtComm (n i j : ℕ) (s : Bool) (h : j + 1 < i) :
    capAt n i * crossingF n (j, s) = crossingF (n + 2) (j, s) * capAt n i := by
  cases s
  · rw [crossingF_neg, crossingF_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      capAt_mul_tlGenF_of_lt n i j h]
  · rw [crossingF_pos, crossingF_pos, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      capAt_mul_tlGenF_of_lt n i j h]

/-- A crossing on the right of a cap commutes with it; its index is shifted by `2`. -/
private theorem capAt_mul_crossingF_of_le_capAtComm (n i j : ℕ) (s : Bool) (h : i ≤ j) :
    capAt n i * crossingF n (j, s) = crossingF (n + 2) (j + 2, s) * capAt n i := by
  cases s
  · rw [crossingF_neg, crossingF_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      capAt_mul_tlGenF_of_le n i j h]
  · rw [crossingF_pos, crossingF_pos, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      capAt_mul_tlGenF_of_le n i j h]

/-- A braid word on the strands on the left of a cap commutes with it. -/
theorem capAt_mul_braidMatrix_of_lt (n i : ℕ) (w : BraidWord) (h : ∀ g ∈ w, g.1 + 1 < i) :
    capAt n i * braidMatrix n w = braidMatrix (n + 2) w * capAt n i := by
  induction w with
  | nil => rw [braidMatrix_nil, braidMatrix_nil, Matrix.mul_one, Matrix.one_mul]
  | cons g w ih =>
    rw [braidMatrix_cons_capAtComm, braidMatrix_cons_capAtComm, ← Matrix.mul_assoc,
      capAt_mul_crossingF_of_lt_capAtComm n i g.1 g.2 (h g List.mem_cons_self), Matrix.mul_assoc,
      ih fun x hx ↦ h x (List.mem_cons_of_mem g hx), Matrix.mul_assoc]

/-- A braid word on the strands on the right of a cap commutes with it; its letters are shifted
by `2`. -/
theorem capAt_mul_braidMatrix_of_le (n i : ℕ) (w : BraidWord) (h : ∀ g ∈ w, i ≤ g.1) :
    capAt n i * braidMatrix n w =
      braidMatrix (n + 2) (w.map fun g ↦ (g.1 + 2, g.2)) * capAt n i := by
  induction w with
  | nil => rw [List.map_nil, braidMatrix_nil, braidMatrix_nil, Matrix.mul_one, Matrix.one_mul]
  | cons g w ih =>
    rw [List.map_cons, braidMatrix_cons_capAtComm, braidMatrix_cons_capAtComm, ← Matrix.mul_assoc,
      capAt_mul_crossingF_of_le_capAtComm n i g.1 g.2 (h g List.mem_cons_self), Matrix.mul_assoc,
      ih fun x hx ↦ h x (List.mem_cons_of_mem g hx), Matrix.mul_assoc]

end AJConjecture
