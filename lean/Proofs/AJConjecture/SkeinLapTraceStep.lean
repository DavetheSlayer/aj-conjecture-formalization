import Mathlib
import AJConjecture.SkeinLapOffset
import AJConjecture.SkeinLongKnot
import AJConjecture.SkeinThickCableCap

/-!
# The lap trace does not depend on the number of laps

Three statements on `lapTrace K k j G ℓ M`, where `M + 2` is the number of strands of the diagram
after `ℓ` laps, `M + 2 (ℓ + 1) = (k + 2) m`.

* Start: no lap, all columns have `k + 2` strands (`AJConjecture.lapProfile_zero`,
  `AJConjecture.thickCable_const`), the cap is at the offset `j` and is followed by `G` on the
  column `0`; with `AJConjecture.skPlace_mul` and `AJConjecture.skPlace_skPlace` this is the knot
  trace of `capAt k j * G` on the `(k + 2)`-cable.
* Step, for `ℓ + 1 < m`: one lap under the trace (`AJConjecture.qtr_thickCable_capAt` for the
  profile `lapProfile K.word k (ℓ + 1)` and the column `p = lapCol K.word (ℓ + 1)`, with
  `AJConjecture.lapProfile_update`, `AJConjecture.strandEnd_lapCol_succ` and
  `AJConjecture.profileOffset_lapProfile`) brings the cap to the bottom of the column `p`, after
  `G`; `p ≠ 0`, so the cap and `G` are on disjoint windows and the interchange law
  (`AJConjecture.skPlace_mul_skPlace_comm`, with `AJConjecture.add_le_profileOffset_lapProfile`)
  moves the cap before `G`, at the offset given by
  `AJConjecture.profileOffset_profileEnd_lapProfile`.
* End, for `ℓ + 1 = m`: the same lap brings the cap to the bottom of the column
  `lapCol K.word m = 0`, at the offset `j`, directly after `G`; every column has `k` strands
  (`AJConjecture.lapProfile_strands`, `AJConjecture.thickCable_congr`,
  `AJConjecture.thickCable_const`): this is the knot trace of `G * capAt k j` on the `k`-cable.
-/

namespace AJConjecture

/-- A cap on the first bundle is a cap of the whole diagram. -/
private theorem skPlace_capAt_lapTraceStep (k j M : ℕ) (hj : j ≤ k) (hk : k ≤ M) :
    skPlace (M + 2) M 0 (capAt k j) = capAt M (0 + j) := by
  rw [capAt, skPlace_skPlace (M + 2) M 0 j skCap (by omega) (by omega) (by omega) (by omega),
    capAt]

/-- The operator `capAt k j * G` on the first bundle of `M + 2` strands. -/
private theorem skPlace_capAt_mul_lapTraceStep (k j M : ℕ) (G : SkMat k (k + 2)) (hj : j ≤ k)
    (hk : k ≤ M) :
    skPlace (M + 2) (M + 2) 0 (capAt k j * G) = capAt M (0 + j) * skPlace M (M + 2) 0 G := by
  rw [skPlace_mul (M + 2) M (M + 2) 0 (capAt k j) G (by omega) (by omega) (by omega),
    skPlace_capAt_lapTraceStep k j M hj hk]

/-- The operator `G * capAt k j` on the first bundle of `M` strands. -/
private theorem skPlace_mul_capAt_lapTraceStep (k j M : ℕ) (G : SkMat k (k + 2)) (hj : j ≤ k)
    (hk : k ≤ M) :
    skPlace M M 0 (G * capAt k j) = skPlace M (M + 2) 0 G * capAt M (0 + j) := by
  rw [skPlace_mul M (M + 2) M 0 G (capAt k j) (by omega) (by omega) (by omega),
    skPlace_capAt_lapTraceStep k j M hj hk]

/-- The knot trace of `capAt k j * G` on a diagram whose number of strands is written as
`M + 2`. -/
private theorem qtr_cable_capAt_mul_lapTraceStep (w : BraidWord) (k j N M : ℕ)
    (G : SkMat k (k + 2)) (hj : j ≤ k) (hk : k ≤ M) (hN : N = M + 2) :
    qtr N (braidMatrix N (cable (k + 2) w) * skPlace N N 0 (capAt k j * G)) =
      qtr (M + 2) (braidMatrix (M + 2) (cable (k + 2) w) * capAt M (0 + j) *
        skPlace M (M + 2) 0 G) := by
  subst hN
  rw [skPlace_capAt_mul_lapTraceStep k j M G hj hk, Matrix.mul_assoc]

/-- The offset of the column `0` is `0`. -/
private theorem profileOffset_zero_lapTraceStep (κ : ℕ → ℕ) : profileOffset κ 0 = 0 := by
  rw [profileOffset, Finset.range_zero, Finset.sum_empty]

/-- One lap under the trace: the cap goes from the top of the column of the lap `ℓ` to the
bottom of the column of the lap `ℓ + 1`, after `G`. -/
private theorem lapTrace_eq_qtr_lapTraceStep (K : BraidKnot) (k j : ℕ) (G : SkMat k (k + 2))
    (ℓ N : ℕ) (hj : j ≤ k) (hℓ : ℓ < K.strands)
    (hN : N + 2 * (ℓ + 1) = (k + 2) * K.strands) :
    lapTrace K k j G ℓ N =
      qtr N (braidMatrix N (thickCable (lapProfile K.word k (ℓ + 1)) K.word) *
        skPlace N (N + 2) 0 G *
        capAt N (profileOffset (lapProfile K.word k (ℓ + 1)) (lapCol K.word (ℓ + 1)) + j)) := by
  have hthin := lapProfile_apply_lapCol K.word k (ℓ + 1) (ℓ + 1) (by omega) le_rfl
  have hoff := profileOffset_lapProfile K k (ℓ + 1) (by omega)
  have h := qtr_thickCable_capAt K.strands N (lapProfile K.word k (ℓ + 1)) K.word
    (lapCol K.word (ℓ + 1)) j K.isOnStrands (lapCol_lt K (ℓ + 1)) (by omega) (by omega)
    (skPlace N (N + 2) 0 G)
  rw [hthin, lapProfile_update K k ℓ hℓ, strandEnd_lapCol_succ] at h
  exact h

/-- Before the first lap, the lap trace is the knot trace of `capAt k j * G` on the
`(k + 2)`-cable. -/
theorem lapTrace_zero (K : BraidKnot) (k j : ℕ) (G : SkMat k (k + 2)) (M : ℕ) (hj : j ≤ k)
    (hM : M + 2 = (k + 2) * K.strands) :
    lapTrace K k j G 0 M = knotTrace K (k + 2) (capAt k j * G) := by
  have hk : k ≤ M := by
    have h1 : k + 2 ≤ (k + 2) * K.strands := Nat.le_mul_of_pos_right _ K.strands_pos
    omega
  have h0 : profileOffset (profileEnd (lapProfile K.word k (0 + 1)) K.word) (lapCol K.word 0) =
      0 := profileOffset_zero_lapTraceStep _
  rw [lapTrace, knotTrace, lapProfile_zero, thickCable_const, h0]
  exact (qtr_cable_capAt_mul_lapTraceStep K.word k j _ M G hj hk hM.symm).symm

/-- One lap that does not end in the column `0` does not change the lap trace. -/
theorem lapTrace_succ (K : BraidKnot) (k j : ℕ) (G : SkMat k (k + 2)) (ℓ M : ℕ) (hj : j ≤ k)
    (hℓ : ℓ + 1 < K.strands) (hM : M + 2 * (ℓ + 2) = (k + 2) * K.strands) :
    lapTrace K k j G ℓ (M + 2) = lapTrace K k j G (ℓ + 1) M := by
  have htop := profileOffset_profileEnd_lapProfile K k ℓ hℓ
  have hbot := add_le_profileOffset_lapProfile K k ℓ hℓ
  have hthin := lapProfile_apply_lapCol K.word k (ℓ + 1) (ℓ + 1) (by omega) le_rfl
  have hoff := profileOffset_lapProfile K k (ℓ + 1) (by omega)
  have hle := profileOffset_add_le (lapProfile K.word k (ℓ + 1)) (lapCol K.word (ℓ + 1))
    K.strands (lapCol_lt K (ℓ + 1))
  have hcomm := skPlace_mul_skPlace_comm (M + 2) (M + 2 + 2) M (M + 2) 0
    (profileOffset (profileEnd (lapProfile K.word k (ℓ + 2)) K.word) (lapCol K.word (ℓ + 1)) + j)
    G skCap (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [show profileOffset (profileEnd (lapProfile K.word k (ℓ + 2)) K.word)
        (lapCol K.word (ℓ + 1)) + j + (k + 2) - k =
      profileOffset (lapProfile K.word k (ℓ + 1)) (lapCol K.word (ℓ + 1)) + j from by omega]
    at hcomm
  rw [lapTrace_eq_qtr_lapTraceStep K k j G ℓ (M + 2) hj (by omega) (by omega), lapTrace,
    Matrix.mul_assoc, Matrix.mul_assoc]
  exact congrArg (fun Y ↦ qtr (M + 2)
    (braidMatrix (M + 2) (thickCable (lapProfile K.word k (ℓ + 1)) K.word) * Y)) hcomm

/-- The last lap ends in the column `0`: the lap trace is the knot trace of `G * capAt k j` on
the `k`-cable. -/
theorem lapTrace_last (K : BraidKnot) (k j : ℕ) (G : SkMat k (k + 2)) (ℓ M : ℕ) (hj : j ≤ k)
    (hℓ : ℓ + 1 = K.strands) (hM : M = k * K.strands) :
    lapTrace K k j G ℓ M = knotTrace K k (G * capAt k j) := by
  subst hM
  have hk : k ≤ k * K.strands := Nat.le_mul_of_pos_right _ K.strands_pos
  have hcol : lapCol K.word (ℓ + 1) = 0 := by
    have h0 : lapCol K.word (ℓ + 1) = lapCol K.word 0 := by
      rw [lapCol_eq_iff, hℓ, Nat.ModEq, Nat.mod_self, Nat.zero_mod]
    exact h0
  have hcable : thickCable (lapProfile K.word k (ℓ + 1)) K.word = cable k K.word := by
    rw [hℓ, thickCable_congr K.strands _ (fun _ ↦ k) K.word K.isOnStrands
      (fun x hx ↦ lapProfile_strands K k x hx), thickCable_const]
  rw [lapTrace_eq_qtr_lapTraceStep K k j G ℓ (k * K.strands) hj (by omega)
      (by rw [hℓ]; ring), hcol, profileOffset_zero_lapTraceStep, hcable, knotTrace,
    skPlace_mul_capAt_lapTraceStep k j (k * K.strands) G hj hk, Matrix.mul_assoc]

end AJConjecture
