import Mathlib
import AJHandoff.TorusInput.RJCycleThick
import AJConjecture.SkeinThickYangBaxter
import AJConjecture.SkeinThickCrossBraid
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinProfileBasic

/-!
# The `r`-th power of the cyclic braid is the full twist (node RA3.2)

`c_(r+1)^(r+1) = (c_r^r ⊗ 1_b) · J_(b r, b)`: the cabled full twist of `r + 1` bundles is the full
twist of the first `r` followed by the full twist of the last bundle with the first `r`
(`(σ_0 ⋯ σ_(r-1))^(r+1) = Δ²_(r+1) = (Δ²_r ⊗ 1) (σ_(r-1) ⋯ σ_0 σ_0 ⋯ σ_(r-1))`).

Route. Write `R_n = X_(b, b(n-1))(0)` on `n` bundles (`rjCycleMat_succ`). Prove by induction on
`j`, for all `n ≥ j`: `R_n^j = X_(bj, b(n-j))(0) · (R_j^j placed at b(n-j))`. Step: split
`X_(1,n-1) = X_(1,m)(0) X_(1,j)(m)` (`m = n - j - 1`, `braidMatrix_thickGen_add_right`), move the
block `R_j^j` past `X_(1,m)(0)` (disjoint windows, `braidMatrix_commute_of_far` or the
interchange law), and use thick Reidemeister III `braidMatrix_thickCross_yangBaxter` for the
bundles `(j, 1, m)`:
`X_(j, m+1)(0) X_(1,m)(0) = X_(j+1, m)(0) X_(j,1)(m)` (both sides split with
`thickGen_add_left` / `braidMatrix_thickGen_add_right`). Then `R_n^n = R_n^(n-1) R_n` with
`j = n - 1` gives `X_(b(n-1), b)(0) (R_(n-1)^(n-1))^{+b} X_(b, b(n-1))(0)`, and (N2)
`braidMatrix_mul_thickCross_fst` / `_snd` moves the block to the front:
`(R_(n-1)^(n-1) ⊗ 1) X_(b(n-1),b)(0) X_(b,b(n-1))(0)`. Numerically checked for `r ≤ 3`, `b ≤ 2`
(design notes). Estimate 180–260 lines.
-/

noncomputable section

namespace AJConjecture

/-- Placement at a fixed position is compatible with powers. -/
private theorem skPlace_pow_cycleTwist (n i k : ℕ) (A : SkMat k k) (h : i + k ≤ n) (p : ℕ) :
    skPlace n n i (A ^ p) = skPlace n n i A ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero, skPlace_one n i k h]
  | succ p ih => rw [pow_succ, pow_succ, skPlace_mul n n n i _ _ h rfl rfl, ih]

/-- Thick Reidemeister III in the form used for the cyclic braid: the bundle of `a` strands
crosses `c + d` strands, then the next `c` strands cross `d`; equivalently the first `a + c`
strands cross `d`, then `a` strands cross `c`. -/
private theorem thickGen_cycleTwist_yangBaxter (N a c d o : ℕ) (h : o + a + c + d ≤ N) :
    braidMatrix N (thickGen a (c + d) o true) * braidMatrix N (thickGen c d o true) =
      braidMatrix N (thickGen (a + c) d o true) * braidMatrix N (thickGen a c (o + d) true) := by
  have hyb := braidMatrix_thickCross_yangBaxter N a c d o true h
  simp only [thickCross, ite_true] at hyb
  rw [braidMatrix_thickGen_add_right, hyb, thickGen_add_left, braidMatrix_append]

/-- The powers of the cyclic braid `R_n = X_(b, b(n-1))(o)` on `n = m + j` bundles:
`R_n^j = X_(bj, bm)(o) · R_j^j` with `R_j` on the last `j` bundles. -/
private theorem thickGen_pow_cycleTwist (N b j : ℕ) :
    ∀ m o : ℕ, o + b * (m + j) ≤ N →
      braidMatrix N (thickGen b (b * (m + j - 1)) o true) ^ j =
        braidMatrix N (thickGen (b * j) (b * m) o true) *
          braidMatrix N (thickGen b (b * (j - 1)) (o + b * m) true) ^ j := by
  induction j with
  | zero =>
    intro m o _
    rw [pow_zero, pow_zero, mul_zero, Matrix.mul_one]
    rfl
  | succ j ih =>
    intro m o h
    have e1 : m + (j + 1) - 1 = m + j := by omega
    have e2 : j + 1 - 1 = j := by omega
    have hI := ih (m + 1) o (by rw [show m + 1 + j = m + (j + 1) by omega]; exact h)
    rw [show m + 1 + j - 1 = m + j by omega, show b * (m + 1) = b + b * m by ring] at hI
    rw [e1, e2, pow_succ, hI, mul_add b m j, braidMatrix_thickGen_add_right N b (b * m) (b * j) o]
    have hcomm : Commute (braidMatrix N (thickGen b (b * (j - 1)) (o + (b + b * m)) true) ^ j)
        (braidMatrix N (thickGen b (b * m) o true)) :=
      ((braidMatrix_commute_of_far N _ _ fun g hg g' hg' ↦ by
        have h1 := mem_thickGen_true hg
        have h2 := mem_thickGen_true hg'
        omega).symm).pow_left j
    have hpos : o + b * j + b + b * m ≤ N := by nlinarith
    have hyb := thickGen_cycleTwist_yangBaxter N (b * j) b (b * m) o hpos
    have hT := ih 1 (o + b * m) (by nlinarith)
    rw [show 1 + j - 1 = j by omega, mul_one] at hT
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (braidMatrix N (thickGen b (b * m) o true)),
      hcomm.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyb, show b * (j + 1) = b * j + b by ring,
      pow_succ, hT, show o + b * m + b = o + (b + b * m) by ring]
    simp only [Matrix.mul_assoc]

/-- The `(r+1)`-th power of the cabled cyclic braid on `r + 1` bundles. -/
theorem rjCycleMat_pow_succ (b r : ℕ) :
    rjCycleMat b (r + 1) ^ (r + 1) =
      skPlace (b * (r + 1)) (b * (r + 1)) 0 (rjCycleMat b r ^ r) * rjFullTwist (b * r) b := by
  cases r with
  | zero =>
    have h0 : ∀ n : ℕ, braidMatrix n (thickGen b 0 0 true) = 1 := fun n ↦ by
      rw [show thickGen b 0 0 true = [] from List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl,
        braidMatrix_nil]
    have hL : rjCycleMat b (0 + 1) = 1 := braidMatrix_nil _
    have hR : rjFullTwist (b * 0) b = 1 := by
      show (rjFullTwist 0 b : SkMat (0 + b) (0 + b)) = 1
      rw [rjFullTwist, braidMatrix_append]
      simp only [thickCross, ite_true, h0, Matrix.mul_one]
      exact braidMatrix_nil _
    rw [hL, hR, pow_zero, one_pow, skPlace_one _ 0 _ (by omega), Matrix.mul_one]
  | succ r =>
    have hw : IsOnStrands (b * (r + 1)) (thickGen b (b * r) 0 true) := fun g hg ↦ by
      have := mem_thickGen_true hg
      rw [mul_add, mul_one]
      omega
    have hmap : ∀ d : ℕ, (thickGen b (b * r) 0 true).map (fun g ↦ (g.1 + d, g.2)) =
        thickGen b (b * r) d true := fun d ↦ by
      have := thickCross_add_off b (b * r) 0 d true
      simp only [thickCross, ite_true, zero_add] at this
      exact this.symm
    have hP := thickGen_pow_cycleTwist (b * (r + 1 + 1)) b (r + 1) 1 0
      (le_of_eq (by ring))
    rw [show 1 + (r + 1) - 1 = r + 1 by omega, show r + 1 - 1 = r by omega, mul_one,
      zero_add] at hP
    have hS := braidMatrix_mul_thickCross_fst (b * (r + 1 + 1)) (b * (r + 1)) b 0 true
      (thickGen b (b * r) 0 true) (by ring_nf; omega) hw
    simp only [zero_add, hmap, thickCross, ite_true] at hS
    have hSp : braidMatrix (b * (r + 1 + 1)) (thickGen (b * (r + 1)) b 0 true) *
        braidMatrix (b * (r + 1 + 1)) (thickGen b (b * r) b true) ^ (r + 1) =
        braidMatrix (b * (r + 1 + 1)) (thickGen b (b * r) 0 true) ^ (r + 1) *
          braidMatrix (b * (r + 1 + 1)) (thickGen (b * (r + 1)) b 0 true) :=
      (SemiconjBy.pow_right hS.symm (r + 1))
    rw [rjCycleMat_succ, rjCycleMat_succ, pow_succ]
    simp only [thickCross, ite_true]
    rw [hP, hSp, skPlace_pow_cycleTwist _ 0 _ _ (by nlinarith),
      ← braidMatrix_map_add_eq_skPlace _ _ 0 _ hw (by nlinarith), hmap, rjFullTwist,
      braidMatrix_append]
    simp only [thickCross, ite_true, Matrix.mul_assoc]
    rfl

end AJConjecture
