import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinPlaceMul
import AJConjecture.SkeinPlaceComm
import AJConjecture.SkeinPlaceNest
import AJConjecture.SkeinTranspose
import AJConjecture.SkeinWeightPlace
import AJConjecture.SkeinThickGenReverse
import AJConjecture.SkeinThickGenInv
import AJConjecture.SkeinThickCableBasic
import AJConjecture.SkeinProfileBasic
import AJConjecture.SkeinHalfTwistCap
import AJConjecture.SkeinBraidMatrixPlace

/-!
# Naturality: closure properties (node RN1)

`RJNat X`: `X` intertwines the weights and slides through the full twist with a bundle of any
thickness on its right. The class is closed under products, scalars, transposition and
`X ↦ X ⊗ 1_b` (an idle bundle on the right).

Route.
* Products: `skPlace_mul` (functoriality of the placement at `0`) and the two hypotheses.
* Transposition: `rjFullTwist a b` is symmetric (`braidMatrix_thickCross_transpose`:
  `ρ(X_(a,b))ᵀ = ρ(X_(b,a))`, so `(X_(a,b) X_(b,a))ᵀ = X_(a,b) X_(b,a)`), `skPlace_transpose`,
  `skWeight` is diagonal.
* `X ⊗ 1_b`: split the bundle of `m + b` strands; with `thickGen_add_left` and
  `braidMatrix_thickGen_add_right`, `J_(m+b,k) = X_(b,k)(m) · (J_(m,k) ⊗ 1_b) · X_(k,b)(m)`
  (the idle bundle crosses the `k` strands, the rest twists, the idle bundle crosses back). The
  outer crossings act on windows disjoint from `X` and pass it by the interchange law
  (`skPlace_mul_skPlace_comm`, with `braidMatrix_map_add_eq_skPlace`); the middle factor is the
  hypothesis placed at `0` (`skPlace_skPlace`).
* Weights: `skWeight_mul_skPlace`.
Estimate 150–220 lines.
-/

noncomputable section

namespace AJConjecture

/-- A thick crossing at the offset `off` is the thick crossing at `0` placed at `off`. -/
private theorem rj_braidMatrix_thickCross_eq_skPlace (N a b off : ℕ) (s : Bool)
    (h : off + a + b ≤ N) :
    braidMatrix N (thickCross a b off s) =
      skPlace N N off (braidMatrix (a + b) (thickCross a b 0 s)) := by
  have e := thickCross_add_off a b 0 off s
  rw [Nat.zero_add] at e
  rw [e, braidMatrix_map_add_eq_skPlace (a + b) N off _ (fun g hg ↦ by
    have := mem_thickCross hg
    omega) (by omega)]

/-- The full twist is the product of its two thick crossings. -/
private theorem rjFullTwist_eq_mul_thickCross (a b : ℕ) :
    rjFullTwist a b = braidMatrix (a + b) (thickCross a b 0 true) *
      braidMatrix (a + b) (thickCross b a 0 true) := by
  rw [rjFullTwist, braidMatrix_append]

/-- The full twist is symmetric. -/
private theorem rjFullTwist_transpose (a b : ℕ) :
    (rjFullTwist a b).transpose = rjFullTwist a b := by
  rw [rjFullTwist_eq_mul_thickCross, Matrix.transpose_mul,
    braidMatrix_thickCross_transpose (a + b) b a 0 true,
    braidMatrix_thickCross_transpose (a + b) a b 0 true]

/-- The full twist of two bundles inside a larger space is a placement at `0`. -/
private theorem rj_braidMatrix_fullTwist_eq_skPlace (N a b : ℕ) (h : a + b ≤ N) :
    braidMatrix N (thickCross a b 0 true ++ thickCross b a 0 true) =
      skPlace N N 0 (rjFullTwist a b) := by
  rw [braidMatrix_append, rj_braidMatrix_thickCross_eq_skPlace N a b 0 true (by omega),
    rj_braidMatrix_thickCross_eq_skPlace N b a 0 true (by omega), rjFullTwist,
    braidMatrix_append, add_comm b a, skPlace_mul N N N 0 _ _ (by omega) rfl rfl]

/-- Splitting the first bundle of the full twist: `J_(m+b,k)` is the crossing of the last `b`
strands with the `k` strands, the full twist `J_(m,k)`, and the crossing back. -/
private theorem rjFullTwist_add_left (m b k : ℕ) :
    rjFullTwist (m + b) k =
      skPlace (m + b + k) (m + b + k) m (braidMatrix (b + k) (thickCross b k 0 true)) *
        skPlace (m + b + k) (m + b + k) 0 (rjFullTwist m k) *
        skPlace (m + b + k) (m + b + k) m (braidMatrix (k + b) (thickCross k b 0 true)) := by
  rw [rjFullTwist_eq_mul_thickCross]
  have h1 : braidMatrix (m + b + k) (thickCross (m + b) k 0 true) =
      braidMatrix (m + b + k) (thickCross b k m true) *
        braidMatrix (m + b + k) (thickCross m k 0 true) := by
    have e := thickGen_add_left m b k 0
    rw [Nat.zero_add] at e
    exact (congrArg (braidMatrix (m + b + k)) e).trans (braidMatrix_append _ _ _)
  have h2 : braidMatrix (m + b + k) (thickCross k (m + b) 0 true) =
      braidMatrix (m + b + k) (thickCross k m 0 true) *
        braidMatrix (m + b + k) (thickCross k b m true) := by
    have e := braidMatrix_thickGen_add_right (m + b + k) k m b 0
    rw [Nat.zero_add] at e
    exact e
  rw [h1, h2, rj_braidMatrix_thickCross_eq_skPlace (m + b + k) b k m true (by omega),
    rj_braidMatrix_thickCross_eq_skPlace (m + b + k) k b m true (by omega),
    ← rj_braidMatrix_fullTwist_eq_skPlace (m + b + k) m k (by omega), braidMatrix_append]
  simp only [Matrix.mul_assoc]

/-- The identity is natural. -/
theorem rjNat_one (m : ℕ) : RJNat (1 : SkMat m m) := by
  refine ⟨by rw [Matrix.mul_one, Matrix.one_mul], fun k ↦ ?_⟩
  rw [skPlace_one (m + k) 0 m (by omega), Matrix.mul_one, Matrix.one_mul]

/-- Natural maps compose. -/
theorem rjNat_mul {m n l : ℕ} {X : SkMat m n} {Y : SkMat n l} (hX : RJNat X) (hY : RJNat Y) :
    RJNat (X * Y) := by
  refine ⟨by rw [← Matrix.mul_assoc, hX.1, Matrix.mul_assoc, hY.1, Matrix.mul_assoc],
    fun k ↦ ?_⟩
  rw [skPlace_mul (m + k) (n + k) (l + k) 0 X Y (by omega) (by omega) (by omega),
    ← Matrix.mul_assoc, hX.2 k, Matrix.mul_assoc, hY.2 k, Matrix.mul_assoc]

/-- A scalar multiple of a natural map is natural. -/
theorem rjNat_smul {m n : ℕ} (c : RatFunc ℚ) {X : SkMat m n} (hX : RJNat X) : RJNat (c • X) := by
  refine ⟨by rw [Matrix.mul_smul, hX.1, Matrix.smul_mul], fun k ↦ ?_⟩
  rw [skPlace_smul, Matrix.mul_smul, hX.2 k, Matrix.smul_mul]

/-- The transpose of a natural map is natural. -/
theorem rjNat_transpose {m n : ℕ} {X : SkMat m n} (hX : RJNat X) : RJNat X.transpose := by
  have hW : ∀ p : ℕ, (skWeight p).transpose = skWeight p := fun p ↦ Matrix.diagonal_transpose _
  refine ⟨?_, fun k ↦ ?_⟩
  · have h := congrArg Matrix.transpose hX.1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hW, hW] at h
    exact h.symm
  · have h := congrArg Matrix.transpose (hX.2 k)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, rjFullTwist_transpose, rjFullTwist_transpose,
      skPlace_transpose] at h
    exact h.symm

/-- A natural map with an idle bundle of `b` strands on its right is natural. -/
theorem rjNat_placeLeft {m n : ℕ} (b : ℕ) {X : SkMat m n} (hX : RJNat X) :
    RJNat (skPlace (m + b) (n + b) 0 X) := by
  refine ⟨skWeight_mul_skPlace _ _ _ X hX.1, fun k ↦ ?_⟩
  have hP : skPlace (m + b + k) (n + b + k) 0 (skPlace (m + b) (n + b) 0 X) =
      skPlace (m + b + k) (n + b + k) 0 X := by
    rw [skPlace_skPlace (m + b + k) (n + b + k) 0 0 X (by omega) (by omega) (by omega)
      (by omega)]
  have hcomm : ∀ (p : ℕ) (B : SkMat p p), p ≤ b + k →
      skPlace (m + b + k) (m + b + k) m B * skPlace (m + b + k) (n + b + k) 0 X =
        skPlace (m + b + k) (n + b + k) 0 X * skPlace (n + b + k) (n + b + k) n B := by
    intro p B hp
    have h := skPlace_mul_skPlace_comm (m + b + k) (n + b + k) (m + b + k) (n + b + k) 0 m X B
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show m + n - m = n from by omega] at h
    exact h.symm
  have hmid : skPlace (m + b + k) (m + b + k) 0 (rjFullTwist m k) *
        skPlace (m + b + k) (n + b + k) 0 X =
      skPlace (m + b + k) (n + b + k) 0 X *
        skPlace (n + b + k) (n + b + k) 0 (rjFullTwist n k) := by
    have h := congrArg (skPlace (m + b + k) (n + b + k) 0) (hX.2 k)
    rw [skPlace_mul (m + b + k) (m + b + k) (n + b + k) 0 _ _ (by omega) (by omega) (by omega),
      skPlace_mul (m + b + k) (n + b + k) (n + b + k) 0 _ _ (by omega) (by omega) (by omega),
      skPlace_skPlace (m + b + k) (n + b + k) 0 0 X (by omega) (by omega) (by omega)
        (by omega)] at h
    exact h
  rw [hP, rjFullTwist_add_left, rjFullTwist_add_left]
  simp only [Matrix.mul_assoc]
  rw [hcomm _ _ (by omega), ← Matrix.mul_assoc (skPlace _ _ 0 (rjFullTwist m k)), hmid,
    Matrix.mul_assoc, ← Matrix.mul_assoc (skPlace _ _ m _), hcomm _ _ (by omega)]
  simp only [Matrix.mul_assoc]

end AJConjecture
