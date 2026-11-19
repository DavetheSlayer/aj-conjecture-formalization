import Mathlib
import AJHandoff.TorusInput.RJLoopOne
import AJHandoff.TorusInput.RJNatTwist
import AJConjecture.SkeinPtrTailPlace

/-!
# A parallel strand in a loop around `f_N` (node RA5.i.2)

A loop of `k + 1` strands carrying `Y ⊗ 1` around `f_N` is the loop of `k` strands carrying `Y`
times the single-strand loop: `f_N ω_(k+1)(Y ⊗ 1) = λ_N f_N ω_k(Y)`.

Route. Split the bundle of `k + 1` strands as `k + 1`:
`J_(N,k+1) = X_(N,k)(0) · (J_(N,1) placed at k) · X_(k,N)(0)` (`thickGen_add_left`,
`braidMatrix_thickGen_add_right`). The outer factors and `1_N ⊗ Y` do not touch the last strand,
so the partial trace over it gives `X_(N,k)(0) (Ω_1 placed at k) X_(k,N)(0)`
(`ptrTail_ptrTail`, `ptrTail_skPlace_mul`, `ptrTail_mul_skPlace`, `ptrTail_skPlace_shift`). The
projector `f_N` slides to the position `k` (`jwAt_mul_braidMatrix_thickCross_fst`), where
`f_N Ω_1 = λ_N f_N` (`rj_axisLoop_one_mul_jwAt`; `Ω_1` commutes with `f_N` by `rjNat_jwAt` and
`rjAxisLoop_mul_of_rjNat`), and slides back. Estimate 100–150 lines.
-/

noncomputable section

namespace AJConjecture

/-- The partial trace commutes with spectator strands on the left (sizes given by equations). -/
private theorem ptrTail_skPlace_shift_of_eq_loopParallel (i k n m m' : ℕ) (hm : m = i + k)
    (hm' : m' = i + n) (h : k ≤ n) (A : SkMat n n) :
    ptrTail m m' (skPlace m' m' i A) = skPlace m m i (ptrTail k n A) := by
  subst hm hm'
  exact ptrTail_skPlace_shift i k n h A

/-- A positive thick crossing on the first strands is the placement of its matrix. -/
private theorem braidMatrix_thickGen_eq_skPlace_loopParallel (n m a b : ℕ) (h : a + b ≤ m)
    (hm : m ≤ n) :
    braidMatrix n (thickGen a b 0 true) = skPlace n n 0 (braidMatrix m (thickGen a b 0 true)) := by
  rw [← braidMatrix_map_add_eq_skPlace m n 0 _ (fun g hg ↦ by
    have := mem_thickGen_true hg
    omega) (by omega)]
  simp

/-- The inner partial trace: the last strand of a loop of `k + 1` strands carrying `Y ⊗ 1` is the
single-strand loop placed after the first `k` strands. -/
private theorem ptrTail_loopWith_succ_loopParallel (N k : ℕ) (Y : SkMat k k) :
    ptrTail (N + k) (N + (k + 1))
        (rjFullTwist N (k + 1) * skPlace (N + (k + 1)) (N + (k + 1)) N
          (skPlace (k + 1) (k + 1) 0 Y)) =
      braidMatrix (N + k) (thickGen N k 0 true) * skPlace (N + k) (N + k) k (rjAxisLoop N 1) *
        braidMatrix (N + k) (thickGen k N 0 true) * skPlace (N + k) (N + k) N Y := by
  have hJ1 : braidMatrix (N + (k + 1)) (thickGen N 1 k true) *
      braidMatrix (N + (k + 1)) (thickGen 1 N k true) =
        skPlace (N + (k + 1)) (N + (k + 1)) k (rjFullTwist N 1) := by
    rw [rjFullTwist, ← braidMatrix_map_add_eq_skPlace (N + 1) _ k _ (fun g hg ↦ by
      rcases List.mem_append.1 hg with hg | hg <;>
      · have := mem_thickCross hg
        omega) (by omega), List.map_append, ← thickCross_add_off, ← thickCross_add_off,
      braidMatrix_append, zero_add]
    rfl
  have hY : skPlace (N + (k + 1)) (N + (k + 1)) N (skPlace (k + 1) (k + 1) 0 Y) =
      skPlace (N + (k + 1)) (N + (k + 1)) 0 (skPlace (N + k) (N + k) N Y) := by
    rw [skPlace_skPlace _ _ N 0 Y (by omega) (by omega) (by omega) (by omega),
      skPlace_skPlace _ _ 0 N Y (by omega) (by omega) (by omega) (by omega), zero_add, add_zero]
  have hL : ptrTail N (N + 1) (rjFullTwist N 1) = rjAxisLoop N 1 := by
    rw [rjAxisLoop, rjLoopWith, show jwAt 1 0 1 = 1 from rfl, skPlace_one _ _ _ (by omega),
      Matrix.mul_one]
  rw [rjFullTwist, braidMatrix_append]
  simp only [thickCross, ite_true]
  rw [braidMatrix_thickGen_add_right, thickGen_add_left k 1 N 0, braidMatrix_append, zero_add,
    braidMatrix_thickGen_eq_skPlace_loopParallel (N + (k + 1)) (N + k) N k le_rfl (by omega),
    braidMatrix_thickGen_eq_skPlace_loopParallel (N + (k + 1)) (N + k) k N (by omega)
      (by omega), hY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (braidMatrix (N + (k + 1)) (thickGen N 1 k true)), hJ1,
    ← skPlace_mul _ _ _ 0 _ _ (by omega) rfl rfl, ptrTail_skPlace_mul _ _ (by omega),
    ptrTail_mul_skPlace _ _ (by omega),
    ptrTail_skPlace_shift_of_eq_loopParallel k N (N + 1) (N + k) (N + (k + 1)) (by omega)
      (by omega) (by omega), hL]

/-- A parallel idle strand in a loop around `f_N` contributes the single-strand loop scalar. -/
theorem rj_jwAt_mul_loopWith_succ (N k : ℕ) (Y : SkMat k k) :
    jwAt N 0 N * rjLoopWith N (k + 1) (skPlace (k + 1) (k + 1) 0 Y) =
      rjHopf N 1 • (jwAt N 0 N * rjLoopWith N k Y) := by
  have hF0 : skPlace (N + k) (N + k) 0 (jwAt N 0 N) = jwAt (N + k) 0 N :=
    (jwAt_eq_skPlace (N + k) 0 N (by omega)).symm
  have hFk : skPlace (N + k) (N + k) k (jwAt N 0 N) = jwAt (N + k) k N :=
    (jwAt_eq_skPlace (N + k) k N (by omega)).symm
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (N + k) N k 0 true (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (N + k) k N 0 true (by omega)
  simp only [thickCross, ite_true, zero_add] at h1 h2
  have hΩ : jwAt (N + k) k N * skPlace (N + k) (N + k) k (rjAxisLoop N 1) =
      rjHopf N 1 • jwAt (N + k) k N := by
    rw [← hFk, ← skPlace_mul _ _ _ k _ _ (by omega) rfl rfl,
      ← rjAxisLoop_mul_of_rjNat 1 (rjNat_jwAt N 0 N (by omega)), rj_axisLoop_one_mul_jwAt,
      skPlace_smul]
  have key : jwAt (N + k) 0 N * (braidMatrix (N + k) (thickGen N k 0 true) *
      skPlace (N + k) (N + k) k (rjAxisLoop N 1) * braidMatrix (N + k) (thickGen k N 0 true) *
        skPlace (N + k) (N + k) N Y) =
      rjHopf N 1 • (skPlace (N + k) (N + k) 0 (jwAt N 0 N) *
        (rjFullTwist N k * skPlace (N + k) (N + k) N Y)) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc _ _
      (skPlace (N + k) (N + k) k (rjAxisLoop N 1)), hΩ, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc _ (jwAt (N + k) k N), h2, ← Matrix.mul_assoc, ← braidMatrix_append, ← hF0]
    have hJ := (rjNat_jwAt N 0 N (by omega)).2 k
    rw [rjFullTwist] at hJ
    simp only [thickCross, ite_true] at hJ
    rw [hJ, rjFullTwist]
    simp only [thickCross, ite_true, Matrix.smul_mul, Matrix.mul_assoc]
  rw [rjLoopWith, ← ptrTail_ptrTail N (N + k) (N + (k + 1)) (by omega) (by omega),
    ptrTail_loopWith_succ_loopParallel, ← ptrTail_skPlace_mul N (N + k) (by omega), hF0, key,
    ptrTail_smul, ptrTail_skPlace_mul N (N + k) (by omega), rjLoopWith]

end AJConjecture
