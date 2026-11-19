import Mathlib
import AJHandoff.TorusInput.RJFusionTwistEigen
import AJConjecture.SkeinJwTrace
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinJwCapComm

/-!
# A single strand encircling `f_N` (node RA5.i.1)

`Ω_1 f_N = λ_N f_N`, `λ_N = -(t^(2N+2) + t^(-2N-2)) = rjHopf N 1`.

Route. `Ω_1 f_N = ptr_N(J_(N,1) (f_N ⊗ 1))` (`rjAxisLoop`, `jwAt` of size `1` is `1`, and
`f_N ⊗ 1` passes into the partial trace by `ptrTail_skPlace_mul`). Wenzl's recursion at `N + 1`:
`f_N ⊗ 1 = f_(N+1) - ([N]/[N+1]) (f_N ⊗ 1) e_(N-1) (f_N ⊗ 1)` (definition of `jwAt`,
`jwAt_eq_skPlace`). On `f_(N+1)` all `2N` crossings of `J_(N,1)` are inside the block
(`braidMatrix_mul_jwAt_of_inside`): eigenvalue `t^(2N)`. The second term is
`π_1 · cup · (f_N ⊗ 1)` with `π_1 = rjFusionProj N 1 1` (`f_(N-1)` is absorbed by `f_N`), so
`rj_fullTwist_mul_fusionProj` (channel `1` of `(N, 1)`) gives the eigenvalue
`θ_(N-1)/(θ_N θ_1) = t^(-2N-4)`. Partial traces: `ptrTail_jwAt`
(`ptr f_(N+1) = -([N+2]/[N+1]) f_N`) and `ptr ((f_N ⊗ 1) e_(N-1) (f_N ⊗ 1)) = f_N`
(`ptrTail_skPlace_mul`, `ptrTail_mul_skPlace`, the Markov property `ptr e_(N-1) = 1` of
`SkeinJwTrace`). Scalar: `-(t^(2N)[N+2] + t^(-2N-4)[N])/[N+1] = -(t^(2N+2) + t^(-2N-2))`. For
`N = 0`: `Ω_1 = δ`. Numerically checked (design notes). Estimate 120–170 lines.
-/

noncomputable section

namespace AJConjecture

/-- The linear system `x P + x⁻¹ Q = -x³ I`, `x⁻¹ P + x Q = -x⁻³ I` forces `Q = I`. -/
private theorem kauffman_system_snd_loopOne {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] (x : K) (hx : x ≠ 0) (hd : x ^ 2 - x⁻¹ ^ 2 ≠ 0) (P Q I : M)
    (h1 : x • P + x⁻¹ • Q = (-x ^ 3) • I) (h2 : x⁻¹ • P + x • Q = (-x⁻¹ ^ 3) • I) : Q = I := by
  have hP : P = (-x ^ 2 - x⁻¹ ^ 2) • I := by
    apply smul_right_injective M hd
    change (x ^ 2 - x⁻¹ ^ 2) • P = (x ^ 2 - x⁻¹ ^ 2) • (-x ^ 2 - x⁻¹ ^ 2) • I
    have h3 : (x ^ 2 - x⁻¹ ^ 2) • P = x • (x • P + x⁻¹ • Q) - x⁻¹ • (x⁻¹ • P + x • Q) := by
      module
    rw [h3, h1, h2]
    module
  have hQ : x⁻¹ • Q = (-x ^ 3) • I - x • P := eq_sub_of_add_eq' h1
  calc Q = (x * x⁻¹) • Q := by rw [mul_inv_cancel₀ hx, one_smul]
    _ = x • ((-x ^ 3) • I - x • P) := by rw [mul_smul, hQ]
    _ = (x * x⁻¹) ^ 2 • I := by rw [hP]; module
    _ = I := by rw [mul_inv_cancel₀ hx, one_pow, one_smul]

/-- The Markov property: the partial trace of the last generator over the last strand is `1`. -/
private theorem ptrTail_tlGenF_last_loopOne (n : ℕ) :
    ptrTail (n + 1) (n + 2) (tlGenF (n + 2) n) = 1 := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have e2 : (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) = RatFunc.X ^ 2 := by norm_cast
  have e2' : (RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) = RatFunc.X⁻¹ ^ 2 := by
    rw [zpow_neg, inv_pow]; norm_cast
  have e3 : (RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) = RatFunc.X ^ 3 := by norm_cast
  have e3' : (RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ) = RatFunc.X⁻¹ ^ 3 := by
    rw [zpow_neg, inv_pow]; norm_cast
  have hd : (RatFunc.X : RatFunc ℚ) ^ 2 - RatFunc.X⁻¹ ^ 2 ≠ 0 := by
    rw [← e2, ← e2']; exact claspAlg_ratFuncX_sq_sub_ne_zero
  have hp := ptrTail_crossingF_last n true
  have hm := ptrTail_crossingF_last n false
  rw [crossingF_pos, ptrTail_add, ptrTail_smul, ptrTail_smul] at hp
  rw [crossingF_neg, ptrTail_add, ptrTail_smul, ptrTail_smul] at hm
  simp only [↓reduceIte, e3] at hp
  simp only [Bool.false_eq_true, ↓reduceIte, e3'] at hm
  exact kauffman_system_snd_loopOne RatFunc.X hX hd _ _ _ hp hm

/-- The scalar identity of the single loop: `t^(2n+2)(-[n+3]) - [n+1] t^(-2n-6) = -[2n+4]`. -/
private theorem loopOne_scalar (n : ℕ) :
    (RatFunc.X : RatFunc ℚ) ^ (2 * (n : ℤ) + 2) * -quantumInt ((n : ℤ) + 3) -
      quantumInt ((n : ℤ) + 1) * (RatFunc.X ^ (-(2 * (n : ℤ)) - 6)) =
      -quantumInt (2 * (n : ℤ) + 4) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hnum : (RatFunc.X : RatFunc ℚ) ^ (2 * (n : ℤ) + 2) *
      -(RatFunc.X ^ (2 * ((n : ℤ) + 3)) - RatFunc.X ^ (-(2 * ((n : ℤ) + 3)))) -
      (RatFunc.X ^ (2 * ((n : ℤ) + 1)) - RatFunc.X ^ (-(2 * ((n : ℤ) + 1)))) *
        RatFunc.X ^ (-(2 * (n : ℤ)) - 6) =
      -(RatFunc.X ^ (2 * (2 * (n : ℤ) + 4)) - RatFunc.X ^ (-(2 * (2 * (n : ℤ) + 4)))) := by
    simp only [mul_add, two_mul, neg_add, zpow_add₀ hX, zpow_neg, zpow_sub₀ hX]
    field_simp
    ring
  simp only [quantumInt, div_eq_mul_inv]
  linear_combination ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))⁻¹ * hnum

/-- The eigenvalue of the full twist on the channel `1` of `(n + 1, 1)`. -/
private theorem kinkScalar_ratio_loopOne (n : ℕ) :
    kinkScalar n / (kinkScalar (n + 1) * kinkScalar 1) =
      (RatFunc.X : RatFunc ℚ) ^ (-(2 * (n : ℤ)) - 6) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hk : ∀ m : ℕ, kinkScalar m ≠ 0 := fun m ↦
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hX)
  rw [div_eq_iff (mul_ne_zero (hk _) (hk _)), kinkScalar, kinkScalar, kinkScalar]
  push_cast
  rw [show (n : ℤ) * ((n : ℤ) + 2) = (-(2 * (n : ℤ)) - 6) +
      (((n : ℤ) + 1) * ((n : ℤ) + 1 + 2) + 3) by ring, zpow_add₀ hX, zpow_add₀ hX]
  ring

/-- The full twist of `n + 1` strands with one strand on `f_(n+2)`. -/
private theorem rjFullTwist_mul_jwAt_loopOne (n : ℕ) :
    rjFullTwist (n + 1) 1 * jwAt (n + 1 + 1) 0 (n + 1 + 1) =
      (RatFunc.X : RatFunc ℚ) ^ (2 * (n : ℤ) + 2) • jwAt (n + 1 + 1) 0 (n + 1 + 1) := by
  rw [rjFullTwist, braidMatrix_mul_jwAt_of_inside (n + 1 + 1) 0 (n + 1 + 1) _ fun g hg ↦ by
      rcases List.mem_append.1 hg with hg | hg <;>
      · have := mem_thickCross hg
        omega,
    writhe_eq_of_forall_sign _ true fun g hg ↦ by
      rcases List.mem_append.1 hg with hg | hg <;> exact (mem_thickCross hg).2.2,
    List.length_append, length_thickCross, length_thickCross]
  simp only [↓reduceIte]
  congr 2
  push_cast
  ring

/-- The full twist of `n + 1` strands with one strand on the turnback `f' e_n f'`. -/
private theorem rjFullTwist_mul_turnback_loopOne (n : ℕ) :
    rjFullTwist (n + 1) 1 * (jwAt (n + 2) 0 (n + 1) * tlGenF (n + 2) n * jwAt (n + 2) 0 (n + 1)) =
      (kinkScalar n / (kinkScalar (n + 1) * kinkScalar 1)) •
        (jwAt (n + 2) 0 (n + 1) * tlGenF (n + 2) n * jwAt (n + 2) 0 (n + 1)) := by
  have hπ := rj_fullTwist_mul_fusionProj (n + 1) 1 1 (by simp)
  rw [rjFusionProj, rjTwistRatio, show n + 1 + 1 - 2 * 1 = n by omega,
    show n + 1 - 1 = n by omega, rjBundleProj, capThick_one,
    show jwAt (n + 1 + 1) (n + 1) 1 = 1 from rfl, Matrix.mul_one] at hπ
  have hc : jwAt (n + 2) 0 (n + 1) * capAt n n * jwAt n 0 n =
      jwAt (n + 2) 0 (n + 1) * capAt n n := by
    rw [Matrix.mul_assoc, ← jwAt_mul_capAt_of_le n 0 n n (by omega), ← Matrix.mul_assoc,
      jwAt_mul_jwAt_of_le (n + 2) 0 (n + 1) 0 n le_rfl (by omega)]
  change rjFullTwist (n + 1) 1 * (jwAt (n + 2) 0 (n + 1) * capAt n n * jwAt n 0 n) =
    _ • (jwAt (n + 2) 0 (n + 1) * capAt n n * jwAt n 0 n) at hπ
  rw [hc] at hπ
  have e : jwAt (n + 2) 0 (n + 1) * tlGenF (n + 2) n * jwAt (n + 2) 0 (n + 1) =
      jwAt (n + 2) 0 (n + 1) * capAt n n * (cupAt n n * jwAt (n + 2) 0 (n + 1)) := by
    rw [← capAt_mul_cupAt n n le_rfl]
    simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mul_assoc, hπ, Matrix.smul_mul]

/-- A single strand encircling `f_N` is the scalar `-(t^(2N+2) + t^(-2N-2))`. -/
theorem rj_axisLoop_one_mul_jwAt (N : ℕ) :
    rjAxisLoop N 1 * jwAt N 0 N = rjHopf N 1 • jwAt N 0 N := by
  rw [rjAxisLoop, rjLoopWith, show jwAt 1 0 1 = 1 from rfl, skPlace_one _ _ _ (by omega),
    Matrix.mul_one, ← ptrTail_mul_skPlace N (N + 1) (by omega)]
  cases N with
  | zero =>
    have hJ : rjFullTwist 0 1 = 1 := braidMatrix_nil _
    have h := ptrTail_jwAt 0
    rw [show jwAt (0 + 1) 0 (0 + 1) = 1 from rfl] at h
    rw [hJ, Matrix.one_mul, show jwAt 0 0 0 = 1 from rfl, skPlace_one _ _ _ (by omega), h,
      rjHopf]
    congr 1
    norm_num [neg_div]
  | succ n =>
    have hF : skPlace (n + 1 + 1) (n + 1 + 1) 0 (jwAt (n + 1) 0 (n + 1)) =
        jwAt (n + 2) 0 (n + 1) := (jwAt_eq_skPlace (n + 2) 0 (n + 1) (by omega)).symm
    have hW : jwAt (n + 2) 0 (n + 1) = jwAt (n + 1 + 1) 0 (n + 1 + 1) +
        (-(quantumInt ((n : ℤ) + 1) / quantumInt ((n : ℤ) + 2))) •
          (jwAt (n + 2) 0 (n + 1) * tlGenF (n + 2) n * jwAt (n + 2) 0 (n + 1)) := by
      rw [show jwAt (n + 1 + 1) 0 (n + 1 + 1) = jwAt (n + 2) 0 (n + 1) +
        (quantumInt ((n : ℤ) + 1) / quantumInt ((n : ℤ) + 2)) • (jwAt (n + 2) 0 (n + 1) *
          tlGenF (n + 2) (0 + n) * jwAt (n + 2) 0 (n + 1)) from by rw [jwAt], Nat.zero_add,
        neg_smul, add_neg_cancel_right]
    have h2 : ptrTail (n + 1) (n + 2)
        (jwAt (n + 2) 0 (n + 1) * tlGenF (n + 2) n * jwAt (n + 2) 0 (n + 1)) =
        jwAt (n + 1) 0 (n + 1) := by
      rw [← hF, Matrix.mul_assoc, ptrTail_skPlace_mul (n + 1) (n + 2) (by omega),
        ptrTail_mul_skPlace (n + 1) (n + 2) (by omega), ptrTail_tlGenF_last_loopOne,
        Matrix.one_mul, jwAt_mul_self]
    have h1 := ptrTail_jwAt (n + 1)
    rw [hF, hW, Matrix.mul_add, Matrix.mul_smul, rjFullTwist_mul_jwAt_loopOne,
      rjFullTwist_mul_turnback_loopOne, smul_smul, ptrTail_add, ptrTail_smul, ptrTail_smul, h1,
      h2, smul_smul, ← add_smul]
    congr 1
    rw [kinkScalar_ratio_loopOne, rjHopf]
    push_cast
    rw [show ((n : ℤ) + 1 + 2) = (n : ℤ) + 3 by ring, show ((n : ℤ) + 1 + 1) = (n : ℤ) + 2 by ring,
      show ((n : ℤ) + 2) * 2 = 2 * (n : ℤ) + 4 by ring]
    linear_combination (quantumInt ((n : ℤ) + 2))⁻¹ * loopOne_scalar n

end AJConjecture
