import Mathlib
import AJHandoff.TorusInput.RJFamilyBase
import AJHandoff.TorusInput.RJCycleTwist
import AJHandoff.TorusInput.RJFusionComplete
import AJHandoff.TorusInput.RJFusionTranspose
import AJConjecture.SkeinPlaceComm

/-!
# Fusing one more bundle (node RA2.2, crux of RA2)

From a good family for `r` bundles, a good family for `r + 1` bundles: each pair `(π_x, ι_x)`
through `f_N` is fused with the new bundle `f_b` along the channels `j ≤ min N b` of `f_N ⊗ f_b`:
`π' = (π_x ⊗ 1_b) π^{(N,b)}_j`, `ι' = d_j⁻¹ ι^{(N,b)}_j (ι_x ⊗ 1_b)` (`rjFamilySucc`).

Route.
* Sum: `f_b^{⊗(r+1)} = (f_b^{⊗ r} ⊗ 1) f_b(last)` (`rjColsProj_succ`)
  `= ∑_x (π_x ⊗ 1)(f_N ⊗ f_b)(ι_x ⊗ 1)` (interchange law `skPlace_mul_skPlace_comm`, absorption
  `π_x f_N = π_x`), then `rj_fusion_complete` for `(N, b)`.
* Spectrum: `N' = N + b - 2j ≤ b(r+1)` with the parity of `b(r+1)`.
* Naturality: `rjNat_mul`, `rjNat_placeLeft`, `rjNat_fusionProj`, `rjNat_fusionIncl`,
  `rjNat_smul`.
* Absorption: `rjColsProj_succ`, `rjFusionProj_absorb`, `rjFusionIncl_absorb`.
* Eigenvalues: `c_(r+1)^(r+1) = (c_r^r ⊗ 1) J_(br,b)` (`rjCycleMat_pow_succ`);
  `J_(br,b) (π_x ⊗ 1) = (π_x ⊗ 1) J_(N,b)` (`RJNat`), `J_(N,b) π_j = λ_j π_j`
  (`rj_fullTwist_mul_fusionProj`), `(c_r^r ⊗ 1)(π_x ⊗ 1) = μ_N (π_x ⊗ 1)` (`skPlace_mul`); and
  `μ_N λ_j = θ_N θ_b^(-r) θ_(N')/(θ_N θ_b) = μ_(N')`. On the right: `ι_j J_(N,b) = λ_j ι_j`
  (`rj_fusionIncl_mul_fullTwist`), `J_(N,b)(ι_x ⊗ 1) = (ι_x ⊗ 1) J_(br,b)` (`RJNat` of `ι_x`),
  and `J_(br,b)` commutes with `c_r^r ⊗ 1` (it is natural for braids, `rjNat_braidMatrix`).
Sizes: `b * (r + 1)` is definitionally `b * r + b`. Estimate 200–280 lines.
-/

noncomputable section

namespace AJConjecture

/-- The family of `r + 1` bundles obtained by fusing each pair with one more bundle. -/
def rjFamilySucc (b r : ℕ) (L : List (RJFusionPair (b * r))) : List (RJFusionPair (b * (r + 1))) :=
  L.flatMap fun x ↦ (List.range (min x.1 b + 1)).map fun j ↦
    ⟨x.1 + b - 2 * j,
      (skPlace (b * (r + 1)) (x.1 + b) 0 x.2.1 * rjFusionProj x.1 b j,
        (rjFusionDim x.1 b j)⁻¹ • (rjFusionIncl x.1 b j * skPlace (x.1 + b) (b * (r + 1)) 0 x.2.2))⟩

/-- Projectors on two adjacent windows starting at `0` commute. -/
private theorem rj_jwAt_comm_familyStep (n a c : ℕ) :
    jwAt n 0 a * jwAt n a c = jwAt n a c * jwAt n 0 a :=
  (jwAt_mul_eq_mul_jwAt n n a a (jwAt n 0 a) c fun l _ ↦
    (jwAt_commute_tlGenF n 0 a (a + l) (Or.inr (by omega))).eq.symm).symm

/-- `f_b` on the second bundle is absorbed by `f_N ⊗ f_b` from the left. -/
private theorem rj_jwAt_mul_bundleProj_familyStep (N b : ℕ) :
    jwAt (N + b) N b * rjBundleProj N b = rjBundleProj N b := by
  rw [rjBundleProj, ← Matrix.mul_assoc, ← rj_jwAt_comm_familyStep, Matrix.mul_assoc,
    jwAt_mul_self]

/-- `f_b` on the second bundle is absorbed by `f_N ⊗ f_b` from the right. -/
private theorem rj_bundleProj_mul_jwAt_familyStep (N b : ℕ) :
    rjBundleProj N b * jwAt (N + b) N b = rjBundleProj N b := by
  rw [rjBundleProj, Matrix.mul_assoc, jwAt_mul_self]

/-- The projector of the new bundle slides past a map placed on the old strands. -/
private theorem rj_jwAt_mul_skPlace_familyStep (b r N : ℕ) (π : SkMat (b * r) N) :
    jwAt (b * (r + 1)) (b * r) b * skPlace (b * (r + 1)) (N + b) 0 π =
      skPlace (b * (r + 1)) (N + b) 0 π * jwAt (N + b) N b := by
  have e : b * (r + 1) = b * r + b := Nat.mul_add_one b r
  rw [jwAt_eq_skPlace _ _ _ (by omega), jwAt_eq_skPlace (N + b) N b le_rfl]
  have h := skPlace_mul_skPlace_comm (b * (r + 1)) (N + b) (b * (r + 1)) (N + b) 0 (b * r) π
    (jwAt b 0 b) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [show b * r + N - b * r = N by omega] at h
  exact h.symm

/-- The projector of the new bundle slides past a map placed on the old strands (inclusion). -/
private theorem rj_jwAt_mul_skPlace_incl_familyStep (b r N : ℕ) (ι : SkMat N (b * r)) :
    jwAt (N + b) N b * skPlace (N + b) (b * (r + 1)) 0 ι =
      skPlace (N + b) (b * (r + 1)) 0 ι * jwAt (b * (r + 1)) (b * r) b := by
  have e : b * (r + 1) = b * r + b := Nat.mul_add_one b r
  rw [jwAt_eq_skPlace _ (b * r) _ (by omega), jwAt_eq_skPlace (N + b) N b le_rfl]
  have h := skPlace_mul_skPlace_comm (N + b) (b * (r + 1)) (N + b) (b * (r + 1)) 0 N ι
    (jwAt b 0 b) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [show N + b * r - N = b * r by omega] at h
  exact h.symm

/-- Placement on the first strands is multiplicative. -/
private theorem rj_skPlace_mul_familyStep (b : ℕ) {m p q : ℕ} (M P Q : ℕ) (hM : M = m + b)
    (hP : P = p + b) (hQ : Q = q + b) (X : SkMat m p) (Y : SkMat p q) :
    skPlace M P 0 X * skPlace P Q 0 Y = skPlace M Q 0 (X * Y) :=
  (skPlace_mul M P Q 0 X Y (by omega) (by omega) (by omega)).symm

/-- Placement of the zero matrix. -/
private theorem rj_skPlace_zero_familyStep (n n' i k l : ℕ) :
    skPlace n n' i (0 : SkMat k l) = 0 := by
  have h := skPlace_smul n n' i 0 (0 : SkMat k l)
  rwa [zero_smul, zero_smul] at h

/-- A list sum over `List.range` is the `Finset.range` sum. -/
private theorem rj_list_sum_range_familyStep {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    (m : ℕ) : ((List.range m).map f).sum = ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
      List.map_singleton, List.sum_singleton]

/-- The channels of one fused pair sum to the placed product times the new projector. -/
private theorem rj_sum_channels_familyStep (b r N : ℕ) (π : SkMat (b * r) N)
    (ι : SkMat N (b * r)) (hπ : π * jwAt N 0 N = π) :
    ∑ j ∈ Finset.range (min N b + 1),
      (skPlace (b * (r + 1)) (N + b) 0 π * rjFusionProj N b j) *
        ((rjFusionDim N b j)⁻¹ • (rjFusionIncl N b j * skPlace (N + b) (b * (r + 1)) 0 ι)) =
      skPlace (b * (r + 1)) (b * (r + 1)) 0 (π * ι) * jwAt (b * (r + 1)) (b * r) b := by
  have hsum : ∑ j ∈ Finset.range (min N b + 1),
      (skPlace (b * (r + 1)) (N + b) 0 π * rjFusionProj N b j) *
        ((rjFusionDim N b j)⁻¹ • (rjFusionIncl N b j * skPlace (N + b) (b * (r + 1)) 0 ι)) =
      skPlace (b * (r + 1)) (N + b) 0 π * rjBundleProj N b *
        skPlace (N + b) (b * (r + 1)) 0 ι := by
    rw [rj_fusion_complete, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hsum, rjBundleProj, jwAt_eq_skPlace (N + b) 0 N (by omega), ← Matrix.mul_assoc,
    rj_skPlace_mul_familyStep b _ _ _ (Nat.mul_add_one b r) rfl rfl, hπ, Matrix.mul_assoc,
    rj_jwAt_mul_skPlace_incl_familyStep, ← Matrix.mul_assoc,
    rj_skPlace_mul_familyStep b _ _ _ (Nat.mul_add_one b r) rfl (Nat.mul_add_one b r)]

/-- The sum over the fused family. -/
private theorem rj_sum_familySucc_familyStep (b r : ℕ) (L : List (RJFusionPair (b * r)))
    (hL : ∀ x ∈ L, x.2.1 * jwAt x.1 0 x.1 = x.2.1) :
    ((rjFamilySucc b r L).map fun y ↦ y.2.1 * y.2.2).sum =
      skPlace (b * (r + 1)) (b * (r + 1)) 0 ((L.map fun x ↦ x.2.1 * x.2.2).sum) *
        jwAt (b * (r + 1)) (b * r) b := by
  induction L with
  | nil =>
    rw [List.map_nil, List.sum_nil, rj_skPlace_zero_familyStep, Matrix.zero_mul]
    rfl
  | cons x L ih =>
    have ih' := ih fun y hy ↦ hL y (List.mem_cons_of_mem _ hy)
    simp only [rjFamilySucc] at ih' ⊢
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih', List.map_cons, List.sum_cons,
      skPlace_add, Matrix.add_mul, List.map_map, rj_list_sum_range_familyStep]
    congr 1
    exact rj_sum_channels_familyStep b r x.1 x.2.1 x.2.2 (hL x List.mem_cons_self)

/-- The product of the eigenvalues of the old pair and of the channel. -/
private theorem rj_twistEigen_mul_twistRatio_familyStep (b r N j : ℕ) :
    rjTwistEigen b r N * rjTwistRatio N b j = rjTwistEigen b (r + 1) (N + b - 2 * j) := by
  have hN := kinkScalar_ne_zero N
  have hb := kinkScalar_ne_zero b
  rw [rjTwistEigen, rjTwistRatio, rjTwistEigen, pow_succ]
  field_simp

/-- The fused colour lies in the spectrum of `r + 1` bundles. -/
private theorem rj_mem_spec_familyStep (b r N j : ℕ) (hN : N ∈ rjSpec b r) (hj : j ≤ min N b) :
    N + b - 2 * j ∈ rjSpec b (r + 1) := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hN
  rw [Finset.mem_range] at hi
  have e : b * (r + 1) = b * r + b := Nat.mul_add_one b r
  refine Finset.mem_image.mpr ⟨i + j, Finset.mem_range.mpr ?_, ?_⟩
  · rw [e]
    omega
  · rw [e]
    omega

/-- The fused map absorbs the column projectors on the left. -/
private theorem rj_colsProj_mul_fused_familyStep (b r N j : ℕ) (π : SkMat (b * r) N)
    (hπ : rjColsProj b r * π = π) :
    rjColsProj b (r + 1) * (skPlace (b * (r + 1)) (N + b) 0 π * rjFusionProj N b j) =
      skPlace (b * (r + 1)) (N + b) 0 π * rjFusionProj N b j := by
  have e : b * (r + 1) = b * r + b := Nat.mul_add_one b r
  rw [rjColsProj_succ, Matrix.mul_assoc, ← Matrix.mul_assoc (jwAt _ _ _),
    rj_jwAt_mul_skPlace_familyStep]
  simp only [← Matrix.mul_assoc]
  rw [rj_skPlace_mul_familyStep b _ _ _ e e rfl, hπ, Matrix.mul_assoc,
    ← (rjFusionProj_absorb N b j).1, ← Matrix.mul_assoc (jwAt _ _ _),
    rj_jwAt_mul_bundleProj_familyStep]

/-- The fused inclusion absorbs the column projectors on the right. -/
private theorem rj_fused_mul_colsProj_familyStep (b r N j : ℕ) (ι : SkMat N (b * r))
    (hι : ι * rjColsProj b r = ι) :
    (rjFusionDim N b j)⁻¹ • (rjFusionIncl N b j * skPlace (N + b) (b * (r + 1)) 0 ι) *
        rjColsProj b (r + 1) =
      (rjFusionDim N b j)⁻¹ • (rjFusionIncl N b j * skPlace (N + b) (b * (r + 1)) 0 ι) := by
  have e : b * (r + 1) = b * r + b := Nat.mul_add_one b r
  rw [Matrix.smul_mul, rjColsProj_succ, Matrix.mul_assoc, ← Matrix.mul_assoc (skPlace _ _ _ ι),
    rj_skPlace_mul_familyStep b _ _ _ rfl e e, hι, ← rj_jwAt_mul_skPlace_incl_familyStep,
    ← Matrix.mul_assoc, ← (rjFusionIncl_absorb N b j).2, Matrix.mul_assoc _ (rjBundleProj N b),
    rj_bundleProj_mul_jwAt_familyStep]

/-- The fused map is an eigenvector of `c^(r+1)`. -/
private theorem rj_cycle_mul_fused_familyStep (b r N j : ℕ) (hj : j ≤ min N b)
    (π : SkMat (b * r) N) (hπN : RJNat π)
    (hπ : rjCycleMat b r ^ r * π = rjTwistEigen b r N • π) :
    rjCycleMat b (r + 1) ^ (r + 1) * (skPlace (b * (r + 1)) (N + b) 0 π * rjFusionProj N b j) =
      rjTwistEigen b (r + 1) (N + b - 2 * j) •
        (skPlace (b * (r + 1)) (N + b) 0 π * rjFusionProj N b j) := by
  have e : b * (r + 1) = b * r + b := Nat.mul_add_one b r
  have hT : rjFullTwist (b * r) b * skPlace (b * (r + 1)) (N + b) 0 π =
      skPlace (b * (r + 1)) (N + b) 0 π * rjFullTwist N b := hπN.2 b
  rw [rjCycleMat_pow_succ, Matrix.mul_assoc, ← Matrix.mul_assoc (rjFullTwist _ _), hT,
    Matrix.mul_assoc, rj_fullTwist_mul_fusionProj N b j hj, ← Matrix.mul_assoc,
    rj_skPlace_mul_familyStep b _ _ _ e e rfl, hπ, skPlace_smul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, mul_comm (rjTwistRatio N b j),
    rj_twistEigen_mul_twistRatio_familyStep]

/-- The fused inclusion is an eigenvector of `c^(r+1)`. -/
private theorem rj_fused_mul_cycle_familyStep (b r N j : ℕ) (hj : j ≤ min N b)
    (ι : SkMat N (b * r)) (hιN : RJNat ι)
    (hι : ι * rjCycleMat b r ^ r = rjTwistEigen b r N • ι) :
    (rjFusionDim N b j)⁻¹ • (rjFusionIncl N b j * skPlace (N + b) (b * (r + 1)) 0 ι) *
        rjCycleMat b (r + 1) ^ (r + 1) =
      rjTwistEigen b (r + 1) (N + b - 2 * j) •
        ((rjFusionDim N b j)⁻¹ • (rjFusionIncl N b j * skPlace (N + b) (b * (r + 1)) 0 ι)) := by
  have e : b * (r + 1) = b * r + b := Nat.mul_add_one b r
  have hT : rjFullTwist N b * skPlace (N + b) (b * (r + 1)) 0 ι =
      skPlace (N + b) (b * (r + 1)) 0 ι * rjFullTwist (b * r) b := hιN.2 b
  rw [Matrix.smul_mul, rjCycleMat_pow_succ, Matrix.mul_assoc, ← Matrix.mul_assoc (skPlace _ _ _ ι),
    rj_skPlace_mul_familyStep b _ _ _ rfl e e, hι, skPlace_smul, Matrix.smul_mul,
    Matrix.mul_smul, ← hT, ← Matrix.mul_assoc, rj_fusionIncl_mul_fullTwist N b j hj,
    Matrix.smul_mul, smul_smul, smul_smul, smul_smul,
    ← rj_twistEigen_mul_twistRatio_familyStep b r N j]
  congr 1
  ring

set_option linter.unusedVariables false in
/-- Fusing one more bundle preserves goodness. -/
theorem rj_goodFamily_succ (b r : ℕ) (hr : 1 ≤ r) (L : List (RJFusionPair (b * r)))
    (hL : RJGoodFamily b r L) : RJGoodFamily b (r + 1) (rjFamilySucc b r L) := by
  obtain ⟨hsum, hmem⟩ := hL
  refine ⟨?_, ?_⟩
  · rw [rj_sum_familySucc_familyStep b r L fun x hx ↦ (hmem x hx).2.2.2.2.1, hsum,
      rjColsProj_succ]
  · intro y hy
    simp only [rjFamilySucc, List.mem_flatMap, List.mem_map, List.mem_range] at hy
    obtain ⟨x, hx, j, hj, rfl⟩ := hy
    obtain ⟨hspec, hπN, hιN, hcπ, hπf, hfι, hιc, heπ, heι⟩ := hmem x hx
    have hj' : j ≤ min x.1 b := by omega
    refine ⟨rj_mem_spec_familyStep b r x.1 j hspec hj',
      rjNat_mul (rjNat_placeLeft b hπN) (rjNat_fusionProj x.1 b j hj'),
      rjNat_smul _ (rjNat_mul (rjNat_fusionIncl x.1 b j hj') (rjNat_placeLeft b hιN)),
      rj_colsProj_mul_fused_familyStep b r x.1 j x.2.1 hcπ, ?_, ?_,
      rj_fused_mul_colsProj_familyStep b r x.1 j x.2.2 hιc,
      rj_cycle_mul_fused_familyStep b r x.1 j hj' x.2.1 hπN heπ,
      rj_fused_mul_cycle_familyStep b r x.1 j hj' x.2.2 hιN heι⟩
    · rw [Matrix.mul_assoc, (rjFusionProj_absorb x.1 b j).2]
    · rw [Matrix.mul_smul, ← Matrix.mul_assoc, (rjFusionIncl_absorb x.1 b j).1]

end AJConjecture
