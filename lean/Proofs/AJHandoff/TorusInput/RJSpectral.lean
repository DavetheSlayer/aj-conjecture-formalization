import Mathlib
import AJHandoff.TorusInput.RJFamilyExists

/-!
# The spectral decomposition of the cabled full twist (node RA2.4)

The eigenvalues `μ_N`, `N` in the spectrum, are pairwise distinct; with a good family `L`:
`P_N π_x = π_x` if `N_x = N` and `0` otherwise; `P_N = ∑_(N_x = N) π_x ι_x`; and
`f_b^{⊗ r} · nodal(c^r) = 0` (so `c^r` is diagonalizable on the image of `f_b^{⊗ r}`).

Route. Distinctness: as `rj_twistRatio_injOn` (`θ_N = (-1)^N t^(N(N+2))`, one parity). For a good
family: `aeval (c^r) p · π_x = p(μ_(N_x)) π_x` (induction on `p`, `Polynomial.induction_on`),
`f_b^{⊗ r} π_x = π_x`, and `Lagrange.basis` takes the value `δ` at the nodes
(`Lagrange.eval_basis_self`, `Lagrange.eval_basis_of_ne`); `f_b^{⊗ r}` commutes with `c^r`
(`rjCycleMat_mul_colsProj`). Then `P_N = P_N f_b^{⊗ r} = ∑_x P_N π_x ι_x`, and the nodal
polynomial vanishes at every `μ_(N_x)`. Compare `AJConjecture.SkeinChannelIdem` for the same
Lagrange algebra. Estimate 120–180 lines.
-/

noncomputable section

namespace AJConjecture

/-- The sign of a colour of the spectrum. -/
private theorem rj_neg_one_pow_sub_spectral (m i : ℕ) (h : 2 * i ≤ m) :
    (-1 : RatFunc ℚ) ^ (m - 2 * i) = (-1) ^ m := by
  conv_rhs => rw [show m = (m - 2 * i) + 2 * i from by omega, pow_add, pow_mul, neg_one_sq,
    one_pow, mul_one]

open Polynomial in
/-- A polynomial in `D` acts on a (rectangular) eigenvector of `D` by its value at the
eigenvalue. -/
private theorem rj_aeval_mul_of_eigen_spectral {m n : ℕ} (D : SkMat m m) (Q : SkMat m n)
    (d : RatFunc ℚ) (h : D * Q = d • Q) (p : (RatFunc ℚ)[X]) :
    aeval D p * Q = p.eval d • Q := by
  have hpow : ∀ k : ℕ, D ^ k * Q = d ^ k • Q := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mul, one_smul]
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, Matrix.mul_smul, ih, smul_smul, pow_succ']
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mul, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, Matrix.mul_assoc, hpow, eval_monomial, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul, smul_smul]

open Polynomial in
/-- An element commuting with `D` commutes with the polynomials in `D`. -/
private theorem rj_commute_aeval_spectral {A : Type*} [Ring A] [Algebra (RatFunc ℚ) A]
    (P D : A) (h : Commute P D) (p : (RatFunc ℚ)[X]) : Commute P (aeval D p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a P).mul_right (h.pow_right n)

/-- The column projectors commute with `c^r`. -/
private theorem rj_commute_colsProj_cyclePow_spectral (b r : ℕ) :
    Commute (rjColsProj b r) (rjCycleMat b r ^ r) :=
  Commute.pow_right (rjCycleMat_mul_colsProj b r).symm r

/-- The column projectors absorb the spectral idempotents on the right. -/
private theorem rj_isoProj_mul_colsProj_spectral (b r N : ℕ) :
    rjIsoProj b r N * rjColsProj b r = rjIsoProj b r N := by
  rw [rjIsoProj, mul_assoc,
    ← (rj_commute_aeval_spectral _ _ (rj_commute_colsProj_cyclePow_spectral b r) _).eq,
    ← mul_assoc, rjColsProj_mul_self]

/-- A polynomial in `c^r` applied to a member of a good family. -/
private theorem rj_aeval_mul_pair_spectral (b r : ℕ) (L : List (RJFusionPair (b * r)))
    (hL : RJGoodFamily b r L) (x : RJFusionPair (b * r)) (hx : x ∈ L)
    (p : Polynomial (RatFunc ℚ)) :
    rjColsProj b r * Polynomial.aeval (rjCycleMat b r ^ r) p * x.2.1 =
      p.eval (rjTwistEigen b r x.1) • x.2.1 := by
  rw [Matrix.mul_assoc, rj_aeval_mul_of_eigen_spectral _ _ _ (hL.2 x hx).2.2.2.2.2.2.2.1,
    Matrix.mul_smul, (hL.2 x hx).2.2.2.1]

/-- The eigenvalues of `c^r` on the colours of the spectrum are pairwise distinct. -/
theorem rj_twistEigen_injOn (b r : ℕ) : Set.InjOn (rjTwistEigen b r) (rjSpec b r) := by
  intro N hN N' hN' h
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hN)
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hN')
  rw [Finset.mem_range] at hi hi'
  have hb : kinkScalar b ^ r ≠ 0 := pow_ne_zero _ (kinkScalar_ne_zero b)
  rw [rjTwistEigen, rjTwistEigen, div_left_inj₀ hb, kinkScalar, kinkScalar,
    rj_neg_one_pow_sub_spectral _ _ (by omega), rj_neg_one_pow_sub_spectral _ _ (by omega)] at h
  have h2 := ratFuncX_zpow_injective (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h)
  have h3 : ((b * r - 2 * i : ℕ) : ℤ) = ((b * r - 2 * i' : ℕ) : ℤ) := by
    have h0 : (0 : ℤ) ≤ ((b * r - 2 * i : ℕ) : ℤ) := Int.natCast_nonneg _
    have h0' : (0 : ℤ) ≤ ((b * r - 2 * i' : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  exact_mod_cast h3

/-- The spectral idempotent on a member of a good family. -/
theorem rj_isoProj_mul_pair (b r N : ℕ) (L : List (RJFusionPair (b * r)))
    (hL : RJGoodFamily b r L) (hN : N ∈ rjSpec b r) (x : RJFusionPair (b * r)) (hx : x ∈ L) :
    rjIsoProj b r N * x.2.1 = if x.1 = N then x.2.1 else 0 := by
  rw [rjIsoProj, rj_aeval_mul_pair_spectral b r L hL x hx]
  split_ifs with h
  · rw [show rjTwistEigen b r x.1 = rjTwistEigen b r N from congrArg _ h,
      Lagrange.eval_basis_self (rj_twistEigen_injOn b r) hN, one_smul]
  · rw [Lagrange.eval_basis_of_ne (Ne.symm h) (hL.2 x hx).1, zero_smul]

/-- Left multiplication of a list sum by a selector. -/
private theorem rj_mul_sum_filter_spectral (b r N : ℕ) (P : SkMat (b * r) (b * r))
    (L : List (RJFusionPair (b * r)))
    (hP : ∀ x ∈ L, P * x.2.1 = if x.1 = N then x.2.1 else 0) :
    P * (L.map fun x ↦ x.2.1 * x.2.2).sum =
      ((L.filter fun x ↦ x.1 = N).map fun x ↦ x.2.1 * x.2.2).sum := by
  induction L with
  | nil => rw [List.map_nil, List.sum_nil, Matrix.mul_zero, List.filter_nil, List.map_nil,
      List.sum_nil]
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, Matrix.mul_add, ← Matrix.mul_assoc,
      hP x List.mem_cons_self, ih fun y hy ↦ hP y (List.mem_cons_of_mem _ hy), List.filter_cons]
    by_cases h : x.1 = N
    · simp only [h, ite_true, decide_true, List.map_cons, List.sum_cons]
    · simp only [h, ite_false, decide_false, Matrix.zero_mul, zero_add]
      rfl

/-- The spectral idempotent is the sum of the members of a good family of its colour. -/
theorem rj_isoProj_eq_sum (b r N : ℕ) (L : List (RJFusionPair (b * r)))
    (hL : RJGoodFamily b r L) (hN : N ∈ rjSpec b r) :
    rjIsoProj b r N = ((L.filter fun x ↦ x.1 = N).map fun x ↦ x.2.1 * x.2.2).sum := by
  rw [← rj_isoProj_mul_colsProj_spectral, ← hL.1]
  exact rj_mul_sum_filter_spectral b r N _ L fun x hx ↦ rj_isoProj_mul_pair b r N L hL hN x hx

/-- The nodal polynomial of the eigenvalues annihilates `c^r` on the image of `f_b^{⊗ r}`. -/
theorem rj_colsProj_mul_aeval_nodal (b r : ℕ) (hr : 1 ≤ r) :
    rjColsProj b r * Polynomial.aeval (rjCycleMat b r ^ r)
      (Lagrange.nodal (rjSpec b r) (rjTwistEigen b r)) = 0 := by
  obtain ⟨L, hL⟩ := rj_goodFamily_exists b r hr
  have h : ∀ L' : List (RJFusionPair (b * r)), (∀ x ∈ L', x ∈ L) →
      rjColsProj b r * Polynomial.aeval (rjCycleMat b r ^ r)
        (Lagrange.nodal (rjSpec b r) (rjTwistEigen b r)) *
          (L'.map fun x ↦ x.2.1 * x.2.2).sum = 0 := by
    intro L' hL'
    induction L' with
    | nil => rw [List.map_nil, List.sum_nil, Matrix.mul_zero]
    | cons x L' ih =>
      rw [List.map_cons, List.sum_cons, Matrix.mul_add, ← Matrix.mul_assoc,
        rj_aeval_mul_pair_spectral b r L hL x (hL' x List.mem_cons_self),
        Lagrange.eval_nodal_at_node (hL.2 x (hL' x List.mem_cons_self)).1, zero_smul,
        Matrix.zero_mul, zero_add, ih fun y hy ↦ hL' y (List.mem_cons_of_mem _ hy)]
  have h' := h L fun x hx ↦ hx
  rw [hL.1, mul_assoc,
    ← (rj_commute_aeval_spectral _ _ (rj_commute_colsProj_cyclePow_spectral b r) _).eq,
    ← mul_assoc, rjColsProj_mul_self] at h'
  exact h'

open Polynomial in
/-- A polynomial in a square skein matrix `D` acts on a (rectangular) eigenvector of `D` by its
value at the eigenvalue. -/
theorem rj_aeval_mul_of_eigen {m n : ℕ} (D : SkMat m m) (Q : SkMat m n) (d : RatFunc ℚ)
    (h : D * Q = d • Q) (p : (RatFunc ℚ)[X]) : aeval D p * Q = p.eval d • Q :=
  rj_aeval_mul_of_eigen_spectral D Q d h p

open Polynomial in
/-- An element commuting with `D` commutes with the polynomials in `D`. -/
theorem rj_commute_aeval {A : Type*} [Ring A] [Algebra (RatFunc ℚ) A] (P D : A)
    (h : Commute P D) (p : (RatFunc ℚ)[X]) : Commute P (aeval D p) :=
  rj_commute_aeval_spectral P D h p

/-- The column projectors absorb the spectral idempotents on the right. -/
theorem rj_isoProj_mul_colsProj (b r N : ℕ) :
    rjIsoProj b r N * rjColsProj b r = rjIsoProj b r N :=
  rj_isoProj_mul_colsProj_spectral b r N

/-- The column projectors absorb the spectral idempotents on the left. -/
theorem rj_colsProj_mul_isoProj (b r N : ℕ) :
    rjColsProj b r * rjIsoProj b r N = rjIsoProj b r N := by
  rw [rjIsoProj, ← mul_assoc, rjColsProj_mul_self]

end AJConjecture
