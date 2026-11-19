import Mathlib
import AJFamily.Quantum.FamTransferCoeff
import AJFamily.Quantum.FamTransferDegree

/-!
# The polynomials of the transfer construction for an arbitrary pole window (Unit Q3)

Source: revision 5, Section 3.3 (`transfer.tex`, "The row in physical color"), eq. (adjoint),
(physicalrow). The window is `d = 2a + 3` for `a ≥ 0` and `d = 2b + 2` for `a = -b < 0`; the
library's construction (`AJFamily/Quantum/FamTransferPoly.lean`, `FamTransferCoeff.lean`) is the
case `d = 2m + 3`. With `x = q^N` and `J = q^j`:

* `twBasisPoly d q i = ∏_{r<i} (q^r - x)(x - q^(r+1) J) ∏_{i≤r<d} (x - q^(r+1))(q^r - x J)`, the
  cleared pole basis `Δ R_i` (times `∏_{r<d} q^r (x - q^(r+1))`);
* `twAdjoint d q = q^d x 𝒜_d`, the cleared adjoint of `𝒵` (eq. (adjoint));
* `twCheb d q k = (q^d x)^k S_k(𝒜_d)`, the adjoint trace polynomials;
* `twMatrix`, `twDet`, `twCoeff d q T`: the coefficient matrix of the basis in the monomials of
  `J`, its determinant, and the Cramer numerators of the solve `∑_i c_i Δ R_i = T` for an
  arbitrary target `T`.

For `d = 2m + 3` these are the library's `famBasisPoly`, `famAdjoint`, `famCheb`, `famMatrix`,
`famDet`, `famCoeff` (by `rfl`, except `famCheb`, whose exponent `4m + 5 = 2d - 1` is written
differently).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The basis polynomials `∏_{r<i} (q^r - x)(x - q^(r+1) J) ∏_{i≤r<d} (x - q^(r+1))(q^r - x J)`
of the pole window `d`. -/
def twBasisPoly {R : Type*} [CommRing R] (d : ℕ) (q : R) (i : ℕ) : R[X][X] :=
  (∏ r ∈ Finset.range i, (C (C (q ^ r) - X) * (C X - C (C (q ^ (r + 1))) * X))) *
    ∏ r ∈ Finset.Ico i d, (C (X - C (q ^ (r + 1))) * (C (C (q ^ r)) - C X * X))

/-- The adjoint `𝒜_d` of `𝒵` on numerators, multiplied by `q^d x` (eq. (adjoint)). -/
def twAdjoint {R : Type*} [CommRing R] (d : ℕ) (q : R) (n : R[X][X]) : R[X][X] :=
  C (C (q ^ d) * X) * X * n +
    divX (C (C (q ^ (d - 1)) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (d - 1))) - C X * X) *
        n.comp (C (C q) * X))

/-- The adjoint trace polynomials `(q^d x)^k S_k(𝒜_d)`: `S_0 = 2`, `S_1 = 𝒜_d`,
`S_(k+2) = 𝒜_d S_(k+1) - q⁻¹ S_k`. -/
def twCheb {R : Type*} [CommRing R] (d : ℕ) (q : R) : ℕ → R[X][X] → R[X][X]
  | 0, n => 2 * n
  | 1, n => twAdjoint d q n
  | k + 2, n =>
      twCheb d q (k + 1) (twAdjoint d q n) - C (C (q ^ (2 * d - 1)) * X ^ 2) * twCheb d q k n

/-- The coefficient matrix of the basis polynomials in the monomial basis of `J`. -/
def twMatrix {R : Type*} [CommRing R] (d : ℕ) (q : R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) R[X] :=
  Matrix.of fun k i ↦ (twBasisPoly d q i).coeff k

/-- The determinant of `twMatrix`. -/
def twDet {R : Type*} [CommRing R] (d : ℕ) (q : R) : R[X] :=
  (twMatrix d q).det

/-- The Cramer numerators of `twMatrix` for the coefficients of a target polynomial `T`. -/
def twCoeff {R : Type*} [CommRing R] (d : ℕ) (q : R) (T : R[X][X]) (i : Fin (d + 1)) : R[X] :=
  Matrix.cramer (twMatrix d q) (fun k ↦ T.coeff k) i

/-! ### The library's objects are the odd windows `d = 2m + 3` -/

theorem famBasisPoly_eq_twBasisPoly {R : Type*} [CommRing R] (m : ℕ) (q : R) (i : ℕ) :
    famBasisPoly m q i = twBasisPoly (2 * m + 3) q i := rfl

theorem famAdjoint_eq_twAdjoint {R : Type*} [CommRing R] (m : ℕ) (q : R) (n : R[X][X]) :
    famAdjoint m q n = twAdjoint (2 * m + 3) q n := rfl

theorem famCheb_eq_twCheb {R : Type*} [CommRing R] (m : ℕ) (q : R) (k : ℕ) (n : R[X][X]) :
    famCheb m q k n = twCheb (2 * m + 3) q k n := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero => rfl
  | one => rfl
  | more k ih0 ih1 =>
    rw [famCheb, twCheb, ih1, ih0, famAdjoint_eq_twAdjoint,
      show 2 * (2 * m + 3) - 1 = 4 * m + 5 by omega]

theorem famDet_eq_twDet {R : Type*} [CommRing R] (m : ℕ) (q : R) :
    famDet m q = twDet (2 * m + 3) q := rfl

theorem famCoeff_eq_twCoeff {R : Type*} [CommRing R] (m : ℕ) (q : R) (i : Fin (2 * m + 4)) :
    famCoeff m q i = twCoeff (2 * m + 3) q (famTarget m q) i := rfl

/-! ### Degrees in `J` -/

/-- The basis polynomials have degree at most `d` in `J`. -/
theorem natDegree_twBasisPoly_le {R : Type*} [CommRing R] (d : ℕ) (q : R) {i : ℕ}
    (hi : i ≤ d) : (twBasisPoly d q i).natDegree ≤ d := by
  unfold twBasisPoly
  have h1 : (∏ r ∈ Finset.range i,
      (C (C (q ^ r) - X) * (C X - C (C (q ^ (r + 1))) * X) : R[X][X])).natDegree ≤ i := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun r _ ↦ ?_).trans (by simp)
    compute_degree
  have h2 : (∏ r ∈ Finset.Ico i d,
      (C (X - C (q ^ (r + 1))) * (C (C (q ^ r)) - C X * X) : R[X][X])).natDegree ≤ d - i := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun r _ ↦ ?_).trans (by simp)
    compute_degree
  exact natDegree_mul_le.trans (by omega)

/-- The cubic factor `(1 - qJ)(x - qJ)(q^(d-1) - xJ)` of the cleared adjoint has degree at
most `3` in `J`. -/
private theorem natDegree_twAdjointCubic_le_windowPoly {R : Type*} [CommRing R] (d : ℕ) (q : R) :
    ((1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (d - 1))) - C X * X) :
      R[X][X]).natDegree ≤ 3 := by
  compute_degree

/-- The substitution `J ↦ qJ` does not raise the degree in `J`. -/
private theorem natDegree_comp_scaling_le_windowPoly {R : Type*} [CommRing R] (q : R)
    (n : R[X][X]) : (n.comp (C (C q) * X)).natDegree ≤ n.natDegree := by
  have hs : (C (C q) * X : R[X][X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  refine natDegree_comp_le.trans ?_
  exact (Nat.mul_le_mul_left _ hs).trans (by omega)

/-- The cleared adjoint raises the degree in `J` by at most two. -/
theorem natDegree_twAdjoint_le {R : Type*} [CommRing R] (d : ℕ) (q : R) (n : R[X][X]) {e : ℕ}
    (hn : n.natDegree ≤ e) : (twAdjoint d q n).natDegree ≤ e + 2 := by
  unfold twAdjoint
  refine natDegree_add_le_of_degree_le ?_ ?_
  · have hX : (C (C (q ^ d) * X) * X : R[X][X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    exact (natDegree_mul_le_of_le hX hn).trans (by omega)
  · rw [natDegree_divX_eq_natDegree_tsub_one]
    have hcomp := natDegree_comp_scaling_le_windowPoly q n
    have h : (C (C (q ^ (d - 1)) * X) * n -
        (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (d - 1))) - C X * X) *
          n.comp (C (C q) * X)).natDegree ≤ e + 3 := by
      refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by omega)) ?_)
      exact (natDegree_mul_le_of_le (natDegree_twAdjointCubic_le_windowPoly d q)
        (hcomp.trans hn)).trans (by omega)
    omega

/-- The `k`-th adjoint trace polynomial raises the degree in `J` by at most `2k`. -/
theorem natDegree_twCheb_le {R : Type*} [CommRing R] (d : ℕ) (q : R) (k : ℕ) (n : R[X][X])
    {e : ℕ} (hn : n.natDegree ≤ e) : (twCheb d q k n).natDegree ≤ e + 2 * k := by
  induction k using Nat.twoStepInduction generalizing n e with
  | zero =>
    rw [twCheb, two_mul]
    exact natDegree_add_le_of_degree_le (by omega) (by omega)
  | one =>
    rw [twCheb]
    exact natDegree_twAdjoint_le d q n hn
  | more k ih0 ih1 =>
    rw [twCheb]
    have h1 := ih1 (twAdjoint d q n) (natDegree_twAdjoint_le d q n hn)
    have h2 := ih0 n hn
    exact (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (by omega)))

end AJConjecture
