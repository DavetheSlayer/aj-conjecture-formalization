import Mathlib
import AJConjecture.QAlgOreMulBasic
import AJConjecture.QAlgOreResidueBasic

/-!
# The residue class is semilinear for left multiplication by `L`

`oreResidueClass` is additive and commutes with left multiplication by constants; left
multiplication by `L` acts by `c ↦ C_R τ(c)` (from `L ⋆ ∑ q_j L^j = ∑ τ(q_j) L^(j+1)` and
`ρ_(j+1) = C_R τ(ρ_j)`); and the class of a monic `R` itself is `0`
(`∑_(j<d) R_j e_j + ρ_d = 0` with `ρ_d = C_R e_(d-1) = -∑_k R_k e_k`).
-/

open Polynomial

namespace AJConjecture

/-- The residue class is additive. -/
theorem oreResidueClass_add {A : Type*} [CommRing A] (τ : A →+* A) (R P Q : A[X]) :
    oreResidueClass τ R (P + Q) = oreResidueClass τ R P + oreResidueClass τ R Q := by
  unfold oreResidueClass
  exact Polynomial.sum_add_index P Q _ (fun m ↦ zero_smul _ _) fun m a b ↦ add_smul _ _ _

/-- The residue class commutes with left multiplication by constants. -/
theorem oreResidueClass_C_mul {A : Type*} [CommRing A] (τ : A →+* A) (R : A[X]) (c : A)
    (Q : A[X]) : oreResidueClass τ R (C c * Q) = c • oreResidueClass τ R Q := by
  unfold oreResidueClass
  rw [Polynomial.C_mul', Polynomial.sum_smul_index Q c (fun m c ↦ c • oreResidue τ R m)
    fun m ↦ zero_smul _ _]
  simp only [Polynomial.sum_def, Finset.smul_sum, mul_smul]

/-- The residue class of a monomial `a L^m` is `a ρ_m`. -/
private theorem oreResidueClass_monomial {A : Type*} [CommRing A] (τ : A →+* A) (R : A[X])
    (m : ℕ) (a : A) : oreResidueClass τ R (monomial m a) = a • oreResidue τ R m := by
  unfold oreResidueClass
  exact Polynomial.sum_monomial_index a _ (zero_smul _ _)

/-- Left multiplication by `L` acts on residue classes by `c ↦ C_R τ(c)`. -/
theorem oreResidueClass_oreMul_X {A : Type*} [CommRing A] (τ : A →+* A) (R Q : A[X]) :
    oreResidueClass τ R (oreMul τ X Q) =
      (oreCompanion R).mulVec fun k ↦ τ (oreResidueClass τ R Q k) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [oreMul_add_right, oreResidueClass_add, hp, hq, oreResidueClass_add, ← Matrix.mulVec_add]
    congr 1
    funext k
    simp only [Pi.add_apply, map_add]
  | monomial n a =>
    have hX : (X : A[X]) = monomial 1 1 := (Polynomial.monomial_one_one_eq_X).symm
    rw [hX, oreMul_monomial_monomial, oreResidueClass_monomial, oreResidueClass_monomial,
      Function.iterate_one, one_mul, add_comm 1 n]
    have h : (fun k ↦ τ ((a • oreResidue τ R n) k)) = τ a • fun k ↦ τ (oreResidue τ R n k) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [h, Matrix.mulVec_smul]
    rfl

/-- The residue `ρ_d` of `L^d`, `d` the degree of `R`, is `-∑_k R_k e_k`. -/
private theorem oreResidue_natDegree_apply {A : Type*} [CommRing A] (τ : A →+* A) (R : A[X])
    (k : Fin R.natDegree) : oreResidue τ R R.natDegree k = -R.coeff k := by
  obtain ⟨n, hn⟩ : ∃ n, R.natDegree = n + 1 := ⟨R.natDegree - 1, by have := k.isLt; omega⟩
  have hn' : n < R.natDegree := by omega
  have hres : oreResidue τ R R.natDegree = oreResidue τ R (n + 1) := congrArg _ hn
  rw [hres]
  change (oreCompanion R).mulVec (fun k ↦ τ (oreResidue τ R n k)) k = _
  simp only [Matrix.mulVec, dotProduct, oreResidue_of_lt τ R hn']
  rw [Finset.sum_eq_single ⟨n, hn'⟩]
  · simp [oreCompanion, hn]
  · intro j _ hj
    have hjn : (j : ℕ) ≠ n := fun h ↦ hj (Fin.ext h)
    simp [hjn]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The residue class of a monic `R` modulo itself is `0`. -/
theorem oreResidueClass_self {A : Type*} [CommRing A] (τ : A →+* A) {R : A[X]}
    (hR : R.Monic) : oreResidueClass τ R R = 0 := by
  funext k
  unfold oreResidueClass
  rw [Polynomial.sum_over_range R (f := fun m c ↦ c • oreResidue τ R m) fun m ↦ zero_smul _ _,
    Finset.sum_range_succ,
    hR.coeff_natDegree, one_smul, Pi.add_apply, Finset.sum_apply, Pi.zero_apply,
    oreResidue_natDegree_apply, Finset.sum_eq_single (k : ℕ)]
  · simp [oreResidue_of_lt τ R k.isLt k]
  · intro m hm hmk
    rw [Finset.mem_range] at hm
    simp [oreResidue_of_lt τ R hm k, Ne.symm hmk]
  · intro h
    exact absurd (Finset.mem_range.mpr k.isLt) h

end AJConjecture
