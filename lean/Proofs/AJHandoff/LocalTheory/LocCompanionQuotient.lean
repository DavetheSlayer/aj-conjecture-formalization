import Mathlib
import AJConjecture.QAlgOreResidueClass
import AJConjecture.QAlgOreCompanionDet
import AJHandoff.LocalTheory.LocJointRing

/-!
# Right factors give quotient difference modules

If `P = S ⋆ R` with `P`, `R` monic, then `D P ⊆ D R` and `D/DP → D/DR` is a quotient of left
modules. In the companion bases `1, u, …` its matrix is `Q = (ρ_0, …, ρ_{n-1})`, the residues of
`u^m` modulo `R` (`oreResidue`, the residues of the library's Theorem A), and the intertwining
relation reads `C_R τ(Q) = Q C_P` (`ρ_{m+1} = C_R τ(ρ_m)` by definition, and
`ρ_n = -∑_{k<n} p_k ρ_k` because the class of `P = S ⋆ R` modulo `R` is zero). The first
`deg R` columns of `Q` are the standard basis, so `Q` is surjective. Finally the companion matrix
of a monic operator with coefficients in `R₀` and unit constant coefficient lies in `GL(R₀)`:
this is (JL) for a scalar operator.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The matrix of the quotient map `D/DP → D/DR`: column `m` is the residue `ρ_m` of `u^m`
modulo `R`. -/
def oreResidueMatrix {A : Type*} [CommRing A] (τ : A →+* A) (R : A[X]) (n : ℕ) :
    Matrix (Fin R.natDegree) (Fin n) A :=
  Matrix.of fun k m ↦ oreResidue τ R m k

/-- The intertwining relation `C_R τ(Q) = Q C_P` of the quotient `D/DP → D/DR`. -/
theorem oreCompanion_mul_map_oreResidueMatrix {A : Type*} [CommRing A] (τ : A →+* A)
    {P S R : A[X]} (hP : P.Monic) (hR : R.Monic) (h : oreMul τ S R = P) :
    oreCompanion R * (oreResidueMatrix τ R P.natDegree).map τ =
      oreResidueMatrix τ R P.natDegree * oreCompanion P := by
  have hres : oreResidueClass τ R P = 0 := by rw [← h]; exact oreResidueClass_oreMul τ hR S
  have hrel : ∑ m ∈ Finset.range (P.natDegree + 1), P.coeff m • oreResidue τ R m = 0 := by
    rw [← hres]
    unfold oreResidueClass
    rw [Polynomial.sum_over_range P (f := fun m c ↦ c • oreResidue τ R m) fun m ↦ zero_smul _ _]
  ext k m
  simp only [Matrix.mul_apply, Matrix.map_apply, oreResidueMatrix, Matrix.of_apply]
  change oreResidue τ R ((m : ℕ) + 1) k = _
  by_cases hm : (m : ℕ) + 1 = P.natDegree
  · rw [Finset.sum_range_succ, hP.coeff_natDegree, one_smul] at hrel
    have hn := congrFun (eq_neg_of_add_eq_zero_right hrel) k
    rw [hm, hn]
    simp only [oreCompanion, Matrix.of_apply, hm, ↓reduceIte, Pi.neg_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_neg_distrib, mul_neg, neg_inj]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ oreResidue τ R j k * P.coeff j)]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  · have hlt : (m : ℕ) + 1 < P.natDegree := by have := m.isLt; omega
    rw [Finset.sum_eq_single ⟨(m : ℕ) + 1, hlt⟩]
    · simp [oreCompanion, hm]
    · intro j _ hj
      have hne : (j : ℕ) ≠ m + 1 := fun h' ↦ hj (Fin.ext h')
      simp [oreCompanion, hm, hne]
    · intro h'
      exact absurd (Finset.mem_univ _) h'

/-- The quotient map is surjective. -/
theorem surjective_mulVecLin_oreResidueMatrix {F : Type*} [Field F] (τ : F →+* F) (R : F[X])
    {n : ℕ} (hn : R.natDegree ≤ n) : Function.Surjective (oreResidueMatrix τ R n).mulVecLin := by
  intro w
  refine ⟨fun m ↦ if h : (m : ℕ) < R.natDegree then w ⟨m, h⟩ else 0, ?_⟩
  funext k
  rw [Matrix.mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, oreResidueMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single ⟨k, lt_of_lt_of_le k.isLt hn⟩]
  · simp [oreResidue_of_lt τ R k.isLt k]
  · intro j _ hj
    by_cases hjd : (j : ℕ) < R.natDegree
    · have hne : (k : ℕ) ≠ j := fun h' ↦ hj (Fin.ext h'.symm)
      simp [oreResidue_of_lt τ R hjd k, hne]
    · simp [hjd]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- (JL) for the companion matrix of a monic operator over `R₀` with unit constant coefficient. -/
theorem isJointRegular_oreCompanion {z₀ : ℂ} {P : (LocJointRing z₀)[X]} (hP : P.Monic)
    (hP0 : IsUnit (P.coeff 0)) :
    IsJointRegular z₀ (oreCompanion (P.map (algebraMap (LocJointRing z₀) LocField))) := by
  have hdeg : P.natDegree = (P.map (algebraMap (LocJointRing z₀) LocField)).natDegree :=
    (hP.natDegree_map _).symm
  refine ⟨Matrix.reindex (finCongr hdeg) (finCongr hdeg) (oreCompanion (A := LocJointRing z₀) P),
    ?_, ?_⟩
  · rw [Matrix.det_reindex_self, det_oreCompanion hP]
    refine IsUnit.mul (IsUnit.pow _ ?_) hP0
    exact IsUnit.of_mul_eq_one (-1 : LocJointRing z₀) (by ring)
  · ext k j
    simp only [oreCompanion, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.of_apply, finCongr_symm, finCongr_apply, Fin.val_cast, coeff_map, hdeg]
    split_ifs <;> simp

end AJConjecture
