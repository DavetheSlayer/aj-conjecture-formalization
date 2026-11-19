import Mathlib
import AJConjecture.QAlgDetSumSmul

/-!
# The maximal minors of a quotient map

Let `O ⊆ F` and `τ` an endomorphism of `F`. A quotient of a difference module with matrix
`A ∈ GL_d(O)` onto one with matrix `B`, given by `Q ∈ F^{r×d}`, satisfies `B τ(Q) = Q A`. Its
`r × r` minors `Δ_s = det(Q columns s)`, `s : Fin r → Fin d`, generate an `O`-submodule `𝔟` of
`F` with `det B · τ(𝔟) = 𝔟`: the minors of `B τ(Q)` are `det B · τ(Δ_s)`, those of `Q A` lie in
`𝔟` by multilinearity (`det_sum_smul_eq_sum`), and conversely `Q = (Q A) A⁻¹`. This is the
determinant of the quotient lattice `Q O^d` of the source, taken over `O` itself rather than
over each meridian valuation ring; no freeness of the lattice is used. If `Q` is surjective some
minor is nonzero.
-/

namespace AJConjecture

/-- The `r × r` minor of `Q` on the columns `s`. -/
def quotMinor {F : Type*} [CommRing F] {r d : ℕ} (Q : Matrix (Fin r) (Fin d) F)
    (s : Fin r → Fin d) : F :=
  (Q.submatrix id s).det

/-- The minors of `M N` lie in the `O`-span of the minors of `M`, for `N` over `O`. -/
private theorem span_quotMinor_mul_le_quotMinors {O F : Type*} [CommRing O] [CommRing F]
    [Algebra O F] {r d : ℕ} (M : Matrix (Fin r) (Fin d) F) (N : Matrix (Fin d) (Fin d) O) :
    Submodule.span O (Set.range (quotMinor (M * N.map (algebraMap O F)))) ≤
      Submodule.span O (Set.range (quotMinor M)) := by
  rw [Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  have hM : quotMinor (M * N.map (algebraMap O F)) s =
      (Matrix.of fun k i ↦ ∑ j, (fun i j ↦ N j (s i)) i j • (fun j k ↦ M k j) j k).det := by
    rw [quotMinor]
    congr 1
    ext k i
    simp only [Matrix.submatrix_apply, id, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
      Algebra.smul_def, mul_comm]
  rw [hM, det_sum_smul_eq_sum]
  exact Submodule.sum_mem _ fun s' _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', rfl⟩)

/-- The minors of a quotient map span a semi-invariant `O`-submodule. -/
theorem span_det_mul_quotMinor_eq {O F : Type*} [CommRing O] [CommRing F] [Algebra O F]
    (τ : F →+* F) {r d : ℕ} {A : Matrix (Fin d) (Fin d) O} (hA : IsUnit A.det)
    {Q : Matrix (Fin r) (Fin d) F} {B : Matrix (Fin r) (Fin r) F}
    (h : B * Q.map τ = Q * A.map (algebraMap O F)) :
    Submodule.span O (Set.range fun s ↦ B.det * τ (quotMinor Q s)) =
      Submodule.span O (Set.range (quotMinor Q)) := by
  set A' := A.map (algebraMap O F)
  have hB : (fun s ↦ B.det * τ (quotMinor Q s)) = quotMinor (Q * A') := by
    funext s
    have hsub : (Q * A').submatrix id s = B * (Q.submatrix id s).map τ := by
      rw [← h]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, id]
    rw [quotMinor, quotMinor, hsub, Matrix.det_mul, RingHom.map_det]
    rfl
  have hQ : Q = (Q * A') * (A⁻¹).map (algebraMap O F) := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv A hA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  rw [hB]
  refine le_antisymm ?_ ?_
  · exact span_quotMinor_mul_le_quotMinors Q A
  · conv_lhs => rw [hQ]
    exact span_quotMinor_mul_le_quotMinors (Q * A') A⁻¹

/-- A surjective `Q` has a nonzero maximal minor. -/
theorem exists_quotMinor_ne_zero {F : Type*} [Field F] {r d : ℕ}
    {Q : Matrix (Fin r) (Fin d) F} (hQ : Function.Surjective Q.mulVecLin) :
    ∃ s, quotMinor Q s ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Q.mulVecLin
    (LinearMap.range_eq_top.2 hQ)
  set P := LinearMap.toMatrix' g
  have hQP : Q * P = 1 := by
    rw [← LinearMap.toMatrix'_toLin' Q, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
      LinearMap.toMatrix'_id]
  by_contra hcon
  push Not at hcon
  have hdet : (Q * P).det = 0 := by
    have hM : Q * P = Matrix.of fun k i ↦ ∑ j, P j i • (fun j k ↦ Q k j) j k := by
      ext k i
      simp only [Matrix.mul_apply, Matrix.of_apply, smul_eq_mul, mul_comm]
    rw [hM, det_sum_smul_eq_sum]
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    have := hcon s
    rw [quotMinor] at this
    change _ • (Q.submatrix id s).det = 0
    rw [this, smul_zero]
  rw [hQP, Matrix.det_one] at hdet
  exact one_ne_zero hdet

end AJConjecture
