import Mathlib
import AJTwist.TwDefs
import AJConjecture.ColoredJones
import AJConjecture.SkeinThickGenReverse
import AJConjecture.SkeinBracketTrace
import AJConjecture.SkeinThickCableBasic

/-!
# The coloured Jones function of the mirror image

`laurentBar` is the involution `t ↦ t⁻¹` of `ℤ[T;T⁻¹]`. For every closed braid `K`,
`coloredJones K.mirror n = laurentBar (coloredJones K n)`.

Route. The crossing matrices of `AJConjecture.bracket` satisfy
`Φ (crossingMatrix m (i, s)) = crossingMatrix m (i, !s)` for the ring automorphism `Φ` of matrices
"apply `laurentBar` to the entries and exchange `e_false ↔ e_true` in every tensor factor", and
the weight of the quantum trace is `Φ`-invariant: `bracket_mirrorWord`. The crossing matrices are
symmetric and the weight commutes with words, so the bracket is invariant under reversal of the
word (`bracket_reverse`). The cable of the mirror word is not the mirror of the cable (the
letters of a thick crossing come in the other order), but
`cableGen c (i, !s) = (mirrorWord (cableGen c (i, s))).reverse` and the matrix of a thick crossing
is symmetric (`braidMatrix_thickCross_transpose` with equal bundles, transported to
`ℤ[T;T⁻¹]` by the injective `laurentToField`): `bracket_cable_mirrorWord`. The writhe changes
sign and its absolute value does not, which gives `coloredJonesPos_mirror`.
-/

open LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The involution `t ↦ t⁻¹` of `ℤ[t, t⁻¹]`. -/
def laurentBar : ℤ[T;T⁻¹] ≃+* ℤ[T;T⁻¹] := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv

theorem laurentBar_T (n : ℤ) : laurentBar (T n : ℤ[T;T⁻¹]) = T (-n) :=
  LaurentPolynomial.invert_T n

theorem laurentBar_laurentBar (p : ℤ[T;T⁻¹]) : laurentBar (laurentBar p) = p :=
  LaurentPolynomial.involutive_invert p

/-- The bracket of a closed braid does not change when the word is reversed. -/
theorem bracket_reverse (m : ℕ) (w : BraidWord) : bracket m w.reverse = bracket m w := by
  apply laurentToField_injective
  rw [laurentToField_bracket, laurentToField_bracket, ← braidMatrix_transpose, qtr, qtr, skWeight,
    ← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.trace_mul_comm]

/-- The exchange `e_false ↔ e_true` in every tensor factor, on the states of `V^{⊗ m}`. -/
private def flipState_mirrorJones (m : ℕ) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  Equiv.piCongrRight fun _ ↦ Equiv.boolNot

/-- The ring automorphism of the matrices on `V^{⊗ m}`: `laurentBar` on the entries and the
exchange of the two basis vectors in every tensor factor. -/
private def barFlip_mirrorJones (m : ℕ) (A : Matrix (Fin m → Bool) (Fin m → Bool) ℤ[T;T⁻¹]) :
    Matrix (Fin m → Bool) (Fin m → Bool) ℤ[T;T⁻¹] :=
  (A.map laurentBar).submatrix (flipState_mirrorJones m) (flipState_mirrorJones m)

/-- The bar-and-exchange map is multiplicative. -/
private theorem barFlip_mul_mirrorJones (m : ℕ)
    (A B : Matrix (Fin m → Bool) (Fin m → Bool) ℤ[T;T⁻¹]) :
    barFlip_mirrorJones m (A * B) = barFlip_mirrorJones m A * barFlip_mirrorJones m B := by
  rw [barFlip_mirrorJones, barFlip_mirrorJones, barFlip_mirrorJones, Matrix.map_mul,
    Matrix.submatrix_mul_equiv]

/-- The bar-and-exchange map commutes with products of lists of matrices. -/
private theorem barFlip_list_prod_mirrorJones (m : ℕ)
    (l : List (Matrix (Fin m → Bool) (Fin m → Bool) ℤ[T;T⁻¹])) :
    barFlip_mirrorJones m l.prod = (l.map (barFlip_mirrorJones m)).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.prod_nil, barFlip_mirrorJones, Matrix.map_one _
      (map_zero _) (map_one _), Matrix.submatrix_one_equiv]
  | cons A l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, barFlip_mul_mirrorJones, ih]

/-- The trace of the bar-and-exchange image is the bar of the trace. -/
private theorem trace_barFlip_mirrorJones (m : ℕ)
    (A : Matrix (Fin m → Bool) (Fin m → Bool) ℤ[T;T⁻¹]) :
    Matrix.trace (barFlip_mirrorJones m A) = laurentBar (Matrix.trace A) := by
  simp only [Matrix.trace, barFlip_mirrorJones, Matrix.diag, Matrix.submatrix_apply,
    Matrix.map_apply, map_sum]
  exact Equiv.sum_comp (flipState_mirrorJones m) fun a ↦ laurentBar (A a a)

/-- The entries of the Temperley–Lieb generator are invariant under bar and exchange. -/
private theorem laurentBar_cupCapEntry_mirrorJones (a₀ a₁ b₀ b₁ : Bool) :
    laurentBar (cupCapEntry (!a₀) (!a₁) (!b₀) (!b₁)) = cupCapEntry a₀ a₁ b₀ b₁ := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    simp [cupCapEntry, laurentBar_T]

/-- The Temperley–Lieb generators are fixed by the bar-and-exchange map. -/
private theorem barFlip_tlGen_mirrorJones (m i : ℕ) :
    barFlip_mirrorJones m (tlGen m i) = tlGen m i := by
  refine Matrix.ext fun a b ↦ ?_
  simp only [barFlip_mirrorJones, Matrix.submatrix_apply, Matrix.map_apply, tlGen, Matrix.of_apply]
  by_cases h : i + 1 < m
  · rw [dite_eq_left h, dite_eq_left h]
    have hiff : (∀ k : Fin m, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 →
        flipState_mirrorJones m a k = flipState_mirrorJones m b k) ↔
        ∀ k : Fin m, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → a k = b k :=
      forall_congr' fun k ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
        Bool.not_inj_iff
    rw [if_congr hiff rfl rfl, apply_ite laurentBar, map_zero]
    by_cases hc : ∀ k : Fin m, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → a k = b k
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact laurentBar_cupCapEntry_mirrorJones _ _ _ _
    · rw [ite_eq_right hc, ite_eq_right hc]
  · rw [dite_eq_right h, dite_eq_right h, map_zero]

/-- The bar-and-exchange map sends a crossing matrix to that of the reversed crossing. -/
private theorem barFlip_crossingMatrix_mirrorJones (m : ℕ) (g : ℕ × Bool) :
    barFlip_mirrorJones m (crossingMatrix m g) = crossingMatrix m (g.1, !g.2) := by
  obtain ⟨i, s⟩ := g
  have htl := barFlip_tlGen_mirrorJones m i
  refine Matrix.ext fun a b ↦ ?_
  have h := congrFun (congrFun htl a) b
  simp only [barFlip_mirrorJones, Matrix.submatrix_apply, Matrix.map_apply] at h
  cases s <;>
    simp [barFlip_mirrorJones, crossingMatrix, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, h, laurentBar_T, apply_ite laurentBar]

/-- The weight of the quantum trace is fixed by the bar-and-exchange map. -/
private theorem barFlip_weight_mirrorJones (m : ℕ) :
    barFlip_mirrorJones m
        (Matrix.diagonal fun a : Fin m → Bool ↦ ∏ k, if a k then -T (-2) else -T 2) =
      Matrix.diagonal fun a : Fin m → Bool ↦ ∏ k, if a k then -T (-2) else -T 2 := by
  rw [barFlip_mirrorJones, Matrix.diagonal_map (map_zero _), Matrix.submatrix_diagonal_equiv]
  congr 1
  funext a
  simp only [Function.comp_apply, map_prod]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  change laurentBar (if (!a k) = true then -T (-2) else -T 2) = _
  cases a k <;> simp [laurentBar_T]

/-- The bracket of the mirror word. -/
theorem bracket_mirrorWord (m : ℕ) (w : BraidWord) :
    bracket m (mirrorWord w) = laurentBar (bracket m w) := by
  have hmap : (mirrorWord w).map (crossingMatrix m) =
      (w.map (crossingMatrix m)).map (barFlip_mirrorJones m) := by
    rw [mirrorWord, List.map_map, List.map_map]
    exact List.map_congr_left fun g _ ↦ (barFlip_crossingMatrix_mirrorJones m g).symm
  rw [bracket, bracket, ← trace_barFlip_mirrorJones, barFlip_mul_mirrorJones,
    barFlip_weight_mirrorJones, barFlip_list_prod_mirrorJones, hmap]

/-- The matrix of a cabled generator is symmetric. -/
private theorem braidMatrix_cableGen_transpose_mirrorJones (n c : ℕ) (g : ℕ × Bool) :
    (braidMatrix n (cableGen c g)).transpose = braidMatrix n (cableGen c g) := by
  rw [cableGen_eq_thickCross, braidMatrix_thickCross_transpose]

/-- The cabled generator of the reversed crossing is the reversed mirror word. -/
private theorem cableGen_not_mirrorJones (c : ℕ) (g : ℕ × Bool) :
    cableGen c (g.1, !g.2) = (mirrorWord (cableGen c g)).reverse := by
  obtain ⟨i, s⟩ := g
  cases s <;>
    simp [cableGen, mirrorWord, List.reverse_flatMap, List.map_flatMap, List.map_reverse,
      Function.comp_def]

/-- The matrix of the cable of the mirror word is the matrix of the mirror of the cable. -/
private theorem braidMatrix_cable_mirrorWord_mirrorJones (n c : ℕ) (w : BraidWord) :
    braidMatrix n (cable c (mirrorWord w)) = braidMatrix n (mirrorWord (cable c w)) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have h1 : cable c (mirrorWord (g :: w)) =
        cableGen c (g.1, !g.2) ++ cable c (mirrorWord w) := by
      simp [cable, mirrorWord]
    have h2 : mirrorWord (cable c (g :: w)) =
        mirrorWord (cableGen c g) ++ mirrorWord (cable c w) := by
      simp [cable, mirrorWord]
    have h3 : braidMatrix n (mirrorWord (cableGen c g)) =
        braidMatrix n (cableGen c (g.1, !g.2)) := by
      rw [← braidMatrix_cableGen_transpose_mirrorJones, braidMatrix_transpose,
        cableGen_not_mirrorJones, List.reverse_reverse]
    rw [h1, h2, braidMatrix_append, braidMatrix_append, ih, h3]

/-- The bracket of a cable of the mirror word. -/
theorem bracket_cable_mirrorWord (m c : ℕ) (w : BraidWord) :
    bracket (c * m) (cable c (mirrorWord w)) = laurentBar (bracket (c * m) (cable c w)) := by
  rw [← bracket_mirrorWord]
  apply laurentToField_injective
  rw [laurentToField_bracket, laurentToField_bracket, braidMatrix_cable_mirrorWord_mirrorJones]

theorem chebyshevBracket_mirrorWord (m : ℕ) (w : BraidWord) (k : ℕ) :
    chebyshevBracket m (mirrorWord w) k = laurentBar (chebyshevBracket m w k) := by
  simp only [chebyshevBracket, map_sum, map_zsmul, bracket_cable_mirrorWord]

theorem coloredJonesPos_mirror (K : BraidKnot) (k : ℕ) :
    coloredJonesPos K.mirror k = laurentBar (coloredJonesPos K k) := by
  have hw : K.mirror.word = mirrorWord K.word := rfl
  have hs : K.mirror.strands = K.strands := rfl
  rw [coloredJonesPos, coloredJonesPos, hw, hs, writhe_mirrorWord, Int.natAbs_neg, map_zsmul,
    map_mul, laurentBar_T, chebyshevBracket_mirrorWord, neg_neg, neg_mul, neg_neg]

/-- The coloured Jones function of the mirror image is the bar of the coloured Jones function. -/
theorem coloredJones_mirror (K : BraidKnot) (n : ℤ) :
    coloredJones K.mirror n = laurentBar (coloredJones K n) := by
  unfold coloredJones
  split_ifs
  · exact coloredJonesPos_mirror K _
  · rw [coloredJonesPos_mirror, map_neg]
  · exact (map_zero _).symm

end AJConjecture
