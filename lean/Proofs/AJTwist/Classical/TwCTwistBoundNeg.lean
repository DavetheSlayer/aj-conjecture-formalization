import Mathlib
import AJFamily.Classical.SatelliteData
import AJTwist.Classical.TwCTwistNFNeg

/-!
# The bound for the twist relation of negative index

Let `a, a₁ ∈ SL₂(ℂ)` with `c = a a₁⁻¹ a⁻¹ a₁` satisfy `c^b a₁ = a c^b` (`b ≥ 1`), with `a` and
the longitude `a² c^b a⁻¹ c^(-b) a a₁⁻¹ a⁻¹` upper triangular. Then `(L - 1) C_b` vanishes at
the diagonal entries `(M, L)` of `a` and the longitude, at every such point (no exceptional
meridian). This is `twist_bound_gen` (`AJFamily.Classical.TwistBoundGen`) for the index `-b`.

Route (as `TwistBoundGen`; its helper lemmas are private and are to be restated here): if `a₁`
is upper triangular the relation gives equal diagonal entries and `L = 1`; otherwise the trace
of `a₁` is that of `a` (the relation makes them conjugate) and a shear conjugation
`[[1, x], [0, 1]]` brings the pair to the normal form `a = [[M, u], [0, M⁻¹]]`,
`a₁ = [[M, 0], [r, M⁻¹]]`, keeping the `(0, 0)` and `(1, 0)` entries of the longitude; for
`u = 0` both are lower triangular with the same diagonal and `L = 1`; for `u ≠ 0` apply
`twist_normal_form_neg`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The entry `(i, j)` of `X` vanishes and its `(0, 0)` entry is `m`. -/
private def tri_twCTwistBoundNeg (i j : Fin 2) (X : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (m : ℂ) : Prop :=
  X.1 i j = 0 ∧ X.1 0 0 = m

/-- Triangular matrices are closed under products, and the first diagonal entry is
multiplicative. -/
private theorem tri_mul_twCTwistBoundNeg {i j : Fin 2} (hij : i ≠ j)
    {X Y : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m n : ℂ} (hX : tri_twCTwistBoundNeg i j X m)
    (hY : tri_twCTwistBoundNeg i j Y n) : tri_twCTwistBoundNeg i j (X * Y) (m * n) := by
  obtain ⟨hX0, rfl⟩ := hX
  obtain ⟨hY0, rfl⟩ := hY
  fin_cases i <;> fin_cases j <;>
    simp_all [tri_twCTwistBoundNeg, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Triangular matrices of determinant one are closed under inversion, which inverts the first
diagonal entry. -/
private theorem tri_inv_twCTwistBoundNeg {i j : Fin 2} (hij : i ≠ j)
    {X : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m : ℂ} (hX : tri_twCTwistBoundNeg i j X m) :
    tri_twCTwistBoundNeg i j X⁻¹ m⁻¹ := by
  obtain ⟨hX0, rfl⟩ := hX
  have hdet := X.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h11 : X.1 1 1 = (X.1 0 0)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    fin_cases i <;> fin_cases j <;> simp_all
  fin_cases i <;> fin_cases j <;>
    simp_all [tri_twCTwistBoundNeg, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- Triangular matrices are closed under powers. -/
private theorem tri_pow_twCTwistBoundNeg {i j : Fin 2} (hij : i ≠ j)
    {X : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m : ℂ} (hX : tri_twCTwistBoundNeg i j X m)
    (n : ℕ) : tri_twCTwistBoundNeg i j (X ^ n) (m ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ⟨by simp [hij], by simp⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact tri_mul_twCTwistBoundNeg hij ih hX

/-- The first diagonal entry of a triangular matrix of determinant one is nonzero. -/
private theorem tri_ne_zero_twCTwistBoundNeg {i j : Fin 2} (hij : i ≠ j)
    {X : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m : ℂ} (hX : tri_twCTwistBoundNeg i j X m) :
    m ≠ 0 := by
  have h := (tri_mul_twCTwistBoundNeg hij hX (tri_inv_twCTwistBoundNeg hij hX)).2
  rw [mul_inv_cancel] at h
  rintro rfl
  simp at h

/-- For triangular `a`, `a₁` with the same first diagonal entry, the longitude has first
diagonal entry `1`. -/
private theorem tri_longitude_twCTwistBoundNeg (b : ℕ) {i j : Fin 2} (hij : i ≠ j)
    (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (M : ℂ) (ha : tri_twCTwistBoundNeg i j a M)
    (ha₁ : tri_twCTwistBoundNeg i j a₁ M) :
    (a ^ 2 * (a * a₁⁻¹ * a⁻¹ * a₁) ^ b * a⁻¹ * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ b)⁻¹ * a *
      a₁⁻¹ * a⁻¹).1 0 0 = 1 := by
  have hM : M ≠ 0 := tri_ne_zero_twCTwistBoundNeg hij ha
  have hc := tri_mul_twCTwistBoundNeg hij (tri_mul_twCTwistBoundNeg hij
    (tri_mul_twCTwistBoundNeg hij ha (tri_inv_twCTwistBoundNeg hij ha₁))
    (tri_inv_twCTwistBoundNeg hij ha)) ha₁
  have hc6 := tri_pow_twCTwistBoundNeg hij hc b
  have hl := tri_mul_twCTwistBoundNeg hij (tri_mul_twCTwistBoundNeg hij
    (tri_mul_twCTwistBoundNeg hij (tri_mul_twCTwistBoundNeg hij (tri_mul_twCTwistBoundNeg hij
    (tri_mul_twCTwistBoundNeg hij (tri_pow_twCTwistBoundNeg hij ha 2) hc6)
    (tri_inv_twCTwistBoundNeg hij ha)) (tri_inv_twCTwistBoundNeg hij hc6)) ha)
    (tri_inv_twCTwistBoundNeg hij ha₁)) (tri_inv_twCTwistBoundNeg hij ha)
  rw [hl.2]
  field_simp

/-- For triangular `a`, `a₁` satisfying the twist relation, the first diagonal entries agree. -/
private theorem tri_entry_eq_twCTwistBoundNeg (b : ℕ) {i j : Fin 2} (hij : i ≠ j)
    (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (μ μ₁ : ℂ) (ha : tri_twCTwistBoundNeg i j a μ)
    (ha₁ : tri_twCTwistBoundNeg i j a₁ μ₁)
    (hrel : (a * a₁⁻¹ * a⁻¹ * a₁) ^ b * a₁ = a * (a * a₁⁻¹ * a⁻¹ * a₁) ^ b) : μ₁ = μ := by
  have hm : μ ≠ 0 := tri_ne_zero_twCTwistBoundNeg hij ha
  have hm₁ : μ₁ ≠ 0 := tri_ne_zero_twCTwistBoundNeg hij ha₁
  have hc := tri_mul_twCTwistBoundNeg hij (tri_mul_twCTwistBoundNeg hij
    (tri_mul_twCTwistBoundNeg hij ha (tri_inv_twCTwistBoundNeg hij ha₁))
    (tri_inv_twCTwistBoundNeg hij ha)) ha₁
  have hc6 := tri_pow_twCTwistBoundNeg hij hc b
  have h1 := (tri_mul_twCTwistBoundNeg hij hc6 ha₁).2
  have h2 := (tri_mul_twCTwistBoundNeg hij ha hc6).2
  rw [hrel] at h1
  have hX : μ * μ₁⁻¹ * μ⁻¹ * μ₁ = 1 := by field_simp
  have h3 := h1.symm.trans h2
  rw [hX, one_pow, mul_one, one_mul] at h3
  exact h3

/-- The value of `(L - 1) P` at a point. -/
private theorem evalPoint_sub_one_mul_twCTwistBoundNeg (P : ℤ[X][X]) (M L : ℂ) :
    evalPoint (mapC ((X - 1) * P)) (M, L) = (L - 1) * evalPoint (mapC P) (M, L) := by
  simp only [evalPoint, mapC, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one]

/-- For a pair in normal form, the longitude eigenvalue is `1` or `(M, L)` is a zero of `C_b`. -/
private theorem of_normal_form_twCTwistBoundNeg (b : ℕ) (hb : 1 ≤ b)
    (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (M u r : ℂ) (hM : M ≠ 0) (ha : a.1 = !![M, u; 0, M⁻¹]) (ha₁ : a₁.1 = !![M, 0; r, M⁻¹])
    (hrel : (a * a₁⁻¹ * a⁻¹ * a₁) ^ b * a₁ = a * (a * a₁⁻¹ * a⁻¹ * a₁) ^ b) :
    (a ^ 2 * (a * a₁⁻¹ * a⁻¹ * a₁) ^ b * a⁻¹ * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ b)⁻¹ * a *
      a₁⁻¹ * a⁻¹).1 0 0 = 1 ∨
    evalPoint (mapC (twistPolyNeg b))
      (M, (a ^ 2 * (a * a₁⁻¹ * a⁻¹ * a₁) ^ b * a⁻¹ * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ b)⁻¹ * a *
        a₁⁻¹ * a⁻¹).1 0 0) = 0 := by
  by_cases hu : u = 0
  · left
    subst hu
    refine tri_longitude_twCTwistBoundNeg b (i := 0) (j := 1) (by decide) a a₁ M ?_ ?_
    · exact ⟨by rw [ha]; rfl, by rw [ha]; rfl⟩
    · exact ⟨by rw [ha₁]; rfl, by rw [ha₁]; rfl⟩
  · right
    have hrel' :
        (a * a₁⁻¹ * a⁻¹ * a₁).1 ^ b * a₁.1 = a.1 * (a * a₁⁻¹ * a⁻¹ * a₁).1 ^ b := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, hrel]
    have hc : (a * a₁⁻¹ * a⁻¹ * a₁).1 = a.1 * a₁.1.adjugate * a.1.adjugate * a₁.1 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    have h := (twist_normal_form_neg b hb M u r hM hu a.1 a₁.1 (a * a₁⁻¹ * a⁻¹ * a₁).1 ha ha₁
      hc hrel').2
    have hl : (a ^ 2 * (a * a₁⁻¹ * a⁻¹ * a₁) ^ b * a⁻¹ * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ b)⁻¹ * a *
        a₁⁻¹ * a⁻¹).1 = a.1 ^ 2 * (a * a₁⁻¹ * a⁻¹ * a₁).1 ^ b * a.1.adjugate *
        (a * a₁⁻¹ * a⁻¹ * a₁).1.adjugate ^ b * a.1 * a₁.1.adjugate * a.1.adjugate := by
      rw [← inv_pow]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
        Matrix.SpecialLinearGroup.coe_inv]
    rw [hl]
    exact h

/-- The upper unitriangular element `[[1, x], [0, 1]]` of `SL₂(ℂ)`. -/
private def shear_twCTwistBoundNeg (x : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- Entries of the conjugate of `X` by the shear `[[1, x], [0, 1]]`. -/
private theorem shear_conj_twCTwistBoundNeg (x : ℂ) (X : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (MulAut.conj (shear_twCTwistBoundNeg x) X).1 =
      !![X.1 0 0 + x * X.1 1 0, X.1 0 1 + x * X.1 1 1 - x * (X.1 0 0 + x * X.1 1 0);
        X.1 1 0, X.1 1 1 - x * X.1 1 0] := by
  have h1 : (shear_twCTwistBoundNeg x).1 = !![1, x; 0, 1] := rfl
  have h2 : (shear_twCTwistBoundNeg x)⁻¹.1 = !![1, -x; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, h1, Matrix.adjugate_fin_two_of, neg_zero]
  rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

/-- A conjugate `Y⁻¹ X Y` has the trace of `X`. -/
private theorem trace_conj_twCTwistBoundNeg (X Y : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (Y⁻¹ * (X * Y)).1.trace = X.1.trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_assoc, mul_inv_cancel, mul_one]

/-- The shear that brings a pair with the same trace, `a` upper triangular and `a₁` not, to
the normal form. -/
private theorem exists_normal_form_twCTwistBoundNeg (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (ha : a.1 1 0 = 0) (hr : a₁.1 1 0 ≠ 0) (htr : a₁.1.trace = a.1.trace) :
    ∃ φ : MulAut (Matrix.SpecialLinearGroup (Fin 2) ℂ),
      (φ a).1 = !![a.1 0 0, (φ a).1 0 1; 0, (a.1 0 0)⁻¹] ∧
      (φ a₁).1 = !![a.1 0 0, 0; a₁.1 1 0, (a.1 0 0)⁻¹] ∧
      ∀ X : Matrix.SpecialLinearGroup (Fin 2) ℂ, X.1 1 0 = 0 → (φ X).1 0 0 = X.1 0 0 := by
  have hM : a.1 0 0 ≠ 0 :=
    tri_ne_zero_twCTwistBoundNeg (i := 1) (j := 0) (by decide) ⟨ha, rfl⟩
  have h11 : a.1 1 1 = (a.1 0 0)⁻¹ := by
    have hdet := a.det_coe
    rw [Matrix.det_fin_two, ha, mul_zero, sub_zero] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, h11] at htr
  obtain ⟨x, hx⟩ : ∃ x : ℂ, x * a₁.1 1 0 = a.1 0 0 - a₁.1 0 0 :=
    ⟨_, div_mul_cancel₀ _ hr⟩
  refine ⟨MulAut.conj (shear_twCTwistBoundNeg x), ?_, ?_, ?_⟩
  · rw [shear_conj_twCTwistBoundNeg, ha, h11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have h00 : (MulAut.conj (shear_twCTwistBoundNeg x) a₁).1 0 0 = a.1 0 0 := by
      rw [shear_conj_twCTwistBoundNeg]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      linear_combination hx
    have h10 : (MulAut.conj (shear_twCTwistBoundNeg x) a₁).1 1 0 = a₁.1 1 0 := by
      rw [shear_conj_twCTwistBoundNeg]
      rfl
    have h11' : (MulAut.conj (shear_twCTwistBoundNeg x) a₁).1 1 1 = (a.1 0 0)⁻¹ := by
      rw [shear_conj_twCTwistBoundNeg]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination htr - hx
    have h01 : (MulAut.conj (shear_twCTwistBoundNeg x) a₁).1 0 1 = 0 := by
      have hdet := (MulAut.conj (shear_twCTwistBoundNeg x) a₁).det_coe
      rw [Matrix.det_fin_two, h00, h10, h11', mul_inv_cancel₀ hM] at hdet
      have h0 : (MulAut.conj (shear_twCTwistBoundNeg x) a₁).1 0 1 * a₁.1 1 0 = 0 := by
        linear_combination -hdet
      exact (mul_eq_zero.mp h0).resolve_right hr
    rw [Matrix.eta_fin_two (MulAut.conj (shear_twCTwistBoundNeg x) a₁).1, h00, h01, h10, h11']
  · intro X hX
    rw [shear_conj_twCTwistBoundNeg, hX]
    simp

/-- The bound `(L - 1) C_b` for the twist relation `c^b a₁ = a c^b` of index `-b`. -/
theorem twist_bound_neg (b : ℕ) (hb : 1 ≤ b) (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (ha : a.1 1 0 = 0)
    (hrel : compMer a a₁ ^ b * a₁ = a * compMer a a₁ ^ b)
    (hl : (a ^ 2 * compMer a a₁ ^ b * a⁻¹ * (compMer a a₁ ^ b)⁻¹ * a * a₁⁻¹ * a⁻¹).1 1 0 = 0) :
    evalPoint (mapC ((X - 1) * twistPolyNeg b))
      (a.1 0 0, (a ^ 2 * compMer a a₁ ^ b * a⁻¹ * (compMer a a₁ ^ b)⁻¹ * a * a₁⁻¹ *
        a⁻¹).1 0 0) = 0 := by
  unfold compMer at hrel hl ⊢
  rw [evalPoint_sub_one_mul_twCTwistBoundNeg]
  have hT : tri_twCTwistBoundNeg 1 0 a (a.1 0 0) := ⟨ha, rfl⟩
  have hM : a.1 0 0 ≠ 0 := tri_ne_zero_twCTwistBoundNeg (by decide) hT
  by_cases hr : a₁.1 1 0 = 0
  · have hT₁ : tri_twCTwistBoundNeg 1 0 a₁ (a₁.1 0 0) := ⟨hr, rfl⟩
    have h00 := tri_entry_eq_twCTwistBoundNeg b (by decide) a a₁ _ _ hT hT₁ hrel
    rw [h00] at hT₁
    rw [tri_longitude_twCTwistBoundNeg b (by decide) a a₁ _ hT hT₁, sub_self, zero_mul]
  · have htr : a₁.1.trace = a.1.trace := by
      rw [eq_inv_mul_of_mul_eq hrel]
      exact trace_conj_twCTwistBoundNeg _ _
    obtain ⟨φ, hφa, hφa₁, hφ00⟩ := exists_normal_form_twCTwistBoundNeg a a₁ ha hr htr
    have hφrel : (φ a * (φ a₁)⁻¹ * (φ a)⁻¹ * φ a₁) ^ b * φ a₁ =
        φ a * (φ a * (φ a₁)⁻¹ * (φ a)⁻¹ * φ a₁) ^ b := by
      simpa only [map_mul, map_pow, map_inv] using congrArg φ hrel
    have hl00 := hφ00 _ hl
    simp only [map_mul, map_pow, map_inv] at hl00
    rcases of_normal_form_twCTwistBoundNeg b hb (φ a) (φ a₁) _ _ _ hM hφa hφa₁ hφrel with h | h
    · rw [hl00] at h
      rw [h, sub_self, zero_mul]
    · rw [hl00] at h
      rw [h, mul_zero]

end AJConjecture
