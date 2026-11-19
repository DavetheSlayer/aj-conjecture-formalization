import Mathlib
import AJFamily.Classical.TwistNormalFormGen

/-!
# The bound for the twist relation

Let `a, a₁ ∈ SL₂(ℂ)` with `c = a a₁⁻¹ a⁻¹ a₁` satisfy `a₁ c^m = c^m a`, with `a` and the
longitude `a² c⁻ᵐ a⁻¹ cᵐ a a₁⁻¹ a⁻¹` upper triangular. Then `(L - 1) B_m` vanishes at the
diagonal entries `(M, L)` of `a` and the longitude: if `a₁` is also upper triangular then
`L = 1`, and otherwise a shear conjugation brings the pair to the normal form of
`twist_normal_form_gen`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The entry `(i, j)` of `X` vanishes and its `(0, 0)` entry is `m`. -/
private def twistBoundGen_tri (i j : Fin 2) (X : Matrix.SpecialLinearGroup (Fin 2) ℂ) (m : ℂ) :
    Prop :=
  X.1 i j = 0 ∧ X.1 0 0 = m

/-- Triangular matrices are closed under products, and the first diagonal entry is
multiplicative. -/
private theorem twistBoundGen_tri_mul {i j : Fin 2} (hij : i ≠ j)
    {X Y : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m n : ℂ} (hX : twistBoundGen_tri i j X m)
    (hY : twistBoundGen_tri i j Y n) : twistBoundGen_tri i j (X * Y) (m * n) := by
  obtain ⟨hX0, rfl⟩ := hX
  obtain ⟨hY0, rfl⟩ := hY
  fin_cases i <;> fin_cases j <;>
    simp_all [twistBoundGen_tri, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Triangular matrices of determinant one are closed under inversion, which inverts the first
diagonal entry. -/
private theorem twistBoundGen_tri_inv {i j : Fin 2} (hij : i ≠ j)
    {X : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m : ℂ} (hX : twistBoundGen_tri i j X m) :
    twistBoundGen_tri i j X⁻¹ m⁻¹ := by
  obtain ⟨hX0, rfl⟩ := hX
  have hdet := X.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h11 : X.1 1 1 = (X.1 0 0)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    fin_cases i <;> fin_cases j <;> simp_all
  fin_cases i <;> fin_cases j <;>
    simp_all [twistBoundGen_tri, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- Triangular matrices are closed under powers. -/
private theorem twistBoundGen_tri_pow {i j : Fin 2} (hij : i ≠ j)
    {X : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m : ℂ} (hX : twistBoundGen_tri i j X m) (n : ℕ) :
    twistBoundGen_tri i j (X ^ n) (m ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ⟨by simp [hij], by simp⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact twistBoundGen_tri_mul hij ih hX

/-- The first diagonal entry of a triangular matrix of determinant one is nonzero. -/
private theorem twistBoundGen_tri_ne_zero {i j : Fin 2} (hij : i ≠ j)
    {X : Matrix.SpecialLinearGroup (Fin 2) ℂ} {m : ℂ} (hX : twistBoundGen_tri i j X m) : m ≠ 0 := by
  have h := (twistBoundGen_tri_mul hij hX (twistBoundGen_tri_inv hij hX)).2
  rw [mul_inv_cancel] at h
  rintro rfl
  simp at h

/-- For triangular `a`, `a₁` with the same first diagonal entry, the longitude has first
diagonal entry `1`. -/
private theorem twistBoundGen_tri_longitude (m : ℕ) {i j : Fin 2} (hij : i ≠ j)
    (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (M : ℂ) (ha : twistBoundGen_tri i j a M)
    (ha₁ : twistBoundGen_tri i j a₁ M) :
    (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
      a₁⁻¹ * a⁻¹).1 0 0 = 1 := by
  have hM : M ≠ 0 := twistBoundGen_tri_ne_zero hij ha
  have hc := twistBoundGen_tri_mul hij (twistBoundGen_tri_mul hij
    (twistBoundGen_tri_mul hij ha (twistBoundGen_tri_inv hij ha₁)) (twistBoundGen_tri_inv hij ha))
    ha₁
  have hc6 := twistBoundGen_tri_pow hij hc m
  have hl := twistBoundGen_tri_mul hij (twistBoundGen_tri_mul hij (twistBoundGen_tri_mul hij
    (twistBoundGen_tri_mul hij (twistBoundGen_tri_mul hij (twistBoundGen_tri_mul hij
    (twistBoundGen_tri_pow hij ha 2) (twistBoundGen_tri_inv hij hc6))
    (twistBoundGen_tri_inv hij ha)) hc6) ha) (twistBoundGen_tri_inv hij ha₁))
    (twistBoundGen_tri_inv hij ha)
  rw [hl.2]
  field_simp

/-- For triangular `a`, `a₁` satisfying the twist relation, the first diagonal entries agree. -/
private theorem twistBoundGen_tri_entry_eq (m : ℕ) {i j : Fin 2} (hij : i ≠ j)
    (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (μ μ₁ : ℂ) (ha : twistBoundGen_tri i j a μ)
    (ha₁ : twistBoundGen_tri i j a₁ μ₁)
    (hrel : a₁ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m = (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a) : μ₁ = μ := by
  have hm : μ ≠ 0 := twistBoundGen_tri_ne_zero hij ha
  have hm₁ : μ₁ ≠ 0 := twistBoundGen_tri_ne_zero hij ha₁
  have hc := twistBoundGen_tri_mul hij (twistBoundGen_tri_mul hij
    (twistBoundGen_tri_mul hij ha (twistBoundGen_tri_inv hij ha₁)) (twistBoundGen_tri_inv hij ha))
    ha₁
  have hc6 := twistBoundGen_tri_pow hij hc m
  have h1 := (twistBoundGen_tri_mul hij ha₁ hc6).2
  have h2 := (twistBoundGen_tri_mul hij hc6 ha).2
  rw [hrel] at h1
  have hX : μ * μ₁⁻¹ * μ⁻¹ * μ₁ = 1 := by field_simp
  have h3 := h1.symm.trans h2
  rw [hX, one_pow, mul_one, one_mul] at h3
  exact h3

/-- The family bound factors as `(L - 1) * B_m(M, L)`. -/
private theorem twistBoundGen_evalPoint_famBound (m : ℕ) (M L : ℂ) :
    evalPoint (mapC (famBound m)) (M, L) = (L - 1) * evalPoint (mapC (famB m)) (M, L) := by
  simp only [evalPoint, mapC, famBound, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one]

/-- For a pair in normal form, the longitude eigenvalue is `1` or `(M, L)` is a zero of `B_m`. -/
private theorem twistBoundGen_of_normal_form (m : ℕ) (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (M u r : ℂ) (hM : M ≠ 0) (ha : a.1 = !![M, u; 0, M⁻¹]) (ha₁ : a₁.1 = !![M, 0; r, M⁻¹])
    (hrel : a₁ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m = (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a) :
    (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
      a₁⁻¹ * a⁻¹).1 0 0 = 1 ∨
    evalPoint (mapC (famB m))
      (M, (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
        a₁⁻¹ * a⁻¹).1 0 0) = 0 := by
  by_cases hu : u = 0
  · left
    subst hu
    refine twistBoundGen_tri_longitude m (i := 0) (j := 1) (by decide) a a₁ M ?_ ?_
    · exact ⟨by rw [ha]; rfl, by rw [ha]; rfl⟩
    · exact ⟨by rw [ha₁]; rfl, by rw [ha₁]; rfl⟩
  · right
    have hrel' :
        a₁.1 * (a * a₁⁻¹ * a⁻¹ * a₁).1 ^ m = (a * a₁⁻¹ * a⁻¹ * a₁).1 ^ m * a.1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, hrel]
    have hc : (a * a₁⁻¹ * a⁻¹ * a₁).1 = a.1 * a₁.1.adjugate * a.1.adjugate * a₁.1 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    have h := (twist_normal_form_gen m M u r hM hu a.1 a₁.1 (a * a₁⁻¹ * a⁻¹ * a₁).1 ha ha₁ hc
      hrel').2
    have hl : (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
        a₁⁻¹ * a⁻¹).1 = a.1 ^ 2 * (a * a₁⁻¹ * a⁻¹ * a₁).1.adjugate ^ m * a.1.adjugate *
        (a * a₁⁻¹ * a⁻¹ * a₁).1 ^ m * a.1 * a₁.1.adjugate * a.1.adjugate := by
      rw [← inv_pow]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
        Matrix.SpecialLinearGroup.coe_inv]
    rw [hl]
    exact h

/-- The upper unitriangular element `[[1, x], [0, 1]]` of `SL₂(ℂ)`. -/
private def twistBoundGen_shear (x : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- Entries of the conjugate of `X` by the shear `[[1, x], [0, 1]]`. -/
private theorem twistBoundGen_shear_conj (x : ℂ) (X : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (MulAut.conj (twistBoundGen_shear x) X).1 =
      !![X.1 0 0 + x * X.1 1 0, X.1 0 1 + x * X.1 1 1 - x * (X.1 0 0 + x * X.1 1 0);
        X.1 1 0, X.1 1 1 - x * X.1 1 0] := by
  have h1 : (twistBoundGen_shear x).1 = !![1, x; 0, 1] := rfl
  have h2 : (twistBoundGen_shear x)⁻¹.1 = !![1, -x; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, h1, Matrix.adjugate_fin_two_of, neg_zero]
  rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

/-- The bound `(L - 1) B_m` for the twist relation `a₁ c^m = c^m a`. -/
theorem twist_bound_gen (m : ℕ) (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (ha : a.1 1 0 = 0)
    (hrel : a₁ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m = (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a)
    (hl : (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
      a₁⁻¹ * a⁻¹).1 1 0 = 0) :
    evalPoint (mapC (famBound m))
      (a.1 0 0, (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
        a₁⁻¹ * a⁻¹).1 0 0) = 0 := by
  rw [twistBoundGen_evalPoint_famBound]
  have hT : twistBoundGen_tri 1 0 a (a.1 0 0) := ⟨ha, rfl⟩
  have hM : a.1 0 0 ≠ 0 := twistBoundGen_tri_ne_zero (by decide) hT
  by_cases hr : a₁.1 1 0 = 0
  · have hT₁ : twistBoundGen_tri 1 0 a₁ (a₁.1 0 0) := ⟨hr, rfl⟩
    have h00 := twistBoundGen_tri_entry_eq m (by decide) a a₁ _ _ hT hT₁ hrel
    rw [h00] at hT₁
    rw [twistBoundGen_tri_longitude m (by decide) a a₁ _ hT hT₁, sub_self, zero_mul]
  · have h11 : a.1 1 1 = (a.1 0 0)⁻¹ := by
      have hdet := a.det_coe
      rw [Matrix.det_fin_two, ha, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    have htr : a₁.1 0 0 + a₁.1 1 1 = a.1 0 0 + (a.1 0 0)⁻¹ := by
      have h1 : a₁ = (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ :=
        eq_mul_inv_of_mul_eq hrel
      have h2 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℂ ↦ X.1.trace) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.trace_fin_two,
        Matrix.trace_fin_two, h11] at h2
      exact h2
    obtain ⟨x, hx⟩ : ∃ x : ℂ, x * a₁.1 1 0 = a.1 0 0 - a₁.1 0 0 :=
      ⟨_, div_mul_cancel₀ _ hr⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : MulAut (Matrix.SpecialLinearGroup (Fin 2) ℂ),
        φ = MulAut.conj (twistBoundGen_shear x) := ⟨_, rfl⟩
    have hφa : (φ a).1 = !![a.1 0 0, (φ a).1 0 1; 0, (a.1 0 0)⁻¹] := by
      rw [hφ, twistBoundGen_shear_conj, ha, h11]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hφa₁ : (φ a₁).1 = !![a.1 0 0, 0; a₁.1 1 0, (a.1 0 0)⁻¹] := by
      have h00 : (φ a₁).1 0 0 = a.1 0 0 := by
        rw [hφ, twistBoundGen_shear_conj]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
        linear_combination hx
      have h10 : (φ a₁).1 1 0 = a₁.1 1 0 := by
        rw [hφ, twistBoundGen_shear_conj]
        rfl
      have h11' : (φ a₁).1 1 1 = (a.1 0 0)⁻¹ := by
        rw [hφ, twistBoundGen_shear_conj]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linear_combination htr - hx
      have h01 : (φ a₁).1 0 1 = 0 := by
        have hdet := (φ a₁).det_coe
        rw [Matrix.det_fin_two, h00, h10, h11', mul_inv_cancel₀ hM] at hdet
        have h0 : (φ a₁).1 0 1 * a₁.1 1 0 = 0 := by linear_combination -hdet
        exact (mul_eq_zero.mp h0).resolve_right hr
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11']
    have hφrel : φ a₁ * (φ a * (φ a₁)⁻¹ * (φ a)⁻¹ * φ a₁) ^ m =
        (φ a * (φ a₁)⁻¹ * (φ a)⁻¹ * φ a₁) ^ m * φ a := by
      simpa only [map_mul, map_pow, map_inv] using congrArg φ hrel
    have hφl : φ (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
        a₁⁻¹ * a⁻¹) = φ a ^ 2 * ((φ a * (φ a₁)⁻¹ * (φ a)⁻¹ * φ a₁) ^ m)⁻¹ * (φ a)⁻¹ *
        (φ a * (φ a₁)⁻¹ * (φ a)⁻¹ * φ a₁) ^ m * φ a * (φ a₁)⁻¹ * (φ a)⁻¹ := by
      simp only [map_mul, map_pow, map_inv]
    have hl00 : (φ (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m *
        a * a₁⁻¹ * a⁻¹)).1 0 0 = (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ *
        (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a * a₁⁻¹ * a⁻¹).1 0 0 := by
      rw [hφ, twistBoundGen_shear_conj, hl]
      simp
    rw [hφl] at hl00
    rcases twistBoundGen_of_normal_form m (φ a) (φ a₁) _ _ _ hM hφa hφa₁ hφrel with h | h
    · rw [hl00] at h
      rw [h, sub_self, zero_mul]
    · rw [hl00] at h
      rw [h, mul_zero]

end AJConjecture
