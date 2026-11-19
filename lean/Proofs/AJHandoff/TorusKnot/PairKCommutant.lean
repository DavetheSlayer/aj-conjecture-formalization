import Mathlib

/-!
# The commutant of a non-scalar `2 × 2` matrix

A non-scalar `2 × 2` matrix `A` over a field has a cyclic vector, so every matrix commuting with
`A` is a polynomial `x + y A` in `A`; two such matrices commute. This is the step "the
centralizer of a nonscalar `ρ(C)` is abelian" of the classical note (§1). Route: write `A`
entrywise; `A B = B A` is a linear system in the entries of `B` of rank `2` when `A` is not
scalar; exhibit `x, y`.
-/

namespace AJConjecture

/-- A matrix commuting with a non-scalar `2 × 2` matrix `A` is of the form `x • 1 + y • A`. -/
private theorem exists_eq_smul_one_add_smul_of_commute_nonscalar {F : Type*} [Field F]
    {A B : Matrix (Fin 2) (Fin 2) F} (hA : ∀ a : F, A ≠ Matrix.scalar (Fin 2) a)
    (hB : Commute A B) : ∃ x y : F, B = x • (1 : Matrix (Fin 2) (Fin 2) F) + y • A := by
  have h := hB.eq
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · by_cases he : A 0 0 - A 1 1 = 0
      · exfalso
        apply hA (A 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc]
        linear_combination -he
      · simp only [hb, hc, zero_mul, mul_zero] at h00 h01 h10
        have h01' : B 0 1 = 0 := by
          have : B 0 1 * (A 0 0 - A 1 1) = 0 := by linear_combination h01
          simpa [he] using this
        have h10' : B 1 0 = 0 := by
          have : B 1 0 * (A 0 0 - A 1 1) = 0 := by linear_combination -h10
          simpa [he] using this
        refine ⟨B 1 1 - (B 0 0 - B 1 1) / (A 0 0 - A 1 1) * A 1 1,
          (B 0 0 - B 1 1) / (A 0 0 - A 1 1), ?_⟩
        ext i j
        fin_cases i <;> fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
            Matrix.one_apply_eq, smul_eq_mul, mul_one]
          field_simp
          ring
        · simp [hb, h01']
        · simp [hc, h10']
        · simp
    · simp only [hb, zero_mul, mul_zero] at h00 h01 h10
      have h01' : B 0 1 = 0 := by
        have : B 0 1 * A 1 0 = 0 := by linear_combination -h00
        simpa [hc] using this
      refine ⟨B 1 1 - B 1 0 / A 1 0 * A 1 1, B 1 0 / A 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one]
        field_simp
        linear_combination h10
      · simp [hb, h01']
      · simp [hc]
      · simp
  · refine ⟨B 1 1 - B 0 1 / A 0 1 * A 1 1, B 0 1 / A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one]
      field_simp
      linear_combination -h01
    · simp [hb]
    · simp
      field_simp
      linear_combination h00
    · simp

/-- Two matrices commuting with a non-scalar `2 × 2` matrix commute with each other. -/
theorem commute_of_commute_nonscalar {F : Type*} [Field F] {A B C : Matrix (Fin 2) (Fin 2) F}
    (hA : ∀ a : F, A ≠ Matrix.scalar (Fin 2) a) (hB : Commute A B) (hC : Commute A C) :
    Commute B C := by
  obtain ⟨x, y, rfl⟩ := exists_eq_smul_one_add_smul_of_commute_nonscalar hA hB
  obtain ⟨x', y', rfl⟩ := exists_eq_smul_one_add_smul_of_commute_nonscalar hA hC
  apply Commute.add_left <;> apply Commute.add_right <;>
    apply Commute.smul_left <;> apply Commute.smul_right <;> simp

end AJConjecture
