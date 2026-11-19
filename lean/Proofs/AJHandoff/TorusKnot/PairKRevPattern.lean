import Mathlib
import AJFamily.Classical.FamilyEval

/-!
# Pattern points: solving the twist relation backwards

At a zero `(M, L)` of `B_m` with `M ≠ 0`, `M⁴ ≠ 1` and `M² + L ≠ 0`, the normal form of
`twist_normal_form_gen` can be solved backwards (`exists_pattern_point`): with
`v = (M² - 1)(1 - L) / (M² + L)`, the matrices `a = [[M, 1], [0, M⁻¹]]` and
`a₁ = [[M, 0], [v, M⁻¹]]` satisfy the twist relation `a₁ c^m = c^m a` for
`c = a a₁⁻¹ a⁻¹ a₁` (non-scalar: `c₀₁ ≠ 0`), and the pattern longitude
`a² c^(-m) a⁻¹ c^m a a₁⁻¹ a⁻¹` is upper triangular with eigenvalue `L`.

Route. `B_m(M, L) = k^m (α S_m(t) - S_(m-1)(t))` with `k = M² (M² + L)²`, `t = tr c` and the
scalar `α` with `a₁ c - c a = α (a₁ - a)`, so the Riley equation `α S_m = S_(m-1)` holds; then
`a₁ c^m - c^m a = (α S_m - S_(m-1)) (a₁ - a) = 0`. The longitude entries are those computed in
`AJFamily.Classical.TwistNormalFormGen`; its eigenvalue `L'` satisfies
`(M² - 1)(1 - L') = v (M² + L')`, which determines `L' = L` since `M² - 1 + v ≠ 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The trace of the commutator `c`, as a function of `M` and `v`. -/
private def revPatTr (M v : ℂ) : ℂ := M ^ 2 * v + v ^ 2 - 2 * v + 2 + v / M ^ 2

/-- The scalar `α` with `a₁ * c - c * a = α • (a₁ - a)`. -/
private def revPatAl (M v : ℂ) : ℂ :=
  M ^ 2 * v - M ^ 2 + v ^ 2 - 3 * v + 3 + v / M ^ 2 - 1 / M ^ 2

/-- The commutator `c` for `a = [[M, 1], [0, M⁻¹]]`, `a₁ = [[M, 0], [v, M⁻¹]]`. -/
private def revPatC (M v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M ^ 2 * v + v ^ 2 - 2 * v + 1, M + v / M - 1 / M;
    M * v + v * v / M - v / M, 1 + v / M ^ 2]

private theorem revPatC_eq (M v : ℂ) (hM : M ≠ 0) :
    !![M, 1; 0, M⁻¹] * (!![M, 0; v, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate * !![M, 0; v, M⁻¹] =
      revPatC M v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [revPatC, Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

private theorem revPatC_mul_self (M v : ℂ) (hM : M ≠ 0) :
    revPatC M v * revPatC M v = revPatTr M v • revPatC M v - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [revPatC, revPatTr, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

private theorem revPatC_adjugate (M v : ℂ) :
    (revPatC M v).adjugate = revPatTr M v • 1 - revPatC M v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [revPatC, revPatTr, Matrix.adjugate_fin_two_of] <;> ring

/-- The defining identity of `α`: `a₁ c - c a = α (a₁ - a)`. -/
private theorem revPatC_twist (M v : ℂ) (hM : M ≠ 0) :
    !![M, 0; v, M⁻¹] * revPatC M v - revPatC M v * !![M, 1; 0, M⁻¹] =
      revPatAl M v • (!![M, 0; v, M⁻¹] - !![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [revPatC, revPatAl] <;>
    field_simp <;> ring

/-- The entries of the longitude after removing the scalar factor. -/
private theorem revPat_longitude_entries (M v : ℂ) (hM : M ≠ 0) :
    (!![M, 1; 0, M⁻¹] ^ 2 * ((revPatTr M v - revPatAl M v) • 1 - revPatC M v) *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (revPatC M v - revPatAl M v • 1) * !![M, 1; 0, M⁻¹] *
      (!![M, 0; v, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧
    M ^ 4 * (!![M, 1; 0, M⁻¹] ^ 2 * ((revPatTr M v - revPatAl M v) • 1 - revPatC M v) *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (revPatC M v - revPatAl M v • 1) * !![M, 1; 0, M⁻¹] *
      (!![M, 0; v, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      (M ^ 2 * v - M ^ 2 + 1) *
        ((M ^ 2 * v - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * v - 2 * M ^ 2 + 1)) := by
  constructor
  · simp [revPatC, revPatTr, revPatAl, Matrix.adjugate_fin_two_of, Matrix.one_fin_two, pow_two]
    left
    field_simp
    ring
  · simp [revPatC, revPatTr, revPatAl, Matrix.adjugate_fin_two_of, Matrix.one_fin_two, pow_two]
    field_simp
    ring

/-- `k² Ŝₙ = k^{n+1} Sₙ` for the homogenised Chebyshev sequence with `τ = k t`. -/
private theorem revPat_sq_mul_homCheb (τ k t : ℂ) (h : τ = k * t) (n : ℕ) :
    k ^ 2 * homCheb τ k n = k ^ (n + 1) * homCheb t 1 n := by
  cases n with
  | zero => simp [homCheb]
  | succ n =>
    rw [homCheb_homog τ k t h n]
    ring

/-- The Riley equation at a zero of `B_(n+1)` with `M ≠ 0`, `M² + L ≠ 0`. -/
private theorem revPat_riley (n : ℕ) {M L : ℂ} (hM : M ≠ 0) (hQ : M ^ 2 + L ≠ 0)
    (hB : evalPoint (mapC (famB (n + 1))) (M, L) = 0) :
    revPatAl M ((M ^ 2 - 1) * (1 - L) / (M ^ 2 + L)) *
        homCheb (revPatTr M ((M ^ 2 - 1) * (1 - L) / (M ^ 2 + L))) 1 (n + 1) =
      homCheb (revPatTr M ((M ^ 2 - 1) * (1 - L) / (M ^ 2 + L))) 1 n := by
  set v := (M ^ 2 - 1) * (1 - L) / (M ^ 2 + L) with hv
  set k := M ^ 2 * (M ^ 2 + L) ^ 2 with hk
  have hk0 : k ≠ 0 := mul_ne_zero (pow_ne_zero 2 hM) (pow_ne_zero 2 hQ)
  rw [evalPoint_famB, evalPoint_famK, evalPoint_famTau, evalPoint_famA, Nat.add_sub_cancel] at hB
  simp only at hB
  have hτ : M ^ 4 * ((M ^ 2 - 1) * (1 - L)) * (M ^ 2 + L) + M ^ 2 * ((M ^ 2 - 1) * (1 - L)) ^ 2 -
      2 * M ^ 2 * ((M ^ 2 - 1) * (1 - L)) * (M ^ 2 + L) + 2 * M ^ 2 * (M ^ 2 + L) ^ 2 +
      (M ^ 2 - 1) * (1 - L) * (M ^ 2 + L) = k * revPatTr M v := by
    rw [hk, revPatTr, hv]
    field_simp
  have hA : M ^ 4 * ((M ^ 2 - 1) * (1 - L)) * (M ^ 2 + L) - M ^ 4 * (M ^ 2 + L) ^ 2 +
      M ^ 2 * ((M ^ 2 - 1) * (1 - L)) ^ 2 - 3 * M ^ 2 * ((M ^ 2 - 1) * (1 - L)) * (M ^ 2 + L) +
      3 * M ^ 2 * (M ^ 2 + L) ^ 2 + (M ^ 2 - 1) * (1 - L) * (M ^ 2 + L) - (M ^ 2 + L) ^ 2 =
      k * revPatAl M v := by
    rw [hk, revPatAl, hv]
    field_simp
  rw [hτ, hA, ← hk, homCheb_homog _ k _ rfl n, revPat_sq_mul_homCheb _ k _ rfl n] at hB
  have h1 : k ^ (n + 1) * (revPatAl M v * homCheb (revPatTr M v) 1 (n + 1) -
      homCheb (revPatTr M v) 1 n) = 0 := by
    rw [← hB]
    ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hk0))

/-- The longitude eigenvalue `L'` determined by the Riley equation satisfies
`(M² - 1)(1 - L') = v (M² + L')`. -/
private theorem revPat_star (n : ℕ) (M v t α L : ℂ) (hM : M ≠ 0)
    (ht : M ^ 2 * t = M ^ 4 * v + M ^ 2 * v ^ 2 - 2 * M ^ 2 * v + 2 * M ^ 2 + v)
    (hα : M ^ 2 * α = M ^ 4 * v - M ^ 4 + M ^ 2 * v ^ 2 - 3 * M ^ 2 * v + 3 * M ^ 2 + v - 1)
    (hS : homCheb t 1 n = α * homCheb t 1 (n + 1))
    (hL : M ^ 4 * L = homCheb t 1 (n + 1) * homCheb t 1 (n + 1) *
      ((M ^ 2 * v - M ^ 2 + 1) *
        ((M ^ 2 * v - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * v - 2 * M ^ 2 + 1)))) :
    (M ^ 2 - 1) * (1 - L) = v * (M ^ 2 + L) := by
  have hC := homCheb_cassini t n
  set S₁ := homCheb t 1 (n + 1)
  set S₀ := homCheb t 1 n
  obtain ⟨K, hK⟩ : ∃ K : ℂ,
      K = (M ^ 2 * v - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * v - 2 * M ^ 2 + 1) := ⟨_, rfl⟩
  rw [← hK] at hL
  have h1 : S₁ ^ 2 * (1 - t * α + α ^ 2) = 1 := by
    linear_combination hC + (t * S₁ - α * S₁ - S₀) * hS
  have hD : M ^ 4 * (1 - t * α + α ^ 2) = -(M ^ 2 + v - 1) * K := by
    rw [hK]
    linear_combination (-(M ^ 2 * α)) * ht +
      (M ^ 2 * α + (M ^ 4 * v - M ^ 4 + M ^ 2 * v ^ 2 - 3 * M ^ 2 * v + 3 * M ^ 2 + v - 1) -
        (M ^ 4 * v + M ^ 2 * v ^ 2 - 2 * M ^ 2 * v + 2 * M ^ 2 + v)) * hα
  have hM4 : M ^ 4 ≠ 0 := pow_ne_zero 4 hM
  have hK0 : K ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hD
    rcases mul_eq_zero.mp hD with h | h
    · exact hM4 h
    · rw [h, mul_zero] at h1
      exact zero_ne_one h1
  have h2 : M ^ 4 * K * (v * (M ^ 2 + L) - (M ^ 2 - 1) * (1 - L)) = 0 := by
    linear_combination ((M ^ 2 + v - 1) * K) * hL +
      (S₁ ^ 2 * (M ^ 2 * v - M ^ 2 + 1) * K) * hD -
      ((M ^ 2 * v - M ^ 2 + 1) * K * M ^ 4) * h1
  have h3 := (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hM4 hK0)
  linear_combination -h3

/-- Pattern points: at a zero `(M, L)` of `B_m` with `M ≠ 0`, `M⁴ ≠ 1`, `M² + L ≠ 0`, matrices
`a` (upper triangular, eigenvalue `M`) and `a₁` with the twist relation, `c = a a₁⁻¹ a⁻¹ a₁`
non-scalar, and the pattern longitude upper triangular with eigenvalue `L`. -/
theorem exists_pattern_point (m : ℕ) (hm : 1 ≤ m) {M L : ℂ} (hM : M ≠ 0) (hM4 : M ^ 4 ≠ 1)
    (hQ : M ^ 2 + L ≠ 0) (hB : evalPoint (mapC (famB m)) (M, L) = 0) :
    ∃ a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ, a.1 1 0 = 0 ∧ a.1 0 0 = M ∧
      (a * a₁⁻¹ * a⁻¹ * a₁).1 0 1 ≠ 0 ∧
      a₁ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m = (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a ∧
      (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
        a₁⁻¹ * a⁻¹).1 1 0 = 0 ∧
      (a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ m)⁻¹ * a⁻¹ * (a * a₁⁻¹ * a⁻¹ * a₁) ^ m * a *
        a₁⁻¹ * a⁻¹).1 0 0 = L := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set v := (M ^ 2 - 1) * (1 - L) / (M ^ 2 + L) with hv
  have hvQ : v * (M ^ 2 + L) = (M ^ 2 - 1) * (1 - L) := by rw [hv]; field_simp
  have hMv : M ^ 2 - 1 + v ≠ 0 := by
    intro h0
    have : (M ^ 2 - 1 + v) * (M ^ 2 + L) = M ^ 4 - 1 := by linear_combination hvQ
    rw [h0, zero_mul] at this
    exact hM4 (by linear_combination -this)
  let a : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨!![M, 1; 0, M⁻¹], by
    simp [Matrix.det_fin_two, hM]⟩
  let a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨!![M, 0; v, M⁻¹], by
    simp [Matrix.det_fin_two, hM]⟩
  have ha : (a : Matrix (Fin 2) (Fin 2) ℂ) = !![M, 1; 0, M⁻¹] := rfl
  have ha₁ : (a₁ : Matrix (Fin 2) (Fin 2) ℂ) = !![M, 0; v, M⁻¹] := rfl
  have hc : ((a * a₁⁻¹ * a⁻¹ * a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = revPatC M v := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, ha, ha₁]
    exact revPatC_eq M v hM
  obtain ⟨h10, h00⟩ := revPat_longitude_entries M v hM
  set t := revPatTr M v
  set α := revPatAl M v
  set C := revPatC M v
  have hS : α * homCheb t 1 (n + 1) = homCheb t 1 n := revPat_riley n hM hQ hB
  set S₁ := homCheb t 1 (n + 1)
  set S₀ := homCheb t 1 n
  have hcc : C * C = t • C - 1 := revPatC_mul_self M v hM
  have hadj : C.adjugate = t • 1 - C := revPatC_adjugate M v
  have hcc' : C.adjugate * C.adjugate = t • C.adjugate - 1 := by
    rw [hadj]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hcc]
    module
  have hp : C ^ (n + 1) = S₁ • (C - α • 1) := by
    rw [pow_succ_eq_homCheb _ _ hcc n]
    change S₁ • C - S₀ • 1 = _
    rw [← hS]
    module
  have hp' : C.adjugate ^ (n + 1) = S₁ • ((t - α) • 1 - C) := by
    rw [pow_succ_eq_homCheb _ _ hcc' n]
    change S₁ • C.adjugate - S₀ • 1 = _
    rw [← hS, hadj]
    module
  have hlong : ((a ^ 2 * ((a * a₁⁻¹ * a⁻¹ * a₁) ^ (n + 1))⁻¹ * a⁻¹ *
      (a * a₁⁻¹ * a⁻¹ * a₁) ^ (n + 1) * a * a₁⁻¹ * a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = (S₁ * S₁) • (!![M, 1; 0, M⁻¹] ^ 2 * ((t - α) • 1 - C) *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate * (C - α • 1) * !![M, 1; 0, M⁻¹] *
      (!![M, 0; v, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.coe_pow, ha, ha₁]
    rw [revPatC_eq M v hM, Matrix.adjugate_pow, hp, hp']
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  refine ⟨a, a₁, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    simp only [C, revPatC, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    intro h0
    apply hMv
    field_simp at h0
    linear_combination h0
  · apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hc, ha, ha₁, hp]
    have htw := revPatC_twist M v hM
    rw [← sub_eq_zero]
    simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, smul_sub]
    rw [show S₁ • (!![M, 0; v, M⁻¹] * C) - S₁ • (α • !![M, 0; v, M⁻¹]) -
        (S₁ • (C * !![M, 1; 0, M⁻¹]) - S₁ • (α • !![M, 1; 0, M⁻¹])) =
        S₁ • ((!![M, 0; v, M⁻¹] * C - C * !![M, 1; 0, M⁻¹]) -
          α • (!![M, 0; v, M⁻¹] - !![M, 1; 0, M⁻¹])) by module, htw, sub_self, smul_zero]
  · rw [hlong, Matrix.smul_apply, h10, smul_zero]
  · rw [hlong, Matrix.smul_apply, smul_eq_mul]
    set L' := S₁ * S₁ * (!![M, 1; 0, M⁻¹] ^ 2 * ((t - α) • 1 - C) *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate * (C - α • 1) * !![M, 1; 0, M⁻¹] *
      (!![M, 0; v, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (!![M, 1; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    have ht : M ^ 2 * t = M ^ 4 * v + M ^ 2 * v ^ 2 - 2 * M ^ 2 * v + 2 * M ^ 2 + v := by
      simp only [t, revPatTr]
      field_simp
    have hα : M ^ 2 * α =
        M ^ 4 * v - M ^ 4 + M ^ 2 * v ^ 2 - 3 * M ^ 2 * v + 3 * M ^ 2 + v - 1 := by
      simp only [α, revPatAl]
      field_simp
    have hL' : M ^ 4 * L' = S₁ * S₁ * ((M ^ 2 * v - M ^ 2 + 1) *
        ((M ^ 2 * v - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * v - 2 * M ^ 2 + 1))) := by
      rw [← h00]
      ring
    have hstar := revPat_star n M v t α L' hM ht hα hS.symm hL'
    have : (M ^ 2 - 1 + v) * (L' - L) = 0 := by linear_combination -hstar - hvQ
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hMv)

end AJConjecture
