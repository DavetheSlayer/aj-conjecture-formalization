import Mathlib
import AJFamily.Classical.FamilyEval

/-!
# The twist relation in normal form

For `a = [[M, u], [0, M⁻¹]]` and `a₁ = [[M, 0], [z, M⁻¹]]` with `u ≠ 0`, let
`c = a a₁⁻¹ a⁻¹ a₁` and suppose `a₁ c^m = c^m a`. Writing `c^m` through the Chebyshev sequence of
the trace of `c`, the relation becomes the Riley equation, and the longitude is upper triangular
with eigenvalue `L` such that `B_m(M, L) = 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The trace of the commutator `c`, as a function of `M` and `v = u * z`. -/
private noncomputable def twistNFGen_tr (M v : ℂ) : ℂ :=
  M ^ 2 * v + v ^ 2 - 2 * v + 2 + v / M ^ 2

/-- The scalar `α` with `a₁ * c - c * a = α • (a₁ - a)`. -/
private noncomputable def twistNFGen_al (M v : ℂ) : ℂ :=
  M ^ 2 * v - M ^ 2 + v ^ 2 - 3 * v + 3 + v / M ^ 2 - 1 / M ^ 2

/-- The commutator `c` in explicit form. -/
private noncomputable def twistNFGen_C (M u z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M ^ 2 * (u * z) + (u * z) ^ 2 - 2 * (u * z) + 1, M * u + u * (u * z) / M - u / M;
    M * z + (u * z) * z / M - z / M, 1 + u * z / M ^ 2]

/-- The commutator `a * a₁⁻¹ * a⁻¹ * a₁` equals the explicit matrix `twistNFGen_C`. -/
private theorem twistNFGen_C_eq (M u z : ℂ) (hM : M ≠ 0) :
    !![M, u; 0, M⁻¹] * (!![M, 0; z, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (!![M, u; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate * !![M, 0; z, M⁻¹] =
      twistNFGen_C M u z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistNFGen_C, Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- Cayley–Hamilton for the commutator. -/
private theorem twistNFGen_C_mul_self (M u z : ℂ) (hM : M ≠ 0) :
    twistNFGen_C M u z * twistNFGen_C M u z =
      twistNFGen_tr M (u * z) • twistNFGen_C M u z - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistNFGen_C, twistNFGen_tr, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The adjugate of the commutator is `t • 1 - c`. -/
private theorem twistNFGen_C_adjugate (M u z : ℂ) :
    (twistNFGen_C M u z).adjugate = twistNFGen_tr M (u * z) • 1 - twistNFGen_C M u z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistNFGen_C, twistNFGen_tr, Matrix.adjugate_fin_two_of] <;> ring

/-- The Riley equation, read off from the `(0, 1)` entry of the relation. -/
private theorem twistNFGen_riley (M u z s₅ s₄ : ℂ) (hM : M ≠ 0) (hu : u ≠ 0)
    (h : !![M, 0; z, M⁻¹] * (s₅ • twistNFGen_C M u z - s₄ • 1) =
      (s₅ • twistNFGen_C M u z - s₄ • 1) * !![M, u; 0, M⁻¹]) :
    s₄ = twistNFGen_al M (u * z) * s₅ := by
  have h01 := congrFun (congrFun h 0) 1
  simp [twistNFGen_C, Matrix.mul_apply, Fin.sum_univ_two] at h01
  unfold twistNFGen_al
  field_simp at h01 ⊢
  linear_combination h01

/-- The entries of the longitude after removing the scalar factor. -/
private theorem twistNFGen_longitude_entries (M u z : ℂ) (hM : M ≠ 0)
    (a a₁ : Matrix (Fin 2) (Fin 2) ℂ) (ha : a = !![M, u; 0, M⁻¹])
    (ha₁ : a₁ = !![M, 0; z, M⁻¹]) :
    (a ^ 2 * ((twistNFGen_tr M (u * z) - twistNFGen_al M (u * z)) • 1 - twistNFGen_C M u z) *
      a.adjugate * (twistNFGen_C M u z - twistNFGen_al M (u * z) • 1) * a * a₁.adjugate *
      a.adjugate : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧
    M ^ 4 * (a ^ 2 *
      ((twistNFGen_tr M (u * z) - twistNFGen_al M (u * z)) • 1 - twistNFGen_C M u z) *
      a.adjugate * (twistNFGen_C M u z - twistNFGen_al M (u * z) • 1) * a * a₁.adjugate *
      a.adjugate : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      (M ^ 2 * (u * z) - M ^ 2 + 1) *
        ((M ^ 2 * (u * z) - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * (u * z) - 2 * M ^ 2 + 1)) := by
  subst ha ha₁
  constructor
  · simp [twistNFGen_C, twistNFGen_tr, twistNFGen_al, Matrix.adjugate_fin_two_of,
      Matrix.one_fin_two, pow_two]
    left
    field_simp
    ring
  · simp [twistNFGen_C, twistNFGen_tr, twistNFGen_al, Matrix.adjugate_fin_two_of,
      Matrix.one_fin_two, pow_two]
    field_simp
    ring

/-- `k² Ŝₙ = k^{n+1} Sₙ` for the homogenised Chebyshev sequence with `τ = k t`. -/
private theorem twistNFGen_sq_mul_homCheb (τ k t : ℂ) (h : τ = k * t) (n : ℕ) :
    k ^ 2 * homCheb τ k n = k ^ (n + 1) * homCheb t 1 n := by
  cases n with
  | zero => simp [homCheb]
  | succ n =>
    rw [homCheb_homog τ k t h n]
    ring

/-- The last step: with `τ = k t` and `A = k α`, the Riley equation `Sₙ = α Sₙ₊₁` gives
`A Ŝₙ₊₁ - k² Ŝₙ = 0`. -/
private theorem twistNFGen_final (n : ℕ) (t α τ A k : ℂ) (hτ : τ = k * t) (hA : A = k * α)
    (hS : homCheb t 1 n = α * homCheb t 1 (n + 1)) :
    A * homCheb τ k (n + 1) - k ^ 2 * homCheb τ k n = 0 := by
  rw [twistNFGen_sq_mul_homCheb τ k t hτ n, homCheb_homog τ k t hτ n, hA, hS]
  ring

/-- The Riley equation and the formula for the longitude eigenvalue give a zero of `B_{n+1}`. -/
private theorem twistNFGen_scalar (n : ℕ) (M v t α L : ℂ) (hM : M ≠ 0)
    (ht : M ^ 2 * t = M ^ 4 * v + M ^ 2 * v ^ 2 - 2 * M ^ 2 * v + 2 * M ^ 2 + v)
    (hα : M ^ 2 * α = M ^ 4 * v - M ^ 4 + M ^ 2 * v ^ 2 - 3 * M ^ 2 * v + 3 * M ^ 2 + v - 1)
    (hS : homCheb t 1 n = α * homCheb t 1 (n + 1))
    (hL : M ^ 4 * L = homCheb t 1 (n + 1) * homCheb t 1 (n + 1) *
      ((M ^ 2 * v - M ^ 2 + 1) *
        ((M ^ 2 * v - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * v - 2 * M ^ 2 + 1)))) :
    evalPoint (mapC (famB (n + 1))) (M, L) = 0 := by
  have hC := homCheb_cassini t n
  rw [evalPoint_famB, evalPoint_famK, evalPoint_famTau, evalPoint_famA, Nat.add_sub_cancel]
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
  have hstar : (M ^ 2 - 1) * (1 - L) = v * (M ^ 2 + L) := by
    have h2 : M ^ 4 * K * (v * (M ^ 2 + L) - (M ^ 2 - 1) * (1 - L)) = 0 := by
      linear_combination ((M ^ 2 + v - 1) * K) * hL +
        (S₁ ^ 2 * (M ^ 2 * v - M ^ 2 + 1) * K) * hD -
        ((M ^ 2 * v - M ^ 2 + 1) * K * M ^ 4) * h1
    have h3 := (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hM4 hK0)
    linear_combination -h3
  dsimp only
  rw [hstar]
  generalize M ^ 2 + L = Q
  refine twistNFGen_final n t α _ _ _ ?_ ?_ hS
  · linear_combination (-Q ^ 2) * ht
  · linear_combination (-Q ^ 2) * hα

/-- The Riley equation and the longitude eigenvalue of the twist relation `a₁ c^m = c^m a`, in
normal form: the longitude is upper triangular and its eigenvalue is a zero of `B_m`. -/
theorem twist_normal_form_gen (m : ℕ) (M u z : ℂ) (hM : M ≠ 0) (hu : u ≠ 0)
    (a a₁ c : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : a = !![M, u; 0, M⁻¹]) (ha₁ : a₁ = !![M, 0; z, M⁻¹])
    (hc : c = a * a₁.adjugate * a.adjugate * a₁) (hrel : a₁ * c ^ m = c ^ m * a) :
    (a ^ 2 * c.adjugate ^ m * a.adjugate * c ^ m * a * a₁.adjugate * a.adjugate) 1 0 = 0 ∧
      evalPoint (mapC (famB m))
        (M, (a ^ 2 * c.adjugate ^ m * a.adjugate * c ^ m * a * a₁.adjugate * a.adjugate) 0 0)
          = 0 := by
  subst ha ha₁
  obtain _ | n := m
  · exfalso
    have h01 := congrFun (congrFun hrel 0) 1
    simp at h01
    exact hu h01.symm
  rw [twistNFGen_C_eq M u z hM] at hc
  subst hc
  have ht : M ^ 2 * twistNFGen_tr M (u * z) = M ^ 4 * (u * z) + M ^ 2 * (u * z) ^ 2 -
      2 * M ^ 2 * (u * z) + 2 * M ^ 2 + u * z := by
    unfold twistNFGen_tr
    field_simp
  have hα : M ^ 2 * twistNFGen_al M (u * z) = M ^ 4 * (u * z) - M ^ 4 + M ^ 2 * (u * z) ^ 2 -
      3 * M ^ 2 * (u * z) + 3 * M ^ 2 + u * z - 1 := by
    unfold twistNFGen_al
    field_simp
  have hcc := twistNFGen_C_mul_self M u z hM
  have hadj := twistNFGen_C_adjugate M u z
  obtain ⟨h10, h00⟩ := twistNFGen_longitude_entries M u z hM _ _ rfl rfl
  set t := twistNFGen_tr M (u * z)
  set α := twistNFGen_al M (u * z)
  set C := twistNFGen_C M u z
  have hcc' : C.adjugate * C.adjugate = t • C.adjugate - 1 := by
    rw [hadj]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hcc]
    module
  have hp := pow_succ_eq_homCheb _ _ hcc n
  have hp' := pow_succ_eq_homCheb _ _ hcc' n
  rw [hp] at hrel
  have hS := twistNFGen_riley M u z _ _ hM hu hrel
  set S₁ := homCheb t 1 (n + 1)
  set S₀ := homCheb t 1 n
  rw [hp, hp', hadj, hS,
    show S₁ • (t • (1 : Matrix (Fin 2) (Fin 2) ℂ) - C) -
      (α * S₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      S₁ • ((t - α) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - C) by module,
    show S₁ • C - (α * S₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      S₁ • (C - α • (1 : Matrix (Fin 2) (Fin 2) ℂ)) by module]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨by rw [h10, mul_zero], twistNFGen_scalar n M (u * z) t α _ hM ht hα hS ?_⟩
  rw [← h00]
  ring

end AJConjecture
