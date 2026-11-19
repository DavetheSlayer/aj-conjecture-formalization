import Mathlib
import AJTwist.Classical.TwCPolysCheb

/-!
# The twist relation of negative index in normal form (crux of Unit C1)

Source: revision 5, Section 7.2 (`classical.tex`, "A containing equation for a signed filling"):
a filling of index `k` gives `T_k = 0`; for `k = -b < 0` the cleared equation is `C_b = 0`.

For `a = [[M, u], [0, M⁻¹]]`, `a₁ = [[M, 0], [z, M⁻¹]]` with `u ≠ 0`, let `c = a a₁⁻¹ a⁻¹ a₁` and
suppose `c^b a₁ = a c^b` (the relation `a₁ c^n = c^n a` with `n = -b`). Then the longitude
`a² c^b a⁻¹ c^(-b) a a₁⁻¹ a⁻¹` is upper triangular with eigenvalue `L` such that
`C_b(M, L) = 0`. This is `twist_normal_form_gen` (`AJFamily.Classical.TwistNormalFormGen`) for
the negative index.

Route (as `TwistNormalFormGen`, with `v = u z`, `t = tr c`): `c a₁ - a c = α' (a₁ - a)` with
`α' = M² + v - 1 + M⁻² = t - α`; with `c^b = S_b c - S_(b-1)` the `(0, 1)` entry of the relation
gives the Riley equation `S_(b-1) = α' S_b`; `c^b = S_b (c - α')`, `c^(-b) = S_b ((t - α') - c)`;
the longitude without the factor `S_b²` has `(1, 0)` entry `0` and `(0, 0)` entry
`(M²v - M² + 1)² (M⁴ + M²v - 2M² + 1) / M⁴` (the same as for the positive index); Cassini gives
`S_b² (1 - t α' + α'²) = 1`, hence `(M² - 1)(1 - L) = v (M² + L)`; then
`(τ - A) Ŝ_b - k² Ŝ_(b-1) = 0` at `(M, L)`, which is `C_b(M, L) (M² + L) = 0`
(`evalPoint_twistPolyNeg_mul`). If `M² + L = 0` the displayed relation gives `M⁴ = 1` and
`C_b(M, -M²) = 0` by `evalPoint_twistPolyNeg_neg_sq`.

Checked: symbolically (`SCR/C/py/v1_negnf.py`: `α'`, the longitude entries, `L(v)`), and
numerically at 60 digits for `b ≤ 5` at generic `M` and at `M ∈ {1, -1, i, e^(iπ/3), e^(iπ/5)}`
(`SCR/C/py/v1_twist_num.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The trace of the commutator `c`, as a function of `M` and `v = u * z`. -/
private noncomputable def tr_twCTwistNFNeg (M v : ℂ) : ℂ :=
  M ^ 2 * v + v ^ 2 - 2 * v + 2 + v / M ^ 2

/-- The scalar `α` with `a₁ * c - c * a = α • (a₁ - a)`; the scalar of the negative index is
`α' = t - α`. -/
private noncomputable def al_twCTwistNFNeg (M v : ℂ) : ℂ :=
  M ^ 2 * v - M ^ 2 + v ^ 2 - 3 * v + 3 + v / M ^ 2 - 1 / M ^ 2

/-- The commutator `c` in explicit form. -/
private noncomputable def comm_twCTwistNFNeg (M u z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M ^ 2 * (u * z) + (u * z) ^ 2 - 2 * (u * z) + 1, M * u + u * (u * z) / M - u / M;
    M * z + (u * z) * z / M - z / M, 1 + u * z / M ^ 2]

/-- The commutator `a * a₁⁻¹ * a⁻¹ * a₁` equals the explicit matrix `comm_twCTwistNFNeg`. -/
private theorem comm_eq_twCTwistNFNeg (M u z : ℂ) (hM : M ≠ 0) :
    !![M, u; 0, M⁻¹] * (!![M, 0; z, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
      (!![M, u; 0, M⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate * !![M, 0; z, M⁻¹] =
      comm_twCTwistNFNeg M u z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm_twCTwistNFNeg, Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- Cayley–Hamilton for the commutator. -/
private theorem comm_mul_self_twCTwistNFNeg (M u z : ℂ) (hM : M ≠ 0) :
    comm_twCTwistNFNeg M u z * comm_twCTwistNFNeg M u z =
      tr_twCTwistNFNeg M (u * z) • comm_twCTwistNFNeg M u z - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm_twCTwistNFNeg, tr_twCTwistNFNeg, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The adjugate of the commutator is `t • 1 - c`. -/
private theorem comm_adjugate_twCTwistNFNeg (M u z : ℂ) :
    (comm_twCTwistNFNeg M u z).adjugate =
      tr_twCTwistNFNeg M (u * z) • 1 - comm_twCTwistNFNeg M u z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm_twCTwistNFNeg, tr_twCTwistNFNeg, Matrix.adjugate_fin_two_of] <;> ring

/-- The Riley equation of the negative index, read off from the `(0, 1)` entry of the
relation: `S_(b-1) = (t - α) S_b`. -/
private theorem riley_twCTwistNFNeg (M u z s₅ s₄ : ℂ) (hM : M ≠ 0) (hu : u ≠ 0)
    (h : (s₅ • comm_twCTwistNFNeg M u z - s₄ • 1) * !![M, 0; z, M⁻¹] =
      !![M, u; 0, M⁻¹] * (s₅ • comm_twCTwistNFNeg M u z - s₄ • 1)) :
    s₄ = (tr_twCTwistNFNeg M (u * z) - al_twCTwistNFNeg M (u * z)) * s₅ := by
  have h01 := congrFun (congrFun h 0) 1
  simp [comm_twCTwistNFNeg, Matrix.mul_apply, Fin.sum_univ_two] at h01
  unfold tr_twCTwistNFNeg al_twCTwistNFNeg
  field_simp at h01 ⊢
  linear_combination h01

/-- The entries of the longitude after removing the scalar factor. -/
private theorem longitude_entries_twCTwistNFNeg (M u z : ℂ) (hM : M ≠ 0)
    (a a₁ : Matrix (Fin 2) (Fin 2) ℂ) (ha : a = !![M, u; 0, M⁻¹])
    (ha₁ : a₁ = !![M, 0; z, M⁻¹]) :
    (a ^ 2 * (comm_twCTwistNFNeg M u z -
        (tr_twCTwistNFNeg M (u * z) - al_twCTwistNFNeg M (u * z)) • 1) *
      a.adjugate * (al_twCTwistNFNeg M (u * z) • 1 - comm_twCTwistNFNeg M u z) * a *
      a₁.adjugate * a.adjugate : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧
    M ^ 4 * (a ^ 2 * (comm_twCTwistNFNeg M u z -
        (tr_twCTwistNFNeg M (u * z) - al_twCTwistNFNeg M (u * z)) • 1) *
      a.adjugate * (al_twCTwistNFNeg M (u * z) • 1 - comm_twCTwistNFNeg M u z) * a *
      a₁.adjugate * a.adjugate : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      (M ^ 2 * (u * z) - M ^ 2 + 1) *
        ((M ^ 2 * (u * z) - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * (u * z) - 2 * M ^ 2 + 1)) := by
  subst ha ha₁
  constructor
  · simp [comm_twCTwistNFNeg, tr_twCTwistNFNeg, al_twCTwistNFNeg, Matrix.adjugate_fin_two_of,
      Matrix.one_fin_two, pow_two]
    left
    field_simp
    ring
  · simp [comm_twCTwistNFNeg, tr_twCTwistNFNeg, al_twCTwistNFNeg, Matrix.adjugate_fin_two_of,
      Matrix.one_fin_two, pow_two]
    field_simp
    ring

/-- `k² Ŝₙ = k^{n+1} Sₙ` for the homogenised Chebyshev sequence with `τ = k t`. -/
private theorem sq_mul_homCheb_twCTwistNFNeg (τ k t : ℂ) (h : τ = k * t) (n : ℕ) :
    k ^ 2 * homCheb τ k n = k ^ (n + 1) * homCheb t 1 n := by
  cases n with
  | zero => simp [homCheb]
  | succ n =>
    rw [homCheb_homog τ k t h n]
    ring

/-- The last step: with `τ = k t` and `A = k α`, the Riley equation `Sₙ = (t - α) Sₙ₊₁` gives
`(τ - A) Ŝₙ₊₁ - k² Ŝₙ = 0`. -/
private theorem final_twCTwistNFNeg (n : ℕ) (t α τ A k : ℂ) (hτ : τ = k * t) (hA : A = k * α)
    (hS : homCheb t 1 n = (t - α) * homCheb t 1 (n + 1)) :
    (τ - A) * homCheb τ k (n + 1) - k ^ 2 * homCheb τ k n = 0 := by
  rw [sq_mul_homCheb_twCTwistNFNeg τ k t hτ n, homCheb_homog τ k t hτ n, hA, hS, hτ]
  ring

/-- The relation `(M² - 1)(1 - L) = v (M² + L)` between the longitude eigenvalue and `v`. -/
private theorem star_twCTwistNFNeg (n : ℕ) (M v t α L : ℂ) (hM : M ≠ 0)
    (ht : M ^ 2 * t = M ^ 4 * v + M ^ 2 * v ^ 2 - 2 * M ^ 2 * v + 2 * M ^ 2 + v)
    (hα : M ^ 2 * α = M ^ 4 * v - M ^ 4 + M ^ 2 * v ^ 2 - 3 * M ^ 2 * v + 3 * M ^ 2 + v - 1)
    (hS : homCheb t 1 n = (t - α) * homCheb t 1 (n + 1))
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
    linear_combination hC + (α * S₁ - S₀) * hS
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

/-- The Riley equation and the formula for the longitude eigenvalue give a zero of `C_(n+1)`. -/
private theorem scalar_twCTwistNFNeg (n : ℕ) (M v t α L : ℂ) (hM : M ≠ 0)
    (ht : M ^ 2 * t = M ^ 4 * v + M ^ 2 * v ^ 2 - 2 * M ^ 2 * v + 2 * M ^ 2 + v)
    (hα : M ^ 2 * α = M ^ 4 * v - M ^ 4 + M ^ 2 * v ^ 2 - 3 * M ^ 2 * v + 3 * M ^ 2 + v - 1)
    (hS : homCheb t 1 n = (t - α) * homCheb t 1 (n + 1))
    (hL : M ^ 4 * L = homCheb t 1 (n + 1) * homCheb t 1 (n + 1) *
      ((M ^ 2 * v - M ^ 2 + 1) *
        ((M ^ 2 * v - M ^ 2 + 1) * (M ^ 4 + M ^ 2 * v - 2 * M ^ 2 + 1)))) :
    evalPoint (mapC (twistPolyNeg (n + 1))) (M, L) = 0 := by
  have hstar := star_twCTwistNFNeg n M v t α L hM ht hα hS hL
  by_cases hQ : M ^ 2 + L = 0
  · obtain rfl : L = -M ^ 2 := by linear_combination hQ
    have hM4 : M ^ 4 - 1 = 0 := by linear_combination hstar
    rw [evalPoint_twistPolyNeg_neg_sq (n + 1) (by omega) M, hM4,
      zero_pow (by omega), mul_zero]
  · have hmul := evalPoint_twistPolyNeg_mul (n + 1) (by omega) M L
    rw [evalPoint_famK, evalPoint_famTau, evalPoint_famA, Nat.add_sub_cancel] at hmul
    refine (mul_eq_zero.mp (hmul.trans ?_)).resolve_right hQ
    dsimp only
    rw [hstar]
    generalize M ^ 2 + L = Q
    refine final_twCTwistNFNeg n t α _ _ _ ?_ ?_ hS
    · linear_combination (-Q ^ 2) * ht
    · linear_combination (-Q ^ 2) * hα

/-- The Riley equation and the longitude eigenvalue of the twist relation of negative index
`c^b a₁ = a c^b`, in normal form: the longitude is upper triangular and its eigenvalue is a
zero of `C_b`. -/
theorem twist_normal_form_neg (b : ℕ) (hb : 1 ≤ b) (M u z : ℂ) (hM : M ≠ 0) (hu : u ≠ 0)
    (a a₁ c : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : a = !![M, u; 0, M⁻¹]) (ha₁ : a₁ = !![M, 0; z, M⁻¹])
    (hc : c = a * a₁.adjugate * a.adjugate * a₁) (hrel : c ^ b * a₁ = a * c ^ b) :
    (a ^ 2 * c ^ b * a.adjugate * c.adjugate ^ b * a * a₁.adjugate * a.adjugate) 1 0 = 0 ∧
      evalPoint (mapC (twistPolyNeg b))
        (M, (a ^ 2 * c ^ b * a.adjugate * c.adjugate ^ b * a * a₁.adjugate * a.adjugate) 0 0)
          = 0 := by
  subst ha ha₁
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  rw [comm_eq_twCTwistNFNeg M u z hM] at hc
  subst hc
  have ht : M ^ 2 * tr_twCTwistNFNeg M (u * z) = M ^ 4 * (u * z) + M ^ 2 * (u * z) ^ 2 -
      2 * M ^ 2 * (u * z) + 2 * M ^ 2 + u * z := by
    unfold tr_twCTwistNFNeg
    field_simp
  have hα : M ^ 2 * al_twCTwistNFNeg M (u * z) = M ^ 4 * (u * z) - M ^ 4 +
      M ^ 2 * (u * z) ^ 2 - 3 * M ^ 2 * (u * z) + 3 * M ^ 2 + u * z - 1 := by
    unfold al_twCTwistNFNeg
    field_simp
  have hcc := comm_mul_self_twCTwistNFNeg M u z hM
  have hadj := comm_adjugate_twCTwistNFNeg M u z
  obtain ⟨h10, h00⟩ := longitude_entries_twCTwistNFNeg M u z hM _ _ rfl rfl
  set t := tr_twCTwistNFNeg M (u * z)
  set α := al_twCTwistNFNeg M (u * z)
  set C := comm_twCTwistNFNeg M u z
  have hcc' : C.adjugate * C.adjugate = t • C.adjugate - 1 := by
    rw [hadj]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hcc]
    module
  have hp := pow_succ_eq_homCheb _ _ hcc n
  have hp' := pow_succ_eq_homCheb _ _ hcc' n
  rw [hp] at hrel
  have hS := riley_twCTwistNFNeg M u z _ _ hM hu hrel
  set S₁ := homCheb t 1 (n + 1)
  set S₀ := homCheb t 1 n
  rw [hp, hp', hadj, hS,
    show S₁ • (t • (1 : Matrix (Fin 2) (Fin 2) ℂ) - C) -
      ((t - α) * S₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      S₁ • (α • (1 : Matrix (Fin 2) (Fin 2) ℂ) - C) by module,
    show S₁ • C - ((t - α) * S₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      S₁ • (C - (t - α) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) by module]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨by rw [h10, mul_zero], scalar_twCTwistNFNeg n M (u * z) t α _ hM ht hα hS ?_⟩
  rw [← h00]
  ring

end AJConjecture
