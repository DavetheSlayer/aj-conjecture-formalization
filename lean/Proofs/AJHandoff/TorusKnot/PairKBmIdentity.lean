import Mathlib
import AJFamily.Classical.FamilyPolynomials
import AJFamily.Quantum.TwistPoly

/-!
# The classical and the quantum `B_m` coincide

The classical twist factor `famB m` (from the companion's `SL₂` relation, `A Ŝ_m - k² Ŝ_{m-1}`)
and the quantum twist polynomial `twistPoly m` (from the transfer symbol) are the same polynomial
for every `m ≥ 1`: both satisfy `B_(m+2) = τ B_(m+1) - x² (L + x)⁴ B_m` with the same `τ` and the
same `B_1`, `B_2`. So the paper's single `B_m` is one object on both sides. (At `m = 0` they differ:
`famB 0 = 0`, `twistPoly 0 = 1`.)
-/

open Polynomial

namespace AJConjecture

/-- `Ẑ` written out in `ℤ[M][L]`. -/
private theorem zetaMoebiusM_eq :
    zetaMoebiusM = C (X ^ 4 + 1) * X ^ 2 - C (X ^ 8 - 2 * X ^ 6 - 2 * X ^ 4 - 2 * X ^ 2 + 1) * X
      + C (X ^ 4 * (X ^ 4 + 1)) := by
  simp only [zetaMoebiusM, symbolZetaMoebius, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.coe_compRingHom]
  simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.one_comp, Polynomial.ofNat_comp]
  have h1 : ((X : ℤ[X]) ^ 2) ^ 2 + 1 = X ^ 4 + 1 := by ring
  have h2 : ((X : ℤ[X]) ^ 2) ^ 4 - ((2 : ℕ) : ℤ[X]) * (X ^ 2) ^ 3 -
      ((2 : ℕ) : ℤ[X]) * (X ^ 2) ^ 2 - ((2 : ℕ) : ℤ[X]) * X ^ 2 + 1 =
        X ^ 8 - 2 * X ^ 6 - 2 * X ^ 4 - 2 * X ^ 2 + 1 := by
    push_cast; ring
  have h3 : ((X : ℤ[X]) ^ 2) ^ 2 = X ^ 4 := by ring
  rw [h2, h1, h3]

/-- The classical `τ` is the quantum `Ẑ`. -/
private theorem famTau_eq : famTau = zetaMoebiusM := by
  rw [zetaMoebiusM_eq]
  simp only [famTau, famX, famP, famQ, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat]
  ring

/-- The classical `A` is the quantum `B_1`. -/
private theorem famA_eq : famA = twistPoly 1 := by
  rw [twistPoly, zetaMoebiusM_eq]
  simp only [famA, famX, famP, famQ, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat]
  ring

/-- `k² = x² (L + x)⁴`. -/
private theorem famK_sq_eq : famK ^ 2 = C (X ^ 4) * (C (X ^ 2) + X) ^ 4 := by
  simp only [famK, famX, famQ, map_pow]
  ring

/-- The classical twist factors satisfy `B_(m+3) = τ B_(m+2) - k² B_(m+1)`. -/
private theorem famB_add_three (m : ℕ) :
    famB (m + 3) = famTau * famB (m + 2) - famK ^ 2 * famB (m + 1) := by
  simp only [famB, show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega,
    Nat.add_sub_cancel, homCheb]
  ring

/-- `famB m = twistPoly m` for `m ≥ 1`. -/
theorem famB_eq_twistPoly (m : ℕ) (hm : 1 ≤ m) : famB m = twistPoly m := by
  have h1 : famB 1 = twistPoly 1 := by
    rw [← famA_eq]
    simp only [famB, homCheb, Nat.sub_self, mul_one, mul_zero, sub_zero]
  have h2 : famB 2 = twistPoly 2 := by
    rw [twistPoly, ← famA_eq, ← famTau_eq, ← famK_sq_eq]
    simp only [famB, show (2 : ℕ) - 1 = 1 from rfl, homCheb, twistPoly]
    ring
  have key : ∀ n, famB (n + 1) = twistPoly (n + 1) ∧ famB (n + 2) = twistPoly (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h1, h2⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [famB_add_three, ih.1, ih.2, famTau_eq, famK_sq_eq]
      rfl
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact (key n).1

end AJConjecture
