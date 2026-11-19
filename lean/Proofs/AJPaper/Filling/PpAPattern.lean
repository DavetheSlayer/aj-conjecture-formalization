import Mathlib
import AJHandoff.TorusKnot.PairKRevPattern
import AJHandoff.TorusKnot.PairKBmIdentity
import AJPaper.Filling.PpAPatternNeg

/-!
# Pattern points of every nonzero index (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`), first two paragraphs.

`ppa_exists_pattern_point`: for `n ≠ 0`, at a zero `(M, L)` of `𝒫_n = twP n` with `M ≠ 0`,
`M⁴ ≠ 1`, `M² + L ≠ 0` there are `a, a₁ ∈ SL₂(ℂ)`, `a` upper triangular with eigenvalue `M`,
with the filling relation `a₁ c^n = c^n a` for `c = compMer a a₁` (the paper's `Y = W^k`,
`P W^(-k) = W^(-k) Q₀`), and such that the pattern longitude
`a² c^(-n) a⁻¹ c^n a a₁⁻¹ a⁻¹` is upper triangular with eigenvalue `L`.

Route: `n = m > 0`: `exists_pattern_point m` with `famB_eq_twistPoly`, `twP_natCast`
(`zpow_natCast`); `n = -b < 0`: `ppa_exists_pattern_point_neg b` with `twP_neg_natCast`
(`zpow_neg`, `zpow_natCast`; `c^b a₁ = a c^b` is `a₁ c^(-b) = c^(-b) a`).

Checked numerically for `-6 ≤ n ≤ 6`, `n ≠ 0` (`SCR/A/py/patpoint.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Pattern points: at a generic zero `(M, L)` of `𝒫_n`, `n ≠ 0`, matrices `a`, `a₁` with the
filling relation of index `n` and pattern longitude of eigenvalue `L`. -/
theorem ppa_exists_pattern_point (n : ℤ) (hn : n ≠ 0) {M L : ℂ} (hM : M ≠ 0)
    (hM4 : M ^ 4 ≠ 1) (hQ : M ^ 2 + L ≠ 0) (hP : evalPoint (mapC (twP n)) (M, L) = 0) :
    ∃ a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ, a.1 1 0 = 0 ∧ a.1 0 0 = M ∧
      a₁ * compMer a a₁ ^ n = compMer a a₁ ^ n * a ∧
      (a ^ 2 * (compMer a a₁ ^ n)⁻¹ * a⁻¹ * compMer a a₁ ^ n * a * a₁⁻¹ * a⁻¹).1 1 0 = 0 ∧
      (a ^ 2 * (compMer a a₁ ^ n)⁻¹ * a⁻¹ * compMer a a₁ ^ n * a * a₁⁻¹ * a⁻¹).1 0 0 = L := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, n = -(b : ℤ) := ⟨n.natAbs, by omega⟩
    have hb : 1 ≤ b := by omega
    rw [twP_neg_natCast b hb] at hP
    obtain ⟨a, a₁, h1, h2, h3, h4, h5⟩ := ppa_exists_pattern_point_neg b hb hM hM4 hQ hP
    refine ⟨a, a₁, h1, h2, ?_, ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq]
      exact h3
    · rw [zpow_neg, zpow_natCast, inv_inv]
      exact h4
    · rw [zpow_neg, zpow_natCast, inv_inv]
      exact h5
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.natAbs, by omega⟩
    have hm : 1 ≤ m := by omega
    rw [twP_natCast, ← famB_eq_twistPoly m hm] at hP
    obtain ⟨a, a₁, h1, h2, -, h3, h4, h5⟩ := exists_pattern_point m hm hM hM4 hQ hP
    refine ⟨a, a₁, h1, h2, ?_, ?_, ?_⟩
    · rw [zpow_natCast]
      exact h3
    · rw [zpow_natCast]
      exact h4
    · rw [zpow_natCast]
      exact h5

end AJConjecture
