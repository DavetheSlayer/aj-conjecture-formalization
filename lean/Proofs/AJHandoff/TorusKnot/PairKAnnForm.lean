import Mathlib
import AJHandoff.TorusKnot.PairKAnnDefs

/-!
# The algebra of the closed forms `F(w, k, l) = Π^w y^k a (Π^w y^l)⁻¹`

If `R = Π^w y Π^(-w)` (a Hurwitz element in the frame of the label `w`), multiplying
`F(w, k, l)` by `R` on the left raises `k`, multiplying by `R⁻¹` on the right raises `l`, and
conjugating by `Π⁻¹` lowers `w` (`pairAnnForm_left`, `_right`, `_conj`, `_conjP`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Left multiplication by `R = Π^w y Π^(-w)` raises `k`. -/
theorem pairAnnForm_left {P y a R : G} {w : ℤ} (hR : R = P ^ w * y * (P ^ w)⁻¹) (k l : ℤ) :
    R * pairAnnForm P y a w k l = pairAnnForm P y a w (k + 1) l := by
  rw [hR, pairAnnForm, pairAnnForm, zpow_add, zpow_one]
  group

/-- Left multiplication by `R⁻¹` lowers `k`. -/
theorem pairAnnForm_left_inv {P y a R : G} {w : ℤ} (hR : R = P ^ w * y * (P ^ w)⁻¹)
    (k l : ℤ) : R⁻¹ * pairAnnForm P y a w k l = pairAnnForm P y a w (k - 1) l := by
  rw [hR, pairAnnForm, pairAnnForm, zpow_sub, zpow_one]
  group

/-- Right multiplication by `R⁻¹` raises `l`. -/
theorem pairAnnForm_right {P y a R : G} {w : ℤ} (hR : R = P ^ w * y * (P ^ w)⁻¹) (k l : ℤ) :
    pairAnnForm P y a w k l * R⁻¹ = pairAnnForm P y a w k (l + 1) := by
  rw [hR, pairAnnForm, pairAnnForm, zpow_add, zpow_one]
  group

/-- Conjugation by `R` raises `k` and `l`. -/
theorem pairAnnForm_conj {P y a R : G} {w : ℤ} (hR : R = P ^ w * y * (P ^ w)⁻¹) (k l : ℤ) :
    R * pairAnnForm P y a w k l * R⁻¹ = pairAnnForm P y a w (k + 1) (l + 1) := by
  rw [pairAnnForm_left hR, pairAnnForm_right hR]

/-- Conjugation by `R⁻¹` lowers `k` and `l`. -/
theorem pairAnnForm_conj_inv {P y a R : G} {w : ℤ} (hR : R = P ^ w * y * (P ^ w)⁻¹)
    (k l : ℤ) : R⁻¹ * pairAnnForm P y a w k l * R = pairAnnForm P y a w (k - 1) (l - 1) := by
  rw [hR, pairAnnForm, pairAnnForm, zpow_sub, zpow_sub, zpow_one]
  group

/-- Conjugation by `Π⁻¹` lowers `w`. -/
theorem pairAnnForm_conjP (P y a : G) (w k l : ℤ) :
    P⁻¹ * pairAnnForm P y a w k l * P = pairAnnForm P y a (w - 1) k l := by
  rw [pairAnnForm, pairAnnForm, zpow_sub, zpow_one]
  group

/-- A closed form with `l = k + 1`: `F(w, k, k + 1) = X a y⁻¹ X⁻¹` with `X = Π^w y^k`. -/
theorem pairAnnForm_succ (P y a : G) (w k : ℤ) :
    pairAnnForm P y a w k (k + 1) = (P ^ w * y ^ k) * a * y⁻¹ * (P ^ w * y ^ k)⁻¹ := by
  rw [pairAnnForm, zpow_add, zpow_one]
  group

/-- A closed form with `l = k`: `F(w, k, k) = X a X⁻¹` with `X = Π^w y^k`. -/
theorem pairAnnForm_self (P y a : G) (w k : ℤ) :
    pairAnnForm P y a w k k = (P ^ w * y ^ k) * a * (P ^ w * y ^ k)⁻¹ := rfl

end AJConjecture
