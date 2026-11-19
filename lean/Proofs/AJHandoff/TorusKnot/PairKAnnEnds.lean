import Mathlib
import AJHandoff.TorusKnot.PairKAnnFrame

/-!
# The two ends of the annulus path

With `U = Π^(w(T_s)) y_0^(K(T_s) - K_0)` (`pairAnnU`):

* `pairAnnEdge_end_s`: `T_s` has `l = k + 1` (`pairAnn_lab_top`), so `e(T_s) = U a y_0⁻¹ U⁻¹`
  (`pairAnnForm_succ`); no relation is needed;
* `pairAnnU_conj`: `y_(r-1) = R'_(s-1)` (`pairAnn_y_last`) is `Π^(w(T_s)) y_0 Π^(-w(T_s))` in the
  frame of `T_s` (`pairAnnHur_eq_top`, `s - 1 ≡ s - 1`), so `U⁻¹ y_(r-1) U = y_0`;
* `pairAnnEdge_end_T`: `e(T_0) = X a X⁻¹` with `X = Π^(-W_0) y_0^(-K_0)` (`pairAnn_ends`:
  `w(T_0) = -W_0`, `k(T_0) = l(T_0) = 0`; `pairAnnForm_self`), and
  `U Λ⁻¹ = Π^(h(s) - W_0) y_0^(l(s) - 1 - K_0) y_0^(rs) Π^(-s) = Π^(-W_0) y_0^(-K_0)` by
  `Λ = Π^s y_0^(-rs)` (`pairRevLam_eq`), `h(s) = s`, `l(s) + rs = 1` (`pairAnn_ends`) and since
  `Π^s` commutes with `y_0` (`pairAnnPi_zpow_comm`; use `Commute.zpow_right`). This is where
  `z = c - r - 1` enters.

Checked exactly (`SCR/ANN/check_closed.py`, `ends`, `conj`).
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- The end `T_s`: `e(T_s) = U a y_0⁻¹ U⁻¹`. -/
theorem pairAnnEdge_end_s (h : IsTorusPair r s) (y : ℕ → G) (a : G) :
    pairAnnEdge r s y a (2 * pairC r s - 1 - s) =
      pairAnnU r s y * a * (y 0)⁻¹ * (pairAnnU r s y)⁻¹ := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨-, -, hP⟩ := pairAnn_lab_top h (t := s) (by omega)
  rw [ite_eq_right (by omega)] at hP
  have hK : pairAnnLam r s (2 * pairC r s - 1 - s) =
      pairAnnKap r s (2 * pairC r s - 1 - s) + 1 := by
    rw [pairAnnKap, hP]
    ring
  rw [pairAnnEdge, hK, show pairAnnKap r s (2 * pairC r s - 1 - s) + 1 - pairAnnKap r s 0 =
    pairAnnKap r s (2 * pairC r s - 1 - s) - pairAnnKap r s 0 + 1 by ring, pairAnnForm_succ,
    pairAnnU]

/-- `U` conjugates `y_(r-1)` to `y_0`. -/
theorem pairAnnU_conj (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹) :
    (pairAnnU r s y)⁻¹ * y (r - 1) * pairAnnU r s y = y 0 := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW, -, -⟩ := pairAnn_lab_top h (t := s) (by omega)
  have hR := pairAnnHur_eq_top h y hy s (s - 1) (by
    rw [Int.modEq_iff_dvd]; exact ⟨0, by omega⟩)
  rw [pairAnn_y_last h y hy, hR, pairAnnU, hW]
  group

/-- The end `T_0 = T`: `e(T) = U (Λ⁻¹ a Λ) U⁻¹`. -/
theorem pairAnnEdge_end_T (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) :
    pairAnnEdge r s y a (2 * pairC r s - 1) =
      pairAnnU r s y * ((pairRevLam r s y)⁻¹ * a * pairRevLam r s y) * (pairAnnU r s y)⁻¹ := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_top h (t := 0) (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_top h (t := s) (by omega)
  obtain ⟨hh0, hl0, -, -, hhs, hls⟩ := pairAnn_ends h
  rw [Nat.sub_zero] at hW1 hL1 hP1
  rw [ite_eq_left rfl] at hP1
  rw [ite_eq_right (by omega)] at hP2
  have hK1 : pairAnnKap r s (2 * pairC r s - 1) = 0 := by rw [pairAnnKap, hL1, hP1, hl0, sub_zero]
  have hK2 : pairAnnKap r s (2 * pairC r s - 1 - s) = pairAnnTopL r s s - 1 := by
    rw [pairAnnKap, hL2, hP2]
  have hW1' : pairAnnW r s (2 * pairC r s - 1) = 0 := by rw [hW1, pairAnnTopW, hh0, Nat.cast_zero]
  have hW2' : pairAnnW r s (2 * pairC r s - 1 - s) = s := by rw [hW2, pairAnnTopW, hhs]
  have hL1' : pairAnnLam r s (2 * pairC r s - 1) = 0 := by rw [hL1, hl0]
  have hcomm : Commute (pairAnnPi r y ^ (s : ℤ)) (y 0) := pairAnnPi_zpow_comm h y hy
  rw [pairAnnEdge, pairAnnU, hW1', hK1, hL1', hW2', hK2, pairRevLam_eq, ← zpow_natCast,
    pairAnnForm]
  generalize pairAnnW r s 0 = w0 at *
  generalize pairAnnKap r s 0 = k0 at *
  set P := pairAnnPi r y
  set Y := y 0
  set L := pairAnnTopL r s s
  set n : ℤ := ((r * s : ℕ) : ℤ)
  -- `U Λ⁻¹ = Π^(-W_0) y_0^(-K_0)`, as `Π^s` commutes with `y_0` and `l(s) + rs = 1`
  have key : P ^ ((s : ℤ) - w0) * Y ^ (L - 1 - k0) * (P ^ (s : ℤ) * Y ^ (-n))⁻¹ =
      P ^ ((0 : ℤ) - w0) * Y ^ ((0 : ℤ) - k0) := by
    have hc' : (P ^ (s : ℤ))⁻¹ * Y ^ (L - 1 - k0 + n) = Y ^ (L - 1 - k0 + n) * (P ^ (s : ℤ))⁻¹ :=
      ((hcomm.zpow_right _).inv_left).eq
    calc P ^ ((s : ℤ) - w0) * Y ^ (L - 1 - k0) * (P ^ (s : ℤ) * Y ^ (-n))⁻¹
        = P ^ ((s : ℤ) - w0) * (Y ^ (L - 1 - k0 + n) * (P ^ (s : ℤ))⁻¹) := by
          rw [zpow_add]; group
      _ = P ^ ((s : ℤ) - w0) * (P ^ (s : ℤ))⁻¹ * Y ^ (L - 1 - k0 + n) := by
          rw [← hc', mul_assoc]
      _ = P ^ ((0 : ℤ) - w0) * Y ^ ((0 : ℤ) - k0) := by
          rw [show L - 1 - k0 + n = (0 : ℤ) - k0 by omega]
          group
  rw [← key]
  group

end AJConjecture
