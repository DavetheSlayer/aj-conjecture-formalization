import Mathlib
import AJHandoff.TorusKnot.PairKAnnFrame

/-!
# The closed forms solve the band equations of the climbs, the runs and `B`

The edge meridians `e_n = pairAnnEdge r s y a n = F(W_n - W_0, K_n - K_0, L_n - K_0)` satisfy the
transitions required by `AJHandoff.TorusKnot.PairKAnnEqLow` and the descents of
`AJHandoff.TorusKnot.PairKAnnEqTop`. Write `w(t) = W(T_t) - W_0`; in each case the Hurwitz element
is taken in the frame of a top level (`pairAnnHur_eq_top`) and the step is one of the moves of
`AJHandoff.TorusKnot.PairKAnnForm`:

* `A_k` (`k < r - 2`): the bottom level `k` has the labels of `T_(k+1)` with `k = l`
  (`pairAnn_lab_bot`), `T_(k+1)` has `k = l - 1` (`pairAnn_lab_top`); `R'_k` in the frame of
  `T_(k+1)`; move `pairAnnForm_left_inv`;
* `D'_j` (`k = r - 3 - j`, level `b₀ + 1 + j = T_(s+1+k)`): `h(s+1+k) = h(k+1)`,
  `l(T_(s+1+k)) = l(T_(k+1)) + 1` (`pairAnn_bottom`); move `pairAnnForm_right`;
* decreasing run: both levels in the lower run, equal labels (`pairAnn_lab_low`);
* `D_0`: lower run `r + E - 3` to upper run `r + E - 2` (`pairAnn_lab_up`, `b₀ - (r + E - 2) = z`,
  `pairAnn_arith`), `l(T_(r-1)) = l(T_(s-1)) - z - 3` (`pairAnn_run`); `R'_(r-2)` in the frame of
  `T_(r-1)`; move `pairAnnForm_left_inv`;
* increasing run and `B` (`b₀` upper run, `2c - r = T_(r-1)`): move `pairAnnForm_conj_inv` in the
  frame of `T_(r-1)`.

Route: unfold `pairAnnEdge`, `pairAnnKap`; rewrite the labels with the regime lemmas of
`AJHandoff.TorusKnot.PairKAnnDefs` (side conditions by `omega` after `pairAnn_arith`,
`pairRev_idxB`); rewrite the Hurwitz element with `pairAnnHur_eq_top` (the congruence is an
equality of integers here); apply the move and close the exponents with `congr 1 <;> ring`/`omega`.
All identities were checked exactly (`SCR/ANN/check_closed.py`).
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- `A_k`: `e(T_(k+1)) = R'_k⁻¹ e_k`. -/
theorem pairAnnEdge_A (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) (k : ℕ) (hk : k < r - 2) :
    pairAnnEdge r s y a (2 * pairC r s - 2 - k) = (pairAnnHur r y k)⁻¹ * pairAnnEdge r s y a k := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_bot h hk
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_top h (t := k + 1) (by omega)
  rw [show 2 * pairC r s - 1 - (k + 1) = 2 * pairC r s - 2 - k by omega,
    ite_eq_right (by omega)] at *
  have hR := pairAnnHur_eq_top h y hy (k + 1) k (by simp [Int.ModEq])
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]
  rw [pairAnnForm_left_inv hR]
  congr 1
  ring

/-- `D'_j`: `e(b₀ + 1 + j) = e(r - 3 - j) R'_(r-3-j)⁻¹`. -/
theorem pairAnnEdge_Dp (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) (j : ℕ) (hj : j < r - 2) :
    pairAnnEdge r s y a (pairIdxB r s + 1 + j) =
      pairAnnEdge r s y a (r - 3 - j) * (pairAnnHur r y (r - 3 - j))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_bot h (n := r - 3 - j) (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_top h (t := s + 1 + (r - 3 - j)) (by omega)
  obtain ⟨hH, hT⟩ := pairAnn_bottom h (r - 3 - j) (by omega)
  rw [show 2 * pairC r s - 1 - (s + 1 + (r - 3 - j)) = pairIdxB r s + 1 + j by omega,
    ite_eq_right (by omega)] at *
  have hR := pairAnnHur_eq_top h y hy (r - 3 - j + 1) (r - 3 - j) (by simp [Int.ModEq])
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]
  rw [pairAnnForm_right hR, pairAnnTopW, pairAnnTopW, hH, hT]
  congr 1 <;> ring

/-- The decreasing run below its top: equal edge meridians. -/
theorem pairAnnEdge_down (h : IsTorusPair r s) (y : ℕ → G) (a : G) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j < pairRunDown r s) :
    pairAnnEdge r s y a (r + pairRunDown r s - 2 - j) =
      pairAnnEdge r s y a (r + pairRunDown r s - 3 - j) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_low h (n := r + pairRunDown r s - 2 - j) (by omega)
    (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_low h (n := r + pairRunDown r s - 3 - j) (by omega)
    (by omega)
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]

/-- `D_0`: `e(r + E - 2) = R'_(r-2)⁻¹ e(r + E - 3)`. -/
theorem pairAnnEdge_downTop (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) :
    pairAnnEdge r s y a (r + pairRunDown r s - 2) =
      (pairAnnHur r y (r - 2))⁻¹ * pairAnnEdge r s y a (r + pairRunDown r s - 3) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_up h (n := r + pairRunDown r s - 2) (by omega)
    (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_low h (n := r + pairRunDown r s - 3) (by omega)
    (by omega)
  obtain ⟨-, hT⟩ := pairAnn_run h
  have hR := pairAnnHur_eq_top h y hy (r - 1) (r - 2) (by
    rw [show r - 1 = r - 2 + 1 by omega]; simp [Int.ModEq])
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]
  rw [pairAnnForm_left_inv hR, hT, show pairIdxB r s - (r + pairRunDown r s - 2) =
    pairRunUp r s by omega]
  congr 1 <;> ring

/-- The increasing run: `e(n + 1) = R'_(r-2)⁻¹ e_n R'_(r-2)`. -/
theorem pairAnnEdge_up (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) (j : ℕ) (hj : j < pairRunUp r s) :
    pairAnnEdge r s y a (r - 1 + pairRunDown r s + j) =
      (pairAnnHur r y (r - 2))⁻¹ * pairAnnEdge r s y a (r - 2 + pairRunDown r s + j) *
        pairAnnHur r y (r - 2) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_up h (n := r - 1 + pairRunDown r s + j) (by omega)
    (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_up h (n := r - 2 + pairRunDown r s + j) (by omega)
    (by omega)
  have hR := pairAnnHur_eq_top h y hy (r - 1) (r - 2) (by
    rw [show r - 1 = r - 2 + 1 by omega]; simp [Int.ModEq])
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]
  rw [pairAnnForm_conj_inv hR, show pairIdxB r s - (r - 2 + pairRunDown r s + j) =
    pairIdxB r s - (r - 1 + pairRunDown r s + j) + 1 by omega]
  congr 1 <;> push_cast <;> ring

/-- `B`: `e(2c - r) = R'_(r-2)⁻¹ e(b₀) R'_(r-2)`. -/
theorem pairAnnEdge_B (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) :
    pairAnnEdge r s y a (2 * pairC r s - r) =
      (pairAnnHur r y (r - 2))⁻¹ * pairAnnEdge r s y a (pairIdxB r s) *
        pairAnnHur r y (r - 2) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_top h (t := r - 1) (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_up h (n := pairIdxB r s) (by omega) le_rfl
  rw [show 2 * pairC r s - 1 - (r - 1) = 2 * pairC r s - r by omega,
    ite_eq_right (by omega)] at *
  have hR := pairAnnHur_eq_top h y hy (r - 1) (r - 2) (by
    rw [show r - 1 = r - 2 + 1 by omega]; simp [Int.ModEq])
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2, Nat.sub_self]
  rw [pairAnnForm_conj_inv hR]
  congr 1 <;> push_cast <;> ring

end AJConjecture
