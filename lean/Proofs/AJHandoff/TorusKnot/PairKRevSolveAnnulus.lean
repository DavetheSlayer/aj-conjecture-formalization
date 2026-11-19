import Mathlib
import AJHandoff.TorusKnot.PairKAnnEqLow
import AJHandoff.TorusKnot.PairKAnnEqTop
import AJHandoff.TorusKnot.PairKAnnClosedLow
import AJHandoff.TorusKnot.PairKAnnClosedTop
import AJHandoff.TorusKnot.PairKAnnEnds

/-!
# The edge meridians along the annulus

`exists_pairRevEdge_annulus`: for `y` satisfying the torus relation and any `a` there are edge
meridians `e_0 = a, e_1, …, e_(2c-1)` on the levels of the braided annulus solving the loop
equation of every block of `pairBlocks r s` except the top-right climb `C` and the two Hopf
letters (these equations do not involve the Hopf loop `H`), and the two ends `T = 2c - 1`,
`T - s` of the annulus path are
`e_(T-s) = U a y_0⁻¹ U⁻¹`, `e_T = U (Λ⁻¹ a Λ) U⁻¹` with `U⁻¹ y_(r-1) U = y_0`,
`Λ = (y_0 ⋯ y_(r-1))^s y_0^(-rs)` (`pairRevLam`, now in `AJHandoff.TorusKnot.PairKAnnDefs`). No
pattern relation is needed here; `hmer` enters only in `exists_pairRevEdge` (the second Hopf
letter).

Proof: the edge meridians are given in closed form, `e = pairAnnEdge r s y a`
(`AJHandoff.TorusKnot.PairKAnnDefs`: `e_n = Π^w y_0^k a (Π^w y_0^l)⁻¹` with explicit integer labels
along the annulus path). Each block position is in one of nine regimes; for each, the loop
equation is reduced to a transition `e_j = X e_i Y` (`AJHandoff.TorusKnot.PairKAnnEqLow`,
`…EqTop`), which the closed forms satisfy (`AJHandoff.TorusKnot.PairKAnnClosedLow`, `…ClosedTop`).
The ends are `AJHandoff.TorusKnot.PairKAnnEnds`, with `U = pairAnnU r s y`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Crux of the reverse inclusion: the edge meridians along the annulus path, with the closed
forms of its two ends. -/
theorem exists_pairRevEdge_annulus {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) :
    ∃ (e : ℕ → G) (U : G), e 0 = a ∧ U⁻¹ * y (r - 1) * U = y 0 ∧
      e (2 * pairC r s - 1 - s) = U * a * (y 0)⁻¹ * U⁻¹ ∧
      e (2 * pairC r s - 1) = U * ((pairRevLam r s y)⁻¹ * a * pairRevLam r s y) * U⁻¹ ∧
      ∀ (H : G) (q : ℕ), q < 2 * pairC r s + 2 → q ≠ pairIdxC r s → q ≠ pairIdxH1 r s →
        q ≠ pairIdxH2 r s →
        pairRevLoop r s y H q = loopPr ((pairBlocks r s).getD q (SBlock.neg 0))
          (fun n ↦ gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s y H) n *
            descProd e 0 n) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  refine ⟨pairAnnEdge r s y a, pairAnnU r s y, pairAnnEdge_zero h y a, pairAnnU_conj h y hy,
    pairAnnEdge_end_s h y a, pairAnnEdge_end_T h y hy a, fun H q hq hC hH1 hH2 ↦ ?_⟩
  change PairAnnEq r s y H (pairAnnEdge r s y a) q
  simp only [pairIdxC, pairIdxH1, pairIdxH2] at hC hH1 hH2
  -- the left climbs
  by_cases h1 : q < r - 2
  · exact pairAnnEq_A h y H _ q h1 (pairAnnEdge_A h y hy a q h1)
  -- the decreasing run
  by_cases h2 : q < r - 2 + pairRunDown r s
  · obtain ⟨j, rfl⟩ : ∃ j, q = r - 2 + j := ⟨q - (r - 2), by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact pairAnnEq_downTop h y hy H _ (pairAnnEdge_downTop h y hy a)
    · exact pairAnnEq_down h y H _ j hj (by omega) (pairAnnEdge_down h y a j hj (by omega))
  -- the increasing run
  by_cases h3 : q < pairIdxB r s
  · obtain ⟨j, rfl⟩ : ∃ j, q = r - 2 + pairRunDown r s + j :=
      ⟨q - (r - 2 + pairRunDown r s), by omega⟩
    exact pairAnnEq_up h y hy H _ j (by omega) (pairAnnEdge_up h y hy a j (by omega))
  -- the big climb and the round `R_0`
  by_cases h4 : q = pairIdxB r s
  · subst h4
    exact pairAnnEq_B h y hy H _ (pairAnnEdge_B h y hy a)
  by_cases h5 : q = pairIdxB r s + 1
  · subst h5
    exact pairAnnEq_R0 h y hy H _ (pairAnnEdge_R0 h y hy a)
  -- the rounds `R_1, …, R_(s-2)`
  by_cases h6 : q ≤ pairIdxB r s + s
  · obtain ⟨τ, rfl⟩ : ∃ τ, q = pairIdxB r s + 2 + τ := ⟨q - (pairIdxB r s + 2), by omega⟩
    exact pairAnnEq_R h y hy H _ τ (by omega) (by omega)
      (pairAnnEdge_R h y hy a τ (by omega) (by omega))
  -- the last round
  by_cases h7 : q = pairIdxB r s + s + 1
  · subst h7
    exact pairAnnEq_Rlast h y hy H _ (pairAnnEdge_Rlast h y hy a)
  -- the right descents
  obtain ⟨j, rfl⟩ : ∃ j, q = pairIdxB r s + s + 3 + j := ⟨q - (pairIdxB r s + s + 3), by omega⟩
  exact pairAnnEq_Dp h y hy H _ j (by omega) (pairAnnEdge_Dp h y hy a j (by omega))

end AJConjecture
