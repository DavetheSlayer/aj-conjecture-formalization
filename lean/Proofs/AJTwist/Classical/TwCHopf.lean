import Mathlib
import AJHandoff.TorusKnot.PairKPeriHopf
import AJTwist.Classical.TwCVirtual
import AJTwist.Classical.TwCBasePos

/-!
# The Hopf loops of the twisted block lists

For a tuple `F` fixed by `twBlocks r s ℓ σ`, the loops of the two Hopf letters are given by the
formulas of the untwisted lists in terms of the edge meridians `β = e_T`, `α = e_(T+1)` of `F`
and the loops of the round `R_0` and the top-right climb `C`:

* `twcHopf_neg`: `H₁ = R_0 β⁻¹ α`, `H₂ = C H₁ α⁻¹ H₁⁻¹ β R_0⁻¹` (as `pairHopf_loops`);
* `twcHopf_pos`: `H₁ = α R_0 β⁻¹`, `H₂ = α H₁⁻¹ C R_0 β⁻¹ H₁⁻¹` (as `twcHopf_loops_pos`).

Route: apply `pairHopf_loops` resp. `twcHopf_loops_pos` to the virtual tuple
`twcVirtual r s ℓ σ F`; its block loops at the positions `pairIdxH1`, `pairIdxH2`, `pairIdxR 0`,
`pairIdxC` (all different from the head position `0`) are those of `twcLoop`
(`loopAt_twcVirtual`, with the new entries restored because `F` is fixed and no block outside
the chain touches them), and its edge meridians at `T`, `T + 1` are those of `F`
(`prePr_twcVirtual`, `prePr_resTuple`: the levels `T, T + 1, T + 2` are above `j₀`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The chain of a fixed tuple restores the new entries. -/
private theorem runTop_take_new_twCHopf {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F)
    (k : Fin (twStrands r s ℓ)) (hk : pairStrands r s ≤ (k : ℕ)) :
    runTop (twStrands r s ℓ) ((twBlocks r s ℓ σ).take (twExtra ℓ + 1)) F k = F k := by
  have ht : (twBlocks r s ℓ σ).take (twExtra ℓ + 1) =
      twChain (pairStrands r s) (twHeadTop r s) ℓ := by
    rw [twBlocks_eq_chain_append, ← length_twChain (pairStrands r s) (twHeadTop r s) ℓ,
      List.take_left]
  have h1 := runTop_apply_of_ge (Nat.le_add_right (pairStrands r s) (twExtra ℓ))
    (twcBase r s σ).tail (fun b hb ↦ twcBase_valid h σ b (List.mem_of_mem_tail hb))
    (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) k hk
  rw [ht, ← h1]
  conv_rhs => rw [← hF, twBlocks_eq_chain_append, runTop_append]
  rfl

/-- The loops off the head position and the edge meridians of the levels `T`, `T + 1` of the
virtual tuple are those of the fixed tuple. -/
private theorem twcVirtual_data_twCHopf {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) :
    (∀ q, q < 2 * pairC r s + 2 → q ≠ 0 →
      loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) q = twcLoop r s ℓ σ F q) ∧
      edgeMer (twcVirtual r s ℓ σ F) (pairTop r s) = edgeMer F (pairTop r s) ∧
      edgeMer (twcVirtual r s ℓ σ F) (pairTop r s + 1) = edgeMer F (pairTop r s + 1) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hj : twHeadTop r s < pairTop r s := by
    unfold twHeadTop
    split_ifs <;> omega
  have hch : ∀ n, pairTop r s ≤ n → n ≤ pairStrands r s →
      prePr (twcVirtual r s ℓ σ F) n = prePr F n := fun n hn hn' ↦ by
    rw [prePr_twcVirtual r s ℓ σ F hn', twcVirtCh, ite_eq_right (by omega)]
  refine ⟨fun q hq hq' ↦ loopAt_twcVirtual h ℓ σ F (runTop_take_new_twCHopf h ℓ σ F hF) hq hq',
    ?_, ?_⟩
  · rw [edgeMer, edgeMer, hch _ (by omega) (by omega), hch _ le_rfl (by omega)]
  · rw [edgeMer, edgeMer, hch _ (by omega) (by omega), hch _ (by omega) (by omega)]

/-- The positions of the Hopf letters, the round `R_0` and the climb `C` are off the head
position. -/
private theorem pairIdx_bounds_twCHopf {r s : ℕ} (h : IsTorusPair r s) :
    (pairIdxH1 r s < 2 * pairC r s + 2 ∧ pairIdxH1 r s ≠ 0) ∧
      (pairIdxH2 r s < 2 * pairC r s + 2 ∧ pairIdxH2 r s ≠ 0) ∧
      (pairIdxR r s 0 < 2 * pairC r s + 2 ∧ pairIdxR r s 0 ≠ 0) ∧
      (pairIdxC r s < 2 * pairC r s + 2 ∧ pairIdxC r s ≠ 0) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  simp only [pairIdxH1, pairIdxH2, pairIdxR, pairIdxC, pairIdxB, ite_true]
  omega

/-- The Hopf loops of a twisted negative-clasp block list. -/
theorem twcHopf_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ true) F = F) :
    twcLoop r s ℓ true F (pairIdxH1 r s) =
        twcLoop r s ℓ true F (pairIdxR r s 0) * (edgeMer F (pairTop r s))⁻¹ *
          edgeMer F (pairTop r s + 1) ∧
      twcLoop r s ℓ true F (pairIdxH2 r s) =
        twcLoop r s ℓ true F (pairIdxC r s) * twcLoop r s ℓ true F (pairIdxH1 r s) *
          (edgeMer F (pairTop r s + 1))⁻¹ * (twcLoop r s ℓ true F (pairIdxH1 r s))⁻¹ *
          edgeMer F (pairTop r s) * (twcLoop r s ℓ true F (pairIdxR r s 0))⁻¹ := by
  obtain ⟨hl, he, he'⟩ := twcVirtual_data_twCHopf h ℓ true F hF
  obtain ⟨h1, h2, h3, h4⟩ := pairIdx_bounds_twCHopf h
  have key := pairHopf_loops h (twcVirtual r s ℓ true F)
  rw [← twcBase_true r s, hl _ h1.1 h1.2, hl _ h2.1 h2.2, hl _ h3.1 h3.2, hl _ h4.1 h4.2, he,
    he'] at key
  exact key

/-- The Hopf loops of a twisted positive-clasp block list. -/
theorem twcHopf_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ false) F = F) :
    twcLoop r s ℓ false F (pairIdxH1 r s) =
        edgeMer F (pairTop r s + 1) * twcLoop r s ℓ false F (pairIdxR r s 0) *
          (edgeMer F (pairTop r s))⁻¹ ∧
      twcLoop r s ℓ false F (pairIdxH2 r s) =
        edgeMer F (pairTop r s + 1) * (twcLoop r s ℓ false F (pairIdxH1 r s))⁻¹ *
          twcLoop r s ℓ false F (pairIdxC r s) * twcLoop r s ℓ false F (pairIdxR r s 0) *
          (edgeMer F (pairTop r s))⁻¹ * (twcLoop r s ℓ false F (pairIdxH1 r s))⁻¹ := by
  obtain ⟨hl, he, he'⟩ := twcVirtual_data_twCHopf h ℓ false F hF
  obtain ⟨h1, h2, h3, h4⟩ := pairIdx_bounds_twCHopf h
  have key := twcHopf_loops_pos h (twcVirtual r s ℓ false F)
  rw [hl _ h1.1 h1.2, hl _ h2.1 h2.2, hl _ h3.1 h3.2, hl _ h4.1 h4.2, he, he'] at key
  exact key

end AJConjecture
