import Mathlib
import AJFamily.Quantum.AbNodeNoSeparation
import AJFamily.Quantum.EbNodeNoSeparation
import AJHandoff.PairDefs
import AJHandoff.LocalTheory.LocNodeResidue
import AJHandoff.TorusQuantum.PairQJetsIndexResidual
import AJHandoff.TorusQuantum.PairQJetsIndexTransfer

/-!
# T-JETS in the language of the local theory

The transfer operator `P_m = famTransferOp m` is embedded by `t ↦ -exp(h/4)`, `M ↦ z` and
written in the backward variable `u = L⁻¹` (`pairQJetRow`; it is the row `∑_i A_i(q, z²) u^i`
with `q = exp(h)` by `pairQJetRow_famTransferOp`); the dilation is `σ(z) = exp(-h/2) z`, `c = -1/2` (M-backward convention,
`pairQJetDilation_c`). Its residual blocks are the reversals `Ĉ, Ê, B̂_m` of `C = L - 1`, `E`,
`B_m` (`pairQJetBlocks m`, indices `0, 1, 2`), with normalizing scalars `pairQJetKappa₁/₂ m`.

For every `m ≥ 2` (no parity hypothesis; `m = rs` for a torus pair, e.g. the odd `m = 15`):
* abelian node (`pairQJets_abNode`): over every `m₀` with `m m₀⁴ - (2m+1) m₀² + m = 0`, the
  point `(z, u) = (m₀, 1)` is an allowed transverse mixed node (`LocAllowedNode`: endpoints
  units, transversality, no other collision on the fibre) of `Ĉ` and `B̂_m`, and both allocation
  indices (formula (4)) are `-1/2`;
* E/B node (`pairQJets_ebNode`): the same for `Ê` and `B̂_m` at `(m₀, 1/L₀)`,
  `L₀ = ebNodeL m m₀`, over every `m₀` with `m(2m+1) m₀⁴ + (4m²+2m+1) m₀² + m(2m+1) = 0`.
The three blocks are residual blocks (`pairQJets_residualBlocks`), so by Lemma 3 of the local
theory (`hasNormalizedIndex_locNodeIndex`) a right pseudo-factor containing one of the two
blocks and not the other has normalized index `-1/2` (`pairQJets_hasNormalizedIndex_abNode`,
`_ebNode`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The fibre condition from the library's collision hypothesis. -/
private theorem pairQJets_fibre {ι : Type*} {b : ι → ℤ[X][X]} {g h k : ι} {m₀ l₀ : ℂ}
    (hall : ∀ i, i = g ∨ i = h ∨ i = k) (hc : NodeCollisionFree (b g) (b h) (b k) m₀ l₀) :
    ∀ i j, i ≠ j → ∀ l : ℂ, evalIntPoint (b i) m₀ l = 0 → evalIntPoint (b j) m₀ l = 0 →
      l = l₀ ∧ ((i = g ∧ j = h) ∨ (i = h ∧ j = g)) := by
  intro i j hij l hi hj
  rcases hall i with rfl | rfl | rfl <;> rcases hall j with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact ⟨hc.1 l hi hj, Or.inl ⟨rfl, rfl⟩⟩
  · exact absurd hi (hc.2 l hj).1
  · exact ⟨hc.1 l hj hi, Or.inr ⟨rfl, rfl⟩⟩
  · exact absurd rfl hij
  · exact absurd hi (hc.2 l hj).2.1
  · exact absurd hj (hc.2 l hi).1
  · exact absurd hj (hc.2 l hi).2.1
  · exact absurd rfl hij

/-- `∂_L (L - 1) = 1`. -/
private theorem evalIntPoint_derivative_X_sub_one_jets (m l : ℂ) :
    evalIntPoint (derivative (X - 1)) m l = 1 := by
  simp [evalIntPoint, evalPoint]

/-- `L - 1` does not depend on `M`. -/
private theorem evalIntPoint_coeffDerivative_X_sub_one_jets (m l : ℂ) :
    evalIntPoint (coeffDerivative (X - 1)) m l = 0 := by
  have h0 : coeffDerivative (X - 1 : ℤ[X][X]) = 0 := by
    rw [coeffDerivative, Polynomial.sum_def]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    rw [coeff_sub, coeff_X, coeff_one]
    split_ifs <;> simp
  simp [h0, evalIntPoint, evalPoint]

/-- **T-JETS at the abelian node.** For `m ≥ 2` and `m₀` over the node `C ∩ B_m`, the point
`(z, u) = (m₀, 1)` is an allowed transverse mixed node of `Ĉ`, `B̂_m` for the backward row of
`famTransferOp m`, and both allocation indices are `-1/2` (`c = -1/2`). -/
theorem pairQJets_abNode (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) :
    LocAllowedNode (pairQJetRow (famTransferOp m)) (pairQJetBlocks m) (pairQJetKappa₁ m)
        (pairQJetKappa₂ m) 0 2 m₀ 1 ∧
      locNodeIndex pairQJetDilation.c m₀ 1 (opJet1 (pairQJetRow (famTransferOp m)))
        (pairQJetBlocks m 0) (pairQJetBlocks m 2) (locCofactor (pairQJetBlocks m) 0 2)
        (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2 ∧
      locNodeIndex pairQJetDilation.c m₀ 1 (opJet1 (pairQJetRow (famTransferOp m)))
        (pairQJetBlocks m 2) (pairQJetBlocks m 0) (locCofactor (pairQJetBlocks m) 2 0)
        (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2 := by
  obtain ⟨h0, h1, h2, hB, hE, hBL, hBM⟩ := abNode_facts m hm hab
  obtain ⟨hlead, hconst⟩ := eval_coeff_specialize_famTransferOp_ne_zero m (by omega) h0 h1 h2
  have hdeg : (specialize (famTransferOp m)).natDegree = (famTransferOp m).natDegree := by
    rw [natDegree_specialize_famTransferOp m (by omega), natDegree_famTransferOp m (by omega)]
  have hall : ∀ i : Fin 3, i = 0 ∨ i = 2 ∨ i = 1 := fun i ↦ by fin_cases i <;> simp
  have hc : NodeCollisionFree (![X - 1, extraFactor, twistPoly m] 0)
      (![X - 1, extraFactor, twistPoly m] 2) (![X - 1, extraFactor, twistPoly m] 1) m₀ 1 :=
    abNode_collisionFree m hm hab
  obtain ⟨hnode, hidx⟩ := pairQJet_allowedNode_index (pairQJets_forwardSym m (by omega))
    hdeg (g := 0) (h := 2) (by decide) h0 one_ne_zero (eval_symbolLeft_ne_zero m h1 h2)
    (eval_symbolRight_ne_zero m h1 h2) hlead hconst
    (by simp [evalIntPoint_X_sub_one]) hB
    (by simp [evalIntPoint, evalPoint]) hBL
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, evalIntPoint_derivative_X_sub_one_jets,
        evalIntPoint_coeffDerivative_X_sub_one_jets, one_mul, mul_zero, sub_zero]
      exact hBM)
    (fun i hi hi' ↦ by
      rcases hall i with rfl | rfl | rfl
      · exact absurd rfl hi
      · exact absurd rfl hi'
      · exact hE)
    (pairQJets_fibre hall hc) (evalIntPoint_weylSymbol_famTransferOp_abNode m hm hab)
  rw [inv_one] at hnode hidx
  have hidx' : locNodeIndex pairQJetDilation.c m₀ 1 (opJet1 (pairQJetRow (famTransferOp m)))
      (pairQJetBlocks m 0) (pairQJetBlocks m 2) (locCofactor (pairQJetBlocks m) 0 2)
      (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2 := hidx
  have hnode' : LocAllowedNode (pairQJetRow (famTransferOp m)) (pairQJetBlocks m)
      (pairQJetKappa₁ m) (pairQJetKappa₂ m) 0 2 m₀ 1 := hnode
  refine ⟨hnode', hidx', ?_⟩
  rw [locCofactor_swap, locNodeIndex_swap (by rw [pairQJetDilation_c]; norm_num) h0 one_ne_zero
    hnode'.jac, hidx']
  norm_num

/-- **T-JETS at the E/B node.** For `m ≥ 2` and `m₀` over the node `E ∩ B_m`, the point
`(z, u) = (m₀, 1/L₀)`, `L₀ = ebNodeL m m₀`, is an allowed transverse mixed node of `Ê`, `B̂_m`
for the backward row of `famTransferOp m`, and both allocation indices are `-1/2`
(`c = -1/2`). -/
theorem pairQJets_ebNode (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (heb : (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0) :
    LocAllowedNode (pairQJetRow (famTransferOp m)) (pairQJetBlocks m) (pairQJetKappa₁ m)
        (pairQJetKappa₂ m) 1 2 m₀ (ebNodeL m m₀)⁻¹ ∧
      locNodeIndex pairQJetDilation.c m₀ (ebNodeL m m₀)⁻¹
        (opJet1 (pairQJetRow (famTransferOp m))) (pairQJetBlocks m 1) (pairQJetBlocks m 2)
        (locCofactor (pairQJetBlocks m) 1 2) (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2 ∧
      locNodeIndex pairQJetDilation.c m₀ (ebNodeL m m₀)⁻¹
        (opJet1 (pairQJetRow (famTransferOp m))) (pairQJetBlocks m 2) (pairQJetBlocks m 1)
        (locCofactor (pairQJetBlocks m) 2 1) (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2 := by
  obtain ⟨h0, h1, h2, -, -, hL0, hC, hE, hB, hEL, hBL, hJ⟩ := ebNode_facts m hm heb
  obtain ⟨hlead, hconst⟩ := eval_coeff_specialize_famTransferOp_ne_zero m (by omega) h0 h1 h2
  have hdeg : (specialize (famTransferOp m)).natDegree = (famTransferOp m).natDegree := by
    rw [natDegree_specialize_famTransferOp m (by omega), natDegree_famTransferOp m (by omega)]
  have hall : ∀ i : Fin 3, i = 1 ∨ i = 2 ∨ i = 0 := fun i ↦ by fin_cases i <;> simp
  have hc : NodeCollisionFree (![X - 1, extraFactor, twistPoly m] 1)
      (![X - 1, extraFactor, twistPoly m] 2) (![X - 1, extraFactor, twistPoly m] 0) m₀
      (ebNodeL m m₀) :=
    ebNode_collisionFree m hm heb
  have hJ' : evalIntPoint (derivative (![X - 1, extraFactor, twistPoly m] 1)) m₀ (ebNodeL m m₀) *
        evalIntPoint (coeffDerivative (![X - 1, extraFactor, twistPoly m] 2)) m₀ (ebNodeL m m₀) -
      evalIntPoint (derivative (![X - 1, extraFactor, twistPoly m] 2)) m₀ (ebNodeL m m₀) *
        evalIntPoint (coeffDerivative (![X - 1, extraFactor, twistPoly m] 1)) m₀
          (ebNodeL m m₀) ≠ 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    intro h
    exact hJ (by linear_combination h)
  obtain ⟨hnode, hidx⟩ := pairQJet_allowedNode_index (pairQJets_forwardSym m (by omega))
    hdeg (g := 1) (h := 2) (by decide) h0 hL0 (eval_symbolLeft_ne_zero m h1 h2)
    (eval_symbolRight_ne_zero m h1 h2) hlead hconst hE hB hEL hBL hJ'
    (fun i hi hi' ↦ by
      rcases hall i with rfl | rfl | rfl
      · exact absurd rfl hi
      · exact absurd rfl hi'
      · exact hC)
    (pairQJets_fibre hall hc) (evalIntPoint_weylSymbol_famTransferOp_ebNode m hm heb)
  have hidx' : locNodeIndex pairQJetDilation.c m₀ (ebNodeL m m₀)⁻¹
      (opJet1 (pairQJetRow (famTransferOp m))) (pairQJetBlocks m 1) (pairQJetBlocks m 2)
      (locCofactor (pairQJetBlocks m) 1 2) (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2 := hidx
  have hnode' : LocAllowedNode (pairQJetRow (famTransferOp m)) (pairQJetBlocks m)
      (pairQJetKappa₁ m) (pairQJetKappa₂ m) 1 2 m₀ (ebNodeL m m₀)⁻¹ := hnode
  refine ⟨hnode', hidx', ?_⟩
  rw [locCofactor_swap, locNodeIndex_swap (by rw [pairQJetDilation_c]; norm_num) h0
    (inv_ne_zero hL0) hnode'.jac, hidx']
  norm_num

/-- Lemma 3 of the local theory at a node of index `-1/2` for both allocations. -/
private theorem pairQJets_normalized {m : ℕ} (hm : 2 ≤ m) {g h : Fin 3} {z₀ lam : ℂ}
    (hn : LocAllowedNode (pairQJetRow (famTransferOp m)) (pairQJetBlocks m) (pairQJetKappa₁ m)
      (pairQJetKappa₂ m) g h z₀ lam)
    (h1 : locNodeIndex pairQJetDilation.c z₀ lam (opJet1 (pairQJetRow (famTransferOp m)))
      (pairQJetBlocks m g) (pairQJetBlocks m h) (locCofactor (pairQJetBlocks m) g h)
      (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2)
    (h2 : locNodeIndex pairQJetDilation.c z₀ lam (opJet1 (pairQJetRow (famTransferOp m)))
      (pairQJetBlocks m h) (pairQJetBlocks m g) (locCofactor (pairQJetBlocks m) h g)
      (pairQJetKappa₁ m) (pairQJetKappa₂ m) = -1 / 2)
    {β : LocPoly} {S R : LocOp} (hβ : locJet0 β ≠ 0)
    (hfac : C β * pairQJetRow (famTransferOp m) = oreMul pairQJetDilation.shiftHom S R)
    (hsep : (LocBlockDvd (pairQJetBlocks m g) (opJet0 R) ∧
        LocBlockDvd (pairQJetBlocks m h) (opJet0 S)) ∨
      (LocBlockDvd (pairQJetBlocks m h) (opJet0 R) ∧
        LocBlockDvd (pairQJetBlocks m g) (opJet0 S))) :
    HasNormalizedIndex pairQJetDilation.c z₀ (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetDen R))
      (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetNum R)) (-1 / 2) := by
  rcases hsep with ⟨hR, hS⟩ | ⟨hR, hS⟩
  · have h := hasNormalizedIndex_locNodeIndex _ hβ hfac (pairQJets_residualBlocks m hm) hn hR hS
    rwa [h1] at h
  · have h := hasNormalizedIndex_locNodeIndex _ hβ hfac (pairQJets_residualBlocks m hm) hn.symm
      hR hS
    rwa [h2] at h

/-- **T-JETS, normalized index at the abelian node.** A right pseudo-factor of the backward row
of `famTransferOp m` that separates `Ĉ` from `B̂_m` (either way) has normalized determinant
index `-1/2` at `z = m₀`. -/
theorem pairQJets_hasNormalizedIndex_abNode (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) {β : LocPoly} {S R : LocOp}
    (hβ : locJet0 β ≠ 0)
    (hfac : C β * pairQJetRow (famTransferOp m) = oreMul pairQJetDilation.shiftHom S R)
    (hsep : (LocBlockDvd (pairQJetBlocks m 0) (opJet0 R) ∧
        LocBlockDvd (pairQJetBlocks m 2) (opJet0 S)) ∨
      (LocBlockDvd (pairQJetBlocks m 2) (opJet0 R) ∧
        LocBlockDvd (pairQJetBlocks m 0) (opJet0 S))) :
    HasNormalizedIndex pairQJetDilation.c m₀ (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetDen R))
      (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetNum R)) (-1 / 2) := by
  obtain ⟨hn, h1, h2⟩ := pairQJets_abNode m hm hab
  exact pairQJets_normalized hm hn h1 h2 hβ hfac hsep

/-- **T-JETS, normalized index at the E/B node.** A right pseudo-factor of the backward row of
`famTransferOp m` that separates `Ê` from `B̂_m` (either way) has normalized determinant index
`-1/2` at `z = m₀`. -/
theorem pairQJets_hasNormalizedIndex_ebNode (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (heb : (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0) {β : LocPoly} {S R : LocOp} (hβ : locJet0 β ≠ 0)
    (hfac : C β * pairQJetRow (famTransferOp m) = oreMul pairQJetDilation.shiftHom S R)
    (hsep : (LocBlockDvd (pairQJetBlocks m 1) (opJet0 R) ∧
        LocBlockDvd (pairQJetBlocks m 2) (opJet0 S)) ∨
      (LocBlockDvd (pairQJetBlocks m 2) (opJet0 R) ∧
        LocBlockDvd (pairQJetBlocks m 1) (opJet0 S))) :
    HasNormalizedIndex pairQJetDilation.c m₀ (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetDen R))
      (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetNum R)) (-1 / 2) := by
  obtain ⟨hn, h1, h2⟩ := pairQJets_ebNode m hm heb
  exact pairQJets_normalized hm hn h1 h2 hβ hfac hsep

/-- For a torus pair `(r, s)`, `m = rs ≥ 6`; the statements above apply to `m = rs` (e.g. the
odd `m = 15` for `(3, 5)`). -/
theorem pairQJets_two_le_of_isTorusPair {r s : ℕ} (h : IsTorusPair r s) : 2 ≤ r * s := by
  obtain ⟨hr, hrs, -⟩ := h
  nlinarith

/-- **T-JETS for a torus pair, abelian node** (`m = rs`). -/
theorem pairQJets_torus_abNode {r s : ℕ} (h : IsTorusPair r s) {m₀ : ℂ}
    (hab : ((r * s : ℕ) : ℂ) * (m₀ ^ 2) ^ 2 - (2 * ((r * s : ℕ) : ℂ) + 1) * m₀ ^ 2 +
      ((r * s : ℕ) : ℂ) = 0) :
    LocAllowedNode (pairQJetRow (famTransferOp (r * s))) (pairQJetBlocks (r * s))
        (pairQJetKappa₁ (r * s)) (pairQJetKappa₂ (r * s)) 0 2 m₀ 1 ∧
      locNodeIndex pairQJetDilation.c m₀ 1 (opJet1 (pairQJetRow (famTransferOp (r * s))))
        (pairQJetBlocks (r * s) 0) (pairQJetBlocks (r * s) 2)
        (locCofactor (pairQJetBlocks (r * s)) 0 2) (pairQJetKappa₁ (r * s))
        (pairQJetKappa₂ (r * s)) = -1 / 2 ∧
      locNodeIndex pairQJetDilation.c m₀ 1 (opJet1 (pairQJetRow (famTransferOp (r * s))))
        (pairQJetBlocks (r * s) 2) (pairQJetBlocks (r * s) 0)
        (locCofactor (pairQJetBlocks (r * s)) 2 0) (pairQJetKappa₁ (r * s))
        (pairQJetKappa₂ (r * s)) = -1 / 2 :=
  pairQJets_abNode _ (pairQJets_two_le_of_isTorusPair h) hab

/-- **T-JETS for a torus pair, E/B node** (`m = rs`). -/
theorem pairQJets_torus_ebNode {r s : ℕ} (h : IsTorusPair r s) {m₀ : ℂ}
    (heb : ((r * s : ℕ) : ℂ) * (2 * ((r * s : ℕ) : ℂ) + 1) * (m₀ ^ 2) ^ 2 +
      (4 * ((r * s : ℕ) : ℂ) ^ 2 + 2 * ((r * s : ℕ) : ℂ) + 1) * m₀ ^ 2 +
      ((r * s : ℕ) : ℂ) * (2 * ((r * s : ℕ) : ℂ) + 1) = 0) :
    LocAllowedNode (pairQJetRow (famTransferOp (r * s))) (pairQJetBlocks (r * s))
        (pairQJetKappa₁ (r * s)) (pairQJetKappa₂ (r * s)) 1 2 m₀ (ebNodeL (r * s) m₀)⁻¹ ∧
      locNodeIndex pairQJetDilation.c m₀ (ebNodeL (r * s) m₀)⁻¹
        (opJet1 (pairQJetRow (famTransferOp (r * s)))) (pairQJetBlocks (r * s) 1)
        (pairQJetBlocks (r * s) 2) (locCofactor (pairQJetBlocks (r * s)) 1 2)
        (pairQJetKappa₁ (r * s)) (pairQJetKappa₂ (r * s)) = -1 / 2 ∧
      locNodeIndex pairQJetDilation.c m₀ (ebNodeL (r * s) m₀)⁻¹
        (opJet1 (pairQJetRow (famTransferOp (r * s)))) (pairQJetBlocks (r * s) 2)
        (pairQJetBlocks (r * s) 1) (locCofactor (pairQJetBlocks (r * s)) 2 1)
        (pairQJetKappa₁ (r * s)) (pairQJetKappa₂ (r * s)) = -1 / 2 :=
  pairQJets_ebNode _ (pairQJets_two_le_of_isTorusPair h) heb

end AJConjecture
