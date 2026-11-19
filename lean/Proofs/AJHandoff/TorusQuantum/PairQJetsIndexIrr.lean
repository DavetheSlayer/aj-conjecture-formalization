import Mathlib
import AJHandoff.LocalTheory.LocGraphTheorem
import AJHandoff.TorusQuantum.PairQJetsIndex

/-!
# T-JETS ⇒ irreducibility of the backward row over `ℂ((h))(z)`

The obstruction graph of the backward row of `famTransferOp m` (`m ≥ 2`) has the edges
`Ĉ — B̂_m` (abelian node) and `Ê — B̂_m` (E/B node), both with allocation index `-1/2 ∉ ℤ`
(`pairQJets_abNode`, `pairQJets_ebNode`). It is connected, so Theorem 4 of the local theory
(`oreIrreducible_of_connected`) shows that the row is irreducible in `ℂ((h))(z)[u; σ]`,
`σ(z) = exp(-h/2) z`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The obstruction graph on the blocks `Ĉ, Ê, B̂_m`: edges `Ĉ — B̂_m` and `Ê — B̂_m`. -/
def pairQJetGraph : SimpleGraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
  symm := ⟨fun i j h ↦ by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
  loopless := ⟨fun i h ↦ by rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp at h⟩

theorem pairQJetGraph_connected : pairQJetGraph.Connected := by
  have h2 : ∀ i, pairQJetGraph.Reachable i 2 := fun i ↦ by
    fin_cases i
    · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, rfl⟩)
    · exact SimpleGraph.Adj.reachable (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · exact SimpleGraph.Reachable.refl _
  exact ⟨fun i j ↦ (h2 i).trans (h2 j).symm⟩

/-- `-1/2` is not an integer. -/
private theorem neg_half_ne_int (n : ℤ) : (-1 / 2 : ℂ) ≠ n := fun h ↦ by
  have h2 : ((2 * n : ℤ) : ℂ) = ((-1 : ℤ) : ℂ) := by push_cast; rw [← h]; ring
  have h3 := Int.cast_injective h2
  omega

/-- A point over the abelian node. -/
private theorem exists_abNode_point_jets (m : ℕ) (hm : 2 ≤ m) :
    ∃ m₀ : ℂ, (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hmC
    (IsAlgClosed.isSquare (discrim (m : ℂ) (-(2 * m + 1)) m))
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- A point over the E/B node. -/
private theorem exists_ebNode_point_jets (m : ℕ) (hm : 2 ≤ m) : ∃ m₀ : ℂ,
    (m : ℂ) * (2 * m + 1) * (m₀ ^ 2) ^ 2 + (4 * m ^ 2 + 2 * m + 1) * m₀ ^ 2 +
      m * (2 * m + 1) = 0 := by
  have ha : (m : ℂ) * (2 * m + 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0))
      (by exact_mod_cast (by omega : 2 * m + 1 ≠ 0))
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha (IsAlgClosed.isSquare
    (discrim ((m : ℂ) * (2 * m + 1)) (4 * m ^ 2 + 2 * m + 1) (m * (2 * m + 1))))
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- **T-JETS ⇒ T-IRR over `ℂ((h))(z)`.** For `m ≥ 2` the backward row of `famTransferOp m` is
irreducible in `ℂ((h))(z)[u; σ]`, `σ(z) = exp(-h/2) z`. -/
theorem pairQJets_oreIrreducible (m : ℕ) (hm : 2 ≤ m) :
    OreIrreducible pairQJetDilation.fieldShiftHom
      ((pairQJetRow (famTransferOp m)).map (algebraMap LocPoly LocField)) := by
  obtain ⟨a₀, hab⟩ := exists_abNode_point_jets m hm
  obtain ⟨e₀, heb⟩ := exists_ebNode_point_jets m hm
  obtain ⟨hna, ha1, ha2⟩ := pairQJets_abNode m hm hab
  obtain ⟨hne, he1, he2⟩ := pairQJets_ebNode m hm heb
  have hS00 : (pairQJetSymbol (famTransferOp m)).coeff 0 ≠ 0 := by
    have h := (eval_coeff_specialize_famTransferOp_ne_zero m (by omega) (m₀ := 2) (by norm_num)
      (by norm_num) (by norm_num)).2
    intro h0
    rw [pairQJetSymbol, coeff_map, coe_mapRingHom] at h0
    rw [h0, eval_zero] at h
    exact h rfl
  have hpos : 0 < (pairQJetRow (famTransferOp m)).natDegree := by
    rw [(natDegree_pairQJetRow hS00).2, natDegree_famTransferOp m (by omega)]
    omega
  refine oreIrreducible_of_connected pairQJetDilation hpos hna.natDegree_eq
    (fun h0 ↦ hna.const_ne (by rw [h0, eval_zero])) (pairQJets_residualBlocks m hm)
    pairQJetGraph pairQJetGraph_connected fun i j hij ↦ ?_
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, _, _, hna, fun n ↦ by rw [ha1]; exact neg_half_ne_int n⟩
  · exact ⟨_, _, _, _, hna.symm, fun n ↦ by rw [ha2]; exact neg_half_ne_int n⟩
  · exact ⟨_, _, _, _, hne, fun n ↦ by rw [he1]; exact neg_half_ne_int n⟩
  · exact ⟨_, _, _, _, hne.symm, fun n ↦ by rw [he2]; exact neg_half_ne_int n⟩

end AJConjecture
