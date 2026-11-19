import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.ExtraFactorIrreducible
import AJFamily.Quantum.AbNodeNoSeparation
import AJFamily.Quantum.TwistPolyIrreducible
import AJHandoff.LocalTheory.LocNodeData
import AJHandoff.TorusQuantum.PairQJetsIndexBlock

/-!
# T-JETS: the residual blocks `Ĉ, Ê, B̂_m` of the backward row

`pairQJets_residualBlocks`: for `m ≥ 2` the reversals of `C = L - 1`, `E`, `B_m` form a residual
block decomposition (`LocResidualBlocks`) of the backward row of `famTransferOp m`: their product
is the residual symbol up to the nonzero scalars `κ₁, κ₂ ∈ ℂ[z]`, each is irreducible over
`ℂ(z)` (reversal preserves irreducibility of a polynomial with nonzero constant term), and they
have the distinct degrees `1, 2, 2m`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The three residual blocks of the backward row: the reversals of `C = L - 1`, `E`, `B_m`. -/
def pairQJetBlocks (m : ℕ) (i : Fin 3) : ℂ[X][X] :=
  pairQJetBlock (![X - 1, extraFactor, twistPoly m] i)

/-- The normalizing scalar `κ₁ = (z² - 1)^d (z⁴ - 1)^d` of the residual symbol. -/
def pairQJetKappa₁ (m : ℕ) : ℂ[X] :=
  ((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3) : ℤ[X]).map (Int.castRingHom ℂ)

/-- The normalizing scalar `κ₂ = Δ_m(1, z²) (z² + 1)² (z² - 1)` of the residual symbol. -/
def pairQJetKappa₂ (m : ℕ) : ℂ[X] :=
  ((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)) : ℤ[X]).map
    (Int.castRingHom ℂ)

/-- The forward symbol identity `κ₁ P₀ = κ₂ ∏ b_i` over `Fin 3`. -/
theorem pairQJets_forwardSym (m : ℕ) (hm : 1 ≤ m) :
    C ((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3)) * specialize (famTransferOp m) =
      C ((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) *
        ∏ i, ![X - 1, extraFactor, twistPoly m] i := by
  rw [specialize_famTransferOp_mul_eq m hm, Fin.prod_univ_three]
  rfl

/-- Reversal preserves irreducibility over a field when the constant term is nonzero. -/
theorem irreducible_reverse_pairQ {K : Type*} [Field K] {p : K[X]} (hp : Irreducible p)
    (h0 : p.coeff 0 ≠ 0) : Irreducible p.reverse := by
  have hdeg : ∀ q : K[X], q.coeff 0 ≠ 0 → q.reverse.natDegree = q.natDegree := fun q hq ↦ by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hq), Nat.sub_zero]
  have hrr : p.reverse.reverse = p := by
    rw [reverse, hdeg p h0, reverse, reflect_reflect]
  refine ⟨fun hu ↦ ?_, fun a b hab ↦ ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    rw [hdeg p h0] at this
    exact (Irreducible.natDegree_pos hp).ne' this
  · have hc : a.coeff 0 * b.coeff 0 ≠ 0 := by
      rw [← mul_coeff_zero, ← hab, coeff_zero_reverse]
      exact leadingCoeff_ne_zero.mpr hp.ne_zero
    have hp' : p = a.reverse * b.reverse := by rw [← hrr, hab, reverse_mul_of_domain]
    have hunit : ∀ q : K[X], q.coeff 0 ≠ 0 → IsUnit q.reverse → IsUnit q := fun q hq hu ↦ by
      have h1 := natDegree_eq_zero_of_isUnit hu
      rw [hdeg q hq] at h1
      rw [eq_C_of_natDegree_eq_zero h1]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hq)
    rcases hp.isUnit_or_isUnit hp' with h | h
    · exact Or.inl (hunit a (left_ne_zero_of_mul hc) h)
    · exact Or.inr (hunit b (right_ne_zero_of_mul hc) h)

/-- The map `ℤ[M] → ℂ(M)`. -/
private abbrev pairQJetToRatFunc : ℤ[X] →+* RatFunc ℂ :=
  (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ))

private theorem pairQJetToRatFunc_injective : Function.Injective pairQJetToRatFunc :=
  (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
    (Polynomial.map_injective _ (Int.cast_injective (α := ℂ)))

/-- A reversed block over `ℂ(z)` is the reversal of the block over `ℂ(M)`. -/
private theorem map_pairQJetBlock (b : ℤ[X][X]) :
    (pairQJetBlock b).map (algebraMap ℂ[X] (RatFunc ℂ)) = (b.map pairQJetToRatFunc).reverse := by
  rw [pairQJetBlock, reverse, reverse, natDegree_map_eq_of_injective pairQJetToRatFunc_injective,
    natDegree_map_intCast_pairQ, ← reflect_map, Polynomial.map_map]

/-- The blocks of the forward symbol, over `ℂ(M)`: irreducible, nonzero constant term. -/
private theorem pairQJets_block_facts (m : ℕ) (hm : 2 ≤ m) (i : Fin 3) :
    Irreducible ((![X - 1, extraFactor, twistPoly m] i).map pairQJetToRatFunc) ∧
      ((![X - 1, extraFactor, twistPoly m] i).map pairQJetToRatFunc).coeff 0 ≠ 0 := by
  have hX : ∀ k : ℕ, pairQJetToRatFunc (X ^ k) ≠ 0 := fun k ↦
    (map_ne_zero_iff _ pairQJetToRatFunc_injective).mpr (pow_ne_zero k X_ne_zero)
  have hC : Irreducible ((X - 1 : ℤ[X][X]).map pairQJetToRatFunc) ∧
      ((X - 1 : ℤ[X][X]).map pairQJetToRatFunc).coeff 0 ≠ 0 := by
    refine ⟨irreducible_of_degree_eq_one ?_, by simp⟩
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
    exact degree_X_sub_C 1
  have hE : Irreducible (extraFactor.map pairQJetToRatFunc) ∧
      (extraFactor.map pairQJetToRatFunc).coeff 0 ≠ 0 := by
    refine ⟨?_, by rw [coeff_map, extraFactor_coeff_zero]; exact hX 4⟩
    have h := irreducible_extraFactor_map
    have hmon : (extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).Monic :=
      extraFactor_monic.map _
    rw [hmon.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℂ),
      Polynomial.map_map] at h
    exact h
  have hB : Irreducible ((twistPoly m).map pairQJetToRatFunc) ∧
      ((twistPoly m).map pairQJetToRatFunc).coeff 0 ≠ 0 :=
    ⟨irreducible_twistPoly_ratFunc m hm, by rw [coeff_map, coeff_zero_twistPoly]; exact hX _⟩
  match i with
  | 0 => exact hC
  | 1 => exact hE
  | 2 => exact hB

/-- The degrees `1, 2, 2m` of the blocks. -/
private theorem pairQJets_block_natDegree (m : ℕ) (i : Fin 3) :
    (![X - 1, extraFactor, twistPoly m] i).natDegree = ![1, 2, 2 * m] i := by
  match i with
  | 0 => exact natDegree_X_sub_one
  | 1 => exact natDegree_extraFactor
  | 2 => exact natDegree_twistPoly m

/-- **T-JETS, residual blocks.** For `m ≥ 2`, `Ĉ, Ê, B̂_m` are residual blocks of the backward
row of `famTransferOp m`. -/
theorem pairQJets_residualBlocks (m : ℕ) (hm : 2 ≤ m) :
    LocResidualBlocks (pairQJetRow (famTransferOp m)) (pairQJetBlocks m) := by
  have hdeg : (specialize (famTransferOp m)).natDegree = (famTransferOp m).natDegree := by
    rw [natDegree_specialize_famTransferOp m (by omega), natDegree_famTransferOp m (by omega)]
  have h2 : (2 : ℂ) ^ 2 ≠ 1 := by norm_num
  have h2' : (2 : ℂ) ^ 2 ≠ -1 := by norm_num
  refine ⟨⟨pairQJetKappa₁ m, pairQJetKappa₂ m, fun h0 ↦ ?_, fun h0 ↦ ?_,
    pairQJet_sym (pairQJets_forwardSym m (by omega)) hdeg⟩, fun i ↦ ?_, fun i j hij hass ↦ ?_⟩
  · exact eval_symbolLeft_ne_zero m h2 h2' (by rw [← pairQJetKappa₁, h0, eval_zero])
  · exact eval_symbolRight_ne_zero m h2 h2' (by rw [← pairQJetKappa₂, h0, eval_zero])
  · rw [pairQJetBlocks, map_pairQJetBlock]
    obtain ⟨hi, hi0⟩ := pairQJets_block_facts m hm i
    exact irreducible_reverse_pairQ hi hi0
  · rw [pairQJetBlocks, pairQJetBlocks, map_pairQJetBlock, map_pairQJetBlock] at hass
    have hd := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hass)
    have hn : ∀ k, ((![X - 1, extraFactor, twistPoly m] k).map pairQJetToRatFunc).reverse.natDegree
        = (![X - 1, extraFactor, twistPoly m] k).natDegree := fun k ↦ by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr
        (Or.inr (pairQJets_block_facts m hm k).2), Nat.sub_zero,
        natDegree_map_eq_of_injective pairQJetToRatFunc_injective]
    rw [hn, hn, pairQJets_block_natDegree, pairQJets_block_natDegree] at hd
    fin_cases i <;> fin_cases j <;> simp_all
    omega

end AJConjecture
