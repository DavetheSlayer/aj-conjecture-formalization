import Mathlib
import AJConjecture.ExtraFactorIrreducible
import AJConjecture.QAlgTwistFactorPrime
import AJFamily.Quantum.FamSymbol
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.FamTransferOpIrreducible
import AJFamily.Quantum.AbNodeFacts
import AJFamily.Quantum.AbNodeWeyl
import AJFamily.Quantum.AbNodeCollision
import AJFamily.Quantum.EbNodeFacts
import AJFamily.Quantum.EbNodeWeyl
import AJFamily.Quantum.EbNodeCollision
import AJFamily.Quantum.TwistPolyPrime
import AJFamily.Quantum.TwistPolyIrreducible
import AJHandoff.PairDefs

/-!
# T-BLOCK, T-JETS and T-IRR for every torus pair

The transfer operator `P_m = famTransferOp m` depends only on `m`, and the library proves its
symbol, its two nodes and its irreducibility for every `m ≥ 2` (no parity hypothesis; the
statements are uniform in `m` and are applied here to `m = rs`, which is odd when `r` and `s`
are odd, e.g. `m = 15` for `(3, 5)`).

* T-BLOCK (`pairQ_symbol`, `pairQ_block`, `pairQ_symbol_ends`): `κ₁ P_(m,0) = κ₂ (L-1) E B_m` in
  `ℤ[M][L]` with `κ₁, κ₂ ∈ ℤ[M]` nonzero (source Q12, forward convention: the backward row
  `L^(-d)(L-1)EB_m` is its reversal); the three factors are prime in `ℚ(M)[L,L⁻¹]`, irreducible
  over `ℂ` resp. `ℂ(M)`, of degrees `1, 2, 2m` (pairwise distinct as `m ≥ 2`); both end
  coefficients of the symbol survive at every `M = m₀` with `m₀ ≠ 0`, `m₀² ≠ ±1`.
* T-JETS (`pairQ_abNode`, `pairQ_ebNode`): at the abelian node (`L-1` meets `B_m`) and at the
  E/B node, the Weyl symbol of `P_m` vanishes and the node is collision free, with the
  transversality facts of the library. In the language of the source this is "both allocation
  indices are `-1/2`" (manuscript, Remark QC:rem:index); the library has no definition of the
  index and uses the index criterion instead of the joint-regularity lattice of the source, so
  "jointly invertible companion over the full field lift" is replaced by the end-coefficient
  clause of `pairQ_symbol_ends` (hypothesis (N3) of the criterion).
* T-IRR (`pairQ_transferOp_irreducible`): `P_m` has order exactly `2m + 3` and every
  pseudo-factorization `β P_m = S ⋆ R` (`β ∈ ℤ[t][M]` nonzero, `S, R ∈ ℤ[t][M][L]`) has
  `deg_L R ∈ {0, 2m + 3}`. The passage to irreducibility in the Ore ring
  `ℚ(t, M)[L, L⁻¹; τ]` (clearing denominators and `L`-powers) is interpretation, as in the
  manuscript (Remark QB:rem:field).
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem pairQ_rs_ge (r s : ℕ) (h : IsTorusPair r s) : 6 ≤ r * s := by
  obtain ⟨hr, hrs, -⟩ := h
  nlinarith

/-- T-BLOCK, the symbol: `κ₁ P_(rs,0) = κ₂ (L - 1) E B_(rs)`. -/
theorem pairQ_symbol (r s : ℕ) (h : IsTorusPair r s) :
    C ((X ^ 2 - 1) ^ (2 * (r * s) + 3) * (X ^ 4 - 1) ^ (2 * (r * s) + 3)) *
        specialize (famTransferOp (r * s)) =
      C ((famDet (r * s) (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) *
        ((X - 1) * extraFactor * twistPoly (r * s)) :=
  specialize_famTransferOp_mul_eq (r * s) (by have := pairQ_rs_ge r s h; omega)

/-- T-BLOCK, the three blocks: prime in the comparison ring, irreducible over `ℂ` (resp. `ℂ(M)`),
of degrees `1`, `2`, `2rs`. -/
theorem pairQ_block (r s : ℕ) (h : IsTorusPair r s) :
    Prime (toComparison (X - 1)) ∧ Prime (toComparison extraFactor) ∧
      Prime (toComparison (twistPoly (r * s))) ∧
      Irreducible (extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) ∧
      Irreducible ((twistPoly (r * s)).map
        ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) ∧
      (X - 1 : ℤ[X][X]).natDegree = 1 ∧ extraFactor.natDegree = 2 ∧
      (twistPoly (r * s)).natDegree = 2 * (r * s) := by
  have hm : 2 ≤ r * s := by have := pairQ_rs_ge r s h; omega
  exact ⟨prime_toComparison_X_sub_one, prime_toComparison_extraFactor,
    prime_toComparison_twistPoly _ hm, irreducible_extraFactor_map,
    irreducible_twistPoly_ratFunc _ hm, natDegree_X_sub_one, natDegree_extraFactor,
    natDegree_twistPoly _⟩

/-- T-BLOCK, both endpoints survive: the leading and the constant coefficient of the symbol are
nonzero at every `M = m₀` with `m₀ ≠ 0`, `m₀² ≠ ±1`. -/
theorem pairQ_symbol_ends (r s : ℕ) (h : IsTorusPair r s) {m₀ : ℂ} (h0 : m₀ ≠ 0)
    (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ -1) :
    ((specialize (famTransferOp (r * s))).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0 ∧
      (((specialize (famTransferOp (r * s))).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0 :=
  eval_coeff_specialize_famTransferOp_ne_zero (r * s)
    (by have := pairQ_rs_ge r s h; omega) h0 h1 h2

/-- T-JETS at the abelian node (`L - 1` meets `B_(rs)`): the Weyl symbol vanishes, the node is
collision free, and the node facts of the library hold. -/
theorem pairQ_abNode (r s : ℕ) (h : IsTorusPair r s) {m₀ : ℂ}
    (hab : ((r * s : ℕ) : ℂ) * (m₀ ^ 2) ^ 2 - (2 * ((r * s : ℕ) : ℂ) + 1) * m₀ ^ 2 +
      ((r * s : ℕ) : ℂ) = 0) :
    evalIntPoint (weylSymbol (famTransferOp (r * s))) m₀ 1 = 0 ∧
      NodeCollisionFree (X - 1) (twistPoly (r * s)) extraFactor m₀ 1 ∧
      (m₀ ≠ 0 ∧ m₀ ^ 2 ≠ 1 ∧ m₀ ^ 2 ≠ -1 ∧
        evalIntPoint (twistPoly (r * s)) m₀ 1 = 0 ∧ evalIntPoint extraFactor m₀ 1 ≠ 0 ∧
        evalIntPoint (derivative (twistPoly (r * s))) m₀ 1 ≠ 0 ∧
        evalIntPoint (coeffDerivative (twistPoly (r * s))) m₀ 1 ≠ 0) := by
  have hm : 2 ≤ r * s := by have := pairQ_rs_ge r s h; omega
  exact ⟨evalIntPoint_weylSymbol_famTransferOp_abNode _ hm hab,
    abNode_collisionFree _ hm hab, abNode_facts _ hm hab⟩

/-- T-JETS at the E/B node (`E` meets `B_(rs)`): the Weyl symbol vanishes and the node is
collision free; `E` and `B_(rs)` both vanish there with independent gradients. -/
theorem pairQ_ebNode (r s : ℕ) (h : IsTorusPair r s) {m₀ : ℂ}
    (heb : ((r * s : ℕ) : ℂ) * (2 * ((r * s : ℕ) : ℂ) + 1) * (m₀ ^ 2) ^ 2 +
      (4 * ((r * s : ℕ) : ℂ) ^ 2 + 2 * ((r * s : ℕ) : ℂ) + 1) * m₀ ^ 2 +
      ((r * s : ℕ) : ℂ) * (2 * ((r * s : ℕ) : ℂ) + 1) = 0) :
    evalIntPoint (weylSymbol (famTransferOp (r * s))) m₀ (ebNodeL (r * s) m₀) = 0 ∧
      NodeCollisionFree extraFactor (twistPoly (r * s)) (X - 1) m₀ (ebNodeL (r * s) m₀) ∧
      evalIntPoint extraFactor m₀ (ebNodeL (r * s) m₀) = 0 ∧
      evalIntPoint (twistPoly (r * s)) m₀ (ebNodeL (r * s) m₀) = 0 ∧
      evalIntPoint (derivative extraFactor) m₀ (ebNodeL (r * s) m₀) *
          evalIntPoint (coeffDerivative (twistPoly (r * s))) m₀ (ebNodeL (r * s) m₀) -
        evalIntPoint (coeffDerivative extraFactor) m₀ (ebNodeL (r * s) m₀) *
          evalIntPoint (derivative (twistPoly (r * s))) m₀ (ebNodeL (r * s) m₀) ≠ 0 := by
  have hm : 2 ≤ r * s := by have := pairQ_rs_ge r s h; omega
  obtain ⟨-, -, -, -, -, -, -, hE, hB, -, -, hJ⟩ := ebNode_facts _ hm heb
  exact ⟨evalIntPoint_weylSymbol_famTransferOp_ebNode _ hm heb,
    ebNode_collisionFree _ hm heb, hE, hB, hJ⟩

/-- T-IRR: the transfer operator of `T(r, s)` has order `2rs + 3` and no right pseudo-factor of
intermediate order. -/
theorem pairQ_transferOp_irreducible (r s : ℕ) (h : IsTorusPair r s) :
    (famTransferOp (r * s)).natDegree = 2 * (r * s) + 3 ∧
      ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp},
        C β * famTransferOp (r * s) = oreMul coeffShift S R →
          R.natDegree = 0 ∨ R.natDegree = 2 * (r * s) + 3 := by
  have hm : 2 ≤ r * s := by have := pairQ_rs_ge r s h; omega
  exact ⟨natDegree_famTransferOp _ (by omega),
    fun hβ _ _ hR ↦ natDegree_eq_zero_or_of_oreMul_eq_famTransferOp _ hm hβ hR⟩

end AJConjecture
