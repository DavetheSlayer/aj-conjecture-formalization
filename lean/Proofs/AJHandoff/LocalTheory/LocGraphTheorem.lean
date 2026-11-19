import Mathlib
import AJHandoff.LocalTheory.LocNormalize
import AJHandoff.LocalTheory.LocPartition
import AJHandoff.LocalTheory.LocNodeResidue
import AJHandoff.LocalTheory.LocFactorIndexInt
import AJHandoff.LocalTheory.LocPseudoField

/-!
# I-NODE, Theorem 4: the obstruction graph

Let `P ∈ ℂ[[h]][z][u]` have positive order, residual symbol `P₀` of full degree with nonzero
constant coefficient, and residual blocks `B_i` (irreducible over `ℂ(z)`, pairwise not
associated). Join `i` and `j` when they meet at an allowed transverse mixed node `(z₀, λ)` whose
allocation index `I_{B_i}` (formula (4)) is not an integer.

* A factor partition cannot cross such an edge: for every pseudo-factorization `β P = S ⋆ R`,
  `B_i` divides `R₀` exactly when `B_j` does (`locBlockDvd_iff_of_forbiddenEdge`).
* If the graph is connected, `P` is irreducible in `ℂ((h))(z)[u; σ]`
  (`oreIrreducible_of_connected`).

Proof. Normalize (`exists_normalized_locPseudoFactor`); by Lemma 2 (`locResidual_partition`)
each block divides exactly one of `R₀`, `S₀`. If `B_i ∣ R₀` and `B_j ∣ S₀`, Lemma 3 gives the
normalized index `I_{B_i}` of `R`; if `B_j ∣ R₀` and `B_i ∣ S₀`, it gives
`I_{B_j} = -1 - I_{B_i}` (`locNodeIndex_swap`, `LocAllowedNode.symm`). Either is nonintegral,
contradicting `exists_int_hasNormalizedIndex_locLogJet` (via Lemma 1) and uniqueness of residues.
A connected graph crosses every nontrivial partition, and a factorization over `F` with both
degrees positive gives a nontrivial partition (Lemma 2); `oreIrreducible_map_iff` passes from
pseudo-factorizations over `ℂ[[h]][z]` to factorizations over `F`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Distinct residual blocks are coprime over `ℂ(z)`. -/
private theorem pairwise_isCoprime_graph {P : LocOp} {ι : Type*} [Fintype ι]
    {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) :
    Pairwise fun i j ↦ IsCoprime ((B i).map (algebraMap ℂ[X] (RatFunc ℂ)))
      ((B j).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
  intro i j hij
  rw [(hB.irreducible i).coprime_iff_not_dvd]
  exact fun hd ↦ hB.not_associated i j hij
    ((hB.irreducible i).associated_of_dvd (hB.irreducible j) hd)

/-- Over `ℂ(z)` the residual symbol is associated to the product of the blocks. -/
private theorem associated_prod_graph {P : LocOp} {ι : Type*} [Fintype ι]
    {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) :
    Associated ((opJet0 P).map (algebraMap ℂ[X] (RatFunc ℂ)))
      (∏ i, (B i).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
  obtain ⟨κ₁, κ₂, hκ₁, hκ₂, heq⟩ := hB.exists_eq
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hu : ∀ κ : ℂ[X], κ ≠ 0 → IsUnit (C (algebraMap ℂ[X] (RatFunc ℂ) κ)) := fun κ hκ ↦
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr hκ))
  have hmap : C (algebraMap ℂ[X] (RatFunc ℂ) κ₁) * (opJet0 P).map (algebraMap ℂ[X] (RatFunc ℂ)) =
      C (algebraMap ℂ[X] (RatFunc ℂ) κ₂) * ∏ i, (B i).map (algebraMap ℂ[X] (RatFunc ℂ)) := by
    rw [← Polynomial.map_C, ← Polynomial.map_C, ← Polynomial.map_prod, ← Polynomial.map_mul,
      ← Polynomial.map_mul, heq]
  have h1 := (associated_unit_mul_left ((opJet0 P).map (algebraMap ℂ[X] (RatFunc ℂ))) _
    (hu κ₁ hκ₁)).symm
  rw [hmap] at h1
  exact h1.trans (associated_unit_mul_left _ _ (hu κ₂ hκ₂))

/-- The residual symbol of a product of residual blocks is square-free over `ℂ(z)`. -/
private theorem squarefree_opJet0_graph {P : LocOp} {ι : Type*} [Fintype ι]
    {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) :
    Squarefree ((opJet0 P).map (algebraMap ℂ[X] (RatFunc ℂ))) :=
  (associated_prod_graph hB).squarefree_iff.mpr
    (Finset.squarefree_prod_of_pairwise_isCoprime
      (fun _ _ _ _ hij ↦ (pairwise_isCoprime_graph hB hij).isRelPrime)
      fun i _ ↦ (hB.irreducible i).squarefree)

/-- Each block divides one side of a pseudo-factorization. -/
private theorem locBlockDvd_or_graph (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (hfac : C β * P = oreMul δ.shiftHom S R) {ι : Type*} [Fintype ι]
    {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) (k : ι) :
    LocBlockDvd (B k) (opJet0 R) ∨ LocBlockDvd (B k) (opJet0 S) := by
  have hprod : opJet0 S * opJet0 R = C (locJet0 β) * opJet0 P := by
    rw [← opJet0_oreMul δ, ← hfac, opJet0, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hdvd : (B k).map (algebraMap ℂ[X] (RatFunc ℂ)) ∣
      (opJet0 S).map (algebraMap ℂ[X] (RatFunc ℂ)) *
        (opJet0 R).map (algebraMap ℂ[X] (RatFunc ℂ)) := by
    rw [← Polynomial.map_mul, hprod, Polynomial.map_mul]
    exact ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (associated_prod_graph hB).symm.dvd).trans (dvd_mul_left _ _)
  exact ((hB.irreducible k).prime.dvd_or_dvd hdvd).symm

/-- Factor partitions cannot cross a nonintegral edge. -/
theorem locBlockDvd_iff_of_forbiddenEdge (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (hβ : locJet0 β ≠ 0) (hfac : C β * P = oreMul δ.shiftHom S R) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) {κ₁ κ₂ : ℂ[X]} {i j : ι}
    {z₀ lam : ℂ} (hn : LocAllowedNode P B κ₁ κ₂ i j z₀ lam)
    (hI : ∀ n : ℤ, locNodeIndex δ.c z₀ lam (opJet1 P) (B i) (B j) (locCofactor B i j) κ₁ κ₂ ≠ n) :
    LocBlockDvd (B i) (opJet0 R) ↔ LocBlockDvd (B j) (opJet0 R) := by
  obtain ⟨n, hnI⟩ := exists_int_hasNormalizedIndex_locLogJet δ hβ hfac hn.z₀_ne hn.natDegree_eq
    hn.lead_ne hn.const_ne
  constructor
  · intro hi
    by_contra hj
    have hjS := (locBlockDvd_or_graph δ hfac hB j).resolve_left hj
    exact hI n ((hasNormalizedIndex_locNodeIndex δ hβ hfac hB hn hi hjS).unique hnI)
  · intro hj
    by_contra hi
    have hiS := (locBlockDvd_or_graph δ hfac hB i).resolve_left hi
    have h := hasNormalizedIndex_locNodeIndex δ hβ hfac hB hn.symm hj hiS
    rw [locCofactor_swap, locNodeIndex_swap δ.c_ne_zero hn.z₀_ne hn.lam_ne hn.jac] at h
    have h' := h.unique hnI
    exact hI (-1 - n) (by push_cast; linear_combination -h')

/-- **Theorem 4.** A connected obstruction graph proves irreducibility over `ℂ((h))(z)`. -/
theorem oreIrreducible_of_connected (δ : LocDilation) {P : LocOp} (hpos : 0 < P.natDegree)
    (hdeg : (opJet0 P).natDegree = P.natDegree) (hconst : (opJet0 P).coeff 0 ≠ 0) {ι : Type*}
    [Fintype ι] [DecidableEq ι] {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B)
    (Γ : SimpleGraph ι) (hΓ : Γ.Connected)
    (hedge : ∀ i j, Γ.Adj i j → ∃ (κ₁ κ₂ : ℂ[X]) (z₀ lam : ℂ),
      LocAllowedNode P B κ₁ κ₂ i j z₀ lam ∧
        ∀ n : ℤ, locNodeIndex δ.c z₀ lam (opJet1 P) (B i) (B j) (locCofactor B i j) κ₁ κ₂ ≠ n) :
    OreIrreducible δ.fieldShiftHom (P.map (algebraMap LocPoly LocField)) := by
  rw [oreIrreducible_map_iff δ.shiftHom δ.fieldShiftHom
    (fun a ↦ by exact δ.fieldShift_algebraMap a) hpos]
  intro β hβ S R h
  have hP0 : opJet0 P ≠ 0 := fun h0 ↦ hconst (by rw [h0, coeff_zero])
  obtain ⟨β', S', R', hβ', hS', hR', -, hRd, hfac', -⟩ :=
    exists_normalized_locPseudoFactor δ hP0 hβ h
  rw [← hRd]
  obtain ⟨hprod, hRdeg, hSdeg, -, -, -⟩ :=
    locResidual_partition δ hβ' hfac' hdeg hconst (squarefree_opJet0_graph hB)
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hdegK : ∀ Q : ℂ[X][X], (Q.map (algebraMap ℂ[X] (RatFunc ℂ))).natDegree = Q.natDegree :=
    fun Q ↦ Polynomial.natDegree_map_eq_of_injective hinj Q
  have hsum : (opJet0 S').natDegree + (opJet0 R').natDegree = P.natDegree := by
    rw [← Polynomial.natDegree_mul hS' hR', hprod, Polynomial.natDegree_C_mul hβ', hdeg]
  have hadj : ∀ i j, Γ.Adj i j →
      (LocBlockDvd (B i) (opJet0 R') ↔ LocBlockDvd (B j) (opJet0 R')) := fun i j hij ↦ by
    obtain ⟨κ₁, κ₂, z₀, lam, hn, hI⟩ := hedge i j hij
    exact locBlockDvd_iff_of_forbiddenEdge δ hβ' hfac' hB hn hI
  have hwalk : ∀ (u v : ι) (w : Γ.Walk u v),
      (LocBlockDvd (B u) (opJet0 R') ↔ LocBlockDvd (B v) (opJet0 R')) := by
    intro u v w
    induction w with
    | nil => exact Iff.rfl
    | cons hadj' _ ih => exact (hadj _ _ hadj').trans ih
  by_cases hex : ∃ i, LocBlockDvd (B i) (opJet0 R')
  · right
    obtain ⟨i, hi⟩ := hex
    have hall : ∀ j, LocBlockDvd (B j) (opJet0 R') := fun j ↦
      (hwalk i j (hΓ.preconnected i j).some).mp hi
    have hdvd := Fintype.prod_dvd_of_coprime (pairwise_isCoprime_graph hB) hall
    have hRK : (opJet0 R').map (algebraMap ℂ[X] (RatFunc ℂ)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinj).mpr hR'
    have hle := Polynomial.natDegree_le_of_dvd hdvd hRK
    rw [← Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated (associated_prod_graph hB)), hdegK, hdegK,
      hdeg] at hle
    omega
  · left
    push Not at hex
    rw [← hRdeg, ← hdegK]
    by_contra hne
    have hRK : (opJet0 R').map (algebraMap ℂ[X] (RatFunc ℂ)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinj).mpr hR'
    obtain ⟨q, hq, hqR⟩ := WfDvdMonoid.exists_irreducible_factor
      (fun hu ↦ hne (Polynomial.natDegree_eq_zero_of_isUnit hu)) hRK
    have hqP : q ∣ ∏ i, (B i).map (algebraMap ℂ[X] (RatFunc ℂ)) := by
      refine (hqR.trans (dvd_mul_left _ ((opJet0 S').map (algebraMap ℂ[X] (RatFunc ℂ))))).trans ?_
      rw [← Polynomial.map_mul, hprod, Polynomial.map_mul, Polynomial.map_C]
      exact (associated_unit_mul_left _ _ (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _ hinj).mpr hβ')))).dvd.trans (associated_prod_graph hB).dvd
    obtain ⟨i, -, hqi⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqP
    exact hex i ((hq.associated_of_dvd (hB.irreducible i) hqi).symm.dvd.trans hqR)


end AJConjecture
