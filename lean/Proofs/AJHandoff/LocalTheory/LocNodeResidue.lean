import Mathlib
import AJConjecture.QAlgSyzygyResidue
import AJConjecture.QAlgNodeIndexArith
import AJHandoff.LocalTheory.LocHJet
import AJHandoff.LocalTheory.LocSymContent
import AJHandoff.LocalTheory.LocSymDivided
import AJHandoff.LocalTheory.LocSymRemainder
import AJHandoff.LocalTheory.LocBlockFibre

/-!
# I-NODE: the determinant residue of a right factor at an allowed node (Lemma 3)

Let `β P = S ⋆ R` be a normalized pseudo-factorization (`β₀ ≠ 0`) and `(z₀, λ)` an allowed
transverse mixed node of the blocks `G = B g`, `H = B h`, with `G` dividing `R₀` and `H` dividing
`S₀` over `ℂ(z)`. Then the logarithmic first jet `ν/Δ` of `r₀/r_d` (that of the companion
determinant `(-1)^d r₀/r_d` of the monic right factor `r_d⁻¹ R`) has at most a simple pole at
`z₀`, with residue `c z₀ I_G`, `I_G` given by formula (4); equivalently its normalized index is
`I_G`.

Proof (port of the library's `pow_dvd_nodeNumer_of_separating_collision`, Theorem C, with the
shift constant `c` and the block fibre lemma): contents (`exists_locNodeContent`), the fibre at
the node (`exists_locNodeFibre`), end coefficients (`locNodeContent_ends`), the divided
first-jet equation (`exists_locNodeSyzygy`), the library's field-generic
`exists_mul_eq_pow_mul_of_syzygy` and `pow_dvd_of_residue_identity`, the value of `N*` at the
node (`eval_locNodeRemainder`), and `hasSimpleResidue_of_pow_dvd`. With
`∇R* = λ_R ∇G`, `∇S* = λ_S ∇H` and `κ₁ λ_R λ_S = β* κ₂ T`, the residue
`-(β* P₁ - c λ z₀ ∂_u S* ∂_z R*)/(λ J*)`, `J* = λ_R λ_S J`, becomes
`-(κ₁ P₁/(κ₂ T) - c λ z₀ H_u G_z)/(λ J) = c z₀ I_G`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The cofactor does not vanish at an allowed node. -/
private theorem evalPoint_locCofactor_ne_zero_nodeResidue {P : LocOp} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {B : ι → ℂ[X][X]} {κ₁ κ₂ : ℂ[X]} {g h : ι} {z₀ lam : ℂ}
    (hn : LocAllowedNode P B κ₁ κ₂ g h z₀ lam) :
    evalPoint (locCofactor B g h) (z₀, lam) ≠ 0 := by
  rw [locCofactor, evalPoint,
    show ((∏ i ∈ (Finset.univ.erase g).erase h, B i).eval₂ (Polynomial.evalRingHom (z₀, lam).1)
      (z₀, lam).2) = ∏ i ∈ (Finset.univ.erase g).erase h, evalPoint (B i) (z₀, lam) from
      map_prod (Polynomial.eval₂RingHom (Polynomial.evalRingHom z₀) lam) B _]
  refine Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_
  obtain ⟨hih, hi'⟩ := Finset.mem_erase.mp hi
  exact hn.other i (Finset.ne_of_mem_erase hi') hih

/-- The arithmetic of the residue at the node: with `y λ λ_R λ_S J = -N̄ r₀*`,
`N̄ = s* r* (β* P₁ - c λ z₀ λ_S H_u λ_R G_z)` and `κ₁ λ_R λ_S = β* κ₂ T`, the value `y(z₀)` is
`c z₀ I_G r₀* r* s*`. -/
private theorem residue_value_nodeResidue {c z₀ lam y Nb r0 rs ss bs P1 lR lS Gu Gz Hu Hz k1 k2
    T : ℂ} (hc : c ≠ 0) (hz₀ : z₀ ≠ 0) (hlam : lam ≠ 0) (hJ : Gu * Hz - Hu * Gz ≠ 0)
    (hk2 : k2 ≠ 0) (hT : T ≠ 0) (hl : lR * lS ≠ 0)
    (hres : y * (lam * (lR * Gu * (lS * Hz) - lS * Hu * (lR * Gz))) = -(Nb * r0))
    (hN : Nb = ss * rs * (bs * P1 - c * lam * z₀ * (lS * Hu) * (lR * Gz)))
    (hκ : k1 * (lR * lS) = bs * k2 * T) :
    y = c * z₀ * (-((k1 * P1) / (k2 * T) - lam * (c * z₀) * Hu * Gz) /
      (c * z₀ * lam * (Gu * Hz - Hu * Gz))) * (r0 * rs * ss) := by
  subst hN
  field_simp
  apply mul_left_cancel₀ hl
  linear_combination (k2 * T) * hres + (P1 * r0 * rs * ss) * hκ

/-- The residue of the logarithmic first jet of `r₀/r_d` at an allowed node is `c z₀ I_G`. -/
theorem hasSimpleResidue_locLogJet_of_allowedNode (δ : LocDilation) {P S R : LocOp}
    {β : LocPoly} (hβ : locJet0 β ≠ 0) (hfac : C β * P = oreMul δ.shiftHom S R) {ι : Type*}
    [Fintype ι] [DecidableEq ι] {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B)
    {κ₁ κ₂ : ℂ[X]} {g h : ι} {z₀ lam : ℂ} (hn : LocAllowedNode P B κ₁ κ₂ g h z₀ lam)
    (hRg : LocBlockDvd (B g) (opJet0 R)) (hSh : LocBlockDvd (B h) (opJet0 S)) :
    HasSimpleResidue
      (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetNum R) / algebraMap ℂ[X] (RatFunc ℂ) (locLogJetDen R))
      z₀ (δ.c * z₀ * locNodeIndex δ.c z₀ lam (opJet1 P) (B g) (B h) (locCofactor B g h) κ₁ κ₂) := by
  -- 1. contents
  obtain ⟨a, b, βs, Ss, Rs, hR, hS, hβ0, hβs, hfac', -, -⟩ :=
    exists_locNodeContent (z₀ := z₀) δ hβ hfac hn.lead_ne
  -- 2. the fibre at the node
  obtain ⟨Rc, lR, lS, hRc, hSroot, hcop, hRu, hRz, hSu, hSz, hκ⟩ :=
    exists_locNodeFibre hB hn hRg hSh hR hS hβs hfac'
  have hRroot : (Rs.map (Polynomial.evalRingHom z₀)).eval lam = 0 := by
    rw [hRc, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hT := evalPoint_locCofactor_ne_zero_nodeResidue hn
  have hl : lR * lS ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hκ
    exact mul_ne_zero (mul_ne_zero hβs hn.κ₂_ne) hT hκ.symm
  have hJne : (derivative (Rs.map (Polynomial.evalRingHom z₀))).eval lam *
        ((innerDerivative Ss).map (Polynomial.evalRingHom z₀)).eval lam -
      (derivative (Ss.map (Polynomial.evalRingHom z₀))).eval lam *
        ((innerDerivative Rs).map (Polynomial.evalRingHom z₀)).eval lam ≠ 0 := by
    rw [hRu, hRz, hSu, hSz]
    have h1 : lR * evalPoint (derivative (B g)) (z₀, lam) *
          (lS * evalPoint (innerDerivative (B h)) (z₀, lam)) -
        lS * evalPoint (derivative (B h)) (z₀, lam) *
          (lR * evalPoint (innerDerivative (B g)) (z₀, lam)) =
        (lR * lS) * (evalPoint (derivative (B g)) (z₀, lam) *
            evalPoint (innerDerivative (B h)) (z₀, lam) -
          evalPoint (derivative (B h)) (z₀, lam) *
            evalPoint (innerDerivative (B g)) (z₀, lam)) := by
      ring
    rw [h1]
    exact mul_ne_zero hl hn.jac
  -- 3. end coefficients
  obtain ⟨hn', hd, hdegR, hlc, hss, hrs, hr0s, hΔ⟩ :=
    locNodeContent_ends δ hβ hfac hn.natDegree_eq hn.lead_ne hn.const_ne hR hS hβs hfac' hRroot
  -- 4. the divided first-jet equation
  obtain ⟨U, hU⟩ := exists_locNodeSyzygy δ hfac hn' hR hS hβ0
  have hY : (C ((X - C z₀) ^ (2 * b) * Ss.coeff S.natDegree) * locJetNumer R).natDegree <
      (Rs.map (Polynomial.evalRingHom z₀)).natDegree := by
    rw [hdegR]
    exact (natDegree_C_mul_le _ _).trans_lt (natDegree_locJetNumer_lt hd)
  -- 5. the abstract residue theorem
  obtain ⟨y, hy, hres⟩ :=
    exists_mul_eq_pow_mul_of_syzygy (2 * a + 2 * b) hU hY hRc hSroot hcop hJne
  rw [coeff_C_mul, coeff_zero_locJetNumer] at hy
  have hy' : (X - C z₀) * (Ss.coeff S.natDegree * locLogJetNum R) =
      (X - C z₀) ^ (2 * a) * y := by
    apply mul_left_cancel₀ (pow_ne_zero (2 * b) (X_sub_C_ne_zero z₀))
    linear_combination hy
  have hR0 : (Rs.map (Polynomial.evalRingHom z₀)).coeff 0 = (Rs.coeff 0).eval z₀ := by
    rw [coeff_map, coe_evalRingHom]
  rw [hR0, hRu, hRz, hSu, hSz] at hres
  -- 6. the value of `N*` at the node and the residue identity
  have hN := eval_locNodeRemainder δ.c (P := P) (z₀ := z₀) (l₀ := lam) hβs hfac' hlc hRroot
    hSroot
  rw [hSu, hRz] at hN
  have hval := residue_value_nodeResidue δ.c_ne_zero hn.z₀_ne hn.lam_ne hn.jac hn.κ₂_ne hT hl
    hres hN hκ
  have hΔ0 : locLogJetDen R ≠ 0 := by
    rw [hΔ]
    refine mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero z₀)) fun h0 ↦ ?_
    have := congrArg (eval z₀) h0
    rw [eval_mul, eval_zero] at this
    exact mul_ne_zero hr0s hrs this
  refine hasSimpleResidue_of_pow_dvd hΔ0 ?_
  have hdvd := pow_dvd_of_residue_identity (Θ := (1 : ℂ))
    (Ω := z₀ - δ.c * z₀ *
      locNodeIndex δ.c z₀ lam (opJet1 P) (B g) (B h) (locCofactor B g h) κ₁ κ₂) hΔ hss hr0s hrs hy'
    (by rw [hval, locNodeIndex]; ring)
  convert hdvd using 1
  rw [C_1, one_mul, C_sub]
  ring

/-- **Lemma 3 (I-NODE).** The right factor whose residual symbol contains `G` and excludes `H`
has normalized determinant index `I_G` (formula (4)) at the node. -/
theorem hasNormalizedIndex_locNodeIndex (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (hβ : locJet0 β ≠ 0) (hfac : C β * P = oreMul δ.shiftHom S R) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) {κ₁ κ₂ : ℂ[X]} {g h : ι}
    {z₀ lam : ℂ} (hn : LocAllowedNode P B κ₁ κ₂ g h z₀ lam)
    (hRg : LocBlockDvd (B g) (opJet0 R)) (hSh : LocBlockDvd (B h) (opJet0 S)) :
    HasNormalizedIndex δ.c z₀ (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetDen R))
      (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetNum R))
      (locNodeIndex δ.c z₀ lam (opJet1 P) (B g) (B h) (locCofactor B g h) κ₁ κ₂) := by
  have h := (hasSimpleResidue_locLogJet_of_allowedNode δ hβ hfac hB hn hRg hSh).div_C_mul_X
    δ.c_ne_zero hn.z₀_ne
  have hcz : δ.c * z₀ ≠ 0 := mul_ne_zero δ.c_ne_zero hn.z₀_ne
  rwa [mul_div_cancel_left₀ _ hcz] at h


end AJConjecture
