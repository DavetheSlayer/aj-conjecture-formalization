import Mathlib
import AJConjecture.QAlgNodeContentFactor
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgOreMulZero
import AJHandoff.LocalTheory.LocOpJets

/-!
# Contents at `z = z₀` and end coefficients of a normalized pseudo-factorization

For a normalized pseudo-factorization `β P = S ⋆ R` (`β₀ ≠ 0`) whose residual symbol has leading
coefficient nonvanishing at `z₀`, the residual symbols split as `R₀ = μ^a R*`, `S₀ = μ^b S*`,
`β₀ = μ^(a+b) β*` with `μ = z - z₀`, `β*(z₀) ≠ 0`, `β* P₀ = S* R*`, and `R*`, `S*` have nonzero
fibre at `z₀` (library lemma `exists_content_of_mul_eq`). If moreover the constant coefficient of
`P₀` does not vanish at `z₀` and the fibre of `R*` has a root, the end coefficients behave as in
the library's `nodeContent_ends`: degrees are kept, the end coefficients of `S*`, `R*` do not
vanish at `z₀`, and the denominator of the logarithmic jet of `R` is `μ^(2a) r₀* r_d*`.
These are Step 2 of Theorem C, ported from `ℤ[t][M]` to `ℂ[[h]][z]`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The residual symbol of `C β * P`. -/
private theorem opJet0_C_mul_symContent (β : LocPoly) (P : LocOp) :
    opJet0 (C β * P) = C (locJet0 β) * opJet0 P := by
  rw [opJet0, Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- The residual factorization `β₀ P₀ = S₀ R₀`. -/
private theorem opJet0_factor_symContent (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (h : C β * P = oreMul δ.shiftHom S R) :
    C (locJet0 β) * opJet0 P = opJet0 S * opJet0 R := by
  rw [← opJet0_oreMul δ, ← h, opJet0_C_mul_symContent]

/-- The fibre of `P₀` at `z₀` is not zero when its leading coefficient does not vanish there. -/
private theorem map_opJet0_ne_zero_symContent {P : LocOp} {z₀ : ℂ}
    (hlead : (opJet0 P).leadingCoeff.eval z₀ ≠ 0) :
    (opJet0 P).map (Polynomial.evalRingHom z₀) ≠ 0 := by
  intro h0
  apply hlead
  have hc := congrArg (fun q ↦ q.coeff (opJet0 P).natDegree) h0
  simpa only [coeff_map, coe_evalRingHom, coeff_zero, coeff_natDegree] using hc

/-- The residual symbol does not raise the degree. -/
private theorem natDegree_opJet0_le_symContent (Q : LocOp) :
    (opJet0 Q).natDegree ≤ Q.natDegree :=
  natDegree_map_le

/-- The primitive part of the residual symbol of `Q` has degree at most `deg Q`. -/
private theorem natDegree_le_of_opJet0_eq_symContent {Q : LocOp} {z₀ : ℂ} {a : ℕ}
    {Qs : ℂ[X][X]} (hQ : opJet0 Q = C ((X - C z₀) ^ a) * Qs) : Qs.natDegree ≤ Q.natDegree := by
  have h1 : (C ((X - C z₀) ^ a) * Qs).natDegree = Qs.natDegree :=
    natDegree_C_mul (pow_ne_zero a (X_sub_C_ne_zero z₀))
  rw [← h1, ← hQ]
  exact natDegree_opJet0_le_symContent Q

theorem exists_locNodeContent (δ : LocDilation) {P S R : LocOp} {β : LocPoly} {z₀ : ℂ}
    (hβ : locJet0 β ≠ 0) (h : C β * P = oreMul δ.shiftHom S R)
    (hlead : (opJet0 P).leadingCoeff.eval z₀ ≠ 0) :
    ∃ (a b : ℕ) (βs : ℂ[X]) (Ss Rs : ℂ[X][X]),
      opJet0 R = C ((X - C z₀) ^ a) * Rs ∧ opJet0 S = C ((X - C z₀) ^ b) * Ss ∧
      locJet0 β = (X - C z₀) ^ (a + b) * βs ∧ βs.eval z₀ ≠ 0 ∧ C βs * opJet0 P = Ss * Rs ∧
      Rs.map (Polynomial.evalRingHom z₀) ≠ 0 ∧ Ss.map (Polynomial.evalRingHom z₀) ≠ 0 := by
  have hfib := map_opJet0_ne_zero_symContent hlead
  obtain ⟨a, b, βs, Ss, Rs, hR, hS, hβs, hβm, hfac⟩ :=
    exists_content_of_mul_eq hβ hfib (opJet0_factor_symContent δ h)
  have hne : (Ss * Rs).map (Polynomial.evalRingHom z₀) ≠ 0 := by
    rw [← hfac, Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom]
    exact mul_ne_zero (C_ne_zero.mpr hβm) hfib
  rw [Polynomial.map_mul] at hne
  exact ⟨a, b, βs, Ss, Rs, hR, hS, hβs, hβm, hfac, right_ne_zero_of_mul hne,
    left_ne_zero_of_mul hne⟩

theorem locNodeContent_ends (δ : LocDilation) {P S R : LocOp} {β : LocPoly} {z₀ l₀ : ℂ}
    (hβ : locJet0 β ≠ 0) (h : C β * P = oreMul δ.shiftHom S R)
    (hdeg : (opJet0 P).natDegree = P.natDegree) (hlead : (opJet0 P).leadingCoeff.eval z₀ ≠ 0)
    (hconst : ((opJet0 P).coeff 0).eval z₀ ≠ 0) {a b : ℕ} {βs : ℂ[X]} {Ss Rs : ℂ[X][X]}
    (hR : opJet0 R = C ((X - C z₀) ^ a) * Rs) (hS : opJet0 S = C ((X - C z₀) ^ b) * Ss)
    (hβs : βs.eval z₀ ≠ 0) (hfac : C βs * opJet0 P = Ss * Rs)
    (hroot : (Rs.map (Polynomial.evalRingHom z₀)).eval l₀ = 0) :
    P.natDegree = S.natDegree + R.natDegree ∧ 0 < R.natDegree ∧
      (Rs.map (Polynomial.evalRingHom z₀)).natDegree = R.natDegree ∧
      βs * (opJet0 P).coeff P.natDegree = Ss.coeff S.natDegree * Rs.coeff R.natDegree ∧
      (Ss.coeff S.natDegree).eval z₀ ≠ 0 ∧ (Rs.coeff R.natDegree).eval z₀ ≠ 0 ∧
      (Rs.coeff 0).eval z₀ ≠ 0 ∧
      locLogJetDen R = (X - C z₀) ^ (2 * a) * (Rs.coeff 0 * Rs.coeff R.natDegree) := by
  have hP0 : opJet0 P ≠ 0 := fun h0 ↦
    hlead (by rw [h0, leadingCoeff_zero, eval_zero])
  have hPne : P ≠ 0 := fun h0 ↦ hP0 (by rw [h0, opJet0, Polynomial.map_zero])
  have hβne : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, map_zero])
  have hn : P.natDegree = S.natDegree + R.natDegree := by
    have hne : oreMul δ.shiftHom S R ≠ 0 := h ▸ mul_ne_zero (C_ne_zero.mpr hβne) hPne
    have hS0 : S ≠ 0 := fun h0 ↦ hne (by rw [h0, oreMul_zero_left])
    have hR0 : R ≠ 0 := fun h0 ↦ hne (by rw [h0, oreMul_zero_right])
    have hinj : Function.Injective δ.shiftHom := δ.shift.injective
    rw [← natDegree_oreMul hinj hS0 hR0, ← h, natDegree_C_mul hβne]
  have hRs := natDegree_le_of_opJet0_eq_symContent hR
  have hSs := natDegree_le_of_opJet0_eq_symContent hS
  have hlc : βs * (opJet0 P).coeff P.natDegree = Ss.coeff S.natDegree * Rs.coeff R.natDegree := by
    have h2 := congrArg (fun q ↦ q.coeff (S.natDegree + R.natDegree)) hfac
    simp only [coeff_C_mul, coeff_mul_add_eq_of_natDegree_le hSs hRs] at h2
    rw [hn]
    exact h2
  have hc0 : βs * (opJet0 P).coeff 0 = Ss.coeff 0 * Rs.coeff 0 := by
    have h2 := congrArg (fun q ↦ q.coeff 0) hfac
    simpa only [mul_coeff_zero, coeff_C_zero] using h2
  have hlcm := congrArg (eval z₀) hlc
  rw [eval_mul, eval_mul, ← hdeg, coeff_natDegree] at hlcm
  have hlcne : eval z₀ (Ss.coeff S.natDegree) * eval z₀ (Rs.coeff R.natDegree) ≠ 0 :=
    hlcm ▸ mul_ne_zero hβs hlead
  have hc0m := congrArg (eval z₀) hc0
  rw [eval_mul, eval_mul] at hc0m
  have hc0ne : eval z₀ (Ss.coeff 0) * eval z₀ (Rs.coeff 0) ≠ 0 :=
    hc0m ▸ mul_ne_zero hβs hconst
  have hrs := right_ne_zero_of_mul hlcne
  have hdegR : (Rs.map (Polynomial.evalRingHom z₀)).natDegree = R.natDegree := by
    refine le_antisymm (natDegree_map_le.trans hRs) (le_natDegree_of_ne_zero ?_)
    rw [coeff_map, coe_evalRingHom]
    exact hrs
  have hpos : 0 < R.natDegree := by
    by_contra h0
    have hd0 : R.natDegree = 0 := by omega
    rw [hd0] at hdegR
    rw [eq_C_of_natDegree_eq_zero hdegR, eval_C, coeff_map, coe_evalRingHom] at hroot
    exact right_ne_zero_of_mul hc0ne hroot
  refine ⟨hn, hpos, hdegR, hlc, left_ne_zero_of_mul hlcne, hrs, right_ne_zero_of_mul hc0ne, ?_⟩
  have hk (k : ℕ) : locJet0 (R.coeff k) = (X - C z₀) ^ a * Rs.coeff k := by
    rw [← coeff_C_mul, ← hR, opJet0, coeff_map]
  rw [locLogJetDen, leadingCoeff, hk, hk]
  ring

end AJConjecture
