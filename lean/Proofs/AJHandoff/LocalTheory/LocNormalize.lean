import Mathlib
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgOreMulZero
import AJHandoff.LocalTheory.LocOpJets

/-!
# Normalization of a pseudo-factorization at `h = 0`

A factorization over `F` of an operator `P ∈ ℂ[[h]][z][u]` is, after clearing denominators, a
pseudo-factorization `β P = S ⋆ R` with `β ∈ ℂ[[h]][z]` nonzero and `S, R ∈ ℂ[[h]][z][u]`. The
residual symbol `P₀` vanishes exactly when `h` divides `P`. Since `h` is prime in the unique
factorisation domain `ℂ[[h]][z]`, central for `⋆` (it is fixed by `σ`), and `(S ⋆ R)₀ = S₀ R₀` in
the domain `ℂ[z][u]`, the powers of `h` can be removed from `β`, `S`, `R`. This is the
multiplicativity of the `h`-adic Gauss valuation in the Ore ring (the residual Ore algebra is the
commutative domain `ℂ(z)[u]`), as in the library's `exists_normalized_pseudoFactor` at `t = -1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The reduction of `f ∈ ℂ[[h]][z]` vanishes exactly when `h` divides `f`. -/
private theorem locJet0_eq_zero_iff_dvd_normalize (f : LocPoly) : locJet0 f = 0 ↔ locH ∣ f := by
  rw [locH, Polynomial.C_dvd_iff_dvd_coeff]
  simp only [PowerSeries.X_dvd_iff, ← coeff_locJet0]
  exact ⟨fun h i ↦ by rw [h, coeff_zero], fun h ↦ by ext i; rw [h, coeff_zero]⟩

theorem opJet0_eq_zero_iff (P : LocOp) : opJet0 P = 0 ↔ C locH ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  simp only [← locJet0_eq_zero_iff_dvd_normalize]
  exact ⟨fun h i ↦ by rw [← coeff_map, ← opJet0, h, coeff_zero],
    fun h ↦ by ext i : 2; rw [opJet0, coeff_map, h, coeff_zero]⟩

/-- The residual symbol of a constant multiple. -/
private theorem opJet0_C_mul_normalize (x : LocPoly) (Q : LocOp) :
    opJet0 (C x * Q) = C (locJet0 x) * opJet0 Q := by
  rw [opJet0, Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- A shift-invariant constant passes through the right factor of an Ore product. -/
private theorem oreMul_C_mul_right_normalize (δ : LocDilation) {x : LocPoly}
    (hx : δ.shiftHom x = x) (S Q : LocOp) :
    oreMul δ.shiftHom S (C x * Q) = C x * oreMul δ.shiftHom S Q := by
  have hit : ∀ i : ℕ, δ.shiftHom^[i] x = x := fun i ↦ Function.iterate_fixed hx i
  have hSC : oreMul δ.shiftHom S (C x) = C x * S := by
    induction S using Polynomial.induction_on' with
    | add p q hp hq => rw [oreMul_add_left, hp, hq, mul_add]
    | monomial i a =>
      rw [← Polynomial.monomial_zero_left, oreMul_monomial_monomial, hit,
        Polynomial.monomial_mul_monomial, zero_add, add_zero, mul_comm]
  rw [← oreMul_C_left, ← oreMul_assoc, hSC, ← oreMul_C_left, oreMul_assoc, oreMul_C_left]

/-- Splitting off the largest power of `h` from a nonzero operator. -/
private theorem exists_opJet0_ne_zero_normalize {S : LocOp} (hS : S ≠ 0) :
    ∃ (b : ℕ) (S' : LocOp), opJet0 S' ≠ 0 ∧ S = C (locH ^ b) * S' := by
  have hu : ¬IsUnit (C locH : LocOp) := by
    rintro ⟨v, hv⟩
    have h0 := opJet0_C_mul_normalize locH (↑v⁻¹ : LocOp)
    rw [← hv, Units.mul_inv, (locJet_locH (LocDilation.exp 1 one_ne_zero)).1, map_zero,
      zero_mul, opJet0, Polynomial.map_one] at h0
    exact one_ne_zero h0
  obtain ⟨n, S', hdvd, hSeq⟩ := WfDvdMonoid.max_power_factor' (α := LocOp) hS hu
  exact ⟨n, S', fun h ↦ hdvd ((opJet0_eq_zero_iff S').1 h), by rw [hSeq, Polynomial.C_pow]⟩

/-- Splitting off the largest power of `h` from a nonzero element of `ℂ[[h]][z]`. -/
private theorem exists_locJet0_ne_zero_normalize {β : LocPoly} (hβ : β ≠ 0) :
    ∃ (a : ℕ) (β' : LocPoly), locJet0 β' ≠ 0 ∧ β = locH ^ a * β' := by
  have hu : ¬IsUnit locH := by
    rintro ⟨v, hv⟩
    have h0 := map_mul locJet0 (v : LocPoly) (↑v⁻¹ : LocPoly)
    rw [Units.mul_inv, map_one, hv, (locJet_locH (LocDilation.exp 1 one_ne_zero)).1,
      zero_mul] at h0
    exact one_ne_zero h0
  obtain ⟨n, β', hdvd, hβeq⟩ := WfDvdMonoid.max_power_factor' (α := LocPoly) hβ hu
  exact ⟨n, β', fun h ↦ hdvd ((locJet0_eq_zero_iff_dvd_normalize β').1 h), hβeq⟩

/-- `h` is nonzero in `ℂ[[h]][z]`. -/
private theorem locH_ne_zero_normalize : locH ≠ 0 := by
  rw [locH, Ne, Polynomial.C_eq_zero]
  exact PowerSeries.X_ne_zero

/-- Removing the powers of `h` from a pseudo-factorization. -/
theorem exists_normalized_locPseudoFactor (δ : LocDilation) {P : LocOp} (hP : opJet0 P ≠ 0)
    {β : LocPoly} (hβ : β ≠ 0) {S R : LocOp} (h : C β * P = oreMul δ.shiftHom S R) :
    ∃ (β' : LocPoly) (S' R' : LocOp), locJet0 β' ≠ 0 ∧ opJet0 S' ≠ 0 ∧ opJet0 R' ≠ 0 ∧
      S'.natDegree = S.natDegree ∧ R'.natDegree = R.natDegree ∧
      C β' * P = oreMul δ.shiftHom S' R' ∧ ∃ a : ℕ, R = C (locH ^ a) * R' := by
  have hP0 : P ≠ 0 := by rintro rfl; exact hP (by rw [opJet0, Polynomial.map_zero])
  have hβP : C β * P ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hβ) hP0
  have hS0 : S ≠ 0 := by rintro rfl; rw [oreMul_zero_left] at h; exact hβP h
  have hR0 : R ≠ 0 := by rintro rfl; rw [oreMul_zero_right] at h; exact hβP h
  obtain ⟨a, β', hβ', rfl⟩ := exists_locJet0_ne_zero_normalize hβ
  obtain ⟨b, S', hS', rfl⟩ := exists_opJet0_ne_zero_normalize hS0
  obtain ⟨c, R', hR', rfl⟩ := exists_opJet0_ne_zero_normalize hR0
  have hpow : ∀ k : ℕ, locH ^ k ≠ 0 := fun k ↦ pow_ne_zero k locH_ne_zero_normalize
  have hjet : ∀ k : ℕ, locJet0 (locH ^ (k + 1)) = 0 := fun k ↦ by
    rw [map_pow, (locJet_locH δ).1, zero_pow k.succ_ne_zero]
  have hfix : δ.shiftHom (locH ^ c) = locH ^ c := by
    rw [map_pow]
    exact congrArg (· ^ c) (locJet_locH δ).2.2
  set T := oreMul δ.shiftHom S' R' with hT
  have h' : C (locH ^ a) * (C β' * P) = C (locH ^ a) * C (locH ^ (b + c - a)) * T ∨
      C (locH ^ (a - (b + c))) * (C β' * P) = T := by
    rw [← oreMul_C_left δ.shiftHom (locH ^ b) S', oreMul_assoc, oreMul_C_left,
      oreMul_C_mul_right_normalize δ hfix,
      ← mul_assoc, ← Polynomial.C_mul, ← pow_add, Polynomial.C_mul, mul_assoc] at h
    rcases le_total a (b + c) with hle | hle
    · left
      rw [← Polynomial.C_mul, ← pow_add, Nat.add_sub_cancel' hle]
      exact h
    · right
      refine mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (hpow (b + c))) ?_
      rw [← mul_assoc, ← Polynomial.C_mul, ← pow_add, Nat.add_sub_cancel' hle, h]
  have hTeq : C β' * P = T := by
    rcases h' with h' | h'
    · rw [mul_assoc] at h'
      have h'' := mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (hpow a)) h'
      rcases Nat.eq_zero_or_eq_succ_pred (b + c - a) with hk | hk
      · rwa [hk, pow_zero, Polynomial.C_1, one_mul] at h''
      · exfalso
        have := congrArg opJet0 h''
        rw [opJet0_C_mul_normalize, opJet0_C_mul_normalize, hk, hjet, map_zero, zero_mul] at this
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβ') hP this
    · rcases Nat.eq_zero_or_eq_succ_pred (a - (b + c)) with hk | hk
      · rwa [hk, pow_zero, Polynomial.C_1, one_mul] at h'
      · exfalso
        have := congrArg opJet0 h'
        rw [opJet0_C_mul_normalize, hk, hjet, map_zero, zero_mul, hT, opJet0_oreMul] at this
        exact mul_ne_zero hS' hR' this.symm
  refine ⟨β', S', R', hβ', hS', hR', ?_, ?_, hTeq, c, rfl⟩
  · rw [Polynomial.natDegree_C_mul (hpow b)]
  · rw [Polynomial.natDegree_C_mul (hpow c)]


/-- The reduction of `f ∈ ℂ[[h]][z]` vanishes exactly when `h` divides `f`. -/
theorem locJet0_eq_zero_iff (f : LocPoly) : locJet0 f = 0 ↔ locH ∣ f :=
  locJet0_eq_zero_iff_dvd_normalize f

end AJConjecture
