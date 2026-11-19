import Mathlib
import AJHandoff.LocalTheory.LocNodeData

/-!
# A residual factorization allocates whole blocks

If `κ₁ P₀ = κ₂ ∏ B_i` is a decomposition into residual blocks and `β₀ P₀ = S₀ R₀` with `β₀ ≠ 0`,
then by unique factorisation in `ℂ(z)[u]` every block divides exactly one of `R₀`, `S₀`, and up
to nonzero scalars of `ℂ[z]` the symbol `R₀` is the product of the blocks dividing it and `S₀`
the product of the others. This is the precise sense in which a right factor "specializes to a
product containing `G` and not `H`".
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Clearing denominators: if `X = q Y` over `ℂ(z)` with `q ≠ 0`, then `w₁ X = w₂ Y` with
nonzero `w₁, w₂ ∈ ℂ[z]`. -/
private theorem exists_C_mul_eq_of_map_eq_blockAlloc {P Q : ℂ[X][X]} {q : RatFunc ℂ}
    (hq : q ≠ 0)
    (h : P.map (algebraMap ℂ[X] (RatFunc ℂ)) = C q * Q.map (algebraMap ℂ[X] (RatFunc ℂ))) :
    ∃ w₁ w₂ : ℂ[X], w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ C w₁ * P = C w₂ * Q := by
  have hinj : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  refine ⟨q.denom, q.num, RatFunc.denom_ne_zero q, RatFunc.num_ne_zero hq,
    Polynomial.map_injective _ hinj ?_⟩
  have hd : algebraMap ℂ[X] (RatFunc ℂ) q.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.denom_ne_zero q)
  have hnum : algebraMap ℂ[X] (RatFunc ℂ) q.num = algebraMap ℂ[X] (RatFunc ℂ) q.denom * q := by
    have h1 := RatFunc.num_div_denom q
    rw [div_eq_iff hd] at h1
    rw [h1, mul_comm]
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, h, hnum, C_mul]
  ring

/-- Two non-associated irreducible blocks are coprime over `ℂ(z)`. -/
private theorem isCoprime_of_not_associated_blockAlloc {f g : (RatFunc ℂ)[X]}
    (hf : Irreducible f) (hg : Irreducible g) (h : ¬ Associated f g) : IsCoprime f g :=
  (Irreducible.coprime_iff_not_dvd hf).mpr fun hd ↦ h (hf.associated_of_dvd hg hd)

set_option linter.unusedVariables false in
open Classical in
theorem exists_locBlockAllocation {P : LocOp} {ι : Type*} [Fintype ι] {B : ι → ℂ[X][X]}
    (hB : LocResidualBlocks P B) (hP : opJet0 P ≠ 0) {β₀ : ℂ[X]} (hβ₀ : β₀ ≠ 0)
    {S₀ R₀ : ℂ[X][X]} (hfac : C β₀ * opJet0 P = S₀ * R₀) :
    (∀ i, LocBlockDvd (B i) R₀ → ¬ LocBlockDvd (B i) S₀) ∧
      ∃ w₁ w₂ w₃ w₄ : ℂ[X], w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧ w₄ ≠ 0 ∧
        C w₁ * R₀ = C w₂ * ∏ i ∈ Finset.univ.filter (fun i ↦ LocBlockDvd (B i) R₀), B i ∧
        C w₃ * S₀ = C w₄ * ∏ i ∈ Finset.univ.filter (fun i ↦ ¬ LocBlockDvd (B i) R₀), B i := by
  obtain ⟨κ₁, κ₂, hκ₁, hκ₂, hsym⟩ := hB.exists_eq
  set m : ℂ[X] →+* RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) with hm
  have hinj : Function.Injective m := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  set f : ι → (RatFunc ℂ)[X] := fun i ↦ (B i).map m with hf
  have hirr : ∀ i, Irreducible (f i) := hB.irreducible
  have hcop : ∀ i j, i ≠ j → IsCoprime (f i) (f j) := fun i j hij ↦
    isCoprime_of_not_associated_blockAlloc (hirr i) (hirr j) (hB.not_associated i j hij)
  have hκ₁m : m κ₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hκ₁
  have hκ₂m : m κ₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hκ₂
  have hβm : m β₀ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hβ₀
  set c : RatFunc ℂ := m β₀ * m κ₂ / m κ₁ with hc
  have hc0 : c ≠ 0 := div_ne_zero (mul_ne_zero hβm hκ₂m) hκ₁m
  have hu : IsUnit (C c : (RatFunc ℂ)[X]) := isUnit_C.mpr hc0.isUnit
  have hE : S₀.map m * R₀.map m = C c * ∏ i, f i := by
    have h1 := congrArg (Polynomial.map m) hfac
    have h2 := congrArg (Polynomial.map m) hsym
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod] at h1 h2
    rw [← h1]
    have h3 : (opJet0 P).map m = C (m κ₂ / m κ₁) * ∏ i, (B i).map m := by
      rw [div_eq_mul_inv, C_mul, mul_comm (C (m κ₂)), mul_assoc, ← h2, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ hκ₁m, C_1, one_mul]
    rw [h3, hc, mul_div_assoc, C_mul, mul_assoc]
  have hprod_dvd : (∏ i, f i) ∣ S₀.map m * R₀.map m := by
    rw [hE]
    exact Dvd.intro_left _ rfl
  refine ⟨fun i hR hS ↦ ?_, ?_⟩
  · -- a block dividing both factors divides the product twice
    have h1 : f i * f i ∣ ∏ j, f j := by
      have := mul_dvd_mul hS hR
      rw [hE] at this
      exact (hu.dvd_mul_left).mp this
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h1
    have h2 : f i ∣ ∏ j ∈ Finset.univ.erase i, f j :=
      (mul_dvd_mul_iff_left (hirr i).ne_zero).mp h1
    obtain ⟨j, hj, hdvd⟩ := Prime.exists_mem_finset_dvd (hirr i).prime h2
    exact hB.not_associated i j (Finset.ne_of_mem_erase hj).symm
      ((hirr i).associated_of_dvd (hirr j) hdvd)
  · set A := Finset.univ.filter (fun i ↦ LocBlockDvd (B i) R₀) with hA
    set N := Finset.univ.filter (fun i ↦ ¬ LocBlockDvd (B i) R₀) with hN
    have hpw : ∀ s : Finset ι, (s : Set ι).Pairwise (Function.onFun IsCoprime f) :=
      fun s i _ j _ hij ↦ hcop i j hij
    have hFA : (∏ i ∈ A, f i) ∣ R₀.map m :=
      Finset.prod_dvd_of_coprime (hpw A) fun i hi ↦ (Finset.mem_filter.mp hi).2
    have hFN : (∏ i ∈ N, f i) ∣ S₀.map m := by
      refine Finset.prod_dvd_of_coprime (hpw N) fun i hi ↦ ?_
      have hi' := (Finset.mem_filter.mp hi).2
      have h1 : f i ∣ S₀.map m * R₀.map m :=
        (Finset.dvd_prod_of_mem f (Finset.mem_univ i)).trans hprod_dvd
      exact ((Prime.dvd_or_dvd (hirr i).prime h1)).resolve_right hi'
    obtain ⟨Q, hQ⟩ := hFA
    obtain ⟨Q', hQ'⟩ := hFN
    have hsplit : ∏ i, f i = (∏ i ∈ A, f i) * ∏ i ∈ N, f i :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hne : (∏ i ∈ A, f i) * ∏ i ∈ N, f i ≠ 0 := by
      rw [← hsplit]
      exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hirr i).ne_zero
    have hQQ : Q' * Q = C c := by
      have h1 : ((∏ i ∈ A, f i) * ∏ i ∈ N, f i) * (Q' * Q) =
          ((∏ i ∈ A, f i) * ∏ i ∈ N, f i) * C c := by
        rw [hsplit, hQ, hQ'] at hE
        linear_combination hE
      exact mul_left_cancel₀ hne h1
    rw [← hQQ] at hu
    obtain ⟨q, hq, hqQ⟩ := Polynomial.isUnit_iff.mp (isUnit_of_mul_isUnit_right hu)
    obtain ⟨q', hq', hqQ'⟩ := Polynomial.isUnit_iff.mp (isUnit_of_mul_isUnit_left hu)
    obtain ⟨w₁, w₂, hw₁, hw₂, hw⟩ := exists_C_mul_eq_of_map_eq_blockAlloc (Q := ∏ i ∈ A, B i)
      hq.ne_zero (by rw [hQ, Polynomial.map_prod, ← hqQ, mul_comm])
    obtain ⟨w₃, w₄, hw₃, hw₄, hw'⟩ := exists_C_mul_eq_of_map_eq_blockAlloc (Q := ∏ i ∈ N, B i)
      hq'.ne_zero (by rw [hQ', Polynomial.map_prod, ← hqQ', mul_comm])
    exact ⟨w₁, w₂, w₃, w₄, hw₁, hw₂, hw₃, hw₄, hw, hw'⟩

end AJConjecture
