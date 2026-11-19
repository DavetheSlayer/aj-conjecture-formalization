import Mathlib
import AJTwist.Select.TwSInvert
import AJTwist.Select.TwSGrowthClass

/-!
# The pullback of a growth class under the normalized inversion

Source: eq. (inversion-shift) of `selection.tex` (revision 5): for
`(𝓑 F)_N = q^(N(N-1)) F_N(t⁻¹)`,
`𝓑(r F) = r(t⁻¹, M⁻¹) 𝓑 F` and `𝓑(u^k F) = q^(-k(k+1)) M^(4k) u^k 𝓑 F`; "thus the same closure
holds for the normalized inversion of the finite module". A growth class is closed under
Laurent monomials `t^i M^j` with `i, j ∈ ℤ`, so its pullback under `𝓑` is a growth class.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The normalized inversion `(𝓑 g)(n) = q^(n(n-1)) g(n)(t⁻¹)` of a sequence. -/
def twsB (g : ℤ → RatFunc ℚ) (n : ℤ) : RatFunc ℚ :=
  qParam ^ (n * (n - 1)) * twsInv (g n)

/-- The pullback of a class of sequences under the normalized inversion. -/
def TwsBPull (U : (ℤ → RatFunc ℚ) → Prop) (g : ℤ → RatFunc ℚ) : Prop :=
  U (twsB g)

/-- `twsInv` inverts the integer powers of `t`. -/
private theorem twsInv_X_zpow_twsInvClass (k : ℤ) :
    twsInv ((RatFunc.X : RatFunc ℚ) ^ k) = (RatFunc.X : RatFunc ℚ) ^ (-k) := by
  rw [map_zpow₀, twsInv_X, inv_zpow, zpow_neg]

/-- The normalized inversion of a product with a sequence of Laurent monomials. -/
private theorem twsB_monomial_mul_twsInvClass (g : ℤ → RatFunc ℚ) (e : ℤ → ℤ) (n : ℤ) :
    twsB (fun m ↦ (RatFunc.X : RatFunc ℚ) ^ e m * g m) n =
      (RatFunc.X : RatFunc ℚ) ^ (-e n) * twsB g n := by
  simp only [twsB, map_mul, twsInv_X_zpow_twsInvClass]
  ring

/-- The normalized inversion of the shifted sequence. -/
private theorem twsB_shift_twsInvClass (g : ℤ → RatFunc ℚ) (n : ℤ) :
    twsB (fun m ↦ g (m + 1)) n =
      (RatFunc.X : RatFunc ℚ) ^ (0 + 2 * n * (-4)) * twsB g (n + 1) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have he : (RatFunc.X : RatFunc ℚ) ^ (4 * (n * (n - 1))) =
      RatFunc.X ^ (0 + 2 * n * (-4)) * RatFunc.X ^ (4 * ((n + 1) * (n + 1 - 1))) := by
    rw [← zpow_add₀ hX]
    congr 1
    ring
  simp only [twsB, qParam_zpow_eq_ratFuncX_zpow]
  rw [he, mul_assoc]

/-- The pullback of a growth class under the normalized inversion is a growth class. -/
theorem twsGrowthClass_bPull {U : (ℤ → RatFunc ℚ) → Prop} (hU : TwsGrowthClass U) :
    TwsGrowthClass (TwsBPull U) where
  zero_tail {g n₀} h := hU.zero_tail (n₀ := n₀) fun n hn ↦ by
    rw [twsB, h n hn, map_zero, mul_zero]
  sub {g₁ g₂} h₁ h₂ := by
    have heq : twsB (fun n ↦ g₁ n - g₂ n) = fun n ↦ twsB g₁ n - twsB g₂ n := by
      funext n
      simp only [twsB, map_sub, mul_sub]
    rw [TwsBPull, heq]
    exact hU.sub h₁ h₂
  monomial {g} i j h := by
    have heq : twsB (fun n ↦ (RatFunc.X : RatFunc ℚ) ^ (i + 2 * n * j) * g n) =
        fun n ↦ (RatFunc.X : RatFunc ℚ) ^ (-i + 2 * n * (-j)) * twsB g n := by
      funext n
      rw [twsB_monomial_mul_twsInvClass g (fun n ↦ i + 2 * n * j) n]
      congr 2
      ring
    rw [TwsBPull, heq]
    exact hU.monomial (-i) (-j) h
  shift {g} h := by
    have heq : twsB (fun n ↦ g (n + 1)) =
        fun n ↦ (RatFunc.X : RatFunc ℚ) ^ (0 + 2 * n * (-4)) * twsB g (n + 1) :=
      funext fun n ↦ twsB_shift_twsInvClass g n
    rw [TwsBPull, heq]
    exact hU.monomial 0 (-4) (hU.shift h)

/-- The inversion of an evaluated coefficient is a Laurent monomial `t^(-A) M^(-B)` times an
evaluated coefficient. -/
private theorem exists_twsInv_evalAtField_twsInvClass (κ : Coeff) :
    ∃ (A B : ℕ) (κ' : Coeff), ∀ n : ℤ, twsInv (evalAtField n κ) =
      (RatFunc.X : RatFunc ℚ) ^ (-(A : ℤ) + 2 * n * (-(B : ℤ))) * evalAtField n κ' := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hadd : ∀ p q : Coeff,
      (∃ (A B : ℕ) (κ' : Coeff), ∀ n : ℤ, twsInv (evalAtField n p) =
        (RatFunc.X : RatFunc ℚ) ^ (-(A : ℤ) + 2 * n * (-(B : ℤ))) * evalAtField n κ') →
      (∃ (A B : ℕ) (κ' : Coeff), ∀ n : ℤ, twsInv (evalAtField n q) =
        (RatFunc.X : RatFunc ℚ) ^ (-(A : ℤ) + 2 * n * (-(B : ℤ))) * evalAtField n κ') →
      ∃ (A B : ℕ) (κ' : Coeff), ∀ n : ℤ, twsInv (evalAtField n (p + q)) =
        (RatFunc.X : RatFunc ℚ) ^ (-(A : ℤ) + 2 * n * (-(B : ℤ))) * evalAtField n κ' := by
    rintro p q ⟨A₁, B₁, κ₁, h₁⟩ ⟨A₂, B₂, κ₂, h₂⟩
    refine ⟨A₁ + A₂, B₁ + B₂, C (X ^ A₂) * X ^ B₂ * κ₁ + C (X ^ A₁) * X ^ B₁ * κ₂, fun n ↦ ?_⟩
    have hE : ∀ (A B : ℕ) (c : Coeff), evalAtField n (C (X ^ A) * X ^ B * c) =
        (RatFunc.X : RatFunc ℚ) ^ ((A : ℤ) + 2 * n * B) * evalAtField n c := by
      intro A B c
      rw [map_mul, zpow_add₀ hX, zpow_mul, zpow_natCast, zpow_natCast]
      congr 1
      simp only [evalAtField, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow]
    have he : ∀ A B A' B' : ℕ, (RatFunc.X : RatFunc ℚ) ^ (-(A : ℤ) + 2 * n * (-(B : ℤ))) =
        RatFunc.X ^ (-((A + A' : ℕ) : ℤ) + 2 * n * (-((B + B' : ℕ) : ℤ))) *
          RatFunc.X ^ ((A' : ℤ) + 2 * n * B') := by
      intro A B A' B'
      rw [← zpow_add₀ hX]
      congr 1
      push_cast
      ring
    rw [map_add, map_add, h₁ n, h₂ n, map_add, hE, hE, he A₁ B₁ A₂ B₂, he A₂ B₂ A₁ B₁,
      add_comm A₂ A₁, add_comm B₂ B₁]
    ring
  induction κ using Polynomial.induction_on' with
  | add p q hp hq => exact hadd p q hp hq
  | monomial b c =>
    induction c using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact hadd _ _ hp hq
    | monomial a z =>
      refine ⟨a, b, C (C z), fun n ↦ ?_⟩
      have h1 : evalAtField n (monomial b (monomial a z)) =
          (z : RatFunc ℚ) * RatFunc.X ^ (a : ℤ) * RatFunc.X ^ (2 * n * b) := by
        rw [evalAtField, coe_eval₂RingHom, eval₂_monomial, coe_eval₂RingHom, eval₂_monomial,
          eq_intCast, zpow_natCast, zpow_mul _ (2 * n), zpow_natCast]
      have h2 : evalAtField n (C (C z)) = (z : RatFunc ℚ) := by
        rw [evalAtField, coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, eval₂_C, eq_intCast]
      rw [h1, h2, map_mul, map_mul, map_intCast, twsInv_X_zpow_twsInvClass,
        twsInv_X_zpow_twsInvClass, mul_assoc, ← zpow_add₀ hX, mul_comm]
      congr 2
      ring

/-- The inversion of an evaluated nonzero coefficient is a Laurent monomial times an evaluated
nonzero coefficient (the reversed polynomial). -/
theorem tws_exists_twsInv_evalAtField {κ : Coeff} (hκ : κ ≠ 0) :
    ∃ κ' : Coeff, κ' ≠ 0 ∧ ∃ i j : ℤ, ∀ n : ℤ,
      twsInv (evalAtField n κ) = (RatFunc.X : RatFunc ℚ) ^ (i + 2 * n * j) * evalAtField n κ' := by
  obtain ⟨A, B, κ', h⟩ := exists_twsInv_evalAtField_twsInvClass κ
  refine ⟨κ', ?_, -(A : ℤ), -(B : ℤ), h⟩
  rintro rfl
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero hκ
  have h0 := h n₀
  rw [map_zero, mul_zero, map_eq_zero] at h0
  exact hn₀ n₀ le_rfl h0

/-- A sequence whose normalized inversion is in the saturation of `U` is in the saturation of
the pullback of `U`. -/
theorem twsSat_bPull {U : (ℤ → RatFunc ℚ) → Prop} (hU : TwsGrowthClass U) {g : ℤ → RatFunc ℚ}
    (h : TwsSat U (twsB g)) : TwsSat (TwsBPull U) g := by
  obtain ⟨κ, hκ, h⟩ := h
  obtain ⟨κ', hκ', i, j, hinv⟩ := tws_exists_twsInv_evalAtField hκ
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have heq : twsB (fun n ↦ evalAtField n κ' * g n) =
      fun n ↦ (RatFunc.X : RatFunc ℚ) ^ (i + 2 * n * j) * (evalAtField n κ * twsB g n) := by
    funext n
    have h1 : twsInv (evalAtField n κ') =
        (RatFunc.X : RatFunc ℚ) ^ (i + 2 * n * j) * evalAtField n κ := by
      have h2 := congrArg twsInv (hinv n)
      rw [twsInv_twsInv, map_mul, twsInv_X_zpow_twsInvClass] at h2
      rw [h2, ← mul_assoc, ← zpow_add₀ hX, add_neg_cancel, zpow_zero, one_mul]
    simp only [twsB, map_mul, h1]
    ring
  refine ⟨κ', hκ', ?_⟩
  rw [TwsBPull, heq]
  exact hU.monomial i j h

/-- A sequence whose normalized inversion is not in the saturation of `U` is not in the
saturation of the pullback of `U`. -/
theorem tws_not_sat_bPull {U : (ℤ → RatFunc ℚ) → Prop} (hU : TwsGrowthClass U)
    {F : ℤ → RatFunc ℚ} (h : ¬ TwsSat U (twsB F)) : ¬ TwsSat (TwsBPull U) F := by
  rintro ⟨κ, hκ, hF⟩
  obtain ⟨κ', hκ', i, j, hinv⟩ := tws_exists_twsInv_evalAtField hκ
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  refine h ⟨κ', hκ', ?_⟩
  have heq : (fun n ↦ (RatFunc.X : RatFunc ℚ) ^ (-i + 2 * n * (-j)) *
      twsB (fun m ↦ evalAtField m κ * F m) n) = fun n ↦ evalAtField n κ' * twsB F n := by
    funext n
    have he : (RatFunc.X : RatFunc ℚ) ^ (-i + 2 * n * (-j)) * RatFunc.X ^ (i + 2 * n * j) = 1 := by
      rw [← zpow_add₀ hX]
      have he' : -i + 2 * n * (-j) + (i + 2 * n * j) = 0 := by ring
      rw [he', zpow_zero]
    simp only [twsB, map_mul, hinv n]
    linear_combination (evalAtField n κ' * qParam ^ (n * (n - 1)) * twsInv (F n)) * he
  rw [← heq]
  exact hU.monomial (-i) (-j) hF

end AJConjecture
