import Mathlib
import AJPaper.Zheng.PpZP41Arith2

/-!
# The surviving indices form one arithmetic progression (Unit PpZ, node `PpZ_P41Prog`)

Source: Zheng, (4.22) and the choice of `j₀` before (4.25).

The odd `j = 2m + 1 ∈ [1, 2a - 1]` with `β ∣ j` and `α ∣ Nj + 2` are exactly
`j = j₁ + 2αβ t`, `0 ≤ t < T = a/(αβ)`, for one odd `j₁ < 2αβ`.

Route. `α` and `β` are coprime and odd, `N` is a unit mod `α` (`ppZPartC_isCoprime`,
`ppZAlpha_dvd_partC`). By the Chinese remainder theorem there is `j₁` with `j₁ ≡ 0 (mod β)`,
`N j₁ ≡ -2 (mod α)`, `j₁ ≡ 1 (mod 2)`, `0 ≤ j₁ < 2αβ` (`Nat.chineseRemainder` twice, or
`Int.emod` of an explicit solution). The two conditions on `j` say `j ≡ j₁ (mod αβ)`; with both
`j` and `j₁` odd and `αβ` odd this is `j ≡ j₁ (mod 2αβ)`; finally `1 ≤ j ≤ 2a - 1 = 2αβT - 1`
gives `0 ≤ t < T` (`ppZ_alpha_beta_quot`).
-/

noncomputable section

namespace AJConjecture

/-- A solution of `β ∣ J`, `α ∣ NJ + 2`, `J` odd, `0 ≤ J < 2αβ`, for coprime `α`, `β`, `N` prime
to `α` and `αβ` odd. -/
private theorem exists_start_P41Prog {α β : ℕ} {N : ℤ} (hodd : Odd (α * β))
    (hαβ : Nat.Coprime α β) (hN : IsCoprime N (α : ℤ)) :
    ∃ j₁ : ℕ, Odd j₁ ∧ j₁ < 2 * (α * β) ∧ (β : ℤ) ∣ (j₁ : ℤ) ∧ (α : ℤ) ∣ N * (j₁ : ℤ) + 2 := by
  have hpos : 0 < α * β := hodd.pos
  have hcop : IsCoprime (N * (β : ℤ)) (α : ℤ) :=
    hN.mul_left (Nat.isCoprime_iff_coprime.mpr hαβ.symm)
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨c, hc⟩ := hodd
  have hc' : (α : ℤ) * β = 2 * c + 1 := by exact_mod_cast hc
  set y : ℤ := -2 * u * β * (1 + α * β) + α * β with hy
  have hD : (0 : ℤ) < 2 * ((α : ℤ) * β) := by
    exact_mod_cast (show 0 < 2 * (α * β) by omega)
  have hJ0 : 0 ≤ y % (2 * ((α : ℤ) * β)) := Int.emod_nonneg _ hD.ne'
  have hJ1 : y % (2 * ((α : ℤ) * β)) < 2 * ((α : ℤ) * β) := Int.emod_lt_of_pos _ hD
  have hJ : y % (2 * ((α : ℤ) * β)) = y - 2 * ((α : ℤ) * β) * (y / (2 * ((α : ℤ) * β))) :=
    Int.emod_def _ _
  set q : ℤ := y / (2 * ((α : ℤ) * β)) with hq
  have hcast : (((y % (2 * ((α : ℤ) * β))).toNat : ℕ) : ℤ) = y % (2 * ((α : ℤ) * β)) :=
    Int.toNat_of_nonneg hJ0
  refine ⟨(y % (2 * ((α : ℤ) * β))).toNat, ?_, ?_, ?_, ?_⟩
  · rw [← Int.odd_natCast, hcast, hJ]
    exact ⟨-u * β * (1 + α * β) - α * β * q + c, by rw [hy]; linear_combination hc'⟩
  · have h : (((y % (2 * ((α : ℤ) * β))).toNat : ℕ) : ℤ) < ((2 * (α * β) : ℕ) : ℤ) := by
      rw [hcast]
      exact_mod_cast hJ1
    exact_mod_cast h
  · rw [hcast, hJ]
    exact ⟨-2 * u * (1 + α * β) + α - 2 * α * q, by rw [hy]; ring⟩
  · rw [hcast, hJ]
    refine ⟨2 * v + N * β * (-2 * u * β + 1 - 2 * q), ?_⟩
    rw [hy]
    linear_combination (-2 : ℤ) * huv

/-- The two congruence conditions on an odd `j` say `j = j₁ + 2αβ t`. -/
private theorem progression_iff_P41Prog {α β a j₁ : ℕ} {N : ℤ} (hodd : Odd (α * β))
    (hαβ : Nat.Coprime α β) (hN : IsCoprime N (α : ℤ)) (hdvd : α * β ∣ a) (hj₁ : Odd j₁)
    (hlt : j₁ < 2 * (α * β)) (hβ : (β : ℤ) ∣ (j₁ : ℤ)) (hα : (α : ℤ) ∣ N * (j₁ : ℤ) + 2)
    {m : ℕ} (hm : m < a) :
    ((β : ℤ) ∣ 2 * (m : ℤ) + 1 ∧ (α : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2) ↔
      ∃ t : ℕ, t < a / (α * β) ∧ 2 * m + 1 = j₁ + 2 * (α * β) * t := by
  have hpos : 0 < α * β := hodd.pos
  constructor
  · rintro ⟨hB, hA⟩
    have h1 : (β : ℤ) ∣ 2 * (m : ℤ) + 1 - j₁ := dvd_sub hB hβ
    have h2 : (α : ℤ) ∣ 2 * (m : ℤ) + 1 - j₁ := by
      refine hN.symm.dvd_of_dvd_mul_left ?_
      have h := dvd_sub hA hα
      rwa [show N * (2 * (m : ℤ) + 1) + 2 - (N * (j₁ : ℤ) + 2) = N * (2 * (m : ℤ) + 1 - j₁) by
        ring] at h
    have h3 : (α : ℤ) * β ∣ 2 * (m : ℤ) + 1 - j₁ :=
      (Nat.isCoprime_iff_coprime.mpr hαβ).mul_dvd h2 h1
    have h4 : (2 : ℤ) ∣ 2 * (m : ℤ) + 1 - j₁ := by
      obtain ⟨c, hc⟩ := hj₁
      exact ⟨m - c, by rw [hc]; push_cast; ring⟩
    have hcop2 : IsCoprime (2 : ℤ) ((α : ℤ) * β) := by
      have := Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_left.mpr hodd)
      exact_mod_cast this
    obtain ⟨t, ht⟩ := hcop2.mul_dvd h4 h3
    obtain ⟨T, hT⟩ := hdvd
    have hT' : (a : ℤ) = (α : ℤ) * β * T := by exact_mod_cast hT
    have hD : (0 : ℤ) < 2 * ((α : ℤ) * β) := by
      exact_mod_cast (show 0 < 2 * (α * β) by omega)
    have hlt' : (j₁ : ℤ) < 2 * ((α : ℤ) * β) := by exact_mod_cast hlt
    have hm' : (m : ℤ) < a := by exact_mod_cast hm
    have ht0 : 0 ≤ t := by
      have h : 2 * ((α : ℤ) * β) * (-1) < 2 * ((α : ℤ) * β) * t := by
        rw [← ht]
        linarith [Int.natCast_nonneg m]
      have := lt_of_mul_lt_mul_left h hD.le
      omega
    have htT : t < T := by
      have h : 2 * ((α : ℤ) * β) * t < 2 * ((α : ℤ) * β) * T := by
        rw [← ht]
        linarith [Int.natCast_nonneg j₁]
      exact lt_of_mul_lt_mul_left h hD.le
    refine ⟨t.toNat, ?_, ?_⟩
    · rw [hT, Nat.mul_div_cancel_left _ hpos]
      omega
    · have hcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0
      have h : ((2 * m + 1 : ℕ) : ℤ) = ((j₁ + 2 * (α * β) * t.toNat : ℕ) : ℤ) := by
        push_cast
        rw [hcast]
        linarith
      exact_mod_cast h
  · rintro ⟨t, -, ht⟩
    have ht' : 2 * (m : ℤ) + 1 = j₁ + 2 * ((α : ℤ) * β) * t := by exact_mod_cast ht
    rw [ht']
    refine ⟨dvd_add hβ ⟨2 * α * t, by ring⟩, ?_⟩
    rw [show N * ((j₁ : ℤ) + 2 * ((α : ℤ) * β) * t) + 2 =
      N * (j₁ : ℤ) + 2 + (α : ℤ) * (2 * N * β * t) by ring]
    exact dvd_add hα (dvd_mul_right _ _)

/-- The indices `m < a` with `β ∣ 2m+1`, `α ∣ N(2m+1) + 2` are `2m + 1 = j₁ + 2αβ t`, `t < T`. -/
theorem ppZ_restricted_progression (a : ℕ) (ha : 1 ≤ a) (hodd : Odd a) (N : ℤ) :
    ∃ j₁ : ℕ, Odd j₁ ∧ j₁ < 2 * (ppZAlpha a N * ppZBeta a N) ∧
      ((ppZBeta a N : ℕ) : ℤ) ∣ (j₁ : ℤ) ∧ ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (j₁ : ℤ) + 2 ∧
      ∀ m : ℕ, m < a →
        ((((ppZBeta a N : ℕ) : ℤ) ∣ 2 * (m : ℤ) + 1 ∧
            ((ppZAlpha a N : ℕ) : ℤ) ∣ N * (2 * (m : ℤ) + 1) + 2) ↔
          ∃ t : ℕ, t < a / (ppZAlpha a N * ppZBeta a N) ∧
            2 * m + 1 = j₁ + 2 * (ppZAlpha a N * ppZBeta a N) * t) := by
  obtain ⟨hdvd, -, hcop⟩ := ppZ_alpha_beta_quot a ha hodd N
  have hoddM : Odd (ppZAlpha a N * ppZBeta a N) := hodd.of_dvd_nat hdvd
  have hN : IsCoprime N ((ppZAlpha a N : ℕ) : ℤ) :=
    (ppZPartC_isCoprime a N).of_isCoprime_of_dvd_right
      (Int.natCast_dvd_natCast.mpr (ppZAlpha_dvd_partC a N))
  obtain ⟨j₁, hj₁, hlt, hβ, hα⟩ := exists_start_P41Prog hoddM hcop hN
  exact ⟨j₁, hj₁, hlt, hβ, hα, fun m hm ↦
    progression_iff_P41Prog hoddM hcop hN hdvd hj₁ hlt hβ hα hm⟩

end AJConjecture
