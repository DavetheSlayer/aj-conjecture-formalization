import Mathlib
import AJPaper.Zheng.PpZP41Galois
import AJPaper.Zheng.PpZP41Fourier

/-!
# Vanishing of the test sums (Unit PpZ, node `PpZ_P41TestSum`)

If one conjugate sum `R(u₀)` vanishes (`u₀` coprime to `a`), then
`∑_{m<a} w_m Φ(E(m)) = 0` for every unit-supported `Φ`.

Route. `ppZ_unitSupported_expansion` gives `Φ(r) = ∑_u φ_u ζ_a^{ur}` over `u < a` coprime to `a`;
exchange the two finite sums: `∑_m w_m Φ(E(m)) = ∑_u φ_u R(u)`, and every `R(u)` vanishes by
`ppZ_conjSum_galois` (`Nat.isCoprime_iff_coprime` turns `Nat.Coprime u a` into `IsCoprime`).
-/

noncomputable section

namespace AJConjecture

/-- The test sums of a unit-supported function vanish when a conjugate sum vanishes. -/
theorem ppZ_testSum_eq_zero {a : ℕ} (ha : 1 ≤ a) (N : ℤ) {u₀ : ℤ} (hu₀ : IsCoprime u₀ (a : ℤ))
    (h : ppZConjSum a N u₀ = 0) (Φ : ℤ → ℂ) (hΦ : PpZUnitSupported a Φ) :
    ∑ m ∈ Finset.range a, (ppZWeight a m : ℂ) * Φ (ppZExp N m) = 0 := by
  obtain ⟨φ, hφ⟩ := ppZ_unitSupported_expansion a ha Φ hΦ
  simp only [hφ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun u hu ↦ ?_
  have hcop : IsCoprime (u : ℤ) (a : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Finset.mem_filter.mp hu).2
  have hR := ppZ_conjSum_galois ha N hu₀ hcop h
  have hsum : ∑ m ∈ Finset.range a, (ppZWeight a m : ℂ) * (φ u * ppZRoot a (u * ppZExp N m)) =
      φ u * ppZConjSum a N u := by
    rw [ppZConjSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  rw [hsum, hR, mul_zero]

end AJConjecture
