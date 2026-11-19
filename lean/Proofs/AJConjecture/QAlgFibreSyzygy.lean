import Mathlib

/-!
# Syzygies of two polynomials with exactly one common root

Over a field let `R = (X - l₀) R^c` with `R^c` coprime to `S`. If `R ∣ S Y` and `deg Y < deg R`
then `Y = α R^c` for a constant `α`: `R^c` divides `S Y`, hence `Y`, and the quotient has degree
less than `1`.
-/

open Polynomial

namespace AJConjecture

/-- A polynomial `Y` of degree less than `deg R` with `R ∣ S Y` is a constant multiple of
`R / (X - l₀)`, when the latter is coprime to `S`. -/
theorem exists_eq_C_mul_of_dvd_mul {k : Type*} [Field k] {R S Y Rc : k[X]} {l₀ : k}
    (hR : R = (X - C l₀) * Rc) (hcop : IsCoprime Rc S) (hdeg : Y.natDegree < R.natDegree)
    (hdvd : R ∣ S * Y) : ∃ α : k, Y = C α * Rc := by
  have hRc : Rc ∣ Y := hcop.dvd_of_dvd_mul_left ((Dvd.intro_left _ hR.symm).trans hdvd)
  obtain ⟨q, rfl⟩ := hRc
  rcases eq_or_ne Rc 0 with h0 | h0
  · rw [hR, h0, mul_zero, natDegree_zero] at hdeg
    exact absurd hdeg (Nat.not_lt_zero _)
  rcases eq_or_ne q 0 with hq | hq
  · exact ⟨0, by rw [hq, mul_zero, C_0, zero_mul]⟩
  have h1 : (Rc * q).natDegree = Rc.natDegree + q.natDegree := natDegree_mul h0 hq
  have h2 : R.natDegree = 1 + Rc.natDegree := by
    rw [hR, natDegree_mul (X_sub_C_ne_zero l₀) h0, natDegree_X_sub_C]
  have h3 : q.natDegree = 0 := by omega
  exact ⟨q.coeff 0, by rw [mul_comm Rc q, ← eq_C_of_natDegree_eq_zero h3]⟩

end AJConjecture
