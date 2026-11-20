import Mathlib
import AJPaper.Zheng.PpZP41Defs

/-!
# Galois conjugation of integer relations among `a`-th roots of unity
(Unit PpZ, node `PpZ_P41Galois`)

Source: Zheng, proof of Proposition 4.1 (the Galois action (4.18)); this is the only field theory
used in the present proof.

`ppZ_root_sum_galois`: if `∑_m c_m ζ_a^{u e_m} = 0` with integers `c_m, e_m` and `u` coprime to
`a`, then `∑_m c_m ζ_a^{v e_m} = 0` for every `v` coprime to `a`.

Route. `ζ_a^u` and `ζ_a^v` are primitive `a`-th roots of unity (`ppZRoot_isPrimitiveRoot`), so
both have minimal polynomial `cyclotomic a ℚ` over `ℚ` (`Polynomial.cyclotomic_eq_minpoly_rat`).
Let `P = ∑_m c_m X^{e_m mod a} ∈ ℚ[X]` (exponents `(e m % a).toNat`; `ppZRoot_eq_of_modEq`,
`ppZRoot_mul`). Then `aeval (ζ_a^u) P = 0`, so `minpoly ℚ (ζ_a^u) ∣ P` (`minpoly.dvd`), hence
`aeval (ζ_a^v) P = 0` (`minpoly.aeval`).
-/

noncomputable section

namespace AJConjecture

/-- The rational polynomial `∑_m c_m X^{e_m mod a}` of an integer relation. -/
private def relationPoly_P41Galois (a : ℕ) (s : Finset ℕ) (c e : ℕ → ℤ) : Polynomial ℚ :=
  ∑ m ∈ s, Polynomial.C (c m : ℚ) * Polynomial.X ^ (e m % (a : ℤ)).toNat

/-- Evaluating the relation polynomial at `ζ_a^w` gives `∑_m c_m ζ_a^{w e_m}`. -/
private theorem aeval_relationPoly_P41Galois {a : ℕ} (ha : 1 ≤ a) (w : ℤ) (s : Finset ℕ)
    (c e : ℕ → ℤ) :
    Polynomial.aeval (ppZRoot a w) (relationPoly_P41Galois a s c e) =
      ∑ m ∈ s, (c m : ℂ) * ppZRoot a (w * e m) := by
  have ha' : (a : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  simp only [relationPoly_P41Galois, map_sum, map_mul, Polynomial.aeval_C, map_pow,
    Polynomial.aeval_X, eq_ratCast, Rat.cast_intCast]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  congr 1
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ ha'), ← ppZRoot_mul]
  exact ppZRoot_eq_of_modEq ha ((Int.mod_modEq _ _).mul_left w)

/-- An integer relation among powers of one primitive `a`-th root of unity holds for all. -/
theorem ppZ_root_sum_galois {a : ℕ} (ha : 1 ≤ a) {u v : ℤ} (hu : IsCoprime u (a : ℤ))
    (hv : IsCoprime v (a : ℤ)) (s : Finset ℕ) (c e : ℕ → ℤ)
    (h : ∑ m ∈ s, (c m : ℂ) * ppZRoot a (u * e m) = 0) :
    ∑ m ∈ s, (c m : ℂ) * ppZRoot a (v * e m) = 0 := by
  have hpu := ppZRoot_isPrimitiveRoot ha hu
  have hpv := ppZRoot_isPrimitiveRoot ha hv
  have hmin : minpoly ℚ (ppZRoot a u) = minpoly ℚ (ppZRoot a v) := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hpu (by omega),
      ← Polynomial.cyclotomic_eq_minpoly_rat hpv (by omega)]
  rw [← aeval_relationPoly_P41Galois ha] at h ⊢
  obtain ⟨Q, hQ⟩ := minpoly.dvd ℚ _ h
  rw [hQ, hmin, map_mul, minpoly.aeval, zero_mul]

/-- If one conjugate sum `R(u)` vanishes, all do. -/
theorem ppZ_conjSum_galois {a : ℕ} (ha : 1 ≤ a) (N : ℤ) {u v : ℤ} (hu : IsCoprime u (a : ℤ))
    (hv : IsCoprime v (a : ℤ)) (h : ppZConjSum a N u = 0) : ppZConjSum a N v = 0 := by
  exact ppZ_root_sum_galois ha hu hv (Finset.range a) (ppZWeight a) (ppZExp N) h

end AJConjecture
