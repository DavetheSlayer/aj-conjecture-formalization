import Mathlib
import AJTwist.Quantum.TwQInnerForcing
import AJTwist.Exist.TwHGaussWindow
import AJTwist.Exist.TwHChebTop

/-!
# The finitely many generators of the inner module

Let `a = twIndex η r s ℓ`, `D = pairQCycloCoeff (twInput η r s ℓ)` (the cyclotomic coefficients
of the twisted input) and `h = |ℓ|`. The generators are

* the trace operators `S_i(V) D`, `0 ≤ i ≤ |a|` (`cycloCheb i D`), and
* the Gaussian periods `𝔊^(c)`, `-h ≤ c ≤ h` (`twHGauss ℓ c`),

`|a| + 2h + 2` sequences in all. Their saturated span contains

* every Gaussian period (`twHSpan_gen_gauss`: `twHSpan_gauss` with the window `c₀ = -h`);
* the right-hand side of the inner equation (`twHSpan_gen_defect`): by eq. (innerforcing) in
  the period form `twQ_defect_eq_periods`,
  `p_a D = -q^(±rs+ℓ) ∑_i c_i (𝔊^(p_i) - J 𝔊^(p_i - 1))`, a combination of periods with
  coefficients constant or a constant times `J` (`twH_cycloCoeff_twPeriodInput` identifies the
  periods);
* the trace operators up to `S_(|a|+1)(V) D` (`twHSpan_gen_cheb`: generators for `i ≤ |a|`,
  `twHSpan_cheb_top` for `i = |a| + 1`).

No hypothesis on `r`, `s` is used: the inner equation holds for all natural `r`, `s` (checked
also for `r s = 0` and for non-coprime pairs, scratch `H/h01_basic.py`, item (f)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The generators of the inner module: `S_i(V) D` for `i ≤ |a|` and the Gaussian periods
`𝔊^(c)` for `|c| ≤ |ℓ|`. -/
def twHGen (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    Fin ((twIndex η r s ℓ).natAbs + 1) ⊕ Fin (2 * ℓ.natAbs + 1) → ℕ → RatFunc ℚ :=
  Sum.elim (fun i ↦ cycloCheb i (pairQCycloCoeff (twInput η r s ℓ)))
    (fun k ↦ twHGauss ℓ ((k : ℕ) - (ℓ.natAbs : ℤ)))

/-- Every Gaussian period lies in the span of the generators. -/
theorem twHSpan_gen_gauss (η : Bool) (r s : ℕ) (ℓ c : ℤ) :
    TwHSpan (twHGen η r s ℓ) (twHGauss ℓ c) := by
  refine twHSpan_gauss (twHGen η r s ℓ) ℓ (-(ℓ.natAbs : ℤ)) (fun c h1 h2 ↦ ?_) c
  have hk : (c + ℓ.natAbs).toNat < 2 * ℓ.natAbs + 1 := by omega
  have h := twHSpan_gen (twHGen η r s ℓ) (Sum.inr ⟨(c + ℓ.natAbs).toNat, hk⟩)
  have hc : (((c + ℓ.natAbs).toNat : ℕ) : ℤ) - (ℓ.natAbs : ℤ) = c := by omega
  simp only [twHGen, Sum.elim_inr, hc] at h
  exact h

/-- The right-hand side `p_a D` of the inner equation lies in the span of the generators. -/
theorem twHSpan_gen_defect (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    TwHSpan (twHGen η r s ℓ) (twDefect (twIndex η r s ℓ) (twInput η r s ℓ)) := by
  have hfun : twDefect (twIndex η r s ℓ) (twInput η r s ℓ) = fun j ↦
      -(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
        ∑ i : Fin 4, twCoef η r s i *
          (twHGauss ℓ (twExp η r s ℓ i) j -
            (X : (RatFunc ℚ)[X]).eval (qParam ^ j) * twHGauss ℓ (twExp η r s ℓ i - 1) j) := by
    funext j
    rw [twQ_defect_eq_periods]
    simp only [twH_cycloCoeff_twPeriodInput, eval_X]
  rw [hfun]
  refine twHSpan_constMul _ (twHSpan_sum Finset.univ
    (fun (i : Fin 4) j ↦ twCoef η r s i * (twHGauss ℓ (twExp η r s ℓ i) j -
      (X : (RatFunc ℚ)[X]).eval (qParam ^ j) * twHGauss ℓ (twExp η r s ℓ i - 1) j))
    fun i _ ↦ twHSpan_constMul _ (twHSpan_sub (twHSpan_gen_gauss η r s ℓ _)
      (twHSpan_polyMul X (twHSpan_gen_gauss η r s ℓ _))))

/-- The trace operators `S_i(V) D`, `i ≤ |a| + 1`, lie in the span of the generators. -/
theorem twHSpan_gen_cheb (η : Bool) (r s : ℕ) (ℓ : ℤ) {i : ℕ}
    (hi : i ≤ (twIndex η r s ℓ).natAbs + 1) :
    TwHSpan (twHGen η r s ℓ) (cycloCheb i (pairQCycloCoeff (twInput η r s ℓ))) := by
  have hlow : ∀ k : ℕ, k ≤ (twIndex η r s ℓ).natAbs →
      TwHSpan (twHGen η r s ℓ) (cycloCheb k (pairQCycloCoeff (twInput η r s ℓ))) := by
    intro k hk
    have h := twHSpan_gen (twHGen η r s ℓ) (Sum.inl ⟨k, Nat.lt_succ_of_le hk⟩)
    simp only [twHGen, Sum.elim_inl] at h
    exact h
  rcases Nat.lt_or_ge i ((twIndex η r s ℓ).natAbs + 1) with h | h
  · exact hlow i (Nat.lt_succ_iff.mp h)
  · rw [le_antisymm hi h]
    exact twHSpan_cheb_top _ _ _ hlow (twHSpan_gen_defect η r s ℓ)

end AJConjecture
