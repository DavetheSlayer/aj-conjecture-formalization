import Mathlib
import AJConjecture
import AJConjecture.AJStatement
import AJFamily.MarkovEquiv
import AJFamily.VolumeDefs
import AJFamily.FamilyMain
import AJFamily.Volume.MahlerExtraFactor
import AJFamily.Volume.WhiteheadVolume
import AJFamily.Volume.WhiteheadSlice
import AJFamily.Volume.WhiteheadSliceConverse

/-!
# Infinitely many counterexamples, and the volume attached to the extra factor

The main theorem has four parts.

1. **Infinitely many counterexamples with the same extra factor.** There are infinitely many
   braid knots, pairwise not Markov equivalent (so, by Markov's theorem, of different knot
   types), for which the localized square-free `SL₂` AJ conjecture `AJSquareFree` fails; for
   each of them the extra factor `E = L² - (M⁴ - 4M² + 1) L + M⁴` divides the (nonzero)
   specialisation at `t = -1` of every nonzero primitive element of the localized annihilator
   of the coloured Jones function, and is coprime to every A-polynomial. In the proof the knots
   are the untwisted negative-clasp Whitehead doubles `Wh(T(2, 2k+1))`, `k ≥ 1`, of the
   right-handed torus knots.
2. **Mahler measure.** `log |E|` is integrable on the torus and `m(E) = 4G/π`, where `G` is
   Catalan's constant.
3. **Volume.** The gluing and completeness equations of the four-tetrahedron triangulation of
   the Whitehead link complement have exactly one positively oriented solution, and the sum of
   the Bloch–Wigner values of its shapes, the hyperbolic volume of the link complement, is
   `4G`. Hence `π m(E)` is the volume of the Whitehead link complement.
4. **The curve `E` is the Whitehead slice.** On the deformations of the triangulation with the
   first cusp complete (meridian derivative `1`, longitude eigenvalue `-1`), the meridian
   eigenvalue `u` of the second cusp and the inverse of its longitude eigenvalue lie on `E`;
   conversely every point of `E` with `M ≠ 0` arises this way.

The definitions are those of the statement files of `AJConjecture`, of `AJFamily.MarkovEquiv`
and of `AJFamily.VolumeDefs`. The module also imports `AJConjecture`, so it contains both main
theorems, `not_ajSquareFreeConjecture` and `ajFamily_main`. Both are among the theorems of the
solution `Solution.lean` that `lake comparator` checks against `Challenge.lean` (see
`comparator.json`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Infinitely many counterexamples to the localized square-free `SL₂` AJ conjecture, the
Mahler measure of the extra factor, the volume of the Whitehead link complement, and the
identification of the extra factor with the eigenvalue curve of the completed Whitehead
slice. -/
theorem ajFamily_main :
    (∃ K : ℕ → BraidKnot, (Pairwise fun i j ↦ ¬ MarkovEquiv (K i) (K j)) ∧ ∀ n,
        ¬ AJSquareFree (K n) ∧
        (∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones (K n)) Q →
          specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet (K n)) A →
          IsCoprime (toComparison extraFactor) (toComparison A)) ∧
    (MeasureTheory.IntegrableOn (torusLogAbs extraFactorℂ) torusBox ∧
        logMahlerMeasure₂ extraFactorℂ = 4 * catalanConstant / Real.pi) ∧
    (∃! z : Fin 4 → ℂ, WhiteheadGluing z ∧ WhiteheadComplete z ∧ ∀ j, 0 < (z j).im) ∧
    (∀ z : Fin 4 → ℂ, WhiteheadGluing z → WhiteheadComplete z → (∀ j, 0 < (z j).im) →
        ∑ j, blochWigner (z j) = 4 * catalanConstant) ∧
    (∀ z : Fin 4 → ℂ, WhiteheadGluing z → (whiteheadPeripheral z).1 = 1 →
        (whiteheadPeripheral z).2.1 = -1 → ∀ u : ℂ, u ^ 2 = (whiteheadPeripheral z).2.2.1 →
          evalPoint extraFactorℂ (u, ((whiteheadPeripheral z).2.2.2)⁻¹) = 0) ∧
    (∀ p : ℂ × ℂ, evalPoint extraFactorℂ p = 0 → p.1 ≠ 0 →
        ∃ z : Fin 4 → ℂ, WhiteheadGluing z ∧ (whiteheadPeripheral z).1 = 1 ∧
          (whiteheadPeripheral z).2.1 = -1 ∧ (whiteheadPeripheral z).2.2.1 = p.1 ^ 2 ∧
          (whiteheadPeripheral z).2.2.2 = p.2⁻¹) :=
  ⟨infinitely_many_counterexamples, mahlerMeasure_extraFactor, whitehead_volume.1,
    whitehead_volume.2, whitehead_slice_mem_extraFactor, exists_whitehead_slice_of_extraFactor⟩

end AJConjecture
