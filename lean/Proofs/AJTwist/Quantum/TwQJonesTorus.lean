import Mathlib
import AJTwist.Quantum.TwQJones
import AJTwist.Quantum.TwQInputBar
import AJHandoff.TorusQuantum.PairQTorusInputProof

/-!
# The coloured Jones function of the twisted Whitehead doubles of torus knots (Unit Q2)

Source: revision 5, Theorem 1.1 and Section 3 (eq. (commoninput), (claspfinite)); Section 8.2
(eq. (mirror-marked): `(W_{-,ℓ}(T_η))^* = W_{+,-ℓ}(T_{-η})`).

With `w = (r - 1) s` the writhe of the positive torus braid `torusPairWord r s`:

* `twQ_coloredJones_negClasp`: a braid knot `K` with
  `IsBandClasp K (torusPairKnot r s h) (2ℓ - 2w) true` and writhe `2w - 2ℓ - 2` (the negative
  clasp over `T(r, s)` with band framing `ℓ`) has the coloured Jones function
  `twFormula true r s ℓ`. For `ℓ = 0` this is `pairQ_coloredJones_of_longKnotOp_torusPair`.
* `twQ_coloredJones_posClasp`: a braid knot `K` with
  `IsBandClasp K (torusPairKnot r s h) (-2ℓ - 2w) false` and writhe `2ℓ + 2w + 2` (the positive
  clasp over `T(r, s)` with band framing `-ℓ`) has the coloured Jones function
  `twQBar (twFormula false r s ℓ)`.
* `twQ_coloredJones_mirror_of_posClasp`: a knot `K'` whose coloured Jones function is the bar of
  that of `K` (the mirror image of `K`; for the closure of the inverse braid this is
  `coloredJones_inv` of the knot package), i.e. the negative clasp over the mirror companion
  `T(r, -s)` with band framing `ℓ`, has the coloured Jones function `twFormula false r s ℓ`.

The companion input is the library's theorem `pairQ_torusInput` (no hypothesis).
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The negative clasp over the right-handed companion: `η = +1`, `a = r s - ℓ`. -/
theorem twQ_coloredJones_negClasp {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (K : BraidKnot)
    (hK : IsBandClasp K (torusPairKnot r s h) (2 * ℓ - 2 * (((r - 1) * s : ℕ) : ℤ)) true)
    (hw : writhe K.word = 2 * (((r - 1) * s : ℕ) : ℤ) - 2 * ℓ - 2) (n : ℤ) :
    laurentToField (coloredJones K n) = twFormula true r s ℓ n := by
  have e : 2 * ℓ - 2 * (((r - 1) * s : ℕ) : ℤ) = 2 * (ℓ - (((r - 1) * s : ℕ) : ℤ)) := by ring
  rw [e] at hK
  have hu : (fun i : ℕ ↦ qParam ^ (((((r - 1) * s : ℕ) : ℤ) + (ℓ - (((r - 1) * s : ℕ) : ℤ))) *
      (i : ℤ) * ((i : ℤ) + 1)) * pairQOddColor r s i) = twInput true r s ℓ := by
    funext i
    rw [twInput_true, add_sub_cancel]
  rw [twFormula, ← hu]
  exact twQ_coloredJones_of_isBandClasp_true K (torusPairKnot r s h) _ _ _
    (pairQ_knotTrace_torusPair_of_input (pairQ_torusInput r s h)) hK (by rw [hw]; ring) n

/-- The positive clasp over the right-handed companion with band framing `-ℓ`: the bar of the
formula of the negative clasp over the mirror companion with twist `ℓ`. -/
theorem twQ_coloredJones_posClasp {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (K : BraidKnot)
    (hK : IsBandClasp K (torusPairKnot r s h) (-(2 * ℓ) - 2 * (((r - 1) * s : ℕ) : ℤ)) false)
    (hw : writhe K.word = 2 * ℓ + 2 * (((r - 1) * s : ℕ) : ℤ) + 2) (n : ℤ) :
    laurentToField (coloredJones K n) = twQBar (twFormula false r s ℓ n) := by
  have e : -(2 * ℓ) - 2 * (((r - 1) * s : ℕ) : ℤ) =
      2 * (-ℓ - (((r - 1) * s : ℕ) : ℤ)) := by ring
  rw [e] at hK
  have hu : (fun i : ℕ ↦ qParam ^ (-(((((r - 1) * s : ℕ) : ℤ) +
      (-ℓ - (((r - 1) * s : ℕ) : ℤ))) * (i : ℤ) * ((i : ℤ) + 1))) *
        twQBar (pairQOddColor r s i)) = twInput false r s ℓ := by
    funext i
    rw [twInput_false]
    congr 2
    ring
  rw [twFormula, ← hu]
  exact twQ_coloredJones_of_isBandClasp_false K (torusPairKnot r s h) _ _ _
    (pairQ_knotTrace_torusPair_of_input (pairQ_torusInput r s h)) hK (by rw [hw]; ring) n

/-- The negative clasp over the mirror companion (`η = -1`, `a = -r s - ℓ`), as the mirror image
`K'` of the positive clasp `K` over the right-handed companion. -/
theorem twQ_coloredJones_mirror_of_posClasp {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (K K' : BraidKnot)
    (hK : IsBandClasp K (torusPairKnot r s h) (-(2 * ℓ) - 2 * (((r - 1) * s : ℕ) : ℤ)) false)
    (hw : writhe K.word = 2 * ℓ + 2 * (((r - 1) * s : ℕ) : ℤ) + 2)
    (hmir : ∀ n : ℤ, coloredJones K' n = LaurentPolynomial.invert (coloredJones K n))
    (n : ℤ) :
    laurentToField (coloredJones K' n) = twFormula false r s ℓ n := by
  rw [hmir, ← twQBar_laurentToField, twQ_coloredJones_posClasp h ℓ K hK hw, twQBar_twQBar]

end AJConjecture
