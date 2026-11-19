import Mathlib
import AJTwist.Classical.TwCFourFamilies
import AJTwist.Main.TwMJones
import AJTwist.Main.TwMNegClasp
import AJTwist.Main.TwMMirrorSurvival
import AJTwist.Main.TwMClauses

/-!
# Theorem 1.1: the four families of twisted Whitehead doubles of torus knots

Source: *Whitehead doubles and the failure of the square-free AJ conjecture*, revision 5
(handoff of 18 November 2026), Theorem 1.1 (`introduction.tex`), proved in Sections 3–8; this
file is Section 8.2 ("since `-ℓ` ranges over all integers and `-η` over both chiralities, this
proves Theorem 1.1") and the assembly.

**Theorem** (`theoremFourFamilies`). For all coprime `2 ≤ r < s` (`IsTorusPair r s`), every twist
`ℓ ∈ ℤ` and both companions `T_η` (`η = true`: `T(r, s)`; `η = false`: its mirror `T(r, -s)`),
the marked satellites `twFamilyKnot r s h σ η ℓ = W_{ε,ℓ}(T_η)` satisfy `TwFamilyClauses`:

* negative clasp (`σ = true`): with the factor `E = L² - (M⁴ - 4M² + 1) L + M⁴`
  (`extraFactor`) and the classical bound `(L - 1) 𝒫_{-ℓ} 𝒫_a`, `a = η r s - ℓ`
  (`twBound (-ℓ) (twIndex η r s ℓ)`, eq. (classicalcontainment));
* positive clasp (`σ = false`): with the factor `E^∨ = M⁴ E(M⁻¹, L)` (`extraFactorMirror`) and
  the bound of the mirror knot `W_{-,-ℓ}(T_{-η})` reversed in `L`
  (`(twBound ℓ (-(twIndex η r s ℓ))).reverse`); the paper transports the bound by `M ↦ M⁻¹`
  instead: the two forms agree up to a unit `± M^j` of `R`, because every eigenvalue set is
  invariant under `(M, L) ↦ (M⁻¹, L⁻¹)` (`eigenvalueSet_symm`);

and `E`, `E^∨` are irreducible in `R = ℚ(M)[L, L⁻¹]`. The clauses are those of `theoremT`
(`PairTClauses`): the localized annihilator of the coloured Jones function is nonzero; a
recurrence polynomial exists; the factor divides the nonzero specialization of every nonzero
primitive element of the localized annihilator; an A-polynomial exists; every A-polynomial
divides the bound and is coprime to the factor in `R`; the localized square-free `SL₂` AJ
statement `AJSquareFree` fails. For `σ = true`, `η = true`, `ℓ = 0` the knot is
`pairWhiteheadKnot r s h` of `theoremT` and the bound is its `famBound (r * s)`
(`twFamilyKnot_untwisted`), so this instance is `PairTClauses (pairWhiteheadKnot r s h) (r * s)`
(`pairTClauses_of_twFamilyClauses`). `twFamilyClauses_twFamilyKnot` is the same theorem as one
statement over `σ`, `η`, `ℓ`, with `twFamilyFactor σ` and `twFamilyBound σ η r s ℓ`.

Assembly.

* Negative clasp (`twFamilyClauses_negClasp`): the coloured Jones function is
  `twFormula η r s ℓ` (`twm_coloredJones_negClasp`: packages Knot and Quantum); existence and
  survival of `E` by `twm_quantum_negClasp` (packages Exist, Select, Factor, Quantum); the
  classical clauses by `twClassClauses_twFamilyKnot_neg` (package Classical).
* Positive clasp (`twFamilyClauses_posClasp`): the knot is the mirror image of the negative-clasp
  knot `W_{-,-ℓ}(T_{-η})` of the family, so its coloured Jones function is the bar of that knot's
  (`twm_laurentToField_coloredJones_mirror`); existence and survival of `E^∨` by the mirror
  transport (`twm_mirror_exists`, `twm_mirror_survival`) of the quantum clauses of that knot; the
  classical clauses by `twClassClauses_twFamilyKnot_pos`.
* `twFamilyClauses_of` (prime factor ⟹ failure of the AJ statement).

This file has no `sorry`: everything open is in the packages named above.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Negative clasp**, both companions, every twist: the clauses with `G = E` and the bound
`(L - 1) 𝒫_{-ℓ} 𝒫_a`. -/
theorem twFamilyClauses_negClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) :
    TwFamilyClauses (twFamilyKnot r s h true η ℓ) extraFactor
      (twBound (-ℓ) (twIndex η r s ℓ)) := by
  have hq := twm_quantum_negClasp h η ℓ _ (twm_coloredJones_negClasp h η ℓ)
  exact twFamilyClauses_of prime_toComparison_extraFactor hq.1 hq.2.2
    (twClassClauses_twFamilyKnot_neg h η ℓ)

/-- **Positive clasp**, both companions, every twist: the clauses with `G = E^∨` and the
reversed bound of the mirror knot. -/
theorem twFamilyClauses_posClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) :
    TwFamilyClauses (twFamilyKnot r s h false η ℓ) extraFactorMirror
      (twBound ℓ (-(twIndex η r s ℓ))).reverse := by
  have hbar : ∀ n : ℤ, laurentToField (coloredJones (twFamilyKnot r s h false η ℓ) n) =
      twQBar (laurentToField (coloredJones (twFamilyKnot r s h true (!η) (-ℓ)) n)) := by
    intro n
    have hm := twm_laurentToField_coloredJones_mirror h true (!η) (-ℓ) n
    rwa [Bool.not_true, Bool.not_not, neg_neg] at hm
  have hq := twm_quantum_negClasp h (!η) (-ℓ) _ (twm_coloredJones_negClasp h (!η) (-ℓ))
  exact twFamilyClauses_of prime_toComparison_extraFactorMirror (twm_mirror_exists hbar hq.1)
    (twm_mirror_survival hbar hq.2.2) (twClassClauses_twFamilyKnot_pos h η ℓ)

/-- The obstruction factor `G` of Theorem 1.1: `E` for the negative clasp (`σ = true`) and
`E^∨ = M⁴ E(M⁻¹, L)` for the positive clasp, for both companions and every twist. -/
def twFamilyFactor (σ : Bool) : ℤ[X][X] :=
  if σ then extraFactor else extraFactorMirror

/-- The classical bound for `W_{ε,ℓ}(T_η)`: `(L - 1) 𝒫_{-ℓ} 𝒫_a` with `a = η r s - ℓ` for the
negative clasp, and the bound of the mirror knot `W_{-,-ℓ}(T_{-η})` reversed in `L` for the
positive clasp. -/
def twFamilyBound (σ η : Bool) (r s : ℕ) (ℓ : ℤ) : ℤ[X][X] :=
  if σ then twBound (-ℓ) (twIndex η r s ℓ) else (twBound ℓ (-(twIndex η r s ℓ))).reverse

/-- **All four families in one statement**: for both clasp signs `σ`, both companions `η` and
every twist `ℓ`, the knot `W_{ε,ℓ}(T_η)` satisfies the clauses with its factor and its bound. -/
theorem twFamilyClauses_twFamilyKnot {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    TwFamilyClauses (twFamilyKnot r s h σ η ℓ) (twFamilyFactor σ) (twFamilyBound σ η r s ℓ) := by
  cases σ
  · exact twFamilyClauses_posClasp h η ℓ
  · exact twFamilyClauses_negClasp h η ℓ

/-- The untwisted negative-clasp double of the right-handed companion is the knot of `theoremT`,
with the same classical bound. -/
theorem twFamilyKnot_untwisted {r s : ℕ} (h : IsTorusPair r s) :
    twFamilyKnot r s h true true 0 = pairWhiteheadKnot r s h ∧
      twBound (-0) (twIndex true r s 0) = famBound (r * s) := by
  refine ⟨twWhiteheadKnot_zero_true h, ?_⟩
  have hr : 2 ≤ r := h.1
  have hs : r < s := h.2.1
  have hm : 1 ≤ r * s := Nat.mul_pos (by omega) (by omega)
  rw [neg_zero, twIndex, ite_eq_left rfl, sub_zero]
  exact twBound_zero_natCast (r * s) hm

/-- The instance `ℓ = 0`, negative clasp, right-handed companion of the four-family theorem is
the first clause of `theoremT`, verbatim. -/
theorem pairTClauses_of_twFamilyClauses {r s : ℕ} (h : IsTorusPair r s) :
    PairTClauses (pairWhiteheadKnot r s h) (r * s) := by
  have h1 := twFamilyClauses_negClasp h true 0
  rwa [(twFamilyKnot_untwisted h).1, (twFamilyKnot_untwisted h).2] at h1

/-- **Theorem 1.1 (both clasp signs, all integer twists, both companion chiralities).** For all
coprime `2 ≤ r < s`, every `ℓ ∈ ℤ` and both companions `T(r, ± s)`, the twisted Whitehead doubles
`W_{-,ℓ}(T_η)` and `W_{+,ℓ}(T_η)` satisfy the clauses `TwFamilyClauses` with the factor `E`,
respectively `E^∨ = M⁴ E(M⁻¹, L)`: nonzero localized annihilator, existence of the recurrence
polynomial, divisibility of the nonzero specialization of every nonzero primitive element of the
localized annihilator by the factor, existence of an A-polynomial, divisibility of every
A-polynomial into the classical bound and its coprimality with the factor in `ℚ(M)[L, L⁻¹]`, and
the failure of the localized square-free `SL₂` AJ statement. The factors `E` and `E^∨` are
irreducible in `ℚ(M)[L, L⁻¹]`, and the case `ℓ = 0`, negative clasp, right-handed companion is
the knot of `theoremT`. -/
theorem theoremFourFamilies :
    (∀ (r s : ℕ) (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ),
      TwFamilyClauses (twFamilyKnot r s h true η ℓ) extraFactor
          (twBound (-ℓ) (twIndex η r s ℓ)) ∧
        TwFamilyClauses (twFamilyKnot r s h false η ℓ) extraFactorMirror
          (twBound ℓ (-(twIndex η r s ℓ))).reverse) ∧
    Irreducible (toComparison extraFactor) ∧ Irreducible (toComparison extraFactorMirror) ∧
    ∀ (r s : ℕ) (h : IsTorusPair r s),
      twFamilyKnot r s h true true 0 = pairWhiteheadKnot r s h ∧
        twBound (-0) (twIndex true r s 0) = famBound (r * s) :=
  ⟨fun _ _ h η ℓ ↦ ⟨twFamilyClauses_negClasp h η ℓ, twFamilyClauses_posClasp h η ℓ⟩,
    prime_toComparison_extraFactor.irreducible, prime_toComparison_extraFactorMirror.irreducible,
    fun _ _ h ↦ twFamilyKnot_untwisted h⟩

end AJConjecture
