import Mathlib
import AJConjecture.AJStatement
import AJTwist.Knot.TwKFamilyWord

/-!
# The extra support `Δ_K` and the torus-companion fingerprint (Unit PpF, definitions)

Source: Section 9 of the paper (`fingerprints.tex`), eq. (45) and Definition 9.1.

"For `f_K = α_K(-1, M, L) ≠ 0`, put `Δ_K = 𝖫(f_K) / gcd_R(𝖫(f_K), A_K)` in
`R = ℚ(M)[L^{±1}]`. Here `𝖫` denotes the square-free part in `R`, the product of the distinct
irreducible factors up to association."

"**Definition 9.1.** Let `P` be an oriented, peripherally marked pattern in the solid torus,
with integer disk twists `P_ℓ`. Let `𝒯` be the family of all nontrivial torus companions, of
both chiralities, with the preferred zero framing. … On the domain where the primitive minimum
exists and `f_{P_ℓ(C)} ≠ 0` for every `ℓ ∈ ℤ` and `C ∈ 𝒯`, define
`F_tor(P) = gcd_{ℓ ∈ ℤ, C ∈ 𝒯} Δ_{P_ℓ(C)}`. … It is taken up to association in `R`."

All objects are defined up to association, without a choice of representatives:

* `IsSquarefreePart f S`: `S` is a square-free part `𝖫(f)`: `S` is square-free and has the same
  prime divisors as `f`. (No such `S` exists for `f = 0` in a ring with infinitely many primes.)
* `IsExtraSupport f A Δ`: `Δ = 𝖫(f) / gcd(𝖫(f), A)`: there are a square-free part `S` of `f` and
  a greatest common divisor `g` of `S` and `A` with `S = g · Δ`.
* `IsExtraSupportOf K Δ`: `Δ` is `Δ_K`: the same with `f = α_K(-1, M, L)` for a recurrence
  polynomial `α_K` of the coloured Jones function and `A = A_K` an A-polynomial of `K`, in the
  comparison ring `R = ℚ(M)[L, L⁻¹]`.
* `IsFingerprintOf 𝒦 F`: every knot of the set `𝒦` has an extra support (the domain of
  Definition 9.1), and `F` is a greatest common divisor in `R` of all of them.
* `ppfTestSet σ`: the tested satellites of the Whitehead pattern `W_-` (`σ = true`) or `W_+`:
  the closed braids with the strands and the word of `W_(ε,ℓ)(T(r, ± s))`, over all coprime
  `2 ≤ r < s`, both signs and all `ℓ ∈ ℤ`.
* `IsTorusFingerprint σ F`: `F` is the torus-companion fingerprint `F_tor(W_ε)`.

`Δ_K` and `F_tor` are determined up to association by these predicates
(`AJPaper.Finger.PpFExists`, `AJPaper.Finger.PpFMain`).

**Interpretations.** (1) Patterns and the satellite operation are not formalized: Definition 9.1
is stated for an arbitrary set of knots, and for the two Whitehead patterns the tested
satellites are the closed braids of the library, as in Theorem 1.1. (2) "All nontrivial torus
companions, of both chiralities" is the family `T(r, s)`, `T(r, -s)` over coprime `2 ≤ r < s`
(every nontrivial torus knot is of this form). (3) `α_K` and `A_K` are the library's
`IsRecurrencePolynomial` and `IsAPolynomialOf (eigenvalueSet K)`; for a primitive `α_K` the
specialization is automatically nonzero.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `S` is a square-free part of `f`: it is square-free and has the same prime divisors as `f`
("the product of the distinct irreducible factors up to association"). -/
def IsSquarefreePart {R : Type*} [CommMonoidWithZero R] (f S : R) : Prop :=
  Squarefree S ∧ ∀ g : R, Prime g → (g ∣ S ↔ g ∣ f)

/-- `Δ` is `𝖫(f) / gcd(𝖫(f), A)`, eq. (45): a square-free part `S` of `f` is the product of a
greatest common divisor `g` of `S` and `A` with `Δ`. -/
def IsExtraSupport {R : Type*} [CommMonoidWithZero R] (f A Δ : R) : Prop :=
  ∃ S g : R, IsSquarefreePart f S ∧ (g ∣ S ∧ g ∣ A ∧ ∀ d : R, d ∣ S → d ∣ A → d ∣ g) ∧
    S = g * Δ

/-- `Δ` is the extra support `Δ_K` of the knot `K`, eq. (45): the square-free part of
`f_K = α_K(-1, M, L)` divided by its greatest common divisor with the A-polynomial `A_K`, in
`ℚ(M)[L, L⁻¹]`. -/
def IsExtraSupportOf (K : BraidKnot) (Δ : ComparisonRing) : Prop :=
  ∃ (α : RecOp) (A : ℤ[X][X]), IsRecurrencePolynomial (coloredJones K) α ∧
    IsAPolynomialOf (eigenvalueSet K) A ∧
    IsExtraSupport (toComparison (specialize α)) (toComparison A) Δ

/-- `F` is a fingerprint of the set of knots `𝒦`, eq. (46): every knot of `𝒦` has an extra
support `Δ_K`, and `F` is a greatest common divisor in `ℚ(M)[L, L⁻¹]` of these extra
supports. -/
def IsFingerprintOf (𝒦 : Set BraidKnot) (F : ComparisonRing) : Prop :=
  (∀ K ∈ 𝒦, ∃ Δ : ComparisonRing, IsExtraSupportOf K Δ) ∧
    (∀ K ∈ 𝒦, ∀ Δ : ComparisonRing, IsExtraSupportOf K Δ → F ∣ Δ) ∧
    ∀ d : ComparisonRing, (∀ K ∈ 𝒦, ∀ Δ : ComparisonRing, IsExtraSupportOf K Δ → d ∣ Δ) →
      d ∣ F

/-- The tested satellites of the Whitehead pattern of clasp sign `σ` (`σ = true`: negative
clasp): the closed braids of `W_(ε,ℓ)(T(r, ± s))` over all coprime `2 ≤ r < s`, both companion
chiralities `η` and all twists `ℓ`. -/
def ppfTestSet (σ : Bool) : Set BraidKnot :=
  {K | ∃ r s : ℕ, IsTorusPair r s ∧ ∃ (η : Bool) (ℓ : ℤ),
    K.strands = twFamilyStrands r s η ℓ ∧ K.word = twFamilyWord r s σ η ℓ}

/-- `F` is the torus-companion fingerprint `F_tor(W_ε)` of the Whitehead pattern of clasp sign
`σ` (Definition 9.1). -/
def IsTorusFingerprint (σ : Bool) (F : ComparisonRing) : Prop :=
  IsFingerprintOf (ppfTestSet σ) F

end AJConjecture
