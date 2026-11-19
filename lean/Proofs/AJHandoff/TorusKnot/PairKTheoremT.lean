import Mathlib
import AJHandoff.TorusKnot.PairKAssembly
import AJHandoff.TorusKnot.PairKDistinct
import AJHandoff.TorusQuantum.PairQTorusInputProof
import AJHandoff.TorusQuantum.PairQTorusInputTwo

/-!
# Theorem T and Theorem F

**Theorem T** (`theoremT`), for the knots `K = pairWhiteheadKnot r s h = Wh⁻₀(T(r, s))`, every
coprime `2 ≤ r < s`, in the baseline predicates of `AJConjecture.AJStatement`:

1. the localized annihilator of the coloured Jones function is nonzero and a recurrence
   polynomial `α` exists (T-MIN, P1);
2. `E` divides the nonzero specialisation of every nonzero primitive element of the localized
   annihilator (arbitrary primitive saturated rows; in particular `α`) (P1);
3. an A-polynomial exists (T-AEX); every A-polynomial `A` divides `(L - 1) B_(rs)` and is coprime
   to `E` in `ℚ(M)[L, L⁻¹]` (T-CLASS);
4. the localized square-free `SL₂` AJ statement fails for `K` (T-AJ);
5. different admissible pairs give closed braids that are not Markov equivalent (T-DIST (a)),
   and the pairs `(3, 3j + 1)`, `j ≥ 1`, are admissible (the infinite new range).

The quantum inputs are P1's `pairQ_formula_package`, `pairQ_knot_package` and its crux
`pairQ_torusInput` (the odd colours of `T(r, s)`); everything else is this package.

**Theorem F** (`theoremF`) is the instance `r = 2`, `s = 2k + 1`, with the companion input
`pairQ_torusInput_two` (proved from the library); the knots are the library's family
(`pairWhiteheadWord_two`), the seven-strand witness being `k = 1`.
-/

open Polynomial

namespace AJConjecture

/-- The clauses of Theorem T for one knot. -/
def PairTClauses (K : BraidKnot) (m : ℕ) : Prop :=
  (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
    (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
    (∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
    (∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A) ∧
    (∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      toComparison A ∣ toComparison (famBound m) ∧
        IsCoprime (toComparison extraFactor) (toComparison A)) ∧
    ¬ AJSquareFree K

/-- The clauses of Theorem T for `Wh⁻₀(T(r, s))`, given the companion input. -/
theorem pairTClauses_of_input {r s : ℕ} (h : IsTorusPair r s) (hT : PairQTorusInput r s h) :
    PairTClauses (pairWhiteheadKnot r s h) (r * s) := by
  have hk := pairQ_knot_package r s h hT (pairWhiteheadKnot r s h)
    (longKnotOp_pairWhiteheadKnot h) (writhe_pairWhiteheadKnot h)
  have hc := pairWhiteheadKnot_counterexample_of_input h hT
  obtain ⟨A, hA, -, -⟩ := exists_aPolynomial_pair h
  exact ⟨hk.2.1, hk.2.2.1, hc.2.1, ⟨A, hA⟩,
    fun A hA ↦ ⟨toComparison_dvd_famBound_pair h hA, isCoprime_extraFactor_pair h hA⟩, hc.1⟩

/-- **Theorem T**, conditional on the companion input for every pair (the coloured Jones
polynomial of `T(r, s)` at odd colours, `PairQTorusInput`). -/
theorem theoremT_of_input (hT : ∀ (r s : ℕ) (h : IsTorusPair r s), PairQTorusInput r s h) :
    (∀ (r s : ℕ) (h : IsTorusPair r s), PairTClauses (pairWhiteheadKnot r s h) (r * s)) ∧
    (∀ (r s r' s' : ℕ) (h : IsTorusPair r s) (h' : IsTorusPair r' s'), (r, s) ≠ (r', s') →
      ¬ MarkovEquiv (pairWhiteheadKnot r s h) (pairWhiteheadKnot r' s' h')) ∧
    (∀ j : ℕ, 1 ≤ j → IsTorusPair 3 (3 * j + 1)) :=
  ⟨fun r s h ↦ pairTClauses_of_input h (hT r s h),
    fun r s r' s' h h' hne ↦ pairWhiteheadKnot_not_markovEquiv h h' (hT r s h)
      (hT r' s' h') hne,
    isTorusPair_three⟩

/-- **Theorem T.** -/
theorem theoremT :
    (∀ (r s : ℕ) (h : IsTorusPair r s), PairTClauses (pairWhiteheadKnot r s h) (r * s)) ∧
    (∀ (r s r' s' : ℕ) (h : IsTorusPair r s) (h' : IsTorusPair r' s'), (r, s) ≠ (r', s') →
      ¬ MarkovEquiv (pairWhiteheadKnot r s h) (pairWhiteheadKnot r' s' h')) ∧
    (∀ j : ℕ, 1 ≤ j → IsTorusPair 3 (3 * j + 1)) :=
  theoremT_of_input pairQ_torusInput

/-- `(2, 2k + 1)` is admissible for `k ≥ 1`. -/
theorem isTorusPair_two (k : ℕ) (hk : 1 ≤ k) : IsTorusPair 2 (2 * k + 1) := by
  refine ⟨le_refl 2, by omega, ?_⟩
  rw [Nat.coprime_mul_left_add_right]
  exact Nat.coprime_one_right 2

/-- **Theorem F**: the instance `r = 2` of Theorem T, for the library's family. -/
theorem theoremF :
    (∀ (k : ℕ) (hk : 1 ≤ k),
      PairTClauses (pairWhiteheadKnot 2 (2 * k + 1) (isTorusPair_two k hk)) (2 * (2 * k + 1)) ∧
        (pairWhiteheadKnot 2 (2 * k + 1) (isTorusPair_two k hk)).word = whiteheadTorusWord k ∧
        (pairWhiteheadKnot 2 (2 * k + 1) (isTorusPair_two k hk)).strands = 4 * k + 3) ∧
    ∀ (k k' : ℕ) (hk : 1 ≤ k) (hk' : 1 ≤ k'), k ≠ k' →
      ¬ MarkovEquiv (pairWhiteheadKnot 2 (2 * k + 1) (isTorusPair_two k hk))
        (pairWhiteheadKnot 2 (2 * k' + 1) (isTorusPair_two k' hk')) :=
  ⟨fun k hk ↦ ⟨pairTClauses_of_input _ (pairQ_torusInput_two _ _), pairWhiteheadWord_two k hk,
      pairStrands_two k⟩,
    fun k k' hk hk' hne ↦ pairWhiteheadKnot_not_markovEquiv _ _ (pairQ_torusInput_two _ _)
      (pairQ_torusInput_two _ _) fun heq ↦ hne (by simp only [Prod.mk.injEq] at heq; omega)⟩

end AJConjecture
