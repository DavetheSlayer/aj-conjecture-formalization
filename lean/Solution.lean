import Mathlib
import AJConjecture
import AJFamily
import AJHandoff
import AJHandoff.TorusKnot.PairKWhDMain
import AJHandoff.TorusKnot.PairKWhDBand
import AJHandoff.TorusKnot.PairKWhDBandTorus
import AJHandoff.TorusKnot.PairKJonesTwoNe
import AJHandoff.Geometry.GeoZhVerbatim
import AJTwist
import AJPaper
import SolutionDefs

/-!
# The solution: the release theorems in braid-word form

The core claims of the v1 release, the four-family theorem (Theorem 1.1 of arXiv:2611.24826v1) and
the further claims of the paper proved in `Proofs/AJPaper/`, stated so that every constant they
mention is a *data* definition (a number of strands, a braid word, a polynomial) or one of the
baseline predicates of `AJConjecture.AJStatement`. The knots are not named by the constants
`pairWhiteheadKnot r s h` and `whiteheadTorusKnot k hk`, whose definitions carry the proofs that
the braid closes up to a knot; instead each claim quantifies over every `K : BraidKnot` with the
given number of strands and the given braid word. Since the remaining fields of a `BraidKnot` are
proofs, there is exactly one such `K`, and the existence clauses below say that it exists (the word
closes up to a knot).

* `release_theoremT`: **Theorem T** for the untwisted negative-clasp Whitehead doubles
  `Wh⁻₀(T(r, s))`, every coprime `2 ≤ r < s`, as the closures of `pairWhiteheadWord r s` on
  `pairStrands r s = 2(r - 1)s + 1` strands: such a knot exists; for it the clauses
  `PairTClauses K (r s)` hold (a recurrence polynomial exists; `E` divides the specialisation of
  every primitive element of the localized annihilator; an A-polynomial exists and every
  A-polynomial divides `(L - 1) B_(rs)` and is coprime to `E`; the localized square-free `SL₂` AJ
  statement fails); different pairs give closed braids that are not Markov equivalent; the pairs
  `(3, 3j + 1)`, `j ≥ 1`, are admissible.
* `release_classicalEquality`: every A-polynomial of `Wh⁻₀(T(r, s))` is associated to
  `(L - 1) B_(rs)` in `ℚ(M)[L, L⁻¹]`.
* `release_minimalRecurrence`: for `W_k`, the closure of `whiteheadTorusWord k` on `4k + 3`
  strands (`k ≥ 1`): such a knot exists, a recurrence polynomial exists, and every recurrence
  polynomial has order `8k + 8` and special symbol `(L - 1)² E B_(2(2k+1))` up to a unit.
* `release_pairWord_two`: the knots `W_k` are the pairs `(2, 2k + 1)` of Theorem T (Theorem F).
* `release_coloredJones_two_ne`: different admissible pairs give different colour-2 coloured Jones
  polynomials (distinctness without Markov's theorem, given isotopy invariance).
* `release_whDouble`: the satellite bridge (T-KNOT, diagram form). The cut-open closed braid of
  Theorem T reaches, by the moves of the checker, the untwisted negative-clasp Whitehead double
  `whDouble C` of the cut-open `T(r, s)`; `C` has framing `(r - 1)s`; `whDouble C` is a long knot of
  writhe `2(r - 1)s - 2`; its band is untwisted; its clasp is negative.
* `release_theoremFourFamilies`: **Theorem 1.1 of the four-family manuscript** (*Whitehead doubles
  and the failure of the square-free AJ conjecture*, revision 5): for all coprime `2 ≤ r < s`,
  every twist `ℓ ∈ ℤ`, both clasp signs (`σ = true`: negative) and both companions (`η = true`:
  `T(r, s)`; `η = false`: `T(r, -s)`), a closed braid with `twFamilyStrands r s η ℓ` strands and
  the word `twFamilyWord r s σ η ℓ` exists, and every such closed braid satisfies
  `TwFamilyClauses` (the clauses of `PairTClauses`: a nonzero element of the localized
  annihilator and a recurrence polynomial exist; the factor divides the nonzero specialisation
  of every nonzero primitive element of the localized annihilator; an A-polynomial exists; every
  A-polynomial divides the bound and is coprime to the factor; the localized square-free `SL₂`
  AJ statement fails) with the factor `E` and the bound `(L - 1) 𝒫_(-ℓ) 𝒫_a`, `a = η r s - ℓ`
  (`twBound (-ℓ) (twIndex η r s ℓ)`), for the negative clasp, and with the factor
  `E^∨ = M⁴ E(M⁻¹, L)` (`extraFactorMirror`) and the `L`-reversed bound of the mirror knot for the
  positive clasp; `E` and `E^∨` are irreducible in `ℚ(M)[L, L⁻¹]`; for `ℓ = 0`, the negative
  clasp and `T(r, s)` the strands, the word and the bound are those of Theorem T. Over
  `T(r, s)` the word is `twWhiteheadWord r s ℓ σ`; over `T(r, -s)` it is the inverse of the word
  of the satellite with the opposite clasp and the opposite twist over `T(r, s)` (the mirror
  identity of the manuscript, used as the definition).
* `release_fourFamilies_coloredJones`: the coloured Jones function of these closed braids is the
  cyclotomic formula of the manuscript with the twisted input (`twFormula η r s ℓ`, the unreduced
  `[n] F_n` with `q = t⁴`) for the negative clasp; for the positive clasp its image under
  `t ↦ t⁻¹` is the formula of the mirror knot (`twFormula (!η) r s (-ℓ)`).
* `release_fillingFactor`, `release_fillingDichotomy`, `release_twistKnots`: **Section 7.6** of
  the paper. Every A-polynomial of the negative-clasp satellite `W_(-,ℓ)(T_η)` is divisible by the
  companion-abelian filling factor `(L - 1) 𝒫_(-ℓ)` (for the positive clasp by the reverse in `L`
  of `(L - 1) 𝒫_ℓ`); it is associated to that factor or to the full bound, and to that factor when
  `a = 0`; and for every `ℓ` the word `ppaTwistWord ℓ` on `3 + twExtra ℓ` strands closes up to
  a knot (the pure closure `Z_ℓ`, a twist knot) whose A-polynomials are associated to
  `(L - 1) 𝒫_(-ℓ)`.
* `release_theoremG`: Theorem G with the knots given by their braid words, without the units whose
  definitions use `private` library lemmas; `release_theoremG_supplement`: those units, stated
  with the replacement definitions of `Proofs/SolutionDefs.lean` (equal to the library's up to
  proof terms).
* `release_hasSimpleResidue_ramify`, `release_hasNormalizedIndex_powerSubst`,
  `release_seq_theoremS`: the I-GAUGE units and the sequence theorem S, likewise stated with
  replacement definitions.

The library theorems that the comparator checks under their own names (their statements mention
only data): `not_ajSquareFreeConjecture`; `ajFamily_main` (infinitely many counterexamples, the
Mahler measure `m(E) = 4G/π`, the Whitehead link volume `4G`, `E` as the Whitehead slice);
`morseReach_whDouble`, `morseWrithe_eq_of_morseReach`, `zero_mem_bandLinkings_whBand` (the
Whitehead double of long-knot diagrams is well defined and untwisted); `zhengEq516_holds`,
`zhengEq519_of_zhengEq512`, `zhengEstimates_of_verbatim`, `geo_phys_of_zhengVerbatim` (G-PHYS
conditional only on Zheng's printed estimates); the units of Theorem I and of the sequence theorem
listed in `comparator.json`; `pairQJets_abNode`, `pairQJets_ebNode` (T-JETS) and
`pairQ_transferOp_oreIrreducible` (T-IRR); and, from `Proofs/AJPaper/`,
`release_corollaryUntwisted` (Corollary 8.3: `A_S ∣ f_S` for the untwisted doubles of all four
families), `release_wholeSymbolAllTwists` (`(L - 1) E 𝒫_a ∣ f_S` for every twist),
`release_subOneDvd` (`L - 1 ∣ f_S`), `ppl_irreducible` (the transfer operator is irreducible for
every index `a`), `release_idealFormulations` (Section 8.5: the ideal formulations of Tran and of
Sikora fail), `corollary_whitehead_fingerprint` (Corollary 9.2), `zhengEstimates_holds` (Zheng's
estimates, for the companions `T(a, 2)` with `a ≥ 3` odd) and `geo_phys_holds` (Theorem B.1 (4)
without hypothesis). `Challenge.lean` is generated from the library (`Proofs/`) and this file by
`tools/make_challenge.py`; `lake comparator` checks the theorems of `comparator.json` against it.
`B_m` is the classical twist factor `famB m`; the quantum `twistPoly m` of the library agrees with
it for `m ≥ 1` (`famB_eq_twistPoly`). The filling polynomial `𝒫_k` of the four-family theorem is
`twP k`: `twistPoly k` for `k ≥ 0` (so `𝒫_0 = 1`) and `twistPolyNeg (-k)`, the `C_(-k)` of the
manuscript, for `k < 0`.
-/

open Polynomial

namespace AJConjecture

/-- A braid knot with the strands and the word of `pairWhiteheadKnot r s h` is that knot: the other
fields of a `BraidKnot` are proofs. -/
private theorem eq_pairWhiteheadKnot_of_word {r s : ℕ} (h : IsTorusPair r s) {K : BraidKnot}
    (hs : K.strands = pairStrands r s) (hw : K.word = pairWhiteheadWord r s) :
    K = pairWhiteheadKnot r s h := by
  obtain ⟨m, w, _, _, _⟩ := K
  dsimp only at hs hw
  subst hs hw
  rfl

/-- A braid knot with the strands and the word of `whiteheadTorusKnot k hk` is that knot. -/
private theorem eq_whiteheadTorusKnot_of_word {k : ℕ} (hk : 1 ≤ k) {K : BraidKnot}
    (hs : K.strands = 4 * k + 3) (hw : K.word = whiteheadTorusWord k) :
    K = whiteheadTorusKnot k hk := by
  obtain ⟨m, w, _, _, _⟩ := K
  dsimp only at hs hw
  subst hs hw
  rfl

/-- **Theorem T** in braid-word form. -/
theorem release_theoremT :
    (∀ r s : ℕ, IsTorusPair r s → ∃ K : BraidKnot,
        K.strands = pairStrands r s ∧ K.word = pairWhiteheadWord r s) ∧
    (∀ r s : ℕ, IsTorusPair r s → ∀ K : BraidKnot,
        K.strands = pairStrands r s → K.word = pairWhiteheadWord r s → PairTClauses K (r * s)) ∧
    (∀ r s r' s' : ℕ, IsTorusPair r s → IsTorusPair r' s' → (r, s) ≠ (r', s') →
        ∀ K K' : BraidKnot, K.strands = pairStrands r s → K.word = pairWhiteheadWord r s →
          K'.strands = pairStrands r' s' → K'.word = pairWhiteheadWord r' s' →
            ¬ MarkovEquiv K K') ∧
    (∀ j : ℕ, 1 ≤ j → IsTorusPair 3 (3 * j + 1)) := by
  refine ⟨fun r s h ↦ ⟨pairWhiteheadKnot r s h, rfl, rfl⟩, fun r s h K hs hw ↦ ?_,
    fun r s r' s' h h' hne K K' hs hw hs' hw' ↦ ?_, theoremT.2.2⟩
  · rw [eq_pairWhiteheadKnot_of_word h hs hw]
    exact theoremT.1 r s h
  · rw [eq_pairWhiteheadKnot_of_word h hs hw, eq_pairWhiteheadKnot_of_word h' hs' hw']
    exact theoremT.2.1 r s r' s' h h' hne

/-- **The classical equality** `A ≐ (L - 1) B_(rs)` in `ℚ(M)[L, L⁻¹]`, in braid-word form. -/
theorem release_classicalEquality :
    ∀ r s : ℕ, IsTorusPair r s → ∀ K : BraidKnot,
      K.strands = pairStrands r s → K.word = pairWhiteheadWord r s →
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
          Associated (toComparison A) (toComparison (famBound (r * s))) := by
  intro r s h K hs hw A hA
  rw [eq_pairWhiteheadKnot_of_word h hs hw] at hA
  exact aPolynomial_pair_associated_famBound h hA

/-- **The minimal recurrence of `W_k`** in braid-word form: order `8k + 8` and special symbol
`(L - 1)² E B_m`, `m = 2(2k + 1)`. -/
theorem release_minimalRecurrence :
    ∀ k : ℕ, 1 ≤ k →
      (∃ K : BraidKnot, K.strands = 4 * k + 3 ∧ K.word = whiteheadTorusWord k) ∧
      ∀ K : BraidKnot, K.strands = 4 * k + 3 → K.word = whiteheadTorusWord k →
        (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
          ∀ α : RecOp, IsRecurrencePolynomial (coloredJones K) α →
            α.natDegree = 8 * k + 8 ∧
              Associated (toComparison (specialize α))
                (toComparison ((X - 1) ^ 2 * extraFactor * famB (2 * (2 * k + 1)))) := by
  intro k hk
  refine ⟨⟨whiteheadTorusKnot k hk, rfl, rfl⟩, fun K hs hw ↦ ?_⟩
  rw [eq_whiteheadTorusKnot_of_word hk hs hw, famB_eq_twistPoly _ (by omega)]
  exact minimalRecurrence_whiteheadTorusKnot k hk

/-- **Theorem F** as a word identity: for `r = 2`, `s = 2k + 1` the knot of Theorem T is `W_k`. -/
theorem release_pairWord_two :
    ∀ k : ℕ, 1 ≤ k → pairStrands 2 (2 * k + 1) = 4 * k + 3 ∧
      pairWhiteheadWord 2 (2 * k + 1) = whiteheadTorusWord k :=
  fun k hk ↦ ⟨pairStrands_two k, pairWhiteheadWord_two k hk⟩

/-- **Distinctness by the coloured Jones polynomial**: closed braids with the words of different
admissible pairs have different colour-2 coloured Jones polynomials. -/
theorem release_coloredJones_two_ne :
    ∀ r s r' s' : ℕ, IsTorusPair r s → IsTorusPair r' s' → (r, s) ≠ (r', s') →
      ∀ K K' : BraidKnot, K.strands = pairStrands r s → K.word = pairWhiteheadWord r s →
        K'.strands = pairStrands r' s' → K'.word = pairWhiteheadWord r' s' →
          coloredJones K 2 ≠ coloredJones K' 2 := by
  intro r s r' s' h h' hne K K' hs hw hs' hw'
  rw [eq_pairWhiteheadKnot_of_word h hs hw, eq_pairWhiteheadKnot_of_word h' hs' hw']
  exact coloredJones_two_pairWhiteheadKnot_ne h h' hne

/-- **The satellite bridge (T-KNOT, diagram form)**: with `C` the closed braid
`(σ_0 ⋯ σ_(r-2))^s` on `r` strands cut open (the right-handed `T(r, s)`), the cut-open closed
braid of Theorem T reaches the untwisted negative-clasp Whitehead double `whDouble C` by the moves
of the checker; `C` is a long-knot diagram of blackboard framing `(r - 1)s`; `whDouble C` has one
orientation, of oriented writhe `2(r - 1)s - 2`; the band of `whDouble C` is untwisted (linking
number `0`, for its unique labelling); and the clasp is negative (both crossings of oriented sign
`-1`). -/
theorem release_whDouble :
    (∀ r s : ℕ, IsTorusPair r s →
      MorseReach 1 (morseLongClosure (pairStrands r s) (pairWhiteheadWord r s))
          (whDouble (morseLongClosure r (torusPairWord r s))) ∧
        IsLongKnotDiagram (morseLongClosure r (torusPairWord r s)) ∧
        morseWrithe (morseLongClosure r (torusPairWord r s)) = (((r - 1) * s : ℕ) : ℤ) ∧
        orientWrithes (whDouble (morseLongClosure r (torusPairWord r s))) =
          [2 * (((r - 1) * s : ℕ) : ℤ) - 2] ∧
        bandLinkings (whBand (morseLongClosure r (torusPairWord r s))) = [0]) ∧
    orientStates (claspWord ++ [(.cap, 1)]) [([true, false, true], 0)] = [([true], -2)] := by
  refine ⟨fun r s h ↦ ?_, orientStates_clasp_negative⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := pairWhiteheadKnot_whDouble h
  exact ⟨h1, h2, h3, h4, bandLinkings_whBand_braidLongDiagram (torusPairKnot r s h)⟩

/-- **Theorem 1.1 (the four families)** in braid-word form: every integer twist `ℓ`, both clasp
signs `σ` and both companions `η` over every coprime `2 ≤ r < s`. A closed braid with the data
`twFamilyStrands r s η ℓ`, `twFamilyWord r s σ η ℓ` exists; each one satisfies the clauses
`TwFamilyClauses` with the factor `E` (negative clasp, `σ = true`), respectively
`E^∨ = M⁴ E(M⁻¹, L)` (positive clasp), and its classical bound; `E` and `E^∨` are irreducible in
`ℚ(M)[L, L⁻¹]`; without twist, for the negative clasp and the companion `T(r, s)` the data and
the bound are those of Theorem T. -/
theorem release_theoremFourFamilies :
    (∀ r s : ℕ, IsTorusPair r s → ∀ (σ η : Bool) (ℓ : ℤ), ∃ K : BraidKnot,
        K.strands = twFamilyStrands r s η ℓ ∧ K.word = twFamilyWord r s σ η ℓ) ∧
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
        K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s true η ℓ →
          TwFamilyClauses K extraFactor (twBound (-ℓ) (twIndex η r s ℓ))) ∧
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
        K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s false η ℓ →
          TwFamilyClauses K extraFactorMirror (twBound ℓ (-(twIndex η r s ℓ))).reverse) ∧
    Irreducible (toComparison extraFactor) ∧ Irreducible (toComparison extraFactorMirror) ∧
    (∀ r s : ℕ, IsTorusPair r s →
        twFamilyStrands r s true 0 = pairStrands r s ∧
          twFamilyWord r s true true 0 = pairWhiteheadWord r s ∧
          twBound (-0) (twIndex true r s 0) = famBound (r * s)) := by
  refine ⟨fun r s h σ η ℓ ↦ ⟨twFamilyKnot r s h σ η ℓ, strands_twFamilyKnot r s h σ η ℓ,
      word_twFamilyKnot r s h σ η ℓ⟩, fun r s h η ℓ K hs hw ↦ ?_, fun r s h η ℓ K hs hw ↦ ?_,
    theoremFourFamilies.2.1, theoremFourFamilies.2.2.1, fun r s h ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw]
    exact (theoremFourFamilies.1 r s h η ℓ).1
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw]
    exact (theoremFourFamilies.1 r s h η ℓ).2
  · exact ⟨(twFamilyWord_untwisted h).1, (twFamilyWord_untwisted h).2,
      (theoremFourFamilies.2.2.2 r s h).2⟩

/-- **The coloured Jones functions of the four families**: for the negative clasp the coloured
Jones function of the closed braid, read in `ℚ(t)`, is the formula `twFormula η r s ℓ` (the
unreduced cyclotomic formula `[n] F_n` with the input twisted by `q^(-a n(n+1))`,
`a = η r s - ℓ`, `q = t⁴`); for the positive clasp its image under `t ↦ t⁻¹` is the formula of the
mirror knot, the negative-clasp satellite with the opposite twist over the mirror companion. -/
theorem release_fourFamilies_coloredJones :
    ∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ →
        (K.word = twFamilyWord r s true η ℓ →
          ∀ n : ℤ, laurentToField (coloredJones K n) = twFormula η r s ℓ n) ∧
        (K.word = twFamilyWord r s false η ℓ →
          ∀ n : ℤ, laurentToField (LaurentPolynomial.invert (coloredJones K n)) =
            twFormula (!η) r s (-ℓ) n) := by
  intro r s h η ℓ K hs
  refine ⟨fun hw n ↦ ?_, fun hw n ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw]
    exact twm_coloredJones_negClasp h η ℓ n
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw]
    have hm := twm_coloredJones_mirror h false η ℓ n
    rw [Bool.not_false] at hm
    rw [← twm_coloredJones_negClasp h (!η) (-ℓ) n, hm]
    rfl

/-- **Section 7.6, the companion-abelian filling factor**, in braid-word form: for coprime
`2 ≤ r < s`, both companions `η` and every twist `ℓ`, every A-polynomial of a closed braid with
the data of the negative-clasp satellite `W_(-,ℓ)(T_η)` is divisible by `(L - 1) 𝒫_(-ℓ)` in
`ℚ(M)[L, L⁻¹]`, and every A-polynomial of a closed braid with the data of the positive-clasp
satellite `W_(+,ℓ)(T_η)` is divisible by the reverse in `L` of `(L - 1) 𝒫_ℓ`. -/
theorem release_fillingFactor :
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s true η ℓ →
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
          toComparison ((X - 1) * twP (-ℓ)) ∣ toComparison A) ∧
    ∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s false η ℓ →
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
          toComparison ((X - 1) * twP ℓ).reverse ∣ toComparison A := by
  refine ⟨fun r s h η ℓ K hs hw A hA ↦ ?_, fun r s h η ℓ K hs hw A hA ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw] at hA
    exact ppa_fillingFactor_dvd_neg h η ℓ hA
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw] at hA
    exact ppa_fillingFactor_dvd_pos h η ℓ hA

/-- **The A-polynomial of the twisted doubles up to one factor** (Section 7.6 with the bound
(41)), in braid-word form: every A-polynomial of the negative-clasp satellite `W_(-,ℓ)(T_η)` is
associated in `ℚ(M)[L, L⁻¹]` to `(L - 1) 𝒫_(-ℓ)` or to the full bound `(L - 1) 𝒫_(-ℓ) 𝒫_a`,
`a = η r s - ℓ`, and to `(L - 1) 𝒫_(-ℓ)` when `a = 0`; for the positive clasp the same holds
with the reverses in `L` of `(L - 1) 𝒫_ℓ` and of `(L - 1) 𝒫_ℓ 𝒫_(-a)`. -/
theorem release_fillingDichotomy :
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s true η ℓ →
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
          (Associated (toComparison A) (toComparison ((X - 1) * twP (-ℓ))) ∨
            Associated (toComparison A) (toComparison (twBound (-ℓ) (twIndex η r s ℓ)))) ∧
          (twIndex η r s ℓ = 0 →
            Associated (toComparison A) (toComparison ((X - 1) * twP (-ℓ))))) ∧
    ∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s false η ℓ →
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
          (Associated (toComparison A) (toComparison ((X - 1) * twP ℓ).reverse) ∨
            Associated (toComparison A)
              (toComparison (twBound ℓ (-(twIndex η r s ℓ))).reverse)) ∧
          (twIndex η r s ℓ = 0 →
            Associated (toComparison A) (toComparison ((X - 1) * twP ℓ).reverse)) := by
  refine ⟨fun r s h η ℓ K hs hw A hA ↦ ?_, fun r s h η ℓ K hs hw A hA ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw] at hA
    exact ⟨ppa_aPolynomial_cases_neg h η ℓ hA,
      fun ha ↦ ppa_aPolynomial_of_index_zero_neg h η ℓ ha hA⟩
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw] at hA
    exact ⟨ppa_aPolynomial_cases_pos h η ℓ hA,
      fun ha ↦ ppa_aPolynomial_of_index_zero_pos h η ℓ ha hA⟩

/-- A braid knot with the strands and the word of `ppaTwistKnot ℓ` is that knot. -/
private theorem eq_ppaTwistKnot_of_word (ℓ : ℤ) {K : BraidKnot}
    (hs : K.strands = 3 + twExtra ℓ) (hw : K.word = ppaTwistWord ℓ) : K = ppaTwistKnot ℓ := by
  obtain ⟨m, w, _, _, _⟩ := K
  dsimp only at hs hw
  subst hs hw
  rfl

/-- **The A-polynomial of the twist knots** (Section 7.6), in braid-word form: for every
`ℓ ∈ ℤ` the word `ppaTwistWord ℓ` on `3 + twExtra ℓ` strands closes up to a knot (the pure
closure `Z_ℓ` of the pattern, a twist knot), and every A-polynomial of such a closed braid is
associated to `(L - 1) 𝒫_(-ℓ)` in `ℚ(M)[L, L⁻¹]`; in the indexing of the paper,
`A_(Z_(-k)) ≐ (L - 1) 𝒫_k`. -/
theorem release_twistKnots :
    ∀ ℓ : ℤ,
      (∃ K : BraidKnot, K.strands = 3 + twExtra ℓ ∧ K.word = ppaTwistWord ℓ) ∧
      ∀ K : BraidKnot, K.strands = 3 + twExtra ℓ → K.word = ppaTwistWord ℓ →
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
          Associated (toComparison A) (toComparison ((X - 1) * twP (-ℓ))) := by
  intro ℓ
  refine ⟨⟨ppaTwistKnot ℓ, rfl, rfl⟩, fun K hs hw A hA ↦ ?_⟩
  rw [eq_ppaTwistKnot_of_word ℓ hs hw] at hA
  exact ppa_aPolynomial_twistKnot ℓ hA

/-- **I-GAUGE, ramified pullback** (`hasSimpleResidue_ramify`), stated with `ratRamifyR`, the
replacement for `ratRamify` (`Proofs/SolutionDefs.lean`; they differ only in a proof term). -/
theorem release_hasSimpleResidue_ramify {f : RatFunc ℂ} {z₀ ι : ℂ} (hf : HasSimpleResidue f z₀ ι)
    {e : ℕ} (he : 0 < e) :
    HasSimpleResidue (ratRamifyR z₀ e he f * (e : RatFunc ℂ) * RatFunc.X ^ (e - 1)) 0 (e * ι) :=
  hasSimpleResidue_ramify hf he

/-- **I-GAUGE, unramified meridian coordinates** (`hasNormalizedIndex_powerSubst`), stated with
`ratPowerSubstR`, the replacement for `ratPowerSubst`. -/
theorem release_hasNormalizedIndex_powerSubst (δ : LocDilation) {a : ℂ} (ha : a ≠ 0) {k : ℕ}
    (hk : 0 < k) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {A B : LocPoly} (hB : locJet0 B ≠ 0)
    {D₀ D₁ : RatFunc ℂ}
    (hD : HasHJet (algebraMap LocPoly LocField A / algebraMap LocPoly LocField B) D₀ D₁) {ι : ℂ}
    (hι : HasNormalizedIndex (locDilationPow δ k hk).c (a * z₀ ^ k) D₀ D₁ ι) :
    HasHJet (algebraMap LocPoly LocField (locPowerSubst a k A) /
        algebraMap LocPoly LocField (locPowerSubst a k B))
      (ratPowerSubstR a k ha hk D₀) (ratPowerSubstR a k ha hk D₁) ∧
    HasNormalizedIndex δ.c z₀ (ratPowerSubstR a k ha hk D₀) (ratPowerSubstR a k ha hk D₁) ι :=
  hasNormalizedIndex_powerSubst δ ha hk hz₀ hB hD hι

/-- **The sequence theorem S** (`seq_theoremS`), stated with `seqEvalR`, the replacement for
`seqEval` (they differ only in the proof that nonzero coefficients evaluate to units). -/
theorem release_seq_theoremS {P : SeqField[X]} (hP : OreIrreducible seqShift P) {F : SeqGerm}
    (hF : F ∉ seqEvalR.range)
    (hPF : diffAct seqEvalR seqGermShift P F ∈ seqEvalR.range) {G : SeqField[X]}
    (hG : diffAct seqEvalR seqGermShift G F = 0) : ∃ H : SeqField[X], G = oreMul seqShift H P :=
  seq_theoremS hP hF hPF hG

section

open Filter Topology

open Classical in
/-- **Theorem G** (bounded v1) in release form: the units of `geo_theoremG` (G-KERNEL, G-CURVE
birationality and `j = 1728`, G-NORM, G-REG, G-REG-COMPACT, G-ACTION, G-MAHLER, G-SHAPE, G-VOL,
G-PHYS), with the knots `whiteheadTorusKnot k hk` given by their braid words. The function-field
isomorphism and the degree `[ℚ(E) : ℚ(r)] = 2` (G-CURVE), `{M, L} = 0` (G-K2) and the pattern
eigenvalue pairs (MARK) are in `release_theoremG_supplement`: their definitions use `private`
lemmas of the library, which a challenge cannot copy, and are restated there with replacements. -/
theorem release_theoremG :
    -- G-KERNEL
    (∀ k : ℕ, 1 ≤ k → ∀ K : BraidKnot, K.strands = 4 * k + 3 → K.word = whiteheadTorusWord k →
      ∀ N B : ℕ, 1 ≤ N → N ≤ B → laurentToField (coloredJones K N) =
        (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) *
          PowerSeries.coeff (N - 1)
            (∑ n ∈ Finset.range B,
              PowerSeries.C (torusOddColor (2 * k + 1) n) * geoClaspGen N n)) ∧
    (∀ x : ℂ, x ≠ 0 → x ^ 2 ≠ 1 →
      Set.BijOn (geoChannelL x) {y | geoChannelT x y = 0}
        {L | L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0}) ∧
    (∀ (a : ℕ) {x y : ℂ}, x ≠ 0 → x ^ 2 ≠ 1 → (y ≠ 0 ∧ y ≠ 1 ∧ y ≠ x ∧ y ≠ -x ∧ y ≠ -1) →
      (geoRatioQ a 1 x (-1) (-y) = 1 ∧ geoRatioZ 1 x (-1) (-y) = 1 ↔ geoChannelT x y = 0) ∧
        geoRatioX 1 x (-1) (-y) = geoChannelL x y) ∧
    -- G-CURVE
    Set.BijOn geoToWeierstrass GeoSmoothTorusLocus GeoWeierstrassOpen ∧
    geoWeierstrass.j = 1728 ∧
    -- G-NORM
    (∃ e : GeoLaurentE ≃+* geoLaurentImage,
      (e (algebraMap GeoCoordE GeoLaurentE geoMer) : GeoKW) = geoNuM ∧
        (e (algebraMap GeoCoordE GeoLaurentE geoLong) : GeoKW) = geoNuL) ∧
    (integralClosure geoLaurentImage GeoKW).restrictScalars ℚ = geoPuncturedImage ∧
    CompactSpace GeoEllipticPoints ∧
    (∀ r : OnePoint ℂ, (geoCoverR ⁻¹' {r}).ncard =
      if r = ((0 : ℂ) : OnePoint ℂ) ∨ r = ((1 : ℂ) : OnePoint ℂ) ∨
          r = ((-1 : ℂ) : OnePoint ℂ) ∨ r = OnePoint.infty then 1 else 2) ∧
    -- G-REG
    (∀ {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ}, HasDerivAt γ γ' t →
      (∀ᶠ s in 𝓝 t, γ s ∈ GeoSmoothTorusLocus) →
      HasDerivAt (fun s ↦ geoRegPrimitive (geoCurveR (γ s)))
        (geoEta (γ t).1 (γ t).2 γ'.1 γ'.2) t) ∧
    (geoRegPrimitive 0 = 0 ∧ geoRegPrimitive 1 = 0 ∧ geoRegPrimitive (-1) = 0 ∧
      geoRegPrimitive Complex.I = 2 * catalanConstant ∧
      geoRegPrimitive (-Complex.I) = -(2 * catalanConstant)) ∧
    -- G-REG-COMPACT
    (Continuous (geoRegPrimitiveP1 ∘ geoCoverR) ∧
      (∀ q ∈ GeoPuncturedModel, q.1 ^ 2 ≠ -1 →
        geoNormMap q ∈ GeoSmoothTorusLocus ∧
          geoRegPrimitive (geoCurveR (geoNormMap q)) = geoRegPrimitiveP1 (-q.1 : ℂ)) ∧
      (∀ P : GeoEllipticPoints, (geoCoverR P = ((0 : ℂ) : OnePoint ℂ) ∨
          geoCoverR P = ((1 : ℂ) : OnePoint ℂ) ∨ geoCoverR P = ((-1 : ℂ) : OnePoint ℂ) ∨
          geoCoverR P = OnePoint.infty) → geoRegPrimitiveP1 (geoCoverR P) = 0) ∧
      (∀ P : GeoEllipticPoints, geoCoverR P = (Complex.I : OnePoint ℂ) →
        geoRegPrimitiveP1 (geoCoverR P) = 2 * catalanConstant) ∧
      (∀ P : GeoEllipticPoints, geoCoverR P = ((-Complex.I : ℂ) : OnePoint ℂ) →
        geoRegPrimitiveP1 (geoCoverR P) = -(2 * catalanConstant))) ∧
    (∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ¬ ∃ c : ℝ, Tendsto (fun p ↦ geoRegPrimitive (geoCurveR p))
      (𝓝[GeoSmoothTorusLocus] (ε, -1)) (𝓝 c)) ∧
    -- G-ACTION: the channel action is a branch; envelope dS_crit = log L dlog x on admissible
    -- lifts; dV_S = -2η, V_S + 2U constant, and V_S = -2U after normalizing at r = 1/2
    (∀ a : ℕ, GeoChannelActionBranch (geoChannelAction a) geoChannelActionDomain) ∧
    (∀ a : ℕ, ∃ ε > 0, ∀ r ∈ Metric.ball (2 : ℂ) ε,
      (Complex.log (-geoX r) + Real.pi * Complex.I,
          Complex.log (1 / r) + Real.pi * Complex.I) ∈ geoChannelActionDomain ∧
        fderiv ℂ (geoChannelAction a)
          (Complex.log (-geoX r) + Real.pi * Complex.I,
            Complex.log (1 / r) + Real.pi * Complex.I) (0, 1) = 0) ∧
    (∀ {S : ℂ × ℂ → ℂ} {Ω : Set (ℂ × ℂ)}, GeoChannelActionBranch S Ω →
      ∀ {ℓ : ℂ → ℂ × ℂ} {r : ℂ}, (r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧ r ^ 2 ≠ -1) →
      DifferentiableAt ℂ ℓ r → ℓ r ∈ Ω →
      (Complex.exp (ℓ r).1 = geoX r ∧ Complex.exp (ℓ r).2 = -1 / r) →
      fderiv ℂ S (ℓ r) (0, 1) = 0 →
      HasDerivAt (fun ρ ↦ S (ℓ ρ)) (fderiv ℂ S (ℓ r) (1, 0) * deriv (fun ρ ↦ (ℓ ρ).1) r) r ∧
        Complex.exp (fderiv ℂ S (ℓ r) (1, 0)) = geoL r) ∧
    (∀ {Ω : Set ℂ}, IsOpen Ω → IsPreconnected Ω → (∀ r ∈ Ω, r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1) →
      ∀ {lx lL s : ℂ → ℂ}, DifferentiableOn ℂ lx Ω → DifferentiableOn ℂ lL Ω →
      (∀ r ∈ Ω, Complex.exp (lx r) = geoX r) → (∀ r ∈ Ω, Complex.exp (lL r) = geoL r) →
      (∀ r ∈ Ω, HasDerivAt s (lL r * deriv lx r) r) →
      (∀ {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ}, HasDerivAt γ γ' t →
          (∀ᶠ τ in 𝓝 t, γ τ ∈ GeoSmoothTorusLocus ∧ geoCurveR (γ τ) ∈ Ω) →
          HasDerivAt (fun τ ↦ (s (geoCurveR (γ τ))).im -
              (lL (geoCurveR (γ τ))).im * (lx (geoCurveR (γ τ))).re)
            (-2 * geoEta (γ t).1 (γ t).2 γ'.1 γ'.2) t) ∧
        (∃ c : ℝ, ∀ r ∈ Ω, (s r).im - (lL r).im * (lx r).re + 2 * geoRegPrimitive r = c) ∧
        ((1 / 2 : ℂ) ∈ Ω → (s (1 / 2)).im - (lL (1 / 2)).im * (lx (1 / 2)).re = 0 →
          ∀ r ∈ Ω, (s r).im - (lL r).im * (lx r).re = -2 * geoRegPrimitive r)) ∧
    -- G-MAHLER (library)
    logMahlerMeasure₂ extraFactorℂ = 4 * catalanConstant / Real.pi ∧
    -- G-SHAPE
    (∀ z : Fin 4 → ℂ, WhiteheadGluing z → (whiteheadPeripheral z).1 = 1 →
      (whiteheadPeripheral z).2.1 = -1 → ∃ w : ℂ, w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 ∧ z = geoSliceShapes w) ∧
    -- G-VOL
    (∀ r : ℂ, r ≠ -1 → r ≠ 1 →
      ∑ j, blochWigner (geoSliceShapes ((1 - r) / (1 + r)) j) = -2 * geoRegPrimitive r) ∧
    ∑ j, blochWigner (geoSliceShapes Complex.I j) = 4 * catalanConstant ∧
    ∑ j, blochWigner (geoSliceShapes Complex.I j)⁻¹ = -(4 * catalanConstant) ∧
    (∀ z : Fin 4 → ℂ, WhiteheadGluing z → WhiteheadComplete z →
      |∑ j, blochWigner (z j)| = 4 * catalanConstant) ∧
    geoHypMeasure geoIdealTetI = ENNReal.ofReal catalanConstant ∧
    -- G-PHYS: from the actual knot to Zheng's diagonal, then the asymptotics (conditional)
    (∀ k : ℕ, 1 ≤ k → ∀ K : BraidKnot, K.strands = 4 * k + 3 → K.word = whiteheadTorusWord k →
      ∀ N : ℕ, 1 ≤ N → laurentToField (coloredJones K N) =
        quantumInt N * torusReducedFormula (2 * k + 1) N) ∧
    (∀ k N : ℕ, 1 ≤ k → 1 ≤ N →
      ∃ P : LaurentPolynomial ℤ, laurentToField P = torusReducedFormula (2 * k + 1) N) ∧
    (∀ (a N : ℕ) (P : LaurentPolynomial ℤ), 1 ≤ N → laurentToField P = torusReducedFormula a N →
      LaurentPolynomial.eval₂ (Int.castRingHom ℂ)
          (Units.mk0 (Complex.exp (Real.pi * Complex.I / (2 * N))) (Complex.exp_ne_zero _)) P =
        geoZhengDiagonal a N) ∧
    (∀ a N n : ℕ, 1 ≤ N →
      geoPhasePow N n (-(8 * a : ℝ)) = geoRootQ N ^ (-(2 * (a : ℤ) * n * (n + 1)))) ∧
    (∀ δ : ℝ, 1 / 2 < δ → δ < 1 →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N n i : ℕ, N₀ ≤ N → n + i < N → GeoInWindow N ((N : ℝ) ^ δ) n i →
        let q := geoRootQ N
        let zi := (1 - q ^ (i + 1)) / (1 - q ^ (n + i + 1))
        let zj := (1 - q ^ (N - n - i)) / (1 - q ^ (N - i))
        ‖q ^ n + 1‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧ ‖q ^ i - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖q ^ (N - 1 - n - i) - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖zi + Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧ ‖zj + Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖q ^ n * zi - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖q ^ n * zj - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1)) ∧
    (∀ a : ℕ, geoRatioQ a 1 1 (-1) (-Complex.I) = 1 ∧ geoRatioZ 1 1 (-1) (-Complex.I) = 1 ∧
      geoRatioX 1 1 (-1) (-Complex.I) = -1 ∧ geoChannelT 1 Complex.I = 0 ∧
      -2 * geoRegPrimitive (-Complex.I) = 4 * catalanConstant) ∧
    (∀ a : ℕ, 3 ≤ a → Odd a → ZhengEstimates a →
      (∀ N : ℕ, 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
        Tendsto (fun N : ℕ ↦ geoZhengDiagonal a N / geoZhengLeading a N) atTop (𝓝 1)) := by
  obtain ⟨h0, h1, h2, h3, h4, -, -, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18, h19,
    h20, h21, -, -, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ :=
    geo_theoremG
  refine ⟨fun k hk K hs hw N B hN hB ↦ ?_, h1, h2, h3, h4, h7, h8, h9, h10, h11, h12, h13, h14,
    h16, h17, h18, h19, h20, h21, h24, h25, h26, h27, h28, fun k hk K hs hw N hN ↦ ?_, h30, h31,
    h32, h33, h34, h35⟩
  · rw [eq_whiteheadTorusKnot_of_word hk hs hw]; exact h0 k hk N B hN hB
  · rw [eq_whiteheadTorusKnot_of_word hk hs hw]; exact h29 k hk N hN

open Classical in
/-- **The units of Theorem G not in `release_theoremG`**: the function-field isomorphism of `E`
with `Y² = X³ - X` and `[ℚ(E) : ℚ(r)] = 2` (G-CURVE), `{M, L} = 0` (G-K2) and the pattern
eigenvalue pairs of the completed slice (MARK), stated with the replacements `geoRfunR`,
`geoMerBar_ne_zeroR`, `geoLongBar_ne_zeroR`, `geoPatternShapeRepR` and the replacement instances
`IsDomain GeoCoordE`, `IsDomain GeoCoordEbar` of `Proofs/SolutionDefs.lean`, which differ
from the library's only in proof terms. -/
theorem release_theoremG_supplement :
    -- G-CURVE: the function fields
    (∃ e : GeoFunFieldE ≃+* geoWeierstrass.toAffine.FunctionField,
      e (algebraMap GeoCoordE GeoFunFieldE geoMer) *
          (-(algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX *
            (1 + algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX))) =
        algebraMap _ geoWeierstrass.toAffine.FunctionField geoWY ∧
      e (algebraMap GeoCoordE GeoFunFieldE geoLong) *
          (1 + algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX) ^ 2 =
        (1 - algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX) ^ 2 ∧
      e.symm (algebraMap _ _ geoWX) =
        -((algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 + algebraMap _ _ geoLong) /
          (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 *
            (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 - 1)))) ∧
    Module.finrank (IntermediateField.adjoin ℚ {geoRfunR}) GeoFunFieldE = 2 ∧
    -- G-K2
    geoSymbol (Units.mk0 geoMerBar geoMerBar_ne_zeroR) (Units.mk0 geoLongBar geoLongBar_ne_zeroR)
      ⊗ₜ[ℤ] (1 : ℚ) = 0 ∧
    -- MARK
    (∀ (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
        (hu : u ^ 2 = (1 + w) / (w * (1 - w))),
      GeoAxisCompleted (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) ∧
        GeoPatternEigenPair (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) (u, (w ^ 2)⁻¹) ∧
        GeoPatternEigenPair (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) (u⁻¹, w ^ 2)) ∧
    {p : ℂ × ℂ | ∃ (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
        (hu : u ^ 2 = (1 + w) / (w * (1 - w))),
        GeoPatternEigenPair (geoPatternShapeRepR w u hw0 hw1 hwm1 hu) p} =
      {p : ℂ × ℂ | evalPoint extraFactorℂ p = 0 ∧ p.1 ≠ 0} := by
  obtain ⟨-, -, -, -, -, h5, h6, -, -, -, -, -, -, -, -, h15, -, -, -, -, -, -, h22, h23, -⟩ :=
    geo_theoremG
  exact ⟨h5, h6, h15, h22, h23⟩

end

end AJConjecture
