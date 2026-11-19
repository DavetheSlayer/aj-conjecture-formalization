# The marked-knot bridge for the core AJ theorem

17 November 2026. Companion to `V1_SCOPE.md` and `WHITEHEAD_BRIDGE.md`. Scope: the untwisted
family only.

The core theorem is a kernel-checked statement about a closed braid: for every coprime
`2 ≤ r < s` the braid word `β_{r,s}` fails the weak AJ identity as the library defines it. This
document answers the question the handoff calls MARK, restricted to what the core theorem needs:

> Do the formal coloured Jones function and the formal A-polynomial belong to the same marked
> knot, in the conventions in which the AJ conjecture is stated, and is that knot the
> zero-framed negative-clasp Whitehead double `Z(T(r, s))`?

## 0. Answer

1. **Yes, and no gap was found.** Both formal invariants are the conventional invariants of one
   knot, the closure of the braid in which a letter `(i, true)` is a positive crossing, in the
   conventions of Lê's paper (the form of the conjecture that is refuted). The bridge from the
   Lean definitions to that statement consists of four standard facts (Section 7); everything else
   is proved in Lean or is a line-by-line reading of an eight-line definition.
2. **The chirality of the two sides agrees.** This is the one point where a silent error would
   matter, because the extra factor `E` is not symmetric under inverting `L` alone. It is checked
   in three independent ways (Section 4), including against the worked example in Lê's own paper.
3. **The refutation does not depend on that agreement.** New Lean theorem: the mirror image `E'` of
   the extra factor is also coprime to every A-polynomial of the family, so the weak AJ identity
   fails for these knots under either pairing of the chiralities of the two sides (Section 5).
   After this, the truth of "the weak AJ conjecture fails for the knot represented by `β_{r,s}`"
   no longer rests on any chirality or orientation convention.
4. **The knot is `Z(T(r, s))`.** Framing zero, negative clasp and right-handed companion are Lean
   theorems about the diagram; what remains external for the *name* of the knot is that the
   diagram moves are isotopies, and the reading of the diagram and of the sources' figures
   (Section 6).
5. **What the handoff unit MARK asks beyond this** (a homeomorphism of marked link exteriors, and
   the use of Tillmann's coordinates `(u, v⁻¹)`) concerns the geometric meaning of `E` in
   Theorem G. The core theorem does not use it: there `E` comes from the recurrence, not from
   geometry (Section 8).

## 1. What has to be identified

Fix a braid word `w` on `m` strands whose closure is connected, and let `K̂(w) ⊂ S³` be the closure
of the braid in which each letter `(i, true)` is a positive crossing of the strands in positions
`i, i + 1` and `(i, false)` a negative one. This is a well-defined unoriented knot type: reading
the word in the other direction, or numbering the positions from the other side, changes the
picture by a rotation of space (about a horizontal, respectively vertical, axis), which preserves
crossing signs. The only binary choice in reading a braid word is therefore the chirality.

The core theorem transfers to the conventional conjecture through four claims.

| | Claim | Lean object | Conventional object |
|---|---|---|---|
| J | the coloured Jones side | `coloredJones K` | Lê's coloured Jones function `J_{K̂}(n) ∈ ℤ[t^{±1}]`, `n ∈ ℤ` |
| G | the peripheral side | `(KnotGroup K, meridian K, longitude K)` | `(π₁(S³ ∖ K̂), μ, λ)`, `λ` the preferred longitude, up to simultaneous inversion of `(μ, λ)` and conjugation |
| A | the A-polynomial | `IsAPolynomialOf (eigenvalueSet K) A` | `A ≐ (L − 1) A_{K̂}` (Cooper–Culler–Gillet–Long–Shalen; Lê §3.2) |
| C | the conjecture | `AJSquareFree K` | implied by Lê's weak AJ conjecture for `K̂` |

Given J, G, A and C, `¬ AJSquareFree K` (a Lean theorem for `K = β_{r,s}`) gives: the weak AJ
conjecture, and with it every stronger form, fails for `K̂(β_{r,s})`. A fifth claim names the knot:

| | Claim | |
|---|---|---|
| N | `K̂(β_{r,s}) = Z(T(r, s))`, the zero-framed negative-clasp Whitehead double of the right-handed torus knot | Section 6 |

## 2. Claim J: the coloured Jones function

**Lê's definition** (math/0407521v4, §§1.1–1.3). The Kauffman bracket `⟨·⟩` of framed links in
`ℝ³` is defined by the skein relations with variable `t` (a crossing is `t` times its A-smoothing
plus `t⁻¹` times the other one, as his figure in §1.1 shows) and `⟨unknot⟩ = −t² − t⁻²`; for a
zero-framed knot `K`,

  `J_K(n + 1) := (−1)ⁿ ⟨S_n(K)⟩`,  `J_K(−n) := −J_K(n)`,  `J_K(0) := 0`,

where `S_n` is the Chebyshev polynomial (`S₀ = 1`, `S₁ = z`, `S_{n+1} = z S_n − S_{n−1}`) and `Kⁿ`
is `n` parallel copies. "The `(−1)ⁿ` sign is added so that when `K` is the trivial knot,
`J_K(n) = [n]`."

**The Lean definition**, read line by line (`KauffmanBracket.lean`, `ColoredJones.lean`):

* `crossingMatrix (i, true) = T·1 + T⁻¹·e_i`, `crossingMatrix (i, false) = T⁻¹·1 + T·e_i`, with
  `e_i` the cup–cap matrix (`e_i² = (−T² − T⁻²) e_i`). In the Kauffman bracket a crossing is
  `A·(A-smoothing) + A⁻¹·(B-smoothing)`, and for a positive crossing of two strands running in the
  braid direction the A-smoothing is the one that keeps the strands vertical. So `(i, true)` is
  the positive crossing with `A = T`.
* `bracket m w` is the weighted trace of the product, with weights `−T^{∓2}`: the state sum of the
  closed braid, each closed loop counting `−T² − T⁻²`.
* `cable c w` replaces each crossing by the `c²` crossings of the same sign of `c` parallel
  strands: `c` blackboard-parallel copies.
* `chebyshevBracket m w k = Σ_j (−1)^j C(k − j, j) ⟨D^{k−2j}⟩ = ⟨S_k(D)⟩`, `D` the diagram with
  its blackboard framing `w(D) = writhe`.
* `coloredJonesPos K k = (−1)^{k(1 + |w|)} T^{−w((k+1)² − 1)} ⟨S_k(D)⟩`. A positive kink
  multiplies `⟨S_k(·)⟩` by `(−1)^k T^{k² + 2k}`, so `⟨S_k(K₀)⟩ = ((−1)^k T^{k²+2k})^{−w} ⟨S_k(D)⟩`
  for the zero-framed knot `K₀`, and the Lean value is `(−1)^k ⟨S_k(K₀)⟩`: Lê's `J(k + 1)`.
* `coloredJones K n` extends it by `J(−n) = −J(n)`, `J(0) = 0`.

So `coloredJones K` is Lê's formula evaluated on the closed-braid diagram of `K̂(w)`, with `t = T`.

**External input X1.** The state sum of a closed braid diagram is the weighted trace of the
product of the matrices `A^{±1} + A^{∓1} e_i` (Kauffman's state model through the Temperley–Lieb
algebra; Kauffman 1987; Jones 1987; Kassel–Turaev, *Braid Groups*, Ch. 4). Expanding the product
gives the `2^n` states, and the weighted trace of a product of the `e_i` is
`(−A² − A⁻²)^{loops}`.

**Formal support.** The Lean function has the properties that characterise it: it is invariant
under the braid relations and under conjugation, and a stabilisation by `σ^{±1}` multiplies it
by the kink factor `−T^{±3}` (`bracket_cancel`, `bracket_farComm`, `bracket_braidRel`,
`bracket_append_comm`, `bracket_stabilize`), the unknot has `J(n) = [n]` (`coloredJones_unknot`), and at every colour the
cabled invariant is unchanged by all the diagram moves (`morseOp_eq_of_morseApplyAll`).

**Calibration against Lê's paper.** Lê §0.1.3 gives, for the right-handed trefoil, the recurrence
polynomial

  `P = (t⁴M¹⁰ − M⁶) L² − (t²M¹⁰ + t⁻¹⁸ − t⁻¹⁰M⁶ − t⁻¹⁴M⁴) L + (t⁻¹⁶ − t⁻⁴M⁴)`

and states that `P J_K = 0` with `J_K(0) = 0`, `J_K(1) = 1` determines `J_K`. Computing
`coloredJones` from the Lean definitions for the closure of `σ₀³` (letters `true`), with exact
arithmetic, for `|n| ≤ 5`: `P` annihilates it at every `n ∈ [−5, 3]`; `J(0) = 0`, `J(1) = 1`. Hence
the Lean values are Lê's `J_K(n)` of the right-handed trefoil for `|n| ≤ 5`. The same `P` does not
annihilate the mirror function `J(t⁻¹)` nor the sign-twisted function `(−1)^{n−1} J(n)`. So the
variable, the normalisation (including the sign, which would otherwise replace `L` by `−L`), the
framing correction and the chirality are Lê's. (`scripts/mark/trefoil_le_control.py`. The closed
formula printed in §0.1.3 carries a factor `(−1)^{n−1}` that is not compatible with the printed
`P` and initial values; the definition in §1.3 and `P` are what the Lean values match.)

## 3. Claim G: the peripheral system

**The Lean definition** (`KnotGroup.lean`). `artinHom m (i, true)` is the automorphism
`x_i ↦ x_i x_{i+1} x_i⁻¹`, `x_{i+1} ↦ x_i` of the free group, `(i, false)` its inverse; a word acts
by the composite `Φ(w)`; `artinWord` records `Φ(w)(x_k) = u_k x_{π(k)} u_k⁻¹`. The group is
`⟨x_0, …, x_{m−1} | x_k = Φ(w)(x_k)⟩`, the meridian is `x_0`, and the longitude is
`Λ · x_0^{−writhe}` with `Λ = u_0 u_{π(0)} ⋯ u_{π^{m−1}(0)}`, the conjugators met along the strand.

**External input X2 (Artin; Birman, *Braids, Links, and Mapping Class Groups*, Thm. 2.2).** Let
`β` be a braid on `m` strands, `D` a disc transverse to the strands with punctures `p_0, …, p_{m−1}`
and `x_k` the standard free generators of `π₁(D ∖ {p_k})`. The complement of the closed braid in
the solid torus has group `F_m ⋊ ⟨t⟩` with `t x_k t⁻¹ = β(x_k)` for the Artin action of `β`, and
filling in the braid axis kills `t`: `π₁(S³ ∖ β̂) = ⟨x_k | x_k = β(x_k)⟩`. The `x_k` are meridians.
If `β(x_k) = u_k x_{π(k)} u_k⁻¹`, then `u_k⁻¹ t` is the class of a path parallel to the strand from
position `k` to position `π(k)`; so `(u_{π^{m−1}(0)}⁻¹ t) ⋯ (u_0⁻¹ t)` is a parallel of the whole
knot, its image `Λ⁻¹` in the knot group is a longitude with some framing, and the preferred
longitude is the one that is null-homologous: `Λ^{±1} x_0^{∓e}` with `e` the exponent sum of `Λ`.

`Φ(w)` is the Artin action of one of the braids obtained from `w` by reversing the word and/or
inverting every letter. Reversal does not change the unoriented closure (Section 1). So X2 gives:
**`(KnotGroup K, meridian K, longitude K)` is the peripheral system of `K̂(w)` or of its mirror
image.** Which of the two is decided by the calibration of Section 4.

**Formal support (new, `PairKMarkCalib.lean`).** For every braid knot:

| Statement | Lean |
|---|---|
| The longitude commutes with the meridian | `commute_meridian_longitude` |
| The longitude is null-homologous: every homomorphism of the knot group to a commutative group sends it to `1` | `map_longitude_eq_one_of_commGroup` |
| The abelianisation sends the meridian to a generator of `ℤ` (so the meridian has infinite order, and the parallels `Λ x_0^j` are pairwise distinct) | `exists_hom_meridian_ofAdd_one` |

These are the algebraic properties that single out the preferred longitude among the parallels
`Λ x_0^j`.

## 4. The chirality of the two sides agrees

The danger: if `coloredJones` were the function of `K̂(w)` and the marked group that of its mirror
image, the formal statement would compare the recurrence of one knot with the A-polynomial of its
mirror. Passing to the mirror image replaces `(μ, λ)` by `(μ, λ⁻¹)`, hence `A(M, L)` by
`A(M, L⁻¹)`, and `E` is not invariant under `L ↦ L⁻¹`. Three independent checks, on the calibration
knot `σ₀³` and on the companion family:

1. **Reading the definitions** (Sections 2, 3): `(i, true)` is the positive crossing on the Jones
   side; on the group side the hand computation for `σ₀³` gives relators equivalent to
   `x_0 x_1 x_0 = x_1 x_0 x_1` and the longitude `x_0 x_1 x_0 x_1⁻¹ x_0 x_1 x_0⁻⁴ = z μ⁻⁶`, with
   `z = (x_0 x_1)³` central. In the standard marking the right-handed torus knot `T(p, q)` has
   `λ μ^{pq}` central (the cabling annulus has slope `+pq`), the left-handed one `λ μ^{−pq}`; both
   cannot hold, since `μ^{2pq}` is not central. (CCGLS, Prop. 2.7, gives `L = x^p M^{−pq}` and the
   factor `L M^{pq} + 1` for a torus knot without naming its handedness; the handedness here comes
   from the slope of the cabling annulus and from Lê's statement quoted in item 3.)
2. **Lean theorems** (`PairKMarkCalib.lean`, `PairKTorusGroup.lean`):

   | Statement | Lean |
   |---|---|
   | Jones side: the colour-2 value of the closure of `σ₀³` is `(T² + T⁻²)(T⁻⁴ + T⁻¹² − T⁻¹⁶)`, that is `[2] · V(T⁻⁴)` with `V(t) = t + t³ − t⁴`, the Jones polynomial of the right-handed trefoil | `coloredJones_two_trefoil` |
   | Group side, whole companion family: for the closure of the positive braid `(σ_0 ⋯ σ_{r−2})^s`, `λ μ^{rs} = Π^s` with `Π = x_0 ⋯ x_{r−1}`, and `Π^s` is central | `longitude_mul_meridian_pow_torusPairKnot`, `torusFullProd_pow_mem_center` |
   | Predicate side: every eigenvalue pair of the closure of `σ₀³` satisfies `L = 1` or `L M⁶ = −1` | `eigenvalueSet_trefoil_subset` |
   | and every point `(M, −M⁻⁶)`, `M ≠ 0`, is an eigenvalue pair (with the abelian line `(M, 1)`, `mem_eigenvalueSet_of_L_eq_one`) | `mem_eigenvalueSet_trefoil` |

   So the Lean A-polynomial of the calibration knot is `(L − 1)(L M⁶ + 1)`, the polynomial of the
   right-handed trefoil, not `(L − 1)(L + M⁶)`.

3. **Lê's worked example.** Lê states that for the right-handed trefoil
   `ε(α_K) = (M⁴ − 1)(L − 1)(L M⁶ + 1)`. His `P` annihilates the Lean coloured Jones function of
   `σ₀³` (Section 2), and its value at `t = −1` is `(M⁴ − 1)(L − 1)(L M⁶ + 1)`; the Lean marked
   group of `σ₀³` has eigenvalue pairs on `(L − 1)(L M⁶ + 1) = 0` (item 2). So for the calibration
   knot the two Lean sides satisfy the AJ identity exactly as in Lê's paper. If either side were
   mirrored, the comparison would be between `L M⁶ + 1` and `L + M⁶` and would fail.

Since both definitions treat every letter uniformly, agreement on one chiral knot is agreement for
every braid word: with X1 and X2, `coloredJones K = J_{K̂(w)}` and
`(KnotGroup K, meridian K, longitude K)` is the peripheral system of the same `K̂(w)`.

## 5. The refutation is independent of the chirality pairing

New Lean file `PairKMirrorRobust.lean` (standard axioms only). Let

  `E' = M⁴L² − (M⁴ − 4M² + 1) L + 1 = L² E(M, L⁻¹) = M⁴ E(M⁻¹, L)`,

the image of `E` under the mirror substitution.

| Statement | Lean |
|---|---|
| `E'` is the image of `E` under `L ↦ L⁻¹`, up to the unit `L²` | `toComparison_extraFactorMirror` |
| There is a zero of `E'` where `(L − 1) B_m ≠ 0`, for every `m ≥ 1` (`M² = 6`, `L = 1/4`: there `B_m < 0`) | `exists_extraFactorMirror_zero_not_famBound_zero` |
| `E'` is coprime to `(L − 1) B_m` in `ℚ(M)[L^{±1}]`, `m ≥ 1` | `isCoprime_extraFactorMirror_famBound` |
| `E'` is coprime to every A-polynomial of `β_{r,s}` | `isCoprime_extraFactorMirror_pair` |
| For every recurrence polynomial `α` and A-polynomial `A` of `β_{r,s}`: `rad(ε(α)) ≠ (A(M, L⁻¹))` | `not_ajSquareFree_mirror_pair` |

Together with the main theorem (`rad(ε(α)) ≠ (A(M, L))`), this covers both possibilities allowed
by X2. If the two sides were mirror to each other, the true comparison for `K̂` would be between
`ε(α)` and `A(M, L⁻¹)`, and the last line refutes it as well. So, granted only X1, X2 in the weak
form "the marked group is that of `K̂(w)` or of its mirror", X3 and X4, **the weak AJ conjecture
fails for the knot `K̂(β_{r,s})`**, with no appeal to Section 4. (The conjecture holds for a knot
if and only if it holds for its mirror image, so it also fails for the mirror.) A computer-algebra
check for `m ≤ 16` preceded the proof (`scripts/mark/robust_coprime.py`).

## 6. Claim N: the knot is `Z(T(r, s))`

The formal facts (all Lean theorems; details and names in `WHITEHEAD_BRIDGE.md`):

| | Fact | What it means in the conventional terms |
|---|---|---|
| a | The closed braid `β_{r,s}`, cut open, is carried by diagram moves to `whDouble C`, with `C` the closed positive braid `(σ_0 ⋯ σ_{r−2})^s` cut open | isotopic diagrams, once the moves are isotopies |
| b | `C` has one orientation and writhe `(r − 1)s`; the companion group satisfies `λ μ^{rs} = Π^s`, central | the companion is the right-handed `T(r, s)` |
| c | `whDouble D` = the blackboard double of `D`, then `w(D)` negative full twists, then the clasp; the two band edges, oriented in parallel, have linking number `0` (for braid companions with a unique labelling) | the band has framing `0`: the double is untwisted, by the definition of the framing as the linking number of the knot with its push-off |
| d | With the knot's orientation the two clasp crossings contribute `−2` to the writhe | the clasp is negative, by the definition of the clasp sign as the sign of its crossings (these are self-crossings, so the sign does not depend on the orientation) |
| e | `whDouble C` has one component, of writhe `2(r − 1)s − 2` | it is a knot |
| f | `whDouble` respects diagram moves | the construction is an operation on framed knot types |
| g | In the knot group: a homomorphism from the companion group with `μ_C ↦ a a₁⁻¹ a⁻¹ a₁`, `a₁ = ℓ⁻¹ a ℓ`, `ℓ` the image of `λ_C`, and `λ = a² ℓ a⁻¹ ℓ⁻¹ a a₁⁻¹ a⁻¹`; every companion representation with matrices satisfying these relations lifts | the zero-framed gluing `μ_C ↦ λ_axis`, `λ_C ↦ μ_axis` of the Whitehead pattern: no power of the axis meridian enters `ℓ` |
| h | The pattern group read off these relations is isomorphic to Tillmann's group of `W⁺` with pattern marking `(μ₁, λ₁⁻¹)` up to conjugation (`geo_pattern_tillmann`) | the pattern is the mirror of the positive-clasp pattern, in agreement with d |

Sign conventions enter only through "letter `true` = positive crossing", which Sections 2 and 4
establish.

External for the name of the knot:

* **X5.** Each diagram move (`zig`, `r2`, `r3`, `cupSlide`, `capSlide`, `kink`, `exch`) is an
  isotopy of framed long knots: planar isotopy, Reidemeister II and III, and the framed
  Reidemeister I move (the elementary direction of Reidemeister's theorem).
* **X6.** A diagram of the Whitehead double with clasp sign `±` and framing `f` of a knot with
  diagram `D` is: the blackboard double of `D`, `f − w(D)` full twists, and a clasp of sign `±`
  (the standard description; e.g. Rolfsen, *Knots and Links*, 4.D; Hedden 2007, §1). With c and d
  this identifies the closure of `whDouble C` as `Wh⁻(T(r, s), 0)`.
* **X7.** The sources' `Z(T(r, s))` is that knot: the G4 comparison reads two negative clasp
  crossings and zero framing in Zheng's diagram `WL(0)`, with right-handed companion
  (`G4_MARKED_PATTERN_THEOREM.md`, §§2, 5). A consistency check: Lean proves a closed formula
  for the coloured Jones function of `β_{r,s}` (`pairQ_laurentToField_coloredJones`), and that
  formula is the one the handoff derives on paper from Zheng's tangle formula for his double
  (unit T-JONES).

None of X5–X7 is needed for the truth of the refutation (Section 5); they are needed to call the
knot `Z(T(r, s))`.

## 7. Claims A and C, and the smallest bridge

**Claim A.** Lê §3.2: let `Ẑ ⊂ (ℂ*)²` be the set of pairs (upper-left entries of `ρ(μ)`, `ρ(λ)`)
over representations made upper triangular on the peripheral subgroup; its Zariski closure in `ℂ²`
has components of dimension `0` or `1`; the union of the one-dimensional components is defined by
`A'_K ∈ ℤ[M, L]` without repeated factors, and `A'_K = (L − 1) A_K`. The Lean `eigenvalueSet K` is
`Ẑ` for the Lean marked group, and `IsAPolynomialOf S A` says: `A` is squarefree over `ℂ`, and an
irreducible `g` divides `A` exactly when its zero curve lies in the Zariski closure of `S`.

*Lemma.* If the closure of `S` is a proper subset of `ℂ²` then `IsAPolynomialOf S A` holds exactly
when `A` is a nonzero constant multiple of `A'`. *Proof.* `S` is the image of an affine algebraic
set under a polynomial map, so its closure is a finite union of irreducible closed sets, of
dimension `≤ 1` by hypothesis. An irreducible curve contained in this union is contained in, hence
equal to, one of the one-dimensional pieces; conversely each such piece is the zero curve of an
irreducible polynomial. So the irreducible factors of `A` are exactly those of `A'`, each once. ∎
For the family the hypothesis is the Lean theorem that `S` lies in `(L − 1) B_{rs} = 0`.
**External input X3**: the definition of the A-polynomial (CCGLS §§2.2–2.3; Lê §3.2).

**Claim C.** Lê §§0.1.2–0.2: `(Mf)(n) = t^{2n} f(n)`, `(Lf)(n) = f(n + 1)`, `LM = t²ML`; the
recurrence ideal is the annihilator of `J_K : ℤ → ℂ[t^{±1}]`; after inverting the polynomials in
`M` it is principal, generated by `α_K = Σ α_{K,i}(t, M) Lⁱ` of minimal `L`-degree with coprime
coefficients in `ℤ[t^{±1}, M]`; `ε` puts `t = −1`. Conjecture 1 (strong): `ε(α_K)` and
`(L − 1) A_K` are equal up to a factor in `M`. Weak version: their zero sets are equal up to lines
`M = const`. The Lean `opApply`, `Annihilates` (all `n ∈ ℤ`), `InLocalizedAnnihilator`,
`IsRecurrencePolynomial` (nonzero, minimal `L`-degree, primitive) and `specialize` (`t ↦ −1`) are
these notions; a Lean recurrence polynomial is Lê's `α_K` up to `± t^a M^b`. Equality of zero sets
up to vertical lines gives equality of radicals in `ℚ(M)[L^{±1}]`, which is `AJSquareFree`. So
Lê's weak conjecture for `K̂` implies `AJSquareFree K`, and `¬ AJSquareFree K` refutes the weak
and the strong conjecture. **External input X4**: the statement of the conjecture (Lê 2006,
Conjecture 1 and the paragraph after it; Garoufalidis 2004).

**The smallest bridge.** Everything outside Lean that the conventional reading of the core theorem
uses:

| | External fact | Used for | Status |
|---|---|---|---|
| X1 | Kauffman's state sum of a closed braid is the Temperley–Lieb trace | J | textbook; finite combinatorial identity |
| X2 | Artin's presentation of the group of a closed braid, with its meridians and parallels | G | textbook (Birman, Thm. 2.2) |
| X3 | Definition of the A-polynomial; the lemma above | A | definition + three-line lemma |
| X4 | Statement of the AJ conjecture in Lê's form | C | definition |
| — | Chirality agreement of X1 and X2 | J with G | **not needed** after Section 5; established anyway in Section 4 |
| X5 | Diagram moves are isotopies | N | textbook |
| X6 | Standard diagram of a Whitehead double | N | definition |
| X7 | The sources' `Z(T(r, s))` is `Wh⁻(T(r, s), 0)` | N | reading of published figures (G4) |

X1–X4 are what the statement "the weak AJ conjecture fails for the knot `K̂(β_{r,s})`" rests on.
X5–X7 are what the name `Z(T(r, s))` rests on. No step is conditional on an unproved mathematical
claim. Each of X1, X2, X5 could be formalised only with a formal notion of knots in `S³` and their
diagrams, which neither Mathlib nor (as checked on 17 November) the Tau Ceti library connects to
braids.

## 8. What the unit MARK asks beyond the core theorem

The handoff's MARK contract is about the geometric side: an orientation-reversing homeomorphism
between Schilder's and Zheng's marked pattern exteriors, the identification of the pattern exterior
with Tillmann's triangulated `W⁺`, and the resulting rule `(M, L) = (u, v⁻¹)` for reading `E` as
the eigenvalue curve of the Whitehead link exterior with the axis cusp complete. Its acceptance
clause asks to "prove the homeomorphism, labelled torus maps and collar gluing before using
`(u, v⁻¹)`".

* The core theorem never uses `(u, v⁻¹)`. There `E` is a factor of the classical limit of every
  recurrence, proved from the coloured Jones function; the classical side is the bound
  `(L − 1) B_{rs}` proved from the knot group.
* For Theorem G the formal content is at the group level and is derived from the braid, not from
  a comparison of figures: fact h above, and the statement that the eigenvalue pairs of the
  pattern group over the completed axis chart are exactly `E ∩ {M ≠ 0}` (`geo_shape_marking`,
  `geo_shape_marking_image`, clauses of `geo_theoremG`). So the rule
  `(M, L) = (u, v⁻¹)` is a Lean theorem about the marked group that the knot group contains.
* Still external there: that the pattern group with its two peripheral pairs is the group of the
  pattern exterior (this follows from N), and that Tillmann's presentation is that of the
  triangulated `W⁺` (Tillmann's thesis; the G4 argument realises the word isomorphism by a
  homeomorphism through Waldhausen's theorem). The homeomorphism itself is not formalised and is
  not needed for any formal statement.

## 9. Reproduction

* Lean (in `lean/Proofs/`): `AJHandoff/TorusKnot/PairKMirrorRobust.lean`,
  `AJHandoff/TorusKnot/PairKMarkCalib.lean` (`lake env lean <file>`; axioms in
  `lean/checks/PrintAxiomsV1.lean`).
* `scripts/mark/lean_defs.py`: the Lean definitions of both invariants transcribed line by line
  (exact Laurent-polynomial and free-group arithmetic); prints the unknot values, the bracket, the
  colour-2 value, the relators and the longitude word of `σ₀³`.
* `scripts/mark/trefoil_le_control.py`: Lê's `P` against the Lean values, with the mirrored and
  sign-twisted controls, and `ε(P)`.
* `scripts/mark/robust_coprime.py`, `mirror_point.py`: coprimality of `E` and `E'` with
  `(L − 1) B_m` for `m ≤ 16`; the witness point.
* `scripts/mark/independent/`: the scripts of the independent check of Section 10 (each takes the
  directory of `leandefs.py` as its first argument).

## 10. Independent check

A separate audit, given only the definitions and the question (not the conclusions above),
reached the same answers by other routes (`scripts/mark/independent/`):

* **Jones side.** The Lean crossing matrices satisfy `T·X(true) − T⁻¹·X(false) = (T² − T⁻²)·1`,
  the Jones skein relation with `t_Jones = T⁻⁴` and `true` as the positive crossing; the matrix
  definition agrees with an independent loop-counting state sum on 16 words; the unknot and its
  stabilisations give `[n]`; the closure of `[(0, true)]³` equals Lê's right-handed trefoil formula
  for `n ≤ 6` (without the misprinted sign), and `[(0, false)]³` equals the Knot Atlas values for
  its `3_1` (braid `σ₁⁻³`); a figure-eight braid equals `[n]` times Habiro's formula for `n ≤ 4`;
  a `5_2` braid has the Jones polynomial of the positive `5_2`.
* **Peripheral side.** For every word tested the longitude commutes with the meridian and has
  exponent sum zero; for `[(0, true)]³` it is `(x_0 x_1)³ x_0⁻⁶`, the eigenvalue relations are
  `L = 1` and `L M⁶ + 1 = 0`; `[(0, false)]³` gives `L + M⁶`, `[(0, true)]⁵` gives `L M¹⁰ + 1`; for
  the `5_2` braid a numerical fit gives a cubic in `L` with boundary slopes `+4` and `+10`, those
  of the positive `5_2`, and the mirror word gives the polynomial with `L` inverted.
* **End to end.** `α = t¹⁸ P` is primitive, annihilates the Lean values for `n ∈ [−5, 3]` and the
  closed formula for `|n| ≤ 30`; no operator of order one with `M`-degree `≤ 30` does; at `t = −1`
  it is `(M⁴ − 1)(L − 1)(L M⁶ + 1)`, whose radical is the ideal of the A-polynomial computed from
  the Lean group. With one side mirrored the specialisation would be `(M⁴ − 1)(L − 1)(L + M⁶)`
  and the identity would fail.
* **Definitions.** `IsRecurrencePolynomial` is Lê's `α_K` (fixed up to `±1` instead of
  `± t^a M^b`); `IsAPolynomialOf (eigenvalueSet K)` is Lê's `A'_K = (L − 1) A_K` up to units of the
  comparison ring; `AJSquareFree` is implied by Lê's weak conjecture.

Two cautions from that audit. Published A-polynomial tables are not a reliable source for
chirality: the Knot Atlas lists the polynomial found here for the positive `5_2` next to the
mirror braid and says its orientation was not checked; the calibration above therefore uses the
torus knot, where the handedness follows from first principles and from Lê's text. And the
peripheral recipe was tested on eight words there, not proved in general; in general it is X2
together with the Lean theorems of Section 3.

