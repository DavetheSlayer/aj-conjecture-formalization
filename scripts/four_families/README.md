# Checks outside Lean for the four families

Independent computations that compare the closed braids of the four-family theorem
([`docs/FOUR_FAMILIES.md`](../../docs/FOUR_FAMILIES.md)) with the manuscript of the handoff of 18 November
2026. They were written from scratch for the audit of 19 November 2026 and share no code with the
Lean development. Their only input from Lean is `lean_words.txt`, the braid words printed by
`lean/tools/TwWords.lean`:

    cd lean && lake env lean tools/TwWords.lean > ../scripts/four_families/lean_words.txt

| Script | Needs | What it checks | Recorded output |
|---|---|---|---|
| `tw_audit_small.py` | numpy | calibration: the bracket of the trefoil and the figure-eight braid; colour 3 of the torus braids against the manuscript's `Φ_{T_+}`; the printed inverse words are the inverses; the word of Theorem T is the word at `ℓ = 0`, negative clasp | `tw_audit_small.out` |
| `tw_audit_alexander.py` | — | for `(r, s) ∈ {(2,3), (2,5), (3,4), (3,5)}`, `-3 ≤ ℓ ≤ 3`, both clasp signs (56 braids): one component, the writhe of the Lean lemma, and Alexander polynomial `d·t² + (1 - 2d)·t + d` with `d = ℓ` (negative clasp), `d = -ℓ` (positive clasp), by the Burau representation in exact arithmetic | `tw_audit_alexander.out` |
| `tw_audit_jones.py` | numpy | the colour-2 value of the Lean coloured Jones function, recomputed from its definition modulo a prime at two points, equals the manuscript's finite-sum formula for 36 knots `twFamilyKnot r s h σ η ℓ`; each matches exactly one of 36 candidate triples (clasp, companion, twist), the expected one | `tw_audit_jones.out` |
| `tw_audit_polys.py` | sympy | `twistPoly k = B_k` and `twistPolyNeg k = C_k` of the manuscript for `k ≤ 6`; `extraFactorMirror = M⁴E(M⁻¹, L)`; the `L`-reversed bound and the bound transported by `M ↦ M⁻¹` differ by a monomial | `tw_audit_polys.out` |

`tw_audit_lib.py` holds the shared routines (parsing, the Kauffman bracket of a closed braid on
weight spaces, cabling, the manuscript's formula modulo a prime). Run each script with
`python3 <script>` from any directory; `tw_audit_jones.py` takes about a minute and a half.

These are evidence that the braids are the knots the manuscript names; they are not proofs. Not
checked: the topology itself; the coloured Jones function of the doubles beyond colour 2 (the
Lean theorem `release_fourFamilies_coloredJones` proves the formula of the Lean development at
every colour); the colour-2 comparison for companions other than `T(2, 3)` and `T(2, 5)` (it uses
braids on at most 15 strands; the Alexander check goes up to 31 strands).
