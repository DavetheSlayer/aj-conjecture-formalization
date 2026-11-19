import Mathlib
import AJHandoff.TorusKnot.PairKRevSolveLoop
import AJHandoff.TorusKnot.PairKRevGapConv

/-!
# The edge meridians along the annulus path: definitions

Notation: `c = (r - 1)s`, `b₀ = 2c - s - r` (`pairIdxB`), `E = (r - 2)(s - 1) + 1`
(`pairRunDown`), `z = c - r - 1` (`pairRunUp`), the top levels `T_t = 2c - 1 - t`
(`0 ≤ t ≤ s + r - 2`, i.e. the levels `b₀ + 1, …, 2c - 1`). For a tuple `y` put
`P(n) = y_0 y_1 ⋯ y_(n-1)` (indices mod `r`, `pairRevCyc`), `Π = P(r)` (`pairAnnPi`) and the
Hurwitz sequence `R'_p = P(p + 1) P(p)⁻¹` (`pairAnnHur`). Under the torus relation `R'` is
`s`-periodic, `R'_(p+r) = Π R'_p Π⁻¹`, `Π^s` commutes with `y_0`, hence
`R'_p = Π^w y_0 Π^(-w)` whenever `w r ≡ p (mod s)` (`AJHandoff.TorusKnot.PairKAnnHurwitz`).

**The annulus path.** The annulus bands of `pairBlocks r s` form one cycle through the levels
`0, …, 2c - 1`; without the top-right climb `C` they form a path from `T_0` to `T_s`. In top
coordinates the rounds `R_τ = b(T_(r+τ), T_τ)` join the levels of a *chain* `ρ, ρ + r, ρ + 2r, …`
(`ρ < r`), which ends at some `t₁ ∈ [s - 1, s + r - 2]`; the chain is continued, through a bottom
level (`D'`, then `A`, for `t₁ ≥ s + 1`), through the runs (`R_(s-1)`, the decreasing and the
increasing run, then `B`, for `t₁ = s - 1`), or through `C` (`t₁ = s`), by the chain starting at
`(t₁ - s) mod r`. So the chains are visited in the order `ρ_i = (-i s) mod r`; the chain of the
top coordinate `t` has index `i(t)` (`pairAnnIdx`: `i(t) < r`, `r ∣ t + i(t) s`) and the number
of round steps from `T_0` to `T_t` telescopes to the height `h(t) = (t + i(t) s) / r`
(`pairAnnHt`).

**Closed forms.** Every edge meridian is `F(w, k, l) = Π^w y_0^k a (Π^w y_0^l)⁻¹`
(`pairAnnForm`) with integer labels: along a chain step `T_τ → T_(τ+r)` the exponent `w` grows by
one and `k, l` drop by one; a bottom connection keeps `w` and lowers `k, l` by one; the run
connection raises `w` by one and lowers `k, l` by `z + 3`. With base-free labels on the top level
`T_t` (`pairAnnTopW`, `pairAnnTopL`)
`w = h(t)`, `l = -h(t) - i(t) - (z + 1)[i(t) ≥ i(r - 1)]`, `k = l - 1` (`k = l` at `T_0`),
and on the other levels
* bottom level `n < r - 2` (between `T_(s+1+n)` and `T_(n+1)`): the labels of `T_(n+1)` with
  `k = l`;
* lower run `r - 2 ≤ n ≤ r + E - 3`: `w = h(r - 1)`, `k = l = l(T_(s-1)) - 2`;
* upper run `r + E - 2 ≤ n ≤ b₀`: `w = h(r - 1)`, `l = l(T_(r-1)) + (b₀ - n) + 1`, `k = l - 1`,
the edge meridians are `e_n = F(W_n - W_0, K_n - K_0, L_n - K_0)` (`pairAnnEdge`), normalised so
that `e_0 = a`. Every annulus band equation is then a *local* identity between the labels of its
two ends (`AJHandoff.TorusKnot.PairKAnnClosedLow`, `…ClosedTop`), and the two path ends are
`e(T_s) = U a y_0⁻¹ U⁻¹`, `e(T_0) = U Λ⁻¹ a Λ U⁻¹` with `U = Π^(W(T_s) - W_0) y_0^(K(T_s) - K_0)`
(`pairAnnU`, `AJHandoff.TorusKnot.PairKAnnEnds`); the second identity is the label identity
`z = c - r - 1`.

All closed forms were checked exactly in the free product of the torus knot group
`⟨u, v | u^r = v^s⟩` with `ℤ = ⟨a⟩` (amalgam normal forms; `R'_p = v^(Ap) v^A u^(-B) v^(-Ap)`,
`Π = v`, `Ar - Bs = 1`) against the edge meridians obtained by solving the band equations along a
spanning tree, for `(r, s) ∈ {(2,3), (2,5), (2,7), (3,4), (3,5), (3,7), (3,8), (4,5), (4,7),
(4,9), (5,6), (5,7), (5,8), (6,7), (7,9)}` (`SCR/ANN/check_closed.py`; the transitions and gap
tables in `SCR/ANN/validate.py`); the label and block-position statements are checked below with
`#guard`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Labels -/

/-- The chain index `i(t) < r` of the top coordinate `t`: the least `i < r` with
`r ∣ t + i s`. -/
def pairAnnIdx (r s t : ℕ) : ℕ :=
  ((List.range r).find? fun i ↦ (t + i * s) % r == 0).getD 0

/-- The height `h(t) = (t + i(t) s) / r`: the number of round steps from `T_0` to `T_t`. -/
def pairAnnHt (r s t : ℕ) : ℕ := (t + pairAnnIdx r s t * s) / r

/-- The base-free `Π`-exponent `h(t)` of the top level `T_t`. -/
def pairAnnTopW (r s t : ℕ) : ℤ := pairAnnHt r s t

/-- The base-free right `y_0`-exponent of the top level `T_t`:
`-h(t) - i(t) - (z + 1)[i(t) ≥ i(r - 1)]` (the run connection lies just before the chain of
index `i(r - 1)`). -/
def pairAnnTopL (r s t : ℕ) : ℤ :=
  -(pairAnnHt r s t : ℤ) - pairAnnIdx r s t -
    if pairAnnIdx r s (r - 1) ≤ pairAnnIdx r s t then (pairRunUp r s : ℤ) + 1 else 0

/-- The base-free `Π`-exponent of the level `n < 2c`. -/
def pairAnnW (r s n : ℕ) : ℤ :=
  if n < r - 2 then pairAnnTopW r s (n + 1)
  else if n ≤ pairIdxB r s then pairAnnTopW r s (r - 1)
  else pairAnnTopW r s (2 * pairC r s - 1 - n)

/-- The base-free right `y_0`-exponent of the level `n < 2c`. -/
def pairAnnLam (r s n : ℕ) : ℤ :=
  if n < r - 2 then pairAnnTopL r s (n + 1)
  else if n ≤ r + pairRunDown r s - 3 then pairAnnTopL r s (s - 1) - 2
  else if n ≤ pairIdxB r s then
    pairAnnTopL r s (r - 1) + ((pairIdxB r s - n : ℕ) : ℤ) + 1
  else pairAnnTopL r s (2 * pairC r s - 1 - n)

/-- The defect `l - k ∈ {0, 1}` of the level `n`: `0` on the bottom levels, the lower run and
`T_0`, `1` elsewhere. -/
def pairAnnEps (r s n : ℕ) : ℤ :=
  if n ≤ r + pairRunDown r s - 3 ∨ n = 2 * pairC r s - 1 then 0 else 1

/-- The base-free left `y_0`-exponent `k = l - ε` of the level `n`. -/
def pairAnnKap (r s n : ℕ) : ℤ := pairAnnLam r s n - pairAnnEps r s n

/-! ### The group elements -/

/-- The image `Λ = (y_0 ⋯ y_(r-1))^s y_0^(-rs)` of the longitude of `T(r, s)` (moved here from
`AJHandoff.TorusKnot.PairKRevSolveAnnulus`, unchanged). -/
def pairRevLam (r s : ℕ) (y : ℕ → G) : G :=
  ((List.range r).map y).prod ^ s * y 0 ^ (-((r * s : ℕ) : ℤ))

/-- `Π = y_0 y_1 ⋯ y_(r-1)`. -/
def pairAnnPi (r : ℕ) (y : ℕ → G) : G := pairRevCyc r y r

/-- The Hurwitz sequence `R'_p = P(p + 1) P(p)⁻¹ = P(p) y_(p mod r) P(p)⁻¹` of the cyclic
products `P = pairRevCyc r y`. -/
def pairAnnHur (r : ℕ) (y : ℕ → G) (p : ℕ) : G :=
  pairRevCyc r y (p + 1) * (pairRevCyc r y p)⁻¹

/-- The closed form `F(w, k, l) = Π^w y^k a (Π^w y^l)⁻¹` of an edge meridian. -/
def pairAnnForm (P y a : G) (w k l : ℤ) : G := P ^ w * y ^ k * a * (P ^ w * y ^ l)⁻¹

/-- The edge meridians along the annulus path, normalised by `e_0 = a`. -/
def pairAnnEdge (r s : ℕ) (y : ℕ → G) (a : G) (n : ℕ) : G :=
  pairAnnForm (pairAnnPi r y) (y 0) a (pairAnnW r s n - pairAnnW r s 0)
    (pairAnnKap r s n - pairAnnKap r s 0) (pairAnnLam r s n - pairAnnKap r s 0)

/-- The conjugator `U = Π^(W(T_s) - W_0) y_0^(K(T_s) - K_0)` of the end `T_s` of the path. -/
def pairAnnU (r s : ℕ) (y : ℕ → G) : G :=
  pairAnnPi r y ^ (pairAnnW r s (2 * pairC r s - 1 - s) - pairAnnW r s 0) *
    y 0 ^ (pairAnnKap r s (2 * pairC r s - 1 - s) - pairAnnKap r s 0)

/-- The loop equation of the block at position `q` of `pairBlocks r s` for the prescribed loops
`pairRevLoop r s y H` and edge meridians `e` (the body of `exists_pairRevEdge_annulus`). -/
def PairAnnEq (r s : ℕ) (y : ℕ → G) (H : G) (e : ℕ → G) (q : ℕ) : Prop :=
  pairRevLoop r s y H q = loopPr ((pairBlocks r s).getD q (SBlock.neg 0))
    (fun n ↦ gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s y H) n * descProd e 0 n)

/-! ### The labels by regime -/

section Regimes

variable {r s : ℕ}

/-- The arithmetic of an admissible pair, with `b₀ = r - 2 + E + z`. -/
theorem pairAnn_arith (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 ∧
      pairIdxB r s = r - 2 + pairRunDown r s + pairRunUp r s ∧ 1 ≤ pairRunDown r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hE1 : 1 ≤ pairRunDown r s := by unfold pairRunDown; omega
  refine ⟨hr, hrs, hc, hE, ?_, hE1⟩
  simp only [pairIdxB, pairRunUp]
  omega

/-- The labels of a bottom level `n < r - 2`: those of `T_(n+1)` with `k = l`. -/
theorem pairAnn_lab_bot (h : IsTorusPair r s) {n : ℕ} (hn : n < r - 2) :
    pairAnnW r s n = pairAnnTopW r s (n + 1) ∧ pairAnnLam r s n = pairAnnTopL r s (n + 1) ∧
      pairAnnEps r s n = 0 := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  refine ⟨ite_eq_left hn, ite_eq_left hn, ite_eq_left (Or.inl (by omega))⟩

/-- The labels of a level of the lower run `r - 2 ≤ n ≤ r + E - 3`. -/
theorem pairAnn_lab_low (h : IsTorusPair r s) {n : ℕ} (h1 : r - 2 ≤ n)
    (h2 : n ≤ r + pairRunDown r s - 3) :
    pairAnnW r s n = pairAnnTopW r s (r - 1) ∧
      pairAnnLam r s n = pairAnnTopL r s (s - 1) - 2 ∧ pairAnnEps r s n = 0 := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  refine ⟨?_, ?_, ite_eq_left (Or.inl h2)⟩
  · rw [pairAnnW, ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [pairAnnLam, ite_eq_right (by omega), ite_eq_left h2]

/-- The labels of a level of the upper run `r + E - 2 ≤ n ≤ b₀`. -/
theorem pairAnn_lab_up (h : IsTorusPair r s) {n : ℕ} (h1 : r + pairRunDown r s - 3 < n)
    (h2 : n ≤ pairIdxB r s) :
    pairAnnW r s n = pairAnnTopW r s (r - 1) ∧
      pairAnnLam r s n = pairAnnTopL r s (r - 1) + ((pairIdxB r s - n : ℕ) : ℤ) + 1 ∧
      pairAnnEps r s n = 1 := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  refine ⟨?_, ?_, ?_⟩
  · rw [pairAnnW, ite_eq_right (by omega), ite_eq_left h2]
  · rw [pairAnnLam, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
  · rw [pairAnnEps, ite_eq_right (by omega)]

/-- The labels of the top level `T_t = 2c - 1 - t`, `t ≤ s + r - 2`. -/
theorem pairAnn_lab_top (h : IsTorusPair r s) {t : ℕ} (ht : t ≤ s + r - 2) :
    pairAnnW r s (2 * pairC r s - 1 - t) = pairAnnTopW r s t ∧
      pairAnnLam r s (2 * pairC r s - 1 - t) = pairAnnTopL r s t ∧
      pairAnnEps r s (2 * pairC r s - 1 - t) = if t = 0 then 0 else 1 := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have ht' : 2 * pairC r s - 1 - (2 * pairC r s - 1 - t) = t := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [pairAnnW, ite_eq_right (by omega), ite_eq_right (by omega), ht']
  · rw [pairAnnLam, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ht']
  · by_cases h0 : t = 0
    · rw [pairAnnEps, ite_eq_left (Or.inr (by omega)), ite_eq_left h0]
    · rw [pairAnnEps, ite_eq_right (by omega), ite_eq_right h0]

/-- The `Π`-exponent of the level `0` is that of `T_1`. -/
theorem pairAnnW_zero (h : IsTorusPair r s) : pairAnnW r s 0 = pairAnnTopW r s 1 := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  rcases Nat.lt_or_ge 0 (r - 2) with h0 | h0
  · rw [pairAnnW, ite_eq_left h0]
  · rw [pairAnnW, ite_eq_right (by omega), ite_eq_left (Nat.zero_le _), show r - 1 = 1 by omega]

/-- The level `0` has defect `0`. -/
theorem pairAnnEps_zero (h : IsTorusPair r s) : pairAnnEps r s 0 = 0 := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  exact ite_eq_left (Or.inl (by omega))

/-- The normalisation `e_0 = a`. -/
theorem pairAnnEdge_zero (h : IsTorusPair r s) (y : ℕ → G) (a : G) :
    pairAnnEdge r s y a 0 = a := by
  have h0 : pairAnnLam r s 0 - pairAnnKap r s 0 = 0 := by
    rw [pairAnnKap, pairAnnEps_zero h, sub_zero, sub_self]
  rw [pairAnnEdge, h0, sub_self, sub_self, pairAnnForm]
  simp

end Regimes

/-! ### Checks -/

section Checks

/-- The positions `q' < q` (in decreasing order) whose block gap contains the level `n`: the
factors of `gapPrefix ((pairBlocks r s).take q) L n`. -/
def pairAnnGapPos (r s q n : ℕ) : List ℕ :=
  (List.range q).reverse.filter fun q' ↦
    decide ((pairBlkRv r s q').lo ≤ n ∧ n ≤ (pairBlkRv r s q').hi)

/-- The positions `q' ≥ q` (in decreasing order) whose block gap contains the level `n`. -/
def pairAnnSufPos (r s q n : ℕ) : List ℕ :=
  ((List.range (2 * pairC r s + 2)).reverse.filter fun q' ↦ q ≤ q').filter fun q' ↦
    decide ((pairBlkRv r s q').lo ≤ n ∧ n ≤ (pairBlkRv r s q').hi)

/-- The positions `a + n - 1, …, a` of a descending product. -/
def pairAnnDescPos (a n : ℕ) : List ℕ := ((List.range n).reverse.map fun i ↦ a + i)

/-- The label identities of `AJHandoff.TorusKnot.PairKAnnArith`. -/
def pairAnnCheckLab (r s : ℕ) : Bool :=
  let z : ℤ := pairRunUp r s
  ((List.range (s + 3 * r)).all fun t ↦
    decide (pairAnnIdx r s t < r) && (t + pairAnnIdx r s t * s) % r == 0 &&
      pairAnnIdx r s (t + r) == pairAnnIdx r s t &&
      pairAnnHt r s (t + r) == pairAnnHt r s t + 1 &&
      ((pairAnnTopW r s t - pairAnnTopW r s 1) * r - ((t : ℤ) - 1)) % s == 0) &&
  ((List.range (r - 2)).all fun k ↦
    pairAnnHt r s (s + 1 + k) == pairAnnHt r s (k + 1) &&
      pairAnnTopL r s (s + 1 + k) == pairAnnTopL r s (k + 1) + 1) &&
  pairAnnHt r s (r - 1) == pairAnnHt r s (s - 1) + 1 &&
  pairAnnTopL r s (r - 1) == pairAnnTopL r s (s - 1) - z - 3 &&
  pairAnnHt r s 0 == 0 && pairAnnTopL r s 0 == 0 && pairAnnHt r s r == 1 &&
  pairAnnTopL r s r == -1 && pairAnnHt r s s == s &&
  pairAnnTopL r s s + ((r * s : ℕ) : ℤ) == 1

/-- The block-position statements of `AJHandoff.TorusKnot.PairKAnnGapLow` and `…GapSuf`. -/
def pairAnnCheckGap (r s : ℕ) : Bool :=
  let c := pairC r s
  let b := pairIdxB r s
  let A := pairAnnDescPos 0 (r - 2)
  -- `pairAnnGap_A`
  ((List.range (r - 1)).all fun q ↦ (List.range (2 * c)).all fun n ↦
    !(q ≤ n && n ≤ 2 * c - 1 - q) || pairAnnGapPos r s q n == pairAnnDescPos 0 q) &&
  -- `pairAnnGap_bot`
  ((List.range (r - 1)).all fun m ↦ (List.range (b + s + 2 + r - m)).all fun q ↦
    pairAnnGapPos r s q m == pairAnnDescPos 0 (min q m)) &&
  -- `pairAnnGap_run`
  ((List.range (b + 1)).all fun q ↦ (List.range (2 * c + 2 - r)).all fun m ↦
    !(r - 2 ≤ q && r - 2 ≤ m && (!(r - 1 ≤ m && m ≤ b) || q ≤ pairIdxRun r s m)) ||
      pairAnnGapPos r s q m == A) &&
  -- `pairAnnGap_runHit`
  ((List.range (b + 1)).all fun m ↦ (List.range (b + s + 2)).all fun q ↦
    !(r - 1 ≤ m && pairIdxRun r s m < q) ||
      pairAnnGapPos r s q m == pairIdxRun r s m :: A) &&
  -- `pairAnnGap_BA`
  ((List.range (s + r - 1)).all fun t ↦ (List.range (2 * c + 2)).all fun q ↦
    !(r - 1 ≤ t && b < q && q ≤ pairIdxR r s (t + 1 - r)) ||
      pairAnnGapPos r s q (2 * c - 1 - t) == b :: A) &&
  -- `pairAnnGap_top0`
  pairAnnGapPos r s (b + 1) (2 * c - 1) == [] && pairAnnGapPos r s (b + 1) (2 * c) == [] &&
  -- `pairAnnGap_sufR`
  ((List.range s).all fun τ ↦ τ == 0 ||
    pairAnnSufPos r s (pairIdxR r s τ) (2 * c - 1 - τ) == [pairIdxC r s, pairIdxR r s τ] &&
      pairAnnSufPos r s (pairIdxR r s τ) (2 * c - τ) == [pairIdxC r s]) &&
  -- `pairAnnGap_sufD`
  ((List.range (r - 2)).all fun j ↦
    pairAnnSufPos r s (pairIdxDp r s j) (b + 1 + j) ==
        pairAnnDescPos (pairIdxDp r s j) (r - 2 - j) &&
      pairAnnSufPos r s (pairIdxDp r s j) (b + 2 + j) ==
        pairAnnDescPos (pairIdxDp r s j + 1) (r - 3 - j))

#guard [(2, 3), (2, 5), (2, 7), (3, 4), (3, 5), (3, 7), (3, 8), (4, 5), (4, 7), (5, 6),
  (5, 7), (4, 9), (5, 8), (6, 7), (7, 9)].all fun p ↦ pairAnnCheckLab p.1 p.2

#guard [(2, 3), (2, 5), (3, 4), (3, 5), (3, 7), (4, 5), (5, 7)].all fun p ↦
  pairAnnCheckGap p.1 p.2

end Checks

end AJConjecture
