import Mathlib
import AJHandoff.TorusKnot.PairKRevGeneric
import AJHandoff.TorusKnot.PairKPeriGapRel
import AJTwist.Classical.TwCChain

/-!
# The twist chain in the reverse direction: prescribed loops and edge meridians (PpA)

Source: arXiv:2611.24826v1, Section 2 (`marking.tex`, "The signed full twist": "The disk twist on
the axis side fixes `λ_A` and sends `μ_A` to `μ_A λ_A`") and Section 7.6. In the closed braids
of the library the `ℓ` full twists are the chain `twChain M j₀ ℓ` (`AJTwist.Knot.TwKBlocks`),
which replaces a band `b(0, j₀)` by `twExtra ℓ + 1` blocks through `twExtra ℓ` new discs on the
levels `M, M + 1, …`.

To build a tuple fixed by a block list containing the chain one prescribes the loop of every
block and the edge meridian of every level (`AJHandoff.TorusKnot.PairKRevGeneric`). For the
chain, with `x` the loop the band `b(0, j₀)` has in the untwisted list and `a` the edge meridian
of the level `0`:

* `ppaChainLoop ℓ x q`: the loop of the `q`-th block of the chain. It is `x` or `x⁻¹`:
  for `ℓ = -n ≤ 0` the blocks `0` and `n, …, 2n - 1` (the first long band, the jump and the
  ascending letters) have loop `x`, the others (`n - 1` descending letters and the last long
  band) `x⁻¹`; for `ℓ = n > 0` the blocks `0, …, n + 2` (the first long band and the ascending
  negative letters) have loop `x`, the others (the jump, the `n` descending letters and the last
  long band) `x⁻¹`;
* `ppaChainTop ℓ a x = x^(1-ℓ) a x^ℓ`: the edge meridian of the level `j₀` (untwisted: `x a`,
  the equation of the band `b(0, j₀)`); the full twists conjugate it by `x^(-ℓ)`;
* `ppaChainEdge M ℓ a x n`: the edge meridian of the new level `n ≥ M`: for `ℓ = -N < 0`,
  `x a` on the levels `M, …, M + N - 1` and `x^(i+2) a x^(-i-1)` on the level `M + N + i`; for
  `ℓ = N > 0`, `x^(i+1-N) a x^(N-i)` on the level `M + i`, `i < N`, and `x a` on the levels
  `M + N, …, M + 2N + 3`.

`ppa_gapPrefix_twChain`: with these loops the chain multiplies the chamber products of the
levels `1, …, j₀` by `x` and no other: on the gap products it is the band `b(0, j₀)` with loop
`x`. (At a new level `M + k` the loops of the long bands, the jump and one letter cancel.)

All formulas were found from the edge meridians of numerical representations and then checked
exactly, as identities in the free group on `a`, `x`, for `M ∈ {3, 5, 7, 12}`, four values of
`j₀` and `-6 ≤ ℓ ≤ 6` (`SCR/A/py/exact.py`, `check_chain`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The prescribed loop of the `q`-th block of the chain `twChain M j₀ ℓ`, for the loop `x` of
the band it replaces. -/
def ppaChainLoop (ℓ : ℤ) (x : G) (q : ℕ) : G :=
  if ℓ ≤ 0 then
    if q = 0 ∨ (ℓ.natAbs ≤ q ∧ q < 2 * ℓ.natAbs) then x else x⁻¹
  else
    if q ≤ ℓ.natAbs + 2 then x else x⁻¹

/-- The edge meridian of the upper level `j₀` of the chain: `x^(1-ℓ) a x^ℓ`. -/
def ppaChainTop (ℓ : ℤ) (a x : G) : G := x ^ (1 - ℓ) * a * x ^ ℓ

/-- The edge meridian of the new level `n ≥ M` of the chain. -/
def ppaChainEdge (M : ℕ) (ℓ : ℤ) (a x : G) (n : ℕ) : G :=
  if ℓ < 0 then
    if n < M + ℓ.natAbs then x * a
    else x ^ (((n - M - ℓ.natAbs : ℕ) : ℤ) + 2) * a *
      (x ^ (((n - M - ℓ.natAbs : ℕ) : ℤ) + 1))⁻¹
  else
    if n < M + ℓ.natAbs then x ^ (((n - M : ℕ) : ℤ) + 1 - ℓ) * a * x ^ (ℓ - ((n - M : ℕ) : ℤ))
    else x * a

/-- Without twist the level `j₀` carries `x a`. -/
theorem ppaChainTop_zero (a x : G) : ppaChainTop 0 a x = x * a := by
  simp [ppaChainTop]

/-- The gap products of a concatenation. -/
private theorem gapPrefix_append_ppaChainDefs (bs cs : List SBlock) (L : ℕ → G) (n : ℕ) :
    gapPrefix (bs ++ cs) L n =
      gapPrefix cs (fun q ↦ L (q + bs.length)) n * gapPrefix bs L n := by
  induction bs generalizing L with
  | nil => simp [gapPrefix]
  | cons b bs ih =>
    simp only [List.cons_append, gapPrefix, ih, List.length_cons, mul_assoc]
    rfl

/-- The gap products of a single block. -/
private theorem gapPrefix_singleton_ppaChainDefs (b : SBlock) (L : ℕ → G) (n : ℕ) :
    gapPrefix [b] L n = if b.lo ≤ n ∧ n ≤ b.hi then L 0 else 1 := by
  simp [gapPrefix]

/-- The gap products of an ascending run of letters with the same loop `y`. -/
private theorem gapPrefix_asc_ppaChainDefs (F : ℕ → SBlock) (A k : ℕ) (L : ℕ → G) (y : G)
    (hF : ∀ i, i < k → (F i).lo = A + i ∧ (F i).hi = A + i) (hL : ∀ q, q < k → L q = y)
    (n : ℕ) :
    gapPrefix ((List.range k).map F) L n = if A ≤ n ∧ n < A + k then y else 1 := by
  induction k with
  | zero =>
    rw [ite_eq_right (by omega)]
    rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, gapPrefix_append_ppaChainDefs,
      ih (fun i hi ↦ hF i (by omega)) (fun q hq ↦ hL q (by omega)), List.map_singleton,
      gapPrefix_singleton_ppaChainDefs, (hF k (by omega)).1, (hF k (by omega)).2,
      List.length_map, List.length_range, Nat.zero_add, hL k (by omega)]
    split_ifs <;> first | (exfalso; omega) | simp

/-- The gap products of a descending run of letters with the same loop `y`. -/
private theorem gapPrefix_desc_ppaChainDefs (F : ℕ → SBlock) (B k : ℕ) (L : ℕ → G) (y : G)
    (hk : k ≤ B + 1) (hF : ∀ i, i < k → (F i).lo = B - i ∧ (F i).hi = B - i)
    (hL : ∀ q, q < k → L q = y) (n : ℕ) :
    gapPrefix ((List.range k).map F) L n = if B < n + k ∧ n ≤ B then y else 1 := by
  induction k with
  | zero =>
    rw [ite_eq_right (by omega)]
    rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, gapPrefix_append_ppaChainDefs,
      ih (by omega) (fun i hi ↦ hF i (by omega)) (fun q hq ↦ hL q (by omega)),
      List.map_singleton, gapPrefix_singleton_ppaChainDefs, (hF k (by omega)).1,
      (hF k (by omega)).2, List.length_map, List.length_range, Nat.zero_add, hL k (by omega)]
    split_ifs <;> first | (exfalso; omega) | simp

/-- The gap products of the chain of a negative twist. -/
private theorem gapPrefix_twChain_neg_ppaChainDefs {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M)
    (N : ℕ) (hN : 1 ≤ N) (x : G) (n : ℕ) :
    gapPrefix (twChain M j₀ (-(N : ℤ))) (ppaChainLoop (-(N : ℤ)) x) n =
      if 1 ≤ n ∧ n ≤ j₀ then x else 1 := by
  have hl : (-(N : ℤ)) < 0 := by omega
  have hloop : ∀ q, ppaChainLoop (-(N : ℤ)) x q =
      if q = 0 ∨ (N ≤ q ∧ q < 2 * N) then x else x⁻¹ := by
    intro q
    rw [ppaChainLoop, ite_eq_left hl.le, Int.natAbs_neg, Int.natAbs_natCast]
  rw [twChain, ite_eq_right hl.ne, ite_eq_left hl, Int.natAbs_neg, Int.natAbs_natCast]
  simp only [gapPrefix_append_ppaChainDefs, gapPrefix_singleton_ppaChainDefs,
    List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil,
    SBlock.lo, SBlock.hi]
  rw [gapPrefix_desc_ppaChainDefs
      (fun i ↦ SBlock.band (M + N - 2 - i) (M + N - 1 - i)) (M + N - 1) _ _ x⁻¹ (by omega)
      (fun i hi ↦ ⟨by simp only [SBlock.lo]; omega, rfl⟩)
      ?_,
    gapPrefix_asc_ppaChainDefs
      (fun i ↦ SBlock.band (M + N + i) (M + N + 1 + i)) (M + N + 1) _ _ x
      (fun i hi ↦ ⟨by simp only [SBlock.lo]; omega, rfl⟩)
      ?_]
  · simp (disch := omega) only [hloop, ite_eq_left, ite_eq_right, ↓reduceIte, true_or]
    split_ifs <;> first | (exfalso; omega) | group
  · intro q hq
    rw [hloop, ite_eq_left (by omega)]
  · intro q hq
    rw [hloop, ite_eq_right (by omega)]

/-- The gap products of the chain of a positive twist. -/
private theorem gapPrefix_twChain_pos_ppaChainDefs {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M)
    (N : ℕ) (hN : 1 ≤ N) (x : G) (n : ℕ) :
    gapPrefix (twChain M j₀ (N : ℤ)) (ppaChainLoop (N : ℤ) x) n =
      if 1 ≤ n ∧ n ≤ j₀ then x else 1 := by
  have hl : 0 < (N : ℤ) := by omega
  have hloop : ∀ q, ppaChainLoop (N : ℤ) x q = if q ≤ N + 2 then x else x⁻¹ := by
    intro q
    rw [ppaChainLoop, ite_eq_right hl.not_ge, Int.natAbs_natCast]
  rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt, Int.natAbs_natCast]
  simp only [gapPrefix_append_ppaChainDefs, gapPrefix_singleton_ppaChainDefs,
    List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil,
    SBlock.lo, SBlock.hi]
  rw [gapPrefix_desc_ppaChainDefs
      (fun i ↦ SBlock.neg (M + N - 1 - i)) (M + N) _ _ x⁻¹ (by omega)
      (fun i hi ↦ by constructor <;> simp only [SBlock.lo, SBlock.hi] <;> omega)
      ?_,
    gapPrefix_asc_ppaChainDefs
      (fun i ↦ SBlock.neg (M + N + 1 + i)) (M + N + 2) _ _ x
      (fun i hi ↦ by constructor <;> simp only [SBlock.lo, SBlock.hi] <;> omega)
      ?_]
  · simp (disch := omega) only [hloop, ite_eq_left, ite_eq_right]
    split_ifs <;> first | (exfalso; omega) | group
  · intro q hq
    rw [hloop, ite_eq_left (by omega)]
  · intro q hq
    rw [hloop, ite_eq_right (by omega)]

/-- With the prescribed loops the chain acts on the gap products as the band `b(0, j₀)` with
loop `x`. -/
theorem ppa_gapPrefix_twChain {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ) (x : G)
    (n : ℕ) :
    gapPrefix (twChain M j₀ ℓ) (ppaChainLoop ℓ x) n = if 1 ≤ n ∧ n ≤ j₀ then x else 1 := by
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, ℓ = -(N : ℤ) := ⟨ℓ.natAbs, by omega⟩
    exact gapPrefix_twChain_neg_ppaChainDefs hj hjM N (by omega) x n
  · simp [twChain, gapPrefix, ppaChainLoop, SBlock.lo, SBlock.hi]
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, ℓ = (N : ℤ) := ⟨ℓ.natAbs, by omega⟩
    exact gapPrefix_twChain_pos_ppaChainDefs hj hjM N (by omega) x n

end AJConjecture
