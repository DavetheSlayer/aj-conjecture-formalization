import Mathlib
import AJHandoff.TorusKnot.PairKRevGapConv
import AJPaper.Filling.PpAChainDefs

/-!
# The loop equations of the twist chain, negative twist (PpA, crux)

Source: arXiv:2611.24826v1, Section 2 (`marking.tex`, eq. (twistgluing)) for the twist; the
chain is the library's realization of it (`AJTwist.Knot.TwKBlocks`).

For `ℓ = -N < 0` the chain is `b(0, M+N-1)`, the `N - 1` descending letters
`b(M+N-2-i, M+N-1-i)`, the jump `b(M, M+N)`, the `N - 1` ascending letters
`b(M+N+i, M+N+1+i)` and `b(j₀, M+2N-1)` (`twChain`), with prescribed loops
`x, x⁻¹, …, x⁻¹, x, x, …, x, x⁻¹`. The edge meridians are `e_0 = a`, `e_(M+i) = x a` (`i < N`),
`e_(M+N+i) = x^(i+2) a x^(-i-1)` (`i < N`) and `e_(j₀) = x^(N+1) a x^(-N)`.

`ppa_twChain_loopEq_neg`: these edge meridians solve the loop equation of every block of the
chain for the prescribed loops `ppaChainLoop ℓ x`: the `q`-th loop is `loopPr` of the `q`-th
block on the chamber products `G_q(n) · e_(n-1) ⋯ e_0`, where `G_q` collects the prescribed
loops of the earlier blocks of the chain (`gapPrefix`).

Route. By `loopPr_band_edge` the equation of a band only involves the edge meridians of its two
levels and the values of `G_q` at four levels. Each `G_q(n)` is a power of `x`: compute it for
the prefix of the chain by `gapPrefix_eq_prod_range` (or by induction along the two runs of
letters, as the private `gapProd_twcAsc_one_twCChain`, `gapProd_twcDesc_one_twCChain` of
`AJTwist.Classical.TwCChain`); then every equation is an identity between powers of `x` around
one `a` and its inverse (`zpow_add`, `group`). Suggested cut if the file grows: (1) the values
of `gapPrefix` of the prefixes at the levels read by each block; (2) the equations of the two
long bands and the jump; (3) the equations of the letters.

Checked exactly in the free group on `a`, `x` (`SCR/A/py/exact.py`, `check_chain`:
`M ∈ {3, 5, 7, 12}`, four values of `j₀`, `|ℓ| ≤ 6`) and on the Lean definitions themselves in
the symmetric group `S₅` (`SCR/A/lean/TestChain.lean`, `|ℓ| ≤ 4`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The gap products of a concatenation. -/
private theorem gapPrefix_append_ppaChainEqNeg (bs cs : List SBlock) (L : ℕ → G) (n : ℕ) :
    gapPrefix (bs ++ cs) L n =
      gapPrefix cs (fun q ↦ L (q + bs.length)) n * gapPrefix bs L n := by
  induction bs generalizing L with
  | nil => simp [gapPrefix]
  | cons b bs ih =>
    simp only [List.cons_append, gapPrefix, ih, List.length_cons, mul_assoc]
    rfl

/-- The gap products of a single block. -/
private theorem gapPrefix_singleton_ppaChainEqNeg (b : SBlock) (L : ℕ → G) (n : ℕ) :
    gapPrefix [b] L n = if b.lo ≤ n ∧ n ≤ b.hi then L 0 else 1 := by
  simp [gapPrefix]

/-- The `q`-th block of the chain of the twist `-N`. -/
private def blkPpaChainEqNeg (M j₀ N q : ℕ) : SBlock :=
  if q = 0 then SBlock.band 0 (M + N - 1)
  else if q < N then SBlock.band (M + N - 1 - q) (M + N - q)
  else if q = N then SBlock.band M (M + N)
  else if q < 2 * N then SBlock.band (M + q - 1) (M + q)
  else SBlock.band j₀ (M + 2 * N - 1)

/-- The first `q` blocks of the chain of the twist `-N` multiply the chamber products of the
levels `1, …, topPpaChainEqNeg M N q` by `x`. -/
private def topPpaChainEqNeg (M N q : ℕ) : ℕ :=
  if q = 0 then 0 else if q ≤ N then M + N - q else M + q - 1

/-- The chain of the twist `-N` by positions. -/
private theorem twChain_eq_map_ppaChainEqNeg (M j₀ N : ℕ) (hN : 1 ≤ N) :
    twChain M j₀ (-(N : ℤ)) = (List.range (2 * N + 1)).map (blkPpaChainEqNeg M j₀ N) := by
  have hl : (-(N : ℤ)) < 0 := by omega
  rw [twChain, ite_eq_right hl.ne, ite_eq_left hl, Int.natAbs_neg, Int.natAbs_natCast]
  refine List.ext_getElem ?_ fun i h₁ h₂ ↦ ?_
  · simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega
  · simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil] at h₁
    simp only [List.getElem_append, List.getElem_map, List.getElem_range,
      List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil, List.getElem_singleton, blkPpaChainEqNeg]
    split_ifs <;> first | rfl | (congr 1 <;> omega)

/-- The prescribed loops of the chain of the twist `-N`. -/
private theorem chainLoop_ppaChainEqNeg (N : ℕ) (x : G) (q : ℕ) :
    ppaChainLoop (-(N : ℤ)) x q = if q = 0 ∨ (N ≤ q ∧ q < 2 * N) then x else x⁻¹ := by
  rw [ppaChainLoop, ite_eq_left (by omega), Int.natAbs_neg, Int.natAbs_natCast]

/-- The gap products of the first `q` blocks of the chain of the twist `-N`. -/
private theorem gapPrefix_range_ppaChainEqNeg {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (N : ℕ)
    (hN : 1 ≤ N) (x : G) (q : ℕ) (hq : q ≤ 2 * N) (n : ℕ) :
    gapPrefix ((List.range q).map (blkPpaChainEqNeg M j₀ N)) (ppaChainLoop (-(N : ℤ)) x) n =
      if 1 ≤ n ∧ n ≤ topPpaChainEqNeg M N q then x else 1 := by
  induction q with
  | zero =>
    rw [show topPpaChainEqNeg M N 0 = 0 from rfl, ite_eq_right (by omega)]
    rfl
  | succ q ih =>
    rw [List.range_succ, List.map_append, gapPrefix_append_ppaChainEqNeg, ih (by omega),
      List.map_singleton, gapPrefix_singleton_ppaChainEqNeg, List.length_map, List.length_range,
      Nat.zero_add, chainLoop_ppaChainEqNeg]
    rcases Nat.eq_zero_or_pos q with rfl | h0
    · simp (disch := omega) only [blkPpaChainEqNeg, topPpaChainEqNeg, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi, ↓reduceIte, true_or]
      split_ifs <;> group
    rcases lt_trichotomy q N with h1 | rfl | h1
    · simp (disch := omega) only [blkPpaChainEqNeg, topPpaChainEqNeg, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi]
      split_ifs <;> first | (exfalso; omega) | group
    · simp (disch := omega) only [blkPpaChainEqNeg, topPpaChainEqNeg, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi, ↓reduceIte]
      split_ifs <;> first | (exfalso; omega) | group
    · simp (disch := omega) only [blkPpaChainEqNeg, topPpaChainEqNeg, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi]
      split_ifs <;> first | (exfalso; omega) | group

/-- The loop equation of the first long band of the chain of the twist `-N`. -/
private theorem loopEq_first_ppaChainEqNeg {M j₀ : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (a x : G) (e : ℕ → G) (he0 : e 0 = a) (hlow : ∀ i, i < N → e (M + i) = x * a) :
    ppaChainLoop (-(N : ℤ)) x 0 = loopPr (blkPpaChainEqNeg M j₀ N 0)
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqNeg M N 0 then x else 1) * descProd e 0 n) := by
  rw [show blkPpaChainEqNeg M j₀ N 0 = SBlock.band 0 (M + (N - 1)) by
    simp only [blkPpaChainEqNeg, ↓reduceIte]; congr 1; omega, loopPr_band_edge,
    chainLoop_ppaChainEqNeg, show topPpaChainEqNeg M N 0 = 0 from rfl, he0, hlow _ (by omega)]
  simp (disch := omega) only [ite_eq_right, ↓reduceIte, true_or]
  group

/-- The loop equations of the descending letters of the chain of the twist `-N`. -/
private theorem loopEq_desc_ppaChainEqNeg {M j₀ : ℕ} (hjM : j₀ < M) (N : ℕ)
    (a x : G) (e : ℕ → G) (hlow : ∀ i, i < N → e (M + i) = x * a) (q : ℕ) (h0 : 0 < q)
    (hq : q < N) :
    ppaChainLoop (-(N : ℤ)) x q = loopPr (blkPpaChainEqNeg M j₀ N q)
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqNeg M N q then x else 1) * descProd e 0 n) := by
  rw [show blkPpaChainEqNeg M j₀ N q = SBlock.band (M + (N - 1 - q)) (M + (N - q)) by
    simp (disch := omega) only [blkPpaChainEqNeg, ite_eq_left, ite_eq_right]; congr 1 <;> omega,
    loopPr_band_edge, chainLoop_ppaChainEqNeg, hlow _ (by omega), hlow _ (by omega)]
  simp (disch := omega) only [topPpaChainEqNeg, ite_eq_left, ite_eq_right]
  group

/-- The loop equation of the jump of the chain of the twist `-N`. -/
private theorem loopEq_jump_ppaChainEqNeg {M j₀ : ℕ} (hjM : j₀ < M) (N : ℕ) (hN : 1 ≤ N)
    (a x : G) (e : ℕ → G) (hlow : ∀ i, i < N → e (M + i) = x * a)
    (hhigh : ∀ i : ℕ, e (M + N + i) = x ^ ((i : ℤ) + 2) * a * (x ^ ((i : ℤ) + 1))⁻¹) :
    ppaChainLoop (-(N : ℤ)) x N = loopPr (blkPpaChainEqNeg M j₀ N N)
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqNeg M N N then x else 1) * descProd e 0 n) := by
  have hM0 := hlow 0 (by omega)
  have hMN := hhigh 0
  rw [Nat.add_zero] at hM0 hMN
  rw [show blkPpaChainEqNeg M j₀ N N = SBlock.band M (M + N) by
    simp (disch := omega) only [blkPpaChainEqNeg, ite_eq_right, ↓reduceIte],
    loopPr_band_edge, chainLoop_ppaChainEqNeg, hM0, hMN]
  simp (disch := omega) only [topPpaChainEqNeg, ite_eq_left, ite_eq_right]
  simp only [Nat.cast_zero]
  group

/-- The loop equations of the ascending letters of the chain of the twist `-N`. -/
private theorem loopEq_asc_ppaChainEqNeg {M j₀ : ℕ} (hjM : j₀ < M) (N : ℕ)
    (a x : G) (e : ℕ → G)
    (hhigh : ∀ i : ℕ, e (M + N + i) = x ^ ((i : ℤ) + 2) * a * (x ^ ((i : ℤ) + 1))⁻¹)
    (i : ℕ) (hi : N + 1 + i < 2 * N) :
    ppaChainLoop (-(N : ℤ)) x (N + 1 + i) = loopPr (blkPpaChainEqNeg M j₀ N (N + 1 + i))
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqNeg M N (N + 1 + i) then x else 1) *
        descProd e 0 n) := by
  rw [show blkPpaChainEqNeg M j₀ N (N + 1 + i) = SBlock.band (M + N + i) (M + N + (i + 1)) by
    simp (disch := omega) only [blkPpaChainEqNeg, ite_eq_left, ite_eq_right]; congr 1 <;> omega,
    loopPr_band_edge, chainLoop_ppaChainEqNeg, hhigh, hhigh]
  simp (disch := omega) only [topPpaChainEqNeg, ite_eq_left, ite_eq_right]
  push_cast
  group

/-- The loop equation of the last long band of the chain of the twist `-(d + 1)`. -/
private theorem loopEq_last_ppaChainEqNeg {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (d : ℕ)
    (a x : G) (e : ℕ → G)
    (hej : e j₀ = x ^ (1 - -((d + 1 : ℕ) : ℤ)) * a * x ^ (-((d + 1 : ℕ) : ℤ)))
    (hhigh : ∀ i : ℕ, e (M + (d + 1) + i) = x ^ ((i : ℤ) + 2) * a * (x ^ ((i : ℤ) + 1))⁻¹) :
    ppaChainLoop (-((d + 1 : ℕ) : ℤ)) x (2 * (d + 1)) =
      loopPr (blkPpaChainEqNeg M j₀ (d + 1) (2 * (d + 1)))
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqNeg M (d + 1) (2 * (d + 1)) then x else 1) *
        descProd e 0 n) := by
  rw [show blkPpaChainEqNeg M j₀ (d + 1) (2 * (d + 1)) = SBlock.band j₀ (M + (d + 1) + d) by
    simp (disch := omega) only [blkPpaChainEqNeg, ite_eq_right]; congr 1; omega,
    loopPr_band_edge, chainLoop_ppaChainEqNeg, hhigh, hej]
  simp (disch := omega) only [topPpaChainEqNeg, ite_eq_left, ite_eq_right]
  push_cast
  group

/-- The loop equations of the chain for a negative twist. -/
theorem ppa_twChain_loopEq_neg {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) {ℓ : ℤ} (hl : ℓ < 0)
    (a x : G) (e : ℕ → G) (he0 : e 0 = a) (hej : e j₀ = ppaChainTop ℓ a x)
    (hnew : ∀ n, M ≤ n → e n = ppaChainEdge M ℓ a x n) (q : ℕ) (hq : q < twExtra ℓ + 1) :
    ppaChainLoop ℓ x q = loopPr ((twChain M j₀ ℓ).getD q (SBlock.neg 0))
      (fun n ↦ gapPrefix ((twChain M j₀ ℓ).take q) (ppaChainLoop ℓ x) n * descProd e 0 n) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, ℓ = -(N : ℤ) := ⟨ℓ.natAbs, by omega⟩
  have hN : 1 ≤ N := by omega
  have hq' : q < 2 * N + 1 := by
    rw [twExtra, ite_eq_left hl.le, Int.natAbs_neg, Int.natAbs_natCast] at hq
    exact hq
  have hlow : ∀ i, i < N → e (M + i) = x * a := fun i hi ↦ by
    rw [hnew _ (by omega), ppaChainEdge, ite_eq_left hl, Int.natAbs_neg, Int.natAbs_natCast,
      ite_eq_left (by omega)]
  have hhigh : ∀ i : ℕ, e (M + N + i) = x ^ ((i : ℤ) + 2) * a * (x ^ ((i : ℤ) + 1))⁻¹ :=
    fun i ↦ by
    rw [hnew _ (by omega), ppaChainEdge, ite_eq_left hl, Int.natAbs_neg, Int.natAbs_natCast,
      ite_eq_right (by omega), show M + N + i - M - N = i by omega]
  rw [twChain_eq_map_ppaChainEqNeg M j₀ N hN, ← List.map_take, List.take_range,
    Nat.min_eq_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq', Option.map_some, Option.getD_some]
  simp only [gapPrefix_range_ppaChainEqNeg hj hjM N hN x q (by omega)]
  rcases Nat.eq_zero_or_pos q with rfl | h0
  · exact loopEq_first_ppaChainEqNeg N hN a x e he0 hlow
  rcases lt_trichotomy q N with h1 | rfl | h1
  · exact loopEq_desc_ppaChainEqNeg hjM N a x e hlow q h0 h1
  · exact loopEq_jump_ppaChainEqNeg hjM q hN a x e hlow hhigh
  rcases Nat.lt_or_ge q (2 * N) with h2 | h2
  · obtain ⟨i, rfl⟩ : ∃ i, q = N + 1 + i := ⟨q - N - 1, by omega⟩
    exact loopEq_asc_ppaChainEqNeg hjM N a x e hhigh i h2
  · obtain rfl : q = 2 * N := by omega
    obtain ⟨d, rfl⟩ : ∃ d, N = d + 1 := ⟨N - 1, by omega⟩
    rw [ppaChainTop] at hej
    exact loopEq_last_ppaChainEqNeg hj hjM d a x e hej hhigh

end AJConjecture
