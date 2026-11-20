import Mathlib
import AJHandoff.TorusKnot.PairKRevGapConv
import AJPaper.Filling.PpAChainDefs

/-!
# The loop equations of the twist chain, positive twist (PpA, crux)

Source: arXiv:2611.24826v1, Section 2 (`marking.tex`, eq. (twistgluing)) for the twist; the
chain is the library's realization of it (`AJTwist.Knot.TwKBlocks`).

For `ℓ = N > 0` the chain is `b(0, M+N+1)`, the `N + 2` ascending negative letters
`σ_(M+N+1+i)⁻¹`, the jump `b(M+N, M+2N+3)`, the `N` descending negative letters
`σ_(M+N-1-i)⁻¹` and `b(j₀, M)` (`twChain`), with prescribed loops `x` (first band and ascending
letters) and `x⁻¹` (jump, descending letters, last band). The edge meridians are `e_0 = a`,
`e_(M+i) = x^(i+1-N) a x^(N-i)` (`i < N`), `e_(M+N+i) = x a` (`i ≤ N + 3`) and
`e_(j₀) = x^(1-N) a x^N`.

`ppa_twChain_loopEq_pos`: these edge meridians solve the loop equation of every block of the
chain for the prescribed loops `ppaChainLoop ℓ x` (statement as `ppa_twChain_loopEq_neg`).

Route. By `loopPr_band_edge` and `loopPr_neg_edge` the equation of a block only involves the
edge meridians of its two levels and the values of `G_q` at four (three) levels. Each `G_q(n)`
is a power of `x`: compute it for the prefix of the chain by `gapPrefix_eq_prod_range`; then
every equation is an identity between powers of `x` around one `a` and its inverse (`zpow_add`,
`group`). Suggested cut if the file grows: (1) the values of `gapPrefix` of the prefixes at the
levels read by each block; (2) the equations of the two long bands and the jump; (3) the
equations of the letters.

Checked exactly in the free group on `a`, `x` (`SCR/A/py/exact.py`, `check_chain`) and on the
Lean definitions in the symmetric group `S₅` (`SCR/A/lean/TestChain.lean`), as for the negative
twist.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The gap products of a concatenation. -/
private theorem gapPrefix_append_ppaChainEqPos (bs cs : List SBlock) (L : ℕ → G) (n : ℕ) :
    gapPrefix (bs ++ cs) L n =
      gapPrefix cs (fun q ↦ L (q + bs.length)) n * gapPrefix bs L n := by
  induction bs generalizing L with
  | nil => simp [gapPrefix]
  | cons b bs ih =>
    simp only [List.cons_append, gapPrefix, ih, List.length_cons, mul_assoc]
    rfl

/-- The gap products of a single block. -/
private theorem gapPrefix_singleton_ppaChainEqPos (b : SBlock) (L : ℕ → G) (n : ℕ) :
    gapPrefix [b] L n = if b.lo ≤ n ∧ n ≤ b.hi then L 0 else 1 := by
  simp [gapPrefix]

/-- The `q`-th block of the chain of the twist `N > 0`. -/
private def blkPpaChainEqPos (M j₀ N q : ℕ) : SBlock :=
  if q = 0 then SBlock.band 0 (M + N + 1)
  else if q ≤ N + 2 then SBlock.neg (M + N + q)
  else if q = N + 3 then SBlock.band (M + N) (M + 2 * N + 3)
  else if q ≤ 2 * N + 3 then SBlock.neg (M + 2 * N + 3 - q)
  else SBlock.band j₀ M

/-- The first `q` blocks of the chain of the twist `N > 0` multiply the chamber products of the
levels `1, …, topPpaChainEqPos M N q` by `x`. -/
private def topPpaChainEqPos (M N q : ℕ) : ℕ :=
  if q = 0 then 0 else if q ≤ N + 3 then M + N + q else M + 2 * N + 4 - q

/-- The chain of the twist `N > 0` by positions. -/
private theorem twChain_eq_map_ppaChainEqPos (M j₀ N : ℕ) (hN : 1 ≤ N) :
    twChain M j₀ (N : ℤ) = (List.range (2 * N + 5)).map (blkPpaChainEqPos M j₀ N) := by
  have hl : 0 < (N : ℤ) := by omega
  rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt, Int.natAbs_natCast]
  refine List.ext_getElem ?_ fun i h₁ h₂ ↦ ?_
  · simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega
  · simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil] at h₁
    simp only [List.getElem_append, List.getElem_map, List.getElem_range,
      List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil, List.getElem_singleton, blkPpaChainEqPos]
    split_ifs <;> first | rfl | (congr 1 <;> omega)

/-- The prescribed loops of the chain of the twist `N > 0`. -/
private theorem chainLoop_ppaChainEqPos (N : ℕ) (hN : 1 ≤ N) (x : G) (q : ℕ) :
    ppaChainLoop (N : ℤ) x q = if q ≤ N + 2 then x else x⁻¹ := by
  rw [ppaChainLoop, ite_eq_right (by omega), Int.natAbs_natCast]

/-- The gap products of the first `q` blocks of the chain of the twist `N > 0`. -/
private theorem gapPrefix_range_ppaChainEqPos {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (N : ℕ)
    (hN : 1 ≤ N) (x : G) (q : ℕ) (hq : q ≤ 2 * N + 4) (n : ℕ) :
    gapPrefix ((List.range q).map (blkPpaChainEqPos M j₀ N)) (ppaChainLoop (N : ℤ) x) n =
      if 1 ≤ n ∧ n ≤ topPpaChainEqPos M N q then x else 1 := by
  induction q with
  | zero =>
    rw [show topPpaChainEqPos M N 0 = 0 from rfl, ite_eq_right (by omega)]
    rfl
  | succ q ih =>
    rw [List.range_succ, List.map_append, gapPrefix_append_ppaChainEqPos, ih (by omega),
      List.map_singleton, gapPrefix_singleton_ppaChainEqPos, List.length_map, List.length_range,
      Nat.zero_add, chainLoop_ppaChainEqPos N hN]
    rcases Nat.eq_zero_or_pos q with rfl | h0
    · simp (disch := omega) only [blkPpaChainEqPos, topPpaChainEqPos, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi, ↓reduceIte]
      split_ifs <;> group
    rcases Nat.lt_or_ge q (N + 3) with h1 | h1
    · simp (disch := omega) only [blkPpaChainEqPos, topPpaChainEqPos, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi]
      split_ifs <;> first | (exfalso; omega) | group
    rcases Nat.eq_or_lt_of_le h1 with rfl | h2
    · simp (disch := omega) only [blkPpaChainEqPos, topPpaChainEqPos, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi, ↓reduceIte]
      split_ifs <;> first | (exfalso; omega) | group
    · simp (disch := omega) only [blkPpaChainEqPos, topPpaChainEqPos, ite_eq_left, ite_eq_right,
        SBlock.lo, SBlock.hi]
      split_ifs <;> first | (exfalso; omega) | group

/-- The loop equation of the first long band of the chain of the twist `N > 0`. -/
private theorem loopEq_first_ppaChainEqPos {M j₀ : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (a x : G) (e : ℕ → G) (he0 : e 0 = a) (hhigh : ∀ i : ℕ, e (M + N + i) = x * a) :
    ppaChainLoop (N : ℤ) x 0 = loopPr (blkPpaChainEqPos M j₀ N 0)
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqPos M N 0 then x else 1) * descProd e 0 n) := by
  rw [show blkPpaChainEqPos M j₀ N 0 = SBlock.band 0 (M + N + 1) by
    simp only [blkPpaChainEqPos, ↓reduceIte], loopPr_band_edge,
    chainLoop_ppaChainEqPos N hN, show topPpaChainEqPos M N 0 = 0 from rfl, he0, hhigh]
  simp (disch := omega) only [ite_eq_left, ite_eq_right]
  group

/-- The loop equations of the ascending letters of the chain of the twist `N > 0`. -/
private theorem loopEq_asc_ppaChainEqPos {M j₀ : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (a x : G) (e : ℕ → G) (hhigh : ∀ i : ℕ, e (M + N + i) = x * a) (i : ℕ)
    (hi : i < N + 2) :
    ppaChainLoop (N : ℤ) x (i + 1) = loopPr (blkPpaChainEqPos M j₀ N (i + 1))
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqPos M N (i + 1) then x else 1) *
        descProd e 0 n) := by
  have h2 : e (M + N + (i + 1) + 1) = x * a := hhigh (i + 2)
  rw [show blkPpaChainEqPos M j₀ N (i + 1) = SBlock.neg (M + N + (i + 1)) by
    simp (disch := omega) only [blkPpaChainEqPos, ite_eq_left, ite_eq_right],
    loopPr_neg_edge, chainLoop_ppaChainEqPos N hN, h2, hhigh]
  simp (disch := omega) only [topPpaChainEqPos, ite_eq_left, ite_eq_right]
  group

/-- The loop equation of the jump of the chain of the twist `N > 0`. -/
private theorem loopEq_jump_ppaChainEqPos {M j₀ : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (a x : G) (e : ℕ → G) (hhigh : ∀ i : ℕ, e (M + N + i) = x * a) :
    ppaChainLoop (N : ℤ) x (N + 3) = loopPr (blkPpaChainEqPos M j₀ N (N + 3))
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqPos M N (N + 3) then x else 1) *
        descProd e 0 n) := by
  have hMN := hhigh 0
  rw [Nat.add_zero] at hMN
  rw [show blkPpaChainEqPos M j₀ N (N + 3) = SBlock.band (M + N) (M + N + (N + 3)) by
    simp (disch := omega) only [blkPpaChainEqPos, ite_eq_right, ↓reduceIte]
    congr 1; omega,
    loopPr_band_edge, chainLoop_ppaChainEqPos N hN, hMN, hhigh]
  simp (disch := omega) only [topPpaChainEqPos, ite_eq_left, ite_eq_right]
  group

/-- The loop equations of the descending letters of the chain of the twist `N > 0`. -/
private theorem loopEq_desc_ppaChainEqPos {M j₀ : ℕ} (hjM : j₀ < M) (N : ℕ) (hN : 1 ≤ N)
    (a x : G) (e : ℕ → G)
    (hlow : ∀ i : ℕ, i ≤ N → e (M + i) = x ^ ((i : ℤ) + 1 - N) * a * x ^ ((N : ℤ) - i))
    (i d : ℕ) (hd : d + i + 1 = N) :
    ppaChainLoop (N : ℤ) x (N + 4 + i) = loopPr (blkPpaChainEqPos M j₀ N (N + 4 + i))
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqPos M N (N + 4 + i) then x else 1) *
        descProd e 0 n) := by
  rw [show blkPpaChainEqPos M j₀ N (N + 4 + i) = SBlock.neg (M + d) by
    simp (disch := omega) only [blkPpaChainEqPos, ite_eq_left, ite_eq_right]
    congr 1; omega,
    loopPr_neg_edge, chainLoop_ppaChainEqPos N hN, hlow d (by omega),
    show M + d + 1 = M + (d + 1) from rfl, hlow (d + 1) (by omega)]
  simp (disch := omega) only [topPpaChainEqPos, ite_eq_left, ite_eq_right]
  push_cast
  group

/-- The loop equation of the last long band of the chain of the twist `N > 0`. -/
private theorem loopEq_last_ppaChainEqPos {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (N : ℕ)
    (hN : 1 ≤ N) (a x : G) (e : ℕ → G)
    (hej : e j₀ = x ^ (1 - (N : ℤ)) * a * x ^ (N : ℤ))
    (hlow : ∀ i : ℕ, i ≤ N → e (M + i) = x ^ ((i : ℤ) + 1 - N) * a * x ^ ((N : ℤ) - i)) :
    ppaChainLoop (N : ℤ) x (2 * N + 4) = loopPr (blkPpaChainEqPos M j₀ N (2 * N + 4))
      (fun n ↦ (if 1 ≤ n ∧ n ≤ topPpaChainEqPos M N (2 * N + 4) then x else 1) *
        descProd e 0 n) := by
  have hM0 := hlow 0 (by omega)
  rw [Nat.add_zero] at hM0
  rw [show blkPpaChainEqPos M j₀ N (2 * N + 4) = SBlock.band j₀ M by
    simp (disch := omega) only [blkPpaChainEqPos, ite_eq_right],
    loopPr_band_edge, chainLoop_ppaChainEqPos N hN, hM0, hej]
  simp (disch := omega) only [topPpaChainEqPos, ite_eq_left, ite_eq_right]
  push_cast
  group

/-- The loop equations of the chain for a positive twist. -/
theorem ppa_twChain_loopEq_pos {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) {ℓ : ℤ} (hl : 0 < ℓ)
    (a x : G) (e : ℕ → G) (he0 : e 0 = a) (hej : e j₀ = ppaChainTop ℓ a x)
    (hnew : ∀ n, M ≤ n → e n = ppaChainEdge M ℓ a x n) (q : ℕ) (hq : q < twExtra ℓ + 1) :
    ppaChainLoop ℓ x q = loopPr ((twChain M j₀ ℓ).getD q (SBlock.neg 0))
      (fun n ↦ gapPrefix ((twChain M j₀ ℓ).take q) (ppaChainLoop ℓ x) n * descProd e 0 n) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, ℓ = (N : ℤ) := ⟨ℓ.natAbs, by omega⟩
  have hN : 1 ≤ N := by omega
  have hq' : q < 2 * N + 5 := by
    rw [twExtra, ite_eq_right hl.not_ge, Int.natAbs_natCast] at hq
    exact hq
  have hhigh : ∀ i : ℕ, e (M + N + i) = x * a := fun i ↦ by
    rw [hnew _ (by omega), ppaChainEdge, ite_eq_right hl.not_gt, Int.natAbs_natCast,
      ite_eq_right (by omega)]
  have hlow : ∀ i : ℕ, i ≤ N → e (M + i) = x ^ ((i : ℤ) + 1 - N) * a * x ^ ((N : ℤ) - i) :=
    fun i hi ↦ by
    rcases Nat.lt_or_ge i N with h1 | h1
    · rw [hnew _ (by omega), ppaChainEdge, ite_eq_right hl.not_gt, Int.natAbs_natCast,
        ite_eq_left (by omega), show M + i - M = i by omega]
    · obtain rfl : i = N := by omega
      have h0 := hhigh 0
      rw [Nat.add_zero] at h0
      rw [h0, add_sub_cancel_left, sub_self, zpow_one, zpow_zero, mul_one]
  rw [twChain_eq_map_ppaChainEqPos M j₀ N hN, ← List.map_take, List.take_range,
    Nat.min_eq_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq', Option.map_some, Option.getD_some]
  simp only [gapPrefix_range_ppaChainEqPos hj hjM N hN x q (by omega)]
  rcases Nat.eq_zero_or_pos q with rfl | h0
  · exact loopEq_first_ppaChainEqPos N hN a x e he0 hhigh
  rcases Nat.lt_or_ge q (N + 3) with h1 | h1
  · obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
    exact loopEq_asc_ppaChainEqPos N hN a x e hhigh i (by omega)
  rcases Nat.eq_or_lt_of_le h1 with rfl | h2
  · exact loopEq_jump_ppaChainEqPos N hN a x e hhigh
  rcases Nat.lt_or_ge q (2 * N + 4) with h3 | h3
  · obtain ⟨i, rfl⟩ : ∃ i, q = N + 4 + i := ⟨q - N - 4, by omega⟩
    exact loopEq_desc_ppaChainEqPos hjM N hN a x e hlow i (N - 1 - i) (by omega)
  · obtain rfl : q = 2 * N + 4 := by omega
    rw [ppaChainTop] at hej
    exact loopEq_last_ppaChainEqPos hj hjM N hN a x e hej hlow

end AJConjecture
