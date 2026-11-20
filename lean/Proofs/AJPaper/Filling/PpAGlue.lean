import Mathlib
import AJHandoff.TorusKnot.PairKRevGeneric
import AJHandoff.TorusKnot.PairKRevGapConv
import AJPaper.Filling.PpAChainEqNeg
import AJPaper.Filling.PpAChainEqPos

/-!
# A fixed tuple of a twisted block list from edge meridians of the untwisted one (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`): the representation of the pattern
group that factors through the twisted filling. In the closed braids of the library the twist
is the chain `twChain M j₀ ℓ` in place of a head band `b(0, j₀)`; this file is the generic
step from the untwisted list `b(0, j₀) :: tail` to the twisted list `twChain M j₀ ℓ ++ tail`. It
is used for the twisted doubles (`tail` the tail of `pairBlocks r s`, both clasp signs) and for
the twist knots (`tail = [σ_1⁻¹, σ_0⁻¹, σ_1⁻¹]`).

* `ppa_twChain_loopEq`: the loop equations of the chain for every `ℓ` (the two signs are
  `ppa_twChain_loopEq_neg`, `ppa_twChain_loopEq_pos`; `ℓ = 0` is the single band:
  `loopPr_band_edge` with `gapPrefix [] = 1`, `ppaChainTop_zero`).
* `ppa_exists_fixedTuple_of_edges`: let `Lb` be loops for the blocks of the untwisted list
  `b(0, j₀) :: tail` (on `M` strands) with all gap products `1`, and `e` edge meridians with
  `e 0 = a`, with the *twisted* value `e j₀ = x^(1-ℓ) a x^ℓ` (`x = Lb 0`), with the chain values
  on the new levels, and solving the loop equation of every block of `tail` — written with the
  gap products of the untwisted list. Then the tuple `F t = D(t)⁻¹ e_t D(t)`,
  `D(t) = e_(t-1) ⋯ e_0`, on `M + twExtra ℓ` strands is fixed by the run of the twisted list,
  its bottom edge meridian is `a`, the loop of its chain is `x`, and the loops of the blocks of
  `tail` are the prescribed ones.

Route for the second statement (as `exists_pairFixedTuple`,
`AJHandoff.TorusKnot.PairKRevTuple`). Prescribe the loops `L' q = ppaChainLoop ℓ x q` for
`q ≤ twExtra ℓ` and `L' (twExtra ℓ + 1 + q) = Lb (q + 1)`. By `gapPrefix` of an append (prove
`gapPrefix (bs ++ cs) L n = gapPrefix cs (fun q ↦ L (q + bs.length)) n * gapPrefix bs L n`, or
use `gapPrefix_eq_prod_range`) and `ppa_gapPrefix_twChain`, the gap products of every prefix
`twChain ++ tail.take q` are those of `(b(0, j₀) :: tail).take (q + 1)` for `Lb`. So the
hypothesis gives the loop equations of the blocks of `tail` in the twisted list, and
`ppa_twChain_loopEq` those of the chain; the chamber products of `F` are the `D(n)`
(the private `prePr_of_edge` of `PairKRevTuple`; restate), and a valid block only reads them up
to the number of strands (the private `loopPr_congr_rt` there). Then `loopAt_eq_of_prescribed`
gives the loops and the gap products `gapPrefix (twChain ++ tail) L' n = 1`, and
`runTop_eq_self_of_gapProd` the fixed tuple. The loop of the chain is its gap product at the
level `1` (`prePr_runTop`, `gapProd_append`), i.e. `x`.

Checked numerically for the block lists of the twisted doubles and of the twist knots
(`SCR/A/py/abel2.py`, `twistrep.py`: the tuple built in this way is fixed to `10⁻¹⁰⁰`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The gap products of a concatenation. -/
private theorem gapPrefix_append_ppaGlue (bs cs : List SBlock) (L : ℕ → G) (n : ℕ) :
    gapPrefix (bs ++ cs) L n =
      gapPrefix cs (fun q ↦ L (q + bs.length)) n * gapPrefix bs L n := by
  induction bs generalizing L with
  | nil => simp [gapPrefix]
  | cons b bs ih =>
    simp only [List.cons_append, gapPrefix, ih, List.length_cons, mul_assoc]
    rfl

/-- The gap products only read the loops of the blocks of the list. -/
private theorem gapPrefix_congr_ppaGlue (bs : List SBlock) (L L' : ℕ → G)
    (h : ∀ q, q < bs.length → L q = L' q) (n : ℕ) : gapPrefix bs L n = gapPrefix bs L' n := by
  induction bs generalizing L L' with
  | nil => rfl
  | cons b bs ih =>
    rw [gapPrefix, gapPrefix,
      ih _ _ (fun q hq ↦ h (q + 1) (by rw [List.length_cons]; omega)),
      h 0 (by rw [List.length_cons]; omega)]

/-- The loop of a valid block only reads the chamber products up to the number of strands. -/
private theorem loopPr_congr_ppaGlue {m : ℕ} (b : SBlock) (hb : b.Valid m) (P Q : ℕ → G)
    (hPQ : ∀ n, n ≤ m → P n = Q n) : loopPr b P = loopPr b Q := by
  cases b with
  | band i j =>
    simp only [SBlock.Valid] at hb
    simp only [loopPr, hPQ (j + 1) (by omega), hPQ j (by omega), hPQ i (by omega),
      hPQ (i + 1) (by omega)]
  | neg i =>
    simp only [SBlock.Valid] at hb
    simp only [loopPr, hPQ i (by omega), hPQ (i + 1) (by omega), hPQ (i + 2) (by omega)]

/-- A block that lives on `m` strands lives on more strands. -/
private theorem valid_mono_ppaGlue {m m' : ℕ} (hm : m ≤ m') (b : SBlock) (hb : b.Valid m) :
    b.Valid m' := by
  cases b <;> simp only [SBlock.Valid] at hb ⊢ <;> omega

/-- The prefix products of a tuple built from edge meridians are the products of the edge
meridians. -/
private theorem prePr_of_edge_ppaGlue {m : ℕ} (e : ℕ → G) (n : ℕ) (hn : n ≤ m) :
    prePr (fun t : Fin m ↦ (descProd e 0 t)⁻¹ * e t * descProd e 0 t) n = descProd e 0 n := by
  induction n with
  | zero => simp [prePr_zero, descProd]
  | succ n ih =>
    rw [prePr_succ _ n (by omega), ih (by omega)]
    simp only [descProd, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.prod_cons, Nat.zero_add]
    group

/-- The prescribed loops of the twisted list `twChain M j₀ ℓ ++ tail`: the chain loops for the
loop `Lb 0`, then the loops `Lb 1, Lb 2, …` of the tail. -/
private def twistedLoopPpaGlue (ℓ : ℤ) (Lb : ℕ → G) (q : ℕ) : G :=
  if q < twExtra ℓ + 1 then ppaChainLoop ℓ (Lb 0) q else Lb (q - twExtra ℓ)

/-- The gap products of the twisted list are those of the untwisted list. -/
private theorem gapPrefix_twisted_ppaGlue {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ)
    (ts : List SBlock) (Lb : ℕ → G) (n : ℕ) :
    gapPrefix (twChain M j₀ ℓ ++ ts) (twistedLoopPpaGlue ℓ Lb) n =
      gapPrefix (SBlock.band 0 j₀ :: ts) Lb n := by
  have hlen := length_twChain M j₀ ℓ
  have hfun : (fun q ↦ twistedLoopPpaGlue ℓ Lb (q + (twChain M j₀ ℓ).length)) =
      fun q ↦ Lb (q + 1) := by
    funext q
    rw [twistedLoopPpaGlue, ite_eq_right (by omega), hlen]
    congr 1
    omega
  rw [gapPrefix_append_ppaGlue, hfun, gapPrefix,
    gapPrefix_congr_ppaGlue (twChain M j₀ ℓ) (twistedLoopPpaGlue ℓ Lb) (ppaChainLoop ℓ (Lb 0))
      (fun q hq ↦ by rw [twistedLoopPpaGlue, ite_eq_left (by omega)]),
    ppa_gapPrefix_twChain hj hjM]
  simp only [SBlock.lo, SBlock.hi, Nat.zero_add]

/-- The loop equations of the chain, for every twist. -/
theorem ppa_twChain_loopEq {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ)
    (a x : G) (e : ℕ → G) (he0 : e 0 = a) (hej : e j₀ = ppaChainTop ℓ a x)
    (hnew : ∀ n, M ≤ n → e n = ppaChainEdge M ℓ a x n) (q : ℕ) (hq : q < twExtra ℓ + 1) :
    ppaChainLoop ℓ x q = loopPr ((twChain M j₀ ℓ).getD q (SBlock.neg 0))
      (fun n ↦ gapPrefix ((twChain M j₀ ℓ).take q) (ppaChainLoop ℓ x) n * descProd e 0 n) := by
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · exact ppa_twChain_loopEq_neg hj hjM hl a x e he0 hej hnew q hq
  · obtain rfl : q = 0 := by
      rw [twExtra] at hq
      simpa using hq
    rw [ppaChainTop_zero] at hej
    rw [show twChain M j₀ 0 = [SBlock.band 0 j₀] by rw [twChain, ite_eq_left rfl],
      List.getD_cons_zero, loopPr_band_edge, hej, he0]
    simp [gapPrefix, ppaChainLoop]
  · exact ppa_twChain_loopEq_pos hj hjM hl a x e he0 hej hnew q hq

/-- A tuple fixed by the twisted list `twChain M j₀ ℓ ++ tail` from loops and edge meridians of
the untwisted list `b(0, j₀) :: tail`. -/
theorem ppa_exists_fixedTuple_of_edges {M j₀ : ℕ} (hj : 0 < j₀) (hjM : j₀ < M) (ℓ : ℤ)
    (tail : List SBlock) (hv : ∀ b ∈ tail, b.Valid M) (Lb : ℕ → G)
    (hgap : ∀ n, gapPrefix (SBlock.band 0 j₀ :: tail) Lb n = 1)
    (a : G) (e : ℕ → G) (he0 : e 0 = a) (hej : e j₀ = ppaChainTop ℓ a (Lb 0))
    (hnew : ∀ n, M ≤ n → e n = ppaChainEdge M ℓ a (Lb 0) n)
    (heq : ∀ q, q < tail.length → Lb (q + 1) = loopPr (tail.getD q (SBlock.neg 0))
      (fun n ↦ gapPrefix ((SBlock.band 0 j₀ :: tail).take (q + 1)) Lb n * descProd e 0 n)) :
    ∃ F : Fin (M + twExtra ℓ) → G,
      runTop (M + twExtra ℓ) (twChain M j₀ ℓ ++ tail) F = F ∧ edgeMer F 0 = a ∧
      twcChainLoop M j₀ ℓ F = Lb 0 ∧
      ∀ q, q < tail.length →
        loopAt (M + twExtra ℓ) (twChain M j₀ ℓ ++ tail) F (twExtra ℓ + 1 + q) = Lb (q + 1) := by
  have hlen := length_twChain M j₀ ℓ
  have hvc : ∀ b ∈ twChain M j₀ ℓ, b.Valid (M + twExtra ℓ) := twChain_valid hj hjM ℓ
  have hvt : ∀ b ∈ tail, b.Valid (M + twExtra ℓ) := fun b hb ↦
    valid_mono_ppaGlue (Nat.le_add_right _ _) b (hv b hb)
  have hvall : ∀ b ∈ twChain M j₀ ℓ ++ tail, b.Valid (M + twExtra ℓ) := fun b hb ↦
    (List.mem_append.1 hb).elim (hvc b) (hvt b)
  set F : Fin (M + twExtra ℓ) → G := fun t ↦ (descProd e 0 t)⁻¹ * e t * descProd e 0 t with hF
  have hchain : ∀ q < (twChain M j₀ ℓ).length, ppaChainLoop ℓ (Lb 0) q =
      loopPr ((twChain M j₀ ℓ).getD q (SBlock.neg 0))
        (fun n ↦ gapPrefix ((twChain M j₀ ℓ).take q) (ppaChainLoop ℓ (Lb 0)) n * prePr F n) := by
    intro q hq
    rw [ppa_twChain_loopEq hj hjM ℓ a (Lb 0) e he0 hej hnew q (by omega)]
    have hmem : (twChain M j₀ ℓ).getD q (SBlock.neg 0) ∈ twChain M j₀ ℓ := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.getElem_mem hq
    refine loopPr_congr_ppaGlue _ (hvc _ hmem) _ _ fun n hn ↦ ?_
    rw [prePr_of_edge_ppaGlue e n hn]
  obtain ⟨-, hGc⟩ := loopAt_eq_of_prescribed (twChain M j₀ ℓ) hvc F (ppaChainLoop ℓ (Lb 0)) hchain
  have hloop : ∀ q < (twChain M j₀ ℓ ++ tail).length, twistedLoopPpaGlue ℓ Lb q =
      loopPr ((twChain M j₀ ℓ ++ tail).getD q (SBlock.neg 0))
        (fun n ↦ gapPrefix ((twChain M j₀ ℓ ++ tail).take q) (twistedLoopPpaGlue ℓ Lb) n *
          prePr F n) := by
    intro q hq
    rcases Nat.lt_or_ge q (twChain M j₀ ℓ).length with h1 | h1
    · rw [List.getD_append _ _ _ _ h1, List.take_append_of_le_length h1.le, twistedLoopPpaGlue,
        ite_eq_left (by omega), hchain q h1]
      congr 1
      funext n
      rw [gapPrefix_congr_ppaGlue _ (twistedLoopPpaGlue ℓ Lb) (ppaChainLoop ℓ (Lb 0))
        fun q' hq' ↦ by
          rw [List.length_take] at hq'
          rw [twistedLoopPpaGlue, ite_eq_left (by omega)]]
    · obtain ⟨q', rfl⟩ : ∃ q', q = (twChain M j₀ ℓ).length + q' :=
        ⟨q - (twChain M j₀ ℓ).length, by omega⟩
      have hq' : q' < tail.length := by
        rw [List.length_append] at hq
        omega
      have hmem : tail.getD q' (SBlock.neg 0) ∈ tail := by
        rw [List.getD_eq_getElem _ _ hq']
        exact List.getElem_mem hq'
      rw [List.getD_append_right _ _ _ _ h1, Nat.add_sub_cancel_left,
        List.take_length_add_append, twistedLoopPpaGlue, ite_eq_right (by omega),
        show (twChain M j₀ ℓ).length + q' - twExtra ℓ = q' + 1 by omega, heq q' hq']
      refine loopPr_congr_ppaGlue _ (hvt _ hmem) _ _ fun n hn ↦ ?_
      rw [prePr_of_edge_ppaGlue e n hn, gapPrefix_twisted_ppaGlue hj hjM, List.take_succ_cons]
  obtain ⟨hL, hG⟩ := loopAt_eq_of_prescribed (twChain M j₀ ℓ ++ tail) hvall F
    (twistedLoopPpaGlue ℓ Lb) hloop
  refine ⟨F, runTop_eq_self_of_gapProd _ hvall F fun n ↦ ?_, ?_, ?_, fun q hq ↦ ?_⟩
  · rw [hG, gapPrefix_twisted_ppaGlue hj hjM, hgap]
  · rw [edgeMer_zero F (by omega)]
    simp only [hF, descProd, List.range_zero, List.reverse_nil, List.map_nil, List.prod_nil,
      inv_one, one_mul, mul_one]
    exact he0
  · rw [twcChainLoop, prePr_runTop _ hvc, mul_inv_cancel_right, hGc,
      ppa_gapPrefix_twChain hj hjM, ite_eq_left ⟨le_rfl, hj⟩]
  · rw [hL _ (by rw [List.length_append]; omega), twistedLoopPpaGlue, ite_eq_right (by omega)]
    congr 1
    omega

end AJConjecture
