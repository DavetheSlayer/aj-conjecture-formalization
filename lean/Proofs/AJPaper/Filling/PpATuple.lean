import Mathlib
import AJTwist.Classical.TwCLoops
import AJPaper.Filling.PpAGlue
import AJPaper.Filling.PpAAnnulus
import AJPaper.Filling.PpAClaspNeg
import AJPaper.Filling.PpAClaspPos

/-!
# The companion-abelian fixed tuples of the twisted doubles (PpA, crux of Section 7.6)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`), last paragraph: "For a negative-clasp
satellite with disk twist `ℓ`, a representation `ρ_P` factoring through `Z_ℓ` kills
`μ_A λ_A^(-ℓ)`. … Define `ρ_C(γ) = ρ_P(λ_A)^(ab(γ))`. These matrices agree on the glued pair in
(twistgluing)."

In the closed braids of the library this becomes: for `a`, `c` in a group with the clasp
relation of the `ℓ`-twisted pattern,

* negative clasp (`ppa_exists_twFixedTuple_neg`): `c = compMer a (c^(-ℓ) a c^ℓ)`,
* positive clasp (`ppa_exists_twFixedTuple_pos`): `c = compMer a (c^ℓ a c^(-ℓ))`,

there is a tuple `F` on the `twStrands r s ℓ` strands, fixed by the run of `twBlocks r s ℓ σ`
(i.e. a homomorphism from the knot group), with bottom edge meridian `a`, whose block loops at
the positions of `pairBlocks r s` (`twcLoop`) are the loops `pairRevLoop r s (fun _ ↦ c) H`
prescribed by the constant companion tuple `c`: `c^(±1)` on the annulus bands. So the companion
tuple of `F` is constant `c` — the companion is represented abelianly.

Route (both signs). With `e`, `U` from `ppa_exists_twEdge_annulus h ℓ a c`, apply
`ppa_exists_edge_clasp_neg` (resp. `_pos`) to `y = fun _ ↦ c`, `Λ = c^ℓ`
(negative: `hmer` as given, `zpow_neg`; positive: `compMer (c^(-ℓ) a c^ℓ) a = c^(-ℓ) (compMer a
(c^ℓ a c^(-ℓ))) c^ℓ = c`), getting `H` and `e'`. Then `ppa_exists_fixedTuple_of_edges` with
`M = pairStrands r s`, `j₀ = twHeadTop r s` (`twHeadTop_pos_lt`),
`tail = (twcBase r s σ).tail` (`twcBase_valid`), `Lb = pairRevLoop r s (fun _ ↦ c) H`, and the
edge meridians `e'` on the levels `< M`, `ppaChainEdge M ℓ a c⁻¹` on the new levels:
* `Lb 0 = c⁻¹` (`pairRevLoop_A` for `r ≥ 3`, `pairRevLoop_run` and
  `pairRevRound r (fun _ ↦ c) t = c` for `r = 2`), so `ppaChainTop ℓ a c⁻¹ = c^(ℓ-1) a c^(-ℓ)`;
* the gap products of the untwisted list are `1`: `twcBase_eq_head_cons`, `gapPrefix_twcBase`,
  `gapPrefix_pairBlocks_eq_one` with `pairGapRels_pairRevLoop`;
* the loop equations of the tail: those of the clasp lemma (`twcBase_eq_head_cons`,
  `List.getD_cons_succ`; for `σ = true`, `twcBase_true`); a block of the tail reads only levels
  `≤ 2c`.
Finally `twBlocks_eq_chain_append`, and `twcLoop` is the loop of the chain at `q = 0`
(`List.take_left` with `length_twChain`) and `loopAt … (q + twExtra ℓ)` at `q ≥ 1`.

Checked numerically: the tuples are built and are fixed, with these loops, for
`(r, s) ∈ {(2,3), (2,5), (3,4), (3,5)}`, `|ℓ| ≤ 3`, negative clasp, and `(2,3)`, `(2,5)`,
`(3,4)`, `|ℓ| ≤ 2`, positive clasp (`SCR/A/py/abel2.py`, `abel3.py`, `clasp.py`, 120–150 digits);
and in the symmetric group `S₅` on the Lean objects (`SCR/A/lean/TestTuple.lean`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The cyclic products of a constant tuple. -/
private theorem pairRevCyc_const_ppaTuple (r : ℕ) (c : G) (n : ℕ) :
    pairRevCyc r (fun _ ↦ c) n = c ^ n := by
  simp [pairRevCyc]

/-- The torus relation of a constant tuple. -/
private theorem torusRel_const_ppaTuple (r s : ℕ) (c : G) (k : ℕ) (_hk : k < r) :
    (fun _ : ℕ ↦ c) k = pairRevCyc r (fun _ ↦ c) s * (fun _ : ℕ ↦ c) ((k + s) % r) *
      (pairRevCyc r (fun _ ↦ c) s)⁻¹ := by
  simp only [pairRevCyc_const_ppaTuple]
  rw [← pow_succ, pow_succ', mul_inv_cancel_right]

/-- The rounds of a constant tuple. -/
private theorem pairRevRound_const_ppaTuple (r : ℕ) (c : G) (t : ℕ) :
    pairRevRound r (fun _ ↦ c) t = c := by
  simp [pairRevRound, pairRevPu, pow_succ']

/-- The prescribed loop of the head band for a constant tuple. -/
private theorem pairRevLoop_const_zero_ppaTuple {r s : ℕ} (h : IsTorusPair r s) (c H : G) :
    pairRevLoop r s (fun _ ↦ c) H 0 = c⁻¹ := by
  have hB := pairRev_idxB h
  have hr := h.1
  by_cases h0 : 0 < r - 2
  · exact pairRevLoop_A (s := s) _ H 0 h0
  · rw [pairRevLoop_run _ H 0 (by omega) (by omega), pairRevRound_const_ppaTuple]

/-- The loop of a valid block only reads the chamber products up to the number of strands. -/
private theorem loopPr_congr_ppaTuple {m : ℕ} (b : SBlock) (hb : b.Valid m) (P Q : ℕ → G)
    (hPQ : ∀ n, n ≤ m → P n = Q n) : loopPr b P = loopPr b Q := by
  cases b with
  | band i j =>
    simp only [SBlock.Valid] at hb
    simp only [loopPr, hPQ (j + 1) (by omega), hPQ j (by omega), hPQ i (by omega),
      hPQ (i + 1) (by omega)]
  | neg i =>
    simp only [SBlock.Valid] at hb
    simp only [loopPr, hPQ i (by omega), hPQ (i + 1) (by omega), hPQ (i + 2) (by omega)]

/-- The chamber products up to the level `N` only read the edge meridians below `N`. -/
private theorem descProd_congr_ppaTuple (e e' : ℕ → G) (N n : ℕ) (hn : n ≤ N)
    (he : ∀ k, k < N → e' k = e k) : descProd e' 0 n = descProd e 0 n := by
  simp only [descProd]
  refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
  have := List.mem_range.1 (List.mem_reverse.1 hi)
  rw [Nat.zero_add]
  exact he i (by omega)

/-- The loop of the twisted list at the head position is the loop of the chain. -/
private theorem twcLoop_zero_ppaTuple (r s : ℕ) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G) :
    twcLoop r s ℓ σ F 0 = twcChainLoop (pairStrands r s) (twHeadTop r s) ℓ F := by
  rw [twcLoop, ite_eq_left rfl, twBlocks_eq_chain_append,
    ← length_twChain (pairStrands r s) (twHeadTop r s) ℓ, List.take_left]
  rfl

/-- The loops of the twisted list off the head position are loops of the blocks of the tail. -/
private theorem twcLoop_succ_ppaTuple (r s : ℕ) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G) (q : ℕ) :
    twcLoop r s ℓ σ F (q + 1) = loopAt (twStrands r s ℓ)
      (twChain (pairStrands r s) (twHeadTop r s) ℓ ++ (twcBase r s σ).tail) F
      (twExtra ℓ + 1 + q) := by
  rw [twcLoop, ite_eq_right (Nat.succ_ne_zero q), twBlocks_eq_chain_append,
    show q + 1 + twExtra ℓ = twExtra ℓ + 1 + q by omega]

/-- The twisted value of the head level in the form of `ppaChainTop`. -/
private theorem ppaChainTop_inv_ppaTuple (ℓ : ℤ) (a c : G) :
    ppaChainTop ℓ a c⁻¹ = c ^ (ℓ - 1) * a * c ^ (-ℓ) := by
  rw [ppaChainTop, inv_zpow', inv_zpow', neg_sub]

/-- From edge meridians of the untwisted base list with the twisted value on the head level to
a fixed tuple of the twisted list, for both clasp signs. -/
private theorem exists_twFixedTuple_of_clasp_ppaTuple {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (σ : Bool) (a c H : G) (e : ℕ → G) (he0 : e 0 = a)
    (hej : e (twHeadTop r s) = c ^ (ℓ - 1) * a * c ^ (-ℓ))
    (heq : ∀ q, 1 ≤ q → q < 2 * pairC r s + 2 →
      pairRevLoop r s (fun _ ↦ c) H q = loopPr ((twcBase r s σ).getD q (SBlock.neg 0))
        (fun n ↦ gapPrefix ((twcBase r s σ).take q) (pairRevLoop r s (fun _ ↦ c) H) n *
          descProd e 0 n)) :
    ∃ F : Fin (twStrands r s ℓ) → G,
      runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F ∧ edgeMer F 0 = a ∧
      ∀ q, q < 2 * pairC r s + 2 →
        twcLoop r s ℓ σ F q = pairRevLoop r s (fun _ ↦ c) H q := by
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  have hL0 := pairRevLoop_const_zero_ppaTuple h c H
  have hcons := twcBase_eq_head_cons h σ
  have hlen : (twcBase r s σ).tail.length = 2 * pairC r s + 1 := by
    rw [List.length_tail, twcBase, List.length_map, length_pairBlocks_rev h]
    rfl
  have hvt : ∀ b ∈ (twcBase r s σ).tail, b.Valid (pairStrands r s) := fun b hb ↦
    twcBase_valid h σ b (List.mem_of_mem_tail hb)
  have hgap : ∀ n, gapPrefix (SBlock.band 0 (twHeadTop r s) :: (twcBase r s σ).tail)
      (pairRevLoop r s (fun _ ↦ c) H) n = 1 := fun n ↦ by
    rw [← hcons, gapPrefix_twcBase]
    exact gapPrefix_pairBlocks_eq_one h _
      (pairGapRels_pairRevLoop h _ (torusRel_const_ppaTuple r s c) H) n
  have hM : 0 < pairStrands r s := by omega
  obtain ⟨F, hF, hF0, hF1, hF2⟩ := ppa_exists_fixedTuple_of_edges hj hjM ℓ (twcBase r s σ).tail
    hvt (pairRevLoop r s (fun _ ↦ c) H) hgap a
    (fun n ↦ if n < pairStrands r s then e n else ppaChainEdge (pairStrands r s) ℓ a c⁻¹ n)
    (by simp only [hM, ite_true, he0])
    (by simp only [hjM, ite_true, hej, hL0, ppaChainTop_inv_ppaTuple])
    (fun n hn ↦ by simp only [Nat.not_lt.2 hn, ite_false, hL0])
    (fun q hq ↦ by
      have h1 := heq (q + 1) (by omega) (by omega)
      rw [hcons, List.getD_cons_succ] at h1
      rw [h1]
      refine loopPr_congr_ppaTuple _ (hvt _ ?_) _ _ fun n hn ↦ ?_
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
        exact List.getElem_mem hq
      · exact congrArg _ (descProd_congr_ppaTuple e _ (pairStrands r s) n hn fun k hk ↦ by
          simp only [hk, ite_true]).symm)
  refine ⟨F, ?_, hF0, fun q hq ↦ ?_⟩
  · rw [twBlocks_eq_chain_append]
    exact hF
  · rcases Nat.eq_zero_or_pos q with rfl | hq0
    · exact (twcLoop_zero_ppaTuple r s ℓ σ F).trans hF1
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact (twcLoop_succ_ppaTuple r s ℓ σ F q').trans (hF2 q' (by omega))

/-- The head level lies on the braided annulus. -/
private theorem twHeadTop_lt_ppaTuple {r s : ℕ} (h : IsTorusPair r s) :
    twHeadTop r s < 2 * pairC r s := by
  obtain ⟨hr, hrs, hc, -⟩ := pairGap_arithRv h
  rw [twHeadTop, pairTop]
  split_ifs <;> omega

/-- Negative clasp: the fixed tuple of `twBlocks r s ℓ true` with meridian `a` and constant
companion tuple `c`. -/
theorem ppa_exists_twFixedTuple_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (a c : G)
    (hmer : c = compMer a ((c ^ ℓ)⁻¹ * a * c ^ ℓ)) :
    ∃ (H : G) (F : Fin (twStrands r s ℓ) → G),
      runTop (twStrands r s ℓ) (twBlocks r s ℓ true) F = F ∧ edgeMer F 0 = a ∧
      ∀ q, q < 2 * pairC r s + 2 →
        twcLoop r s ℓ true F q = pairRevLoop r s (fun _ ↦ c) H q := by
  have hj := twHeadTop_lt_ppaTuple h
  obtain ⟨e, U, he0, hej, hU, hTs, hT, heq⟩ := ppa_exists_twEdge_annulus h ℓ a c
  obtain ⟨H, e', he', heq'⟩ := ppa_exists_edge_clasp_neg h (fun _ ↦ c)
    (torusRel_const_ppaTuple r s c) a (c ^ ℓ) U e hU hTs hT hmer heq
  refine ⟨H, exists_twFixedTuple_of_clasp_ppaTuple h ℓ true a c H e'
    ((he' 0 (by omega)).trans he0) ((he' _ hj).trans hej) ?_⟩
  rw [twcBase_true]
  exact heq'

/-- Positive clasp: the fixed tuple of `twBlocks r s ℓ false` with meridian `a` and constant
companion tuple `c`. -/
theorem ppa_exists_twFixedTuple_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (a c : G)
    (hmer : c = compMer a (c ^ ℓ * a * (c ^ ℓ)⁻¹)) :
    ∃ (H : G) (F : Fin (twStrands r s ℓ) → G),
      runTop (twStrands r s ℓ) (twBlocks r s ℓ false) F = F ∧ edgeMer F 0 = a ∧
      ∀ q, q < 2 * pairC r s + 2 →
        twcLoop r s ℓ false F q = pairRevLoop r s (fun _ ↦ c) H q := by
  have hj := twHeadTop_lt_ppaTuple h
  have hZ : Commute c (c ^ ℓ) := (Commute.refl c).zpow_right ℓ
  have hmer' : c = compMer ((c ^ ℓ)⁻¹ * a * c ^ ℓ) a := by
    calc c = (c ^ ℓ)⁻¹ * c * c ^ ℓ := by rw [mul_assoc, hZ.eq, inv_mul_cancel_left]
      _ = (c ^ ℓ)⁻¹ * compMer a (c ^ ℓ * a * (c ^ ℓ)⁻¹) * c ^ ℓ := by rw [← hmer]
      _ = compMer ((c ^ ℓ)⁻¹ * a * c ^ ℓ) a := by
        simp only [compMer]
        group
  obtain ⟨e, U, he0, hej, hU, hTs, hT, heq⟩ := ppa_exists_twEdge_annulus h ℓ a c
  obtain ⟨H, e', he', heq'⟩ := ppa_exists_edge_clasp_pos h (fun _ ↦ c)
    (torusRel_const_ppaTuple r s c) a (c ^ ℓ) U e hU hTs hT hmer' heq
  exact ⟨H, exists_twFixedTuple_of_clasp_ppaTuple h ℓ false a c H e'
    ((he' 0 (by omega)).trans he0) ((he' _ hj).trans hej) heq'⟩

end AJConjecture
