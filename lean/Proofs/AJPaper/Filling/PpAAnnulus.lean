import Mathlib
import AJHandoff.TorusKnot.PairKRevSolveAnnulus
import AJPaper.Filling.PpASide

/-!
# The edge meridians along the annulus for an abelian companion and a twisted head band (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`), last paragraph: "Define
`ρ_C(γ) = ρ_P(λ_A)^(ab(γ))`": the companion is represented through its abelianization, so every
generator of the group of `T(r, s)` goes to the same element `c` (the image of the axis
longitude `λ_A`), and the companion longitude goes to `1`.

`ppa_exists_twEdge_annulus`: for `a`, `c` in a group and `ℓ ∈ ℤ` there are edge meridians
`e_0 = a, e_1, …, e_(2c-1)` on the levels of the braided annulus of `pairBlocks r s` such that

* the level `j₀ = twHeadTop r s` carries the twisted value `c^(ℓ-1) a c^(-ℓ)` (untwisted:
  `c⁻¹ a`, the equation of the head band, whose prescribed loop is `c⁻¹`);
* the loop equation of every block other than the head band, the top-right climb `C` and the
  two Hopf letters holds for the prescribed loops `pairRevLoop r s (fun _ ↦ c) H` (they are
  `c^(±1)` on the annulus bands);
* the two ends of the annulus path are `e_(T-s) = U a c⁻¹ U⁻¹`, `e_T = U (c^(-ℓ) a c^ℓ) U⁻¹`
  for some `U` commuting with `c`: the ends of `exists_pairRevEdge_annulus` with the companion
  longitude replaced by `c^ℓ`, the image of `λ_C μ_C^ℓ` (eq. (twistgluing)).

Route. Apply `exists_pairRevEdge_annulus h (fun _ ↦ c)` (the torus relation is trivial for a
constant tuple: `pairRevCyc r (fun _ ↦ c) s = c ^ s`), getting `e⁰`, `U⁰` with
`e⁰_(T-s) = U⁰ a c⁻¹ U⁰⁻¹`, `e⁰_T = U⁰ a U⁰⁻¹` (`pairRevLam r s (fun _ ↦ c) = 1`),
`U⁰⁻¹ c U⁰ = c`, and all annulus equations. Put
`e n = c^ℓ e⁰ n c^(-ℓ)` if `ppaSide r s n`, and `e n = e⁰ n` otherwise, and `U = c^ℓ U⁰`.
* `e 0 = a`, the two ends: `ppaSide_ends` and `U⁰ c = c U⁰`.
* `e j₀`: the equation of the head band for `e⁰` (position `0`, `gapPrefix [] = 1`,
  `loopPr_band_edge`) is `e⁰ j₀ = c⁻¹ a`; the prescribed loop at `0` is `c⁻¹` for `r ≥ 3`
  (`pairRevLoop_A`) and for `r = 2` (`pairRevLoop_run`; `pairRevRound r (fun _ ↦ c) t = c`).
* the equation of a block `q` as in the statement: by `ppaSide_band` it is a band `b(i, j)`
  with `j ≤ T` and both levels on the same part. By `loopPr_band_edge` the equation reads
  `ℓ_q = G(j+1) e_j G(j)⁻¹ (G(i) e_i⁻¹ G(i+1)⁻¹)`. If both levels are on the first part it is
  the equation for `e⁰`. Otherwise conjugate the equation for `e⁰` by `c^ℓ`: `ℓ_q` is a power of
  `c`, and so is every `G(n) = gapPrefix (take q) … n` that is read, because the prescribed
  loops other than `H^(±1)` are `c^(±1)` (`pairRevLoop_A`, `_run`, `_B`, `_R`, `_C`, `_Dp` for a
  constant tuple) and the Hopf letters only contribute at the level `2c`, which is read only
  for `j = T`, by the round `R_0` standing before the first Hopf letter (use
  `gapPrefix_eq_prod_range` and `pairBlk_lohiRv`: a product of elements commuting with `c`
  commutes with `c`).

Checked exactly in the free group on `a`, `c` for 28 pairs `(r, s)` with `r ≤ 6`, `s ≤ 13` and
`|ℓ| ≤ 4` (`SCR/A/py/exact.py`, `check_twisted`), and on the Lean objects in the symmetric group
`S₅` for `(2,3)`, `(2,5)`, `(3,4)`, `(3,5)` (`SCR/A/lean/TestAnnulus.lean`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The cyclic products of a constant tuple. -/
private theorem pairRevCyc_const_ppaAnnulus (r : ℕ) (c : G) (n : ℕ) :
    pairRevCyc r (fun _ ↦ c) n = c ^ n := by
  simp [pairRevCyc]

/-- The rounds of a constant tuple. -/
private theorem pairRevRound_const_ppaAnnulus (r : ℕ) (c : G) (t : ℕ) :
    pairRevRound r (fun _ ↦ c) t = c := by
  simp [pairRevRound, pairRevPu, pow_succ']

/-- The longitude of a constant tuple is trivial. -/
private theorem pairRevLam_const_ppaAnnulus (r s : ℕ) (c : G) :
    pairRevLam r s (fun _ ↦ c) = 1 := by
  simp only [pairRevLam, List.map_const', List.prod_replicate, List.length_range, ← pow_mul,
    zpow_neg, zpow_natCast, mul_inv_cancel]

/-- The prescribed loops of a constant tuple other than the Hopf loops commute with `c`. -/
private theorem pairRevLoop_const_commute_ppaAnnulus (r s : ℕ) (c H : G) (q : ℕ)
    (h1 : q ≠ pairIdxH1 r s) (h2 : q ≠ pairIdxH2 r s) :
    Commute (pairRevLoop r s (fun _ ↦ c) H q) c := by
  simp only [pairIdxH1, pairIdxH2] at h1 h2
  simp only [pairRevLoop, pairRevRound_const_ppaAnnulus]
  split_ifs
  · exact (Commute.refl c).inv_left
  · exact (Commute.refl c).inv_left
  · exact (Commute.refl c).inv_left
  · exact Commute.refl c
  · exact Commute.refl c
  · exact (Commute.refl c).inv_left
  · exact Commute.refl c
  · exact Commute.one_left c

/-- The prescribed loop of the head band for a constant tuple. -/
private theorem pairRevLoop_const_zero_ppaAnnulus {r s : ℕ} (h : IsTorusPair r s) (c H : G) :
    pairRevLoop r s (fun _ ↦ c) H 0 = c⁻¹ := by
  have hB := pairRev_idxB h
  have hr := h.1
  by_cases h0 : 0 < r - 2
  · exact pairRevLoop_A (s := s) _ H 0 h0
  · rw [pairRevLoop_run _ H 0 (by omega) (by omega), pairRevRound_const_ppaAnnulus]

/-- A gap product of loops commuting with `x` commutes with `x`. -/
private theorem gapPrefix_commute_ppaAnnulus (bs : List SBlock) (L : ℕ → G) (n : ℕ) (x : G)
    (hL : ∀ q, q < bs.length → (bs.getD q (SBlock.neg 0)).lo ≤ n →
      n ≤ (bs.getD q (SBlock.neg 0)).hi → Commute (L q) x) :
    Commute (gapPrefix bs L n) x := by
  induction bs generalizing L with
  | nil => exact Commute.one_left x
  | cons b bs ih =>
    rw [gapPrefix]
    refine Commute.mul_left (ih _ fun q hq h1 h2 ↦ hL (q + 1) (by simpa using hq) h1 h2) ?_
    split_ifs with hb
    · exact hL 0 (by simp) hb.1 hb.2
    · exact Commute.one_left x

/-- The gap products of the prescribed loops of a constant tuple commute with `c` at every
level other than the Hopf level `2c`. -/
private theorem gapPrefix_take_commute_ppaAnnulus {r s : ℕ} (h : IsTorusPair r s) (c H : G)
    (q n : ℕ) (hq : q < 2 * pairC r s + 2) (hn : n ≠ 2 * pairC r s) :
    Commute (gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s (fun _ ↦ c) H) n) c := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  refine gapPrefix_commute_ppaAnnulus _ _ _ _ fun q' hq' h1 h2 ↦ ?_
  rw [List.length_take, length_pairBlocks_rev h] at hq'
  have hq'' : q' < q := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq'', ← List.getD_eq_getElem?_getD,
    pairBlocks_getDRv h q' (by omega)] at h1 h2
  have hl := pairBlk_lohiRv h q'
  refine pairRevLoop_const_commute_ppaAnnulus r s c H q' ?_ ?_
  · simp only [pairIdxH1, pairIdxB]
    omega
  · simp only [pairIdxH2]
    omega

/-- Conjugating the two edge meridians of a band equation by an element commuting with the
loop and the gap products. -/
private theorem band_eq_conj_ppaAnnulus (Z L g1 g2 g3 g4 x y : G) (hL : Commute L Z)
    (h1 : Commute g1 Z) (h2 : Commute g2 Z) (h3 : Commute g3 Z) (h4 : Commute g4 Z)
    (h0 : L = g1 * x * g2⁻¹ * (g3 * y⁻¹ * g4⁻¹)) :
    L = g1 * (Z * x * Z⁻¹) * g2⁻¹ * (g3 * (Z * y * Z⁻¹)⁻¹ * g4⁻¹) := by
  have hφ : ∀ g, Commute g Z → MulAut.conj Z g = g := fun g hg ↦ by
    rw [MulAut.conj_apply, ← hg.eq]
    group
  calc L = MulAut.conj Z L := (hφ L hL).symm
    _ = MulAut.conj Z (g1 * x * g2⁻¹ * (g3 * y⁻¹ * g4⁻¹)) := by rw [← h0]
    _ = _ := by
      simp only [map_mul, map_inv, hφ g1 h1, hφ g2 h2, hφ g3 h3, hφ g4 h4, MulAut.conj_apply]

/-- The edge meridians along the annulus for the constant companion tuple `c`, with the head
band twisted `ℓ` times. -/
theorem ppa_exists_twEdge_annulus {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (a c : G) :
    ∃ (e : ℕ → G) (U : G), e 0 = a ∧ e (twHeadTop r s) = c ^ (ℓ - 1) * a * c ^ (-ℓ) ∧
      U⁻¹ * c * U = c ∧
      e (2 * pairC r s - 1 - s) = U * a * c⁻¹ * U⁻¹ ∧
      e (2 * pairC r s - 1) = U * ((c ^ ℓ)⁻¹ * a * c ^ ℓ) * U⁻¹ ∧
      ∀ (H : G) (q : ℕ), 1 ≤ q → q < 2 * pairC r s + 2 → q ≠ pairIdxC r s →
        q ≠ pairIdxH1 r s → q ≠ pairIdxH2 r s →
        pairRevLoop r s (fun _ ↦ c) H q =
          loopPr ((pairBlocks r s).getD q (SBlock.neg 0))
            (fun n ↦ gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s (fun _ ↦ c) H) n *
              descProd e 0 n) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairGap_arithRv h
  have hB := pairRev_idxB h
  obtain ⟨e, U, he0, hU, hTs, hT, heq⟩ := exists_pairRevEdge_annulus h (fun _ ↦ c)
    (fun k _ ↦ by
      simp only [pairRevCyc_const_ppaAnnulus]
      rw [← pow_succ, pow_succ', mul_inv_cancel_right]) a
  simp only [pairRevLam_const_ppaAnnulus, inv_one, one_mul, mul_one] at hT
  obtain ⟨hs0, hsj, hsT, hsTs⟩ := ppaSide_ends h
  have hUc : Commute U c := by
    rw [Commute, SemiconjBy]
    conv_lhs => rw [← hU]
    group
  have hUZ : Commute U (c ^ ℓ) := hUc.zpow_right ℓ
  have hj0 : e (twHeadTop r s) = c⁻¹ * a := by
    have h0 := heq 1 0 (by omega) (by simp only [pairIdxC]; omega)
      (by simp only [pairIdxH1]; omega) (by simp only [pairIdxH2]; omega)
    have hb0 : (pairBlocks r s).getD 0 (SBlock.neg 0) = SBlock.band 0 (twHeadTop r s) := by
      rw [pairBlocks_eq_head_cons h]
      rfl
    rw [hb0, loopPr_band_edge, pairRevLoop_const_zero_ppaAnnulus h] at h0
    simp only [List.take_zero, gapPrefix, one_mul, inv_one, mul_one, he0] at h0
    rw [h0]
    group
  refine ⟨fun n ↦ if ppaSide r s n then c ^ ℓ * e n * (c ^ ℓ)⁻¹ else e n, c ^ ℓ * U, ?_, ?_, ?_,
    ?_, ?_, fun H q hq1 hq hC hH1 hH2 ↦ ?_⟩
  · simp only [hs0, Bool.false_eq_true, ite_false, he0]
  · simp only [hsj, ite_true, hj0, zpow_sub_one, zpow_neg, mul_assoc]
  · rw [show (c ^ ℓ * U)⁻¹ * c * (c ^ ℓ * U) = U⁻¹ * c * U by group]
    exact hU
  · simp only [hsTs, ite_true, hTs]
    group
  · simp only [hsT, Bool.false_eq_true, ite_false, hT]
    rw [show c ^ ℓ * U * ((c ^ ℓ)⁻¹ * a * c ^ ℓ) * (c ^ ℓ * U)⁻¹ =
      c ^ ℓ * (U * (c ^ ℓ)⁻¹) * a * (c ^ ℓ * U⁻¹) * (c ^ ℓ)⁻¹ by group,
      hUZ.inv_right.eq, hUZ.symm.inv_right.eq]
    group
  · obtain ⟨i, j, hblk, hij, hj, hside⟩ := ppaSide_band h q hq1 hq hC hH1 hH2
    have h0 := heq H q hq hC hH1 hH2
    rw [hblk, loopPr_band_edge] at h0 ⊢
    cases hsj' : ppaSide r s j with
    | false =>
      simp only [hside, hsj', Bool.false_eq_true, ite_false]
      exact h0
    | true =>
      have hjT : j ≠ 2 * pairC r s - 1 := fun hj' ↦ by
        rw [hj', hsT] at hsj'
        exact Bool.false_ne_true hsj'
      have hG : ∀ n, n ≠ 2 * pairC r s → Commute
          (gapPrefix ((pairBlocks r s).take q) (pairRevLoop r s (fun _ ↦ c) H) n) (c ^ ℓ) :=
        fun n hn ↦ (gapPrefix_take_commute_ppaAnnulus h c H q n hq hn).zpow_right ℓ
      simp only [hside, hsj', ite_true]
      exact band_eq_conj_ppaAnnulus _ _ _ _ _ _ _ _
        ((pairRevLoop_const_commute_ppaAnnulus r s c H q hH1 hH2).zpow_right ℓ)
        (hG _ (by omega)) (hG _ (by omega)) (hG _ (by omega)) (hG _ (by omega)) h0

end AJConjecture
