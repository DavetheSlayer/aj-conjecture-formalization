import Mathlib
import AJHandoff.TorusKnot.PairKPeriGeneric
import AJTwist.Knot.TwKKnot
import AJPaper.Filling.PpATuple
import AJPaper.Filling.PpAForward

/-!
# The companion-abelian representations of the twisted doubles (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`), last paragraph: "The resulting
satellite representation has the same outer eigenvalue pair."

For `a`, `c` in a group `G` with the clasp relation of the `ℓ`-twisted pattern there is a
homomorphism from the knot group of the closed braid `twWhiteheadKnot r s h ℓ σ` to `G` with
meridian `a` whose longitude is the outer longitude word of the pattern in `a` and the axis
meridian `t = c^ℓ`:

* `ppa_exists_rep_twWhiteheadKnot_neg` (`σ = true`, `c = compMer a (t⁻¹ a t)`):
  `λ ↦ a² t a⁻¹ t⁻¹ a (t⁻¹ a t)⁻¹ a⁻¹`;
* `ppa_exists_rep_twWhiteheadKnot_pos` (`σ = false`, `c = compMer a (t a t⁻¹)`):
  `λ⁻¹ ↦ a² t⁻¹ a⁻¹ t a (t a t⁻¹)⁻¹ a⁻¹`.

Route. Let `H`, `F` be given by `ppa_exists_twFixedTuple_neg` (resp. `_pos`). The braid relations
hold for a tuple fixed by the braid (the private `revLift_artinRels_of_fixed_reduce` of
`AJHandoff.TorusKnot.PairKRevReduce`; `braidRun_fst_apply`, `lift_artinWord_snd`), so
`ρ = PresentedGroup.toGroup` sends the generators to `F`; `ρ (meridian) = F 0 = edgeMer F 0 = a`
(`edgeMer_zero`). By `map_longitude_eq_orbitLoop` (block list `twBlocks r s ℓ σ`,
`twBlocks_valid`) `ρ (longitude)` is the orbit loop of `F` and commutes with `a`, so
`ppa_isWhPattern_of_fixed_neg` (resp. `_pos`) applies. Its companion data are computed from the
loops: the companion tuple only reads the loops of the positions `< 2c + 2` (the private
`pairCompFun_congr_rt` of `AJHandoff.TorusKnot.PairKRevTuple`), so
`pairCompFun r s (twcLoop …) k = pairCompFun r s (pairRevLoop r s (fun _ ↦ c) H) k = c`
(`pairCompFun_pairRevLoop`) for `k < r`, and
`pairCompLong r s (twcLoop …) = (c^r)^s c^(-rs) = 1` (`List.prod` of a constant list,
`pow_mul`, `zpow_natCast`). Hence `t = c^ℓ`, and the second relation of `IsWhPattern` is the
formula.

Checked numerically (`SCR/A/py/abel2.py`, `abel3.py`: the library's longitude of the tuple
equals the word, for `(r, s) ∈ {(2,3), (2,5), (3,4), (3,5)}`, `|ℓ| ≤ 3`, and for the positive
clasp of `(2,3)`, `|ℓ| ≤ 2`), and in `S₅` on the Lean objects (`SCR/A/lean/TestTuple.lean`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The braid relations hold for a tuple fixed by the braid. -/
private theorem lift_artinRels_of_fixed_ppaRealize (K : BraidKnot)
    (f : Fin K.strands → G) (hf : (braidRun K.strands K.word f).1 = f) :
    ∀ x ∈ artinRels K, FreeGroup.lift f x = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, map_mul, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, lift_artinWord_snd, ← braidRun_fst_apply, hf]

/-- A tuple fixed by the run of the twisted block list is a representation of the knot group:
its meridian is the bottom edge meridian, its longitude the orbit loop, and they commute. -/
private theorem exists_rep_of_fixed_ppaRealize {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (σ : Bool) (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) :
    ∃ ρ : KnotGroup (twWhiteheadKnot r s h ℓ σ) →* G,
      ρ (meridian (twWhiteheadKnot r s h ℓ σ)) = edgeMer F 0 ∧
        ρ (longitude (twWhiteheadKnot r s h ℓ σ)) =
          orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F ∧
        orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F * edgeMer F 0 =
          edgeMer F 0 * orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F := by
  let ρ : KnotGroup (twWhiteheadKnot r s h ℓ σ) →* G :=
    PresentedGroup.toGroup (f := F)
      (lift_artinRels_of_fixed_ppaRealize (twWhiteheadKnot r s h ℓ σ) F hF)
  have hρ : ∀ t, ρ (PresentedGroup.of t) = F t := fun t ↦ PresentedGroup.toGroup.of _
  have hgen : (fun t : Fin (twWhiteheadKnot r s h ℓ σ).strands ↦ ρ (PresentedGroup.of t)) = F :=
    funext hρ
  have hmer : ρ (meridian (twWhiteheadKnot r s h ℓ σ)) = edgeMer F 0 :=
    (hρ _).trans (edgeMer_zero F (twWhiteheadKnot r s h ℓ σ).strands_pos).symm
  obtain ⟨hl, hc⟩ := map_longitude_eq_orbitLoop (twWhiteheadKnot r s h ℓ σ) (twBlocks r s ℓ σ)
    rfl (twBlocks_valid h ℓ σ) ρ
  rw [hgen] at hl hc
  rw [hmer] at hc
  exact ⟨ρ, hmer, hl, hc⟩

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_ppaRealize (g g' : ℕ → G) (a n : ℕ)
    (hg : ∀ i, i < n → g (a + i) = g' (a + i)) : descProd g a n = descProd g' a n := by
  simp only [descProd]
  refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
  exact hg i (List.mem_range.1 (List.mem_reverse.1 hi))

/-- The companion tuple only reads the loops of the first `2c + 2` blocks. -/
private theorem pairCompFun_congr_ppaRealize {r s : ℕ} (h : IsTorusPair r s) (L L' : ℕ → G)
    (hL : ∀ q, q < 2 * pairC r s + 2 → L q = L' q) (k : ℕ) :
    pairCompFun r s L k = pairCompFun r s L' k := by
  obtain ⟨hr, hrs, -⟩ := h
  have hc : r ≤ pairC r s := by
    simp only [pairC]
    nlinarith [Nat.sub_add_cancel (show 1 ≤ r by omega)]
  have hB : pairIdxB r s < 2 * pairC r s + 2 := by simp only [pairIdxB]; omega
  have hR : pairIdxR r s 0 < 2 * pairC r s + 2 := by
    simp only [pairIdxR, pairIdxB, ite_true]; omega
  have hw : ∀ n, n ≤ r - 1 → pairWin r s L n = pairWin r s L' n := by
    intro n hn
    unfold pairWin
    split_ifs
    · exact hL _ hR
    · rw [hL _ hB]
    · rw [hL _ hB, hL (r - 1 - n) (by omega),
        descProd_congr_ppaRealize L L' (r - n) (n - 2) fun i hi ↦ hL _ (by omega)]
  have hpre : ((List.range (r - 2 - k)).map fun i ↦ pairWin r s L (i + 1)) =
      (List.range (r - 2 - k)).map fun i ↦ pairWin r s L' (i + 1) :=
    List.map_congr_left fun i hi ↦ hw _ (by have := List.mem_range.1 hi; omega)
  rw [pairCompFun, pairCompFun, hpre, hw (r - 1 - k) (by omega)]

/-- The companion data of loops that agree with the prescribed loops of the constant tuple `c`:
the companion meridian is `c` and the companion longitude is trivial. -/
private theorem compData_const_ppaRealize {r s : ℕ} (h : IsTorusPair r s) (c H : G) (L : ℕ → G)
    (hL : ∀ q, q < 2 * pairC r s + 2 → L q = pairRevLoop r s (fun _ ↦ c) H q) :
    pairCompFun r s L 0 = c ∧ pairCompLong r s L = 1 := by
  have hk : ∀ k, k < r → pairCompFun r s L k = c := fun k hk ↦ by
    rw [pairCompFun_congr_ppaRealize h L _ hL k, pairCompFun_pairRevLoop h _ H k hk]
  have hr := h.1
  refine ⟨hk 0 (by omega), ?_⟩
  have hl : (List.finRange r).map (pairCompTuple r s L) = List.replicate r c := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb ↦ ?_⟩
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
    exact hk k k.2
  rw [pairCompLong, hl, List.prod_replicate, hk 0 (by omega), ← pow_mul, zpow_neg, zpow_natCast,
    mul_inv_cancel]

/-- Negative clasp: the representation of the knot group of `W_(-,ℓ)(T(r, s))` with meridian `a`
that is abelian on the companion, with value `c` on its meridian. -/
theorem ppa_exists_rep_twWhiteheadKnot_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (a c : G)
    (hmer : c = compMer a ((c ^ ℓ)⁻¹ * a * c ^ ℓ)) :
    ∃ ρ : KnotGroup (twWhiteheadKnot r s h ℓ true) →* G,
      ρ (meridian (twWhiteheadKnot r s h ℓ true)) = a ∧
        ρ (longitude (twWhiteheadKnot r s h ℓ true)) =
          a ^ 2 * c ^ ℓ * a⁻¹ * (c ^ ℓ)⁻¹ * a * ((c ^ ℓ)⁻¹ * a * c ^ ℓ)⁻¹ * a⁻¹ := by
  obtain ⟨H, F, hF, hF0, hL⟩ := ppa_exists_twFixedTuple_neg h ℓ a c hmer
  obtain ⟨ρ, hm, hl, hc⟩ := exists_rep_of_fixed_ppaRealize h ℓ true F hF
  obtain ⟨hz, hΛ⟩ := compData_const_ppaRealize h c H _ hL
  have hp := (ppa_isWhPattern_of_fixed_neg h ℓ F hF hc).2
  rw [hz, hΛ, one_mul, hF0] at hp
  exact ⟨ρ, hm.trans hF0, hl.trans hp⟩

/-- Positive clasp: the representation of the knot group of `W_(+,ℓ)(T(r, s))` with meridian `a`
that is abelian on the companion, with value `c` on its meridian. -/
theorem ppa_exists_rep_twWhiteheadKnot_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (a c : G)
    (hmer : c = compMer a (c ^ ℓ * a * (c ^ ℓ)⁻¹)) :
    ∃ ρ : KnotGroup (twWhiteheadKnot r s h ℓ false) →* G,
      ρ (meridian (twWhiteheadKnot r s h ℓ false)) = a ∧
        (ρ (longitude (twWhiteheadKnot r s h ℓ false)))⁻¹ =
          a ^ 2 * (c ^ ℓ)⁻¹ * a⁻¹ * c ^ ℓ * a * (c ^ ℓ * a * (c ^ ℓ)⁻¹)⁻¹ * a⁻¹ := by
  obtain ⟨H, F, hF, hF0, hL⟩ := ppa_exists_twFixedTuple_pos h ℓ a c hmer
  obtain ⟨ρ, hm, hl, hc⟩ := exists_rep_of_fixed_ppaRealize h ℓ false F hF
  obtain ⟨hz, hΛ⟩ := compData_const_ppaRealize h c H _ hL
  have hp := (ppa_isWhPattern_of_fixed_pos h ℓ F hF hc).2
  rw [hz, hΛ, one_mul, hF0, inv_inv] at hp
  refine ⟨ρ, hm.trans hF0, ?_⟩
  rw [hl]
  exact hp

end AJConjecture
