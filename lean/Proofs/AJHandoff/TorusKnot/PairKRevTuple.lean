import Mathlib
import AJHandoff.TorusKnot.PairKPeripheral
import AJHandoff.TorusKnot.PairKRevGeneric
import AJHandoff.TorusKnot.PairKRevGapConv
import AJHandoff.TorusKnot.PairKRevSolveLoop
import AJHandoff.TorusKnot.PairKRevSolveEdge

/-!
# The fixed tuple of a companion representation and pattern data

`exists_pairFixedTuple`: for every homomorphism `ψ` from the group of `T(r, s)` to a group `G`
and every `a ∈ G` with `ψ(μ_C) = compMer a (Λ⁻¹ a Λ)`, `Λ = ψ(λ_C)`, there is a tuple on the
`2c + 1` strands of `pairBlocks r s`, fixed by the run of the block word, with bottom entry `a`
and companion tuple (`pairCompTuple` of its block loops) the images of Artin's generators of
`T(r, s)`. Equivalently: the knot group of `Wh⁻₀(T(r, s))` is the amalgam of the group of
`T(r, s)` and the group `⟨μ, Λ | [Λ, compMer μ (Λ⁻¹ μ Λ)]⟩` of the Whitehead link along the
companion boundary torus (`μ_C ↦ compMer μ (Λ⁻¹ μ Λ)`, `λ_C ↦ Λ`), i.e. the converse of the
chamber-product computation of `isWhSatellite_pairWhiteheadKnot`.

Assembly: with `y_k = ψ(x_k)` (a tuple fixed by `(σ_0 ⋯ σ_(r-2))^s`, i.e. satisfying the torus
relation of `braidRun_torusPairWord_fst`), the prescribed loops `pairRevLoop r s y H` satisfy the
gap relations and have companion tuple `y` (`AJHandoff.TorusKnot.PairKRevSolveLoop`); edge
meridians solving their loop equations (`exists_pairRevEdge`, the crux) give a tuple whose block
loops are the prescribed ones (`loopAt_eq_of_prescribed`), whose gap products are therefore `1`
(`gapPrefix_pairBlocks_eq_one`), so that it is fixed by the run (`runTop_eq_self_of_gapProd`).
-/

namespace AJConjecture

section Congr

variable {G : Type*} [Group G]

/-- The loop of a valid block only reads the chamber products up to the number of strands. -/
private theorem loopPr_congr_rt {m : ℕ} (b : SBlock) (hb : b.Valid m) (P Q : ℕ → G)
    (hPQ : ∀ n, n ≤ m → P n = Q n) : loopPr b P = loopPr b Q := by
  cases b with
  | band i j =>
    simp only [SBlock.Valid] at hb
    simp only [loopPr, hPQ (j + 1) (by omega), hPQ j (by omega), hPQ i (by omega),
      hPQ (i + 1) (by omega)]
  | neg i =>
    simp only [SBlock.Valid] at hb
    simp only [loopPr, hPQ i (by omega), hPQ (i + 1) (by omega), hPQ (i + 2) (by omega)]

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_rt (g h : ℕ → G) (a n : ℕ) (H : ∀ i, i < n → g (a + i) = h (a + i)) :
    descProd g a n = descProd h a n := by
  simp only [descProd]
  refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
  exact H i (List.mem_range.1 (List.mem_reverse.1 hi))

/-- The companion tuple only reads the loops of the first `2c + 2` blocks. -/
private theorem pairCompFun_congr_rt {r s : ℕ} (h : IsTorusPair r s) (L L' : ℕ → G)
    (hL : ∀ q, q < 2 * pairC r s + 2 → L q = L' q) (k : ℕ) :
    pairCompFun r s L k = pairCompFun r s L' k := by
  obtain ⟨hr, hrs, -⟩ := h
  have hc : r ≤ pairC r s := by
    simp only [pairC]
    nlinarith [Nat.sub_add_cancel (show 1 ≤ r by omega)]
  have hB : pairIdxB r s < 2 * pairC r s + 2 := by simp only [pairIdxB]; omega
  have hR : pairIdxR r s 0 < 2 * pairC r s + 2 := by simp only [pairIdxR, pairIdxB, ite_true]; omega
  have hw : ∀ n, n ≤ r - 1 → pairWin r s L n = pairWin r s L' n := by
    intro n hn
    unfold pairWin
    split_ifs
    · exact hL _ hR
    · rw [hL _ hB]
    · rw [hL _ hB, hL (r - 1 - n) (by omega),
        descProd_congr_rt L L' (r - n) (n - 2) fun i hi ↦ hL _ (by omega)]
  have hpre : ((List.range (r - 2 - k)).map fun i ↦ pairWin r s L (i + 1)) =
      (List.range (r - 2 - k)).map fun i ↦ pairWin r s L' (i + 1) :=
    List.map_congr_left fun i hi ↦ hw _ (by have := List.mem_range.1 hi; omega)
  rw [pairCompFun, pairCompFun, hpre, hw (r - 1 - k) (by omega)]

end Congr

/-- The prefix products of a tuple built from edge meridians are the products of the edge
meridians. -/
private theorem prePr_of_edge {G : Type*} [Group G] {m : ℕ} (e : ℕ → G) (n : ℕ) (hn : n ≤ m) :
    prePr (fun t : Fin m ↦ (descProd e 0 t)⁻¹ * e t * descProd e 0 t) n = descProd e 0 n := by
  induction n with
  | zero => simp [prePr_zero, descProd]
  | succ n ih =>
    rw [prePr_succ _ n (by omega), ih (by omega)]
    simp only [descProd, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.prod_cons, Nat.zero_add]
    group

/-- Crux of the reverse inclusion: companion representations with pattern data come from fixed
tuples of `pairBlocks r s`. -/
theorem exists_pairFixedTuple {r s : ℕ} (h : IsTorusPair r s) {G : Type*} [Group G]
    (ψ : KnotGroup (torusPairKnot r s h) →* G) (a : G)
    (hmer : ψ (meridian _) = compMer a ((ψ (longitude _))⁻¹ * a * ψ (longitude _))) :
    ∃ f : Fin (pairStrands r s) → G, runTop (pairStrands r s) (pairBlocks r s) f = f ∧
      f ⟨0, by simp [pairStrands]⟩ = a ∧
      ∀ k : Fin r, pairCompTuple r s (loopAt (pairStrands r s) (pairBlocks r s) f) k =
        ψ (PresentedGroup.of k) := by
  have hr : 0 < r := by have := h.1; omega
  -- the images of the generators, extended periodically
  set y : ℕ → G := fun i ↦ ψ (PresentedGroup.of ⟨i % r, Nat.mod_lt _ hr⟩) with hydef
  have hyk : ∀ k : Fin r, y k = ψ (PresentedGroup.of k) := fun k ↦ by
    simp only [hydef, Nat.mod_eq_of_lt k.isLt]
    rfl
  have hymod : ∀ t, y (t % r) = y t := fun t ↦ by simp only [hydef, Nat.mod_mod]
  -- the torus relation
  have hfix := braidRun_fst_of_hom (torusPairKnot r s h) ψ
  have hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹ := by
    intro k hk
    have h1 := congrFun hfix ⟨k, hk⟩
    change (braidRun r (torusPairWord r s) fun j : Fin r ↦ ψ (PresentedGroup.of j)).1 ⟨k, hk⟩ =
      ψ (PresentedGroup.of ⟨k, hk⟩) at h1
    rw [braidRun_torusPairWord_fst hr] at h1
    have hcyc : pairRevCyc r y s = ((List.range s).map fun t ↦
        ψ (PresentedGroup.of (⟨t % r, Nat.mod_lt _ hr⟩ : Fin r))).prod :=
      congrArg List.prod (List.map_congr_left fun t _ ↦ hymod t)
    rw [hcyc, hymod]
    exact (hyk ⟨k, hk⟩).trans h1.symm
  -- the meridian condition
  have hμ : ψ (meridian (torusPairKnot r s h)) = y 0 := by
    simp only [hydef, meridian, Nat.zero_mod]
  have hΛ : ψ (longitude (torusPairKnot r s h)) = pairRevLam r s y := by
    have hl : ∀ l : List (Fin r), ψ ((l.map fun j : Fin r ↦
        (PresentedGroup.of j : KnotGroup (torusPairKnot r s h))).prod) =
          (l.map fun j : Fin r ↦ y (j : ℕ)).prod := by
      intro l
      induction l with
      | nil => simp
      | cons k l ih =>
        rw [List.map_cons, List.prod_cons, map_mul, ih, List.map_cons, List.prod_cons, hyk]
    have hfull : ψ (torusFullProd h) = ((List.range r).map y).prod :=
      (hl (List.finRange r)).trans (by rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl)
    rw [longitude_torusPairKnot, map_mul, map_zpow, map_pow, hfull, hμ, pairRevLam]
  rw [hμ, hΛ] at hmer
  -- the prescribed loops and the edge meridians
  obtain ⟨H, e, he0, heq⟩ := exists_pairRevEdge h y hy a hmer
  set ℓ := pairRevLoop r s y H with hℓ
  set f : Fin (pairStrands r s) → G := fun t ↦ (descProd e 0 t)⁻¹ * e t * descProd e 0 t
    with hf
  have hv := pairBlocks_valid h
  have hlen := length_pairBlocks_rev h
  have hloop : ∀ q < (pairBlocks r s).length, ℓ q = loopPr ((pairBlocks r s).getD q
      (SBlock.neg 0)) (fun n ↦ gapPrefix ((pairBlocks r s).take q) ℓ n *
        prePr f n) := by
    intro q hq
    rw [heq q (by omega)]
    have hmem : (pairBlocks r s).getD q (SBlock.neg 0) ∈ pairBlocks r s := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.getElem_mem hq
    refine loopPr_congr_rt _ (hv _ hmem) _ _ fun n hn ↦ ?_
    rw [prePr_of_edge e n hn]
  obtain ⟨hL, hG⟩ := loopAt_eq_of_prescribed (pairBlocks r s) hv f ℓ hloop
  have hgap : PairGapRels r s ℓ := pairGapRels_pairRevLoop h y hy H
  refine ⟨f, runTop_eq_self_of_gapProd (pairBlocks r s) hv f fun n ↦ ?_, ?_, fun k ↦ ?_⟩
  · rw [hG, gapPrefix_pairBlocks_eq_one h ℓ hgap]
  · simp only [hf, descProd, List.range_zero, List.reverse_nil, List.map_nil, List.prod_nil,
      inv_one, one_mul, mul_one]
    exact he0
  · rw [pairCompTuple, pairCompFun_congr_rt h _ ℓ (fun q hq ↦ hL q (by omega)),
      pairCompFun_pairRevLoop h y H k k.isLt, hyk]

end AJConjecture
