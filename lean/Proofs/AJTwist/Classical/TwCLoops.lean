import Mathlib
import AJTwist.Classical.TwCRestrict
import AJTwist.Classical.TwCChain
import AJTwist.Classical.TwCGapForward

/-!
# The block loops of a twisted block list at the positions of `pairBlocks r s`

For a tuple `F` on `twStrands r s ℓ` strands, `twcLoop r s ℓ σ F q` is the loop of the block of
`twBlocks r s ℓ σ` that stands for the block of `pairBlocks r s` at position `q`: for `q ≥ 1`
the loop of the same block (now at position `q + twExtra ℓ`), and for the head block `q = 0`
the loop of the chain (the ratio of the chamber products of level `1` above and below it).

`pairGapRels_twcLoop`: if `F` is fixed by the run of `twBlocks r s ℓ σ`, these loops satisfy
the gap relations `PairGapRels r s` of the untwisted block list, for both clasp signs. So every
theorem of the library stated for loops with `PairGapRels` applies to them: the companion tuple
(`pairCompTuple_fixed`), the rounds (`AJHandoff.TorusKnot.PairKOrbRounds`), the pure forms
(`pairOrb_step`), `pairOrb_compFun_zero`, `pairOrb_compLong`.

Route: all gap products of `F` are `1` (`prePr_runTop`). Split the list with
`twBlocks_eq_chain_append` and `gapProd_append`; the blocks of the tail live on the old strands
(`twcBase_valid`), so the chain restores the new entries (`runTop_apply_of_ge` and `F` fixed),
and by `prePr_runTop_twChain` its gap factor is the chain loop at the levels `1, …, j₀` — the
gap of the head block `b(0, j₀)` — and `1` at the other old levels. With `gapProd_resTuple`,
`loopAt_resTuple` and `gapPrefix_eq_prod_range` this is
`gapPrefix (twcBase r s σ) (twcLoop r s ℓ σ F) n = 1` for all `n`; conclude with
`gapPrefix_twcBase` and `pairGapRels_of_gapPrefix`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The block loops of `twBlocks r s ℓ σ` on the tuple `F`, indexed by the positions of
`pairBlocks r s`; at the head position `0` the loop of the chain. -/
def twcLoop (r s : ℕ) (ℓ : ℤ) (σ : Bool) (F : Fin (twStrands r s ℓ) → G) (q : ℕ) : G :=
  if q = 0 then
    prePr (runTop (twStrands r s ℓ) ((twBlocks r s ℓ σ).take (twExtra ℓ + 1)) F) 1 *
      (prePr F 1)⁻¹
  else loopAt (twStrands r s ℓ) (twBlocks r s ℓ σ) F (q + twExtra ℓ)

/-- The gap products of a block list are the gap products of its block loops. -/
private theorem gapProd_eq_gapPrefix_twCLoops {m : ℕ} (bs : List SBlock) (f : Fin m → G)
    (n : ℕ) : gapProd m bs f n = gapPrefix bs (loopAt m bs f) n := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    have hs : (fun q ↦ loopAt m (b :: bs) f (q + 1)) = loopAt m bs (b.step m f) := by
      funext q
      simp only [loopAt, List.getD_cons_succ, List.take_succ_cons, runTop_cons]
    have h0 : loopAt m (b :: bs) f 0 = b.loop f := by
      simp only [loopAt, List.getD_cons_zero, List.take_zero, runTop_nil]
    rw [gapProd, gapPrefix, hs, h0, ih, SBlock.gapLoop]

/-- Prescribed loops have trivial gap product at a level above all gap intervals. -/
private theorem gapPrefix_eq_one_twCLoops (bs : List SBlock) (L : ℕ → G) (n : ℕ)
    (hn : ∀ b ∈ bs, b.hi < n) : gapPrefix bs L n = 1 := by
  induction bs generalizing L with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hn
    rw [gapPrefix, ih _ hn.2, ite_eq_right (by omega), mul_one]

/-- The upper end of the gap interval of a block living on `m` strands is below `m`. -/
private theorem hi_lt_twCLoops {m : ℕ} (b : SBlock) (hb : b.Valid m) : b.hi < m := by
  cases b <;> simp only [SBlock.Valid, SBlock.hi] at hb ⊢ <;> omega

/-- The first `twExtra ℓ + 1` blocks of the twisted list are the chain. -/
private theorem take_twBlocks_twCLoops (r s : ℕ) (ℓ : ℤ) (σ : Bool) :
    (twBlocks r s ℓ σ).take (twExtra ℓ + 1) = twChain (pairStrands r s) (twHeadTop r s) ℓ := by
  rw [twBlocks_eq_chain_append, ← length_twChain (pairStrands r s) (twHeadTop r s) ℓ,
    List.take_left]

/-- The blocks of the tail of the base list live on the old strands. -/
private theorem twcBase_tail_valid_twCLoops {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    ∀ b ∈ (twcBase r s σ).tail, b.Valid (pairStrands r s) := fun b hb ↦
  twcBase_valid h σ b (List.mem_of_mem_tail hb)

/-- The chain of a fixed tuple restores the new entries. -/
private theorem runTop_twChain_new_twCLoops {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F)
    (k : Fin (twStrands r s ℓ)) (hk : pairStrands r s ≤ (k : ℕ)) :
    runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F k = F k := by
  have h1 := runTop_apply_of_ge (Nat.le_add_right (pairStrands r s) (twExtra ℓ))
    (twcBase r s σ).tail (twcBase_tail_valid_twCLoops h σ)
    (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) k hk
  rw [← h1]
  conv_rhs => rw [← hF, twBlocks_eq_chain_append, runTop_append]
  rfl

/-- The loop at the head position is the loop of the chain. -/
private theorem twcLoop_zero_twCLoops (r s : ℕ) (ℓ : ℤ) (σ : Bool) (F : Fin (twStrands r s ℓ) → G) :
    twcLoop r s ℓ σ F 0 = twcChainLoop (pairStrands r s) (twHeadTop r s) ℓ F := by
  rw [twcLoop, ite_eq_left rfl, take_twBlocks_twCLoops]
  rfl

/-- The loops off the head position are the block loops of the tail of the base list, run on
the tuple above the chain. -/
private theorem twcLoop_succ_twCLoops (r s : ℕ) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G) (q : ℕ) :
    twcLoop r s ℓ σ F (q + 1) = loopAt (twStrands r s ℓ) (twcBase r s σ).tail
      (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) q := by
  rw [twcLoop, ite_eq_right (Nat.succ_ne_zero q), twBlocks_eq_chain_append,
    show q + 1 + twExtra ℓ = (twChain (pairStrands r s) (twHeadTop r s) ℓ).length + q by
      rw [length_twChain]; omega,
    loopAt_append_right]

/-- The gap factor of the chain of a fixed tuple at an old level. -/
private theorem gapProd_twChain_twCLoops {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) {n : ℕ}
    (hn : n ≤ pairStrands r s) :
    gapProd (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F n =
      if 1 ≤ n ∧ n ≤ twHeadTop r s then twcLoop r s ℓ σ F 0 else 1 := by
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  have h1 := (prePr_runTop _ (twChain_valid hj hjM ℓ) F n).symm.trans
    (prePr_runTop_twChain hj hjM ℓ F (runTop_twChain_new_twCLoops h ℓ σ F hF) hn)
  rw [twcLoop_zero_twCLoops]
  by_cases hc : 1 ≤ n ∧ n ≤ twHeadTop r s
  · rw [ite_eq_left hc] at h1 ⊢
    exact mul_right_cancel h1
  · rw [ite_eq_right hc] at h1 ⊢
    exact mul_right_cancel (h1.trans (one_mul _).symm)

/-- The loops of a fixed tuple of a twisted block list satisfy the gap relations of
`pairBlocks r s`. -/
theorem pairGapRels_twcLoop {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) :
    PairGapRels r s (twcLoop r s ℓ σ F) := by
  refine pairGapRels_of_gapPrefix h _ fun n ↦ ?_
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  rw [← gapPrefix_twcBase r s σ]
  rcases Nat.lt_or_ge (pairStrands r s) n with hn | hn
  · exact gapPrefix_eq_one_twCLoops _ _ n fun b hb ↦
      (hi_lt_twCLoops b (twcBase_valid h σ b hb)).trans hn
  · have hall : gapProd (twStrands r s ℓ) (twBlocks r s ℓ σ) F n = 1 := by
      have hv : ∀ b ∈ twBlocks r s ℓ σ, b.Valid (twStrands r s ℓ) := twBlocks_valid h ℓ σ
      have h1 := prePr_runTop _ hv F n
      rw [hF] at h1
      exact (mul_eq_right.1 h1.symm)
    rw [twBlocks_eq_chain_append, gapProd_append, gapProd_twChain_twCLoops h ℓ σ F hF hn,
      gapProd_eq_gapPrefix_twCLoops] at hall
    rw [twcBase_eq_head_cons h σ, gapPrefix]
    have hs : (fun q ↦ twcLoop r s ℓ σ F (q + 1)) = loopAt (twStrands r s ℓ) (twcBase r s σ).tail
        (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) :=
      funext fun q ↦ twcLoop_succ_twCLoops r s ℓ σ F q
    rw [hs]
    exact hall

end AJConjecture
