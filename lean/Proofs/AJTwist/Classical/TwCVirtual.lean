import Mathlib
import AJHandoff.TorusKnot.PairKPeriGapRel
import AJTwist.Classical.TwCLoops

/-!
# The virtual tuple: a twisted run as a run of the untwisted blocks

Let `F` be a tuple on `twStrands r s ℓ` strands whose new entries are restored by the chain
(true for a tuple fixed by `twBlocks r s ℓ σ`). On the old chamber products the chain acts as
the head band `b(0, j₀)` with loop `L = twcLoop r s ℓ σ F 0` instead of the loop of the band
(`prePr_runTop_twChain`). A band `b(0, j₀)` multiplies the chamber products `P_1, …, P_(j₀)` by
its loop `P_(j₀+1) P_(j₀)⁻¹ P_1⁻¹`, which only reads `P_1`, `P_(j₀)`, `P_(j₀+1)`; so the chamber
products above the chain are also obtained from the true band applied to the *virtual tuple*
`twcVirtual r s ℓ σ F` on the old `2c + 1` strands, whose chamber products are those of `F`
except at the levels `1, …, j₀`, where they are multiplied on the left by
`d = μ⁻¹ L⁻¹ e_(j₀)` (`μ = F 0`, `e_(j₀)` the edge meridian of the level `j₀`; `d = 1` when `L`
is the loop of the band). The virtual tuple differs from `F` in the entries `0` and `j₀` only.

* `runTop_twcVirtual`: the run of the untwisted list `twcBase r s σ` on the virtual tuple is the
  restriction of the run of the twisted list on `F`;
* `loopAt_twcVirtual`: off the head position, the block loops of the two runs agree.

Hence every theorem of the library about the run of `pairBlocks r s` on an *arbitrary* tuple
(`stLoop_pairBlocks_core`, `pairHopf_loops`) applies to the twisted lists.

Route for `runTop_twcVirtual`: by `twcBase_eq_head_cons`, `twBlocks_eq_chain_append`,
`runTop_cons`, `runTop_append` it is enough to compare the tuples above the first block, through
their chamber products: `SBlock.prePr_step` and the definition of `SBlock.loop` on the virtual
side (the loop of the band on the virtual tuple is `L d⁻¹`), `prePr_runTop_twChain` and
`prePr_resTuple` on the twisted side; then `resTuple_runTop` for the common tail.
`loopAt_twcVirtual` follows with `loopAt_append_right`, `loopAt_resTuple`.

Checked numerically (`SCR/C/py/w2_twk_all.py`, on `SU(2)` representations of the groups of
`twBlocks`): `(2,3)` with `ℓ ∈ {-2, -1, 1}`, `(3,4)` with `ℓ ∈ {-2, -1, 1, 2}`, both clasp
signs among them: both statements to `10⁻¹³`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The chamber products of the virtual tuple: those of `F`, multiplied on the left by
`d = (F 0)⁻¹ L⁻¹ e_(j₀)` at the levels `1, …, j₀`. -/
def twcVirtCh (r s : ℕ) (ℓ : ℤ) (σ : Bool) (F : Fin (twStrands r s ℓ) → G) (n : ℕ) : G :=
  if 1 ≤ n ∧ n ≤ twHeadTop r s then
    (prePr F 1)⁻¹ * (twcLoop r s ℓ σ F 0)⁻¹ * edgeMer F (twHeadTop r s) * prePr F n
  else prePr F n

/-- The virtual tuple on the old strands. -/
def twcVirtual (r s : ℕ) (ℓ : ℤ) (σ : Bool) (F : Fin (twStrands r s ℓ) → G) :
    Fin (pairStrands r s) → G :=
  fun k ↦ (twcVirtCh r s ℓ σ F k)⁻¹ * twcVirtCh r s ℓ σ F (k + 1)

theorem pairStrands_le_twStrands (r s : ℕ) (ℓ : ℤ) : pairStrands r s ≤ twStrands r s ℓ :=
  Nat.le_add_right _ _

/-- The chamber products of the virtual tuple. -/
theorem prePr_twcVirtual (r s : ℕ) (ℓ : ℤ) (σ : Bool) (F : Fin (twStrands r s ℓ) → G) {n : ℕ}
    (hn : n ≤ pairStrands r s) :
    prePr (twcVirtual r s ℓ σ F) n = twcVirtCh r s ℓ σ F n := by
  induction n with
  | zero =>
    rw [prePr_zero, twcVirtCh, ite_eq_right (by omega), prePr_zero]
  | succ n ih =>
    rw [prePr_succ _ n (by omega), ih (by omega), twcVirtual, mul_inv_cancel_left]

/-- A tuple is determined by its chamber products. -/
private theorem ext_of_prePr_twCVirtual {m : ℕ} (f f' : Fin m → G)
    (hP : ∀ n, n ≤ m → prePr f n = prePr f' n) : f = f' := by
  funext k
  have h1 := prePr_succ f k k.2
  rw [hP _ k.2, hP _ k.2.le, prePr_succ f' k k.2] at h1
  exact (mul_left_cancel h1).symm

/-- The first `twExtra ℓ + 1` blocks of the twisted list are the chain. -/
private theorem take_twBlocks_twCVirtual (r s : ℕ) (ℓ : ℤ) (σ : Bool) :
    (twBlocks r s ℓ σ).take (twExtra ℓ + 1) = twChain (pairStrands r s) (twHeadTop r s) ℓ := by
  rw [twBlocks_eq_chain_append, ← length_twChain (pairStrands r s) (twHeadTop r s) ℓ,
    List.take_left]

/-- The blocks of the tail of the base list live on the old strands. -/
private theorem twcBase_tail_valid_twCVirtual {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    ∀ b ∈ (twcBase r s σ).tail, b.Valid (pairStrands r s) := fun b hb ↦
  twcBase_valid h σ b (List.mem_of_mem_tail hb)

/-- The head band on the virtual tuple gives the restriction of the tuple above the chain. -/
private theorem step_twcVirtual_twCVirtual {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hnew : ∀ k : Fin (twStrands r s ℓ), pairStrands r s ≤ (k : ℕ) →
      runTop (twStrands r s ℓ) ((twBlocks r s ℓ σ).take (twExtra ℓ + 1)) F k = F k) :
    (SBlock.band 0 (twHeadTop r s)).step (pairStrands r s) (twcVirtual r s ℓ σ F) =
      resTuple (pairStrands_le_twStrands r s ℓ)
        (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) := by
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  have hL : twcLoop r s ℓ σ F 0 = twcChainLoop (pairStrands r s) (twHeadTop r s) ℓ F := by
    rw [twcLoop, ite_eq_left rfl, take_twBlocks_twCVirtual]
    rfl
  rw [take_twBlocks_twCVirtual] at hnew
  refine ext_of_prePr_twCVirtual _ _ fun n hn ↦ ?_
  have hch : prePr (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) n =
      if 1 ≤ n ∧ n ≤ twHeadTop r s then twcLoop r s ℓ σ F 0 * prePr F n else prePr F n := by
    rw [hL]
    exact prePr_runTop_twChain hj hjM ℓ F hnew hn
  rw [prePr_resTuple _ _ hn, hch, SBlock.prePr_step _ (show (SBlock.band 0 (twHeadTop r s)).Valid
    (pairStrands r s) from ⟨hj, hjM⟩), prePr_twcVirtual r s ℓ σ F hn]
  simp only [SBlock.gapLoop, SBlock.lo, SBlock.hi, zero_add]
  by_cases hc : 1 ≤ n ∧ n ≤ twHeadTop r s
  · rw [ite_eq_left hc, ite_eq_left hc, SBlock.loop, prePr_twcVirtual r s ℓ σ F (by omega),
      prePr_twcVirtual r s ℓ σ F (by omega), prePr_twcVirtual r s ℓ σ F (Nat.zero_le _),
      prePr_twcVirtual r s ℓ σ F (by omega)]
    simp only [twcVirtCh]
    rw [ite_eq_left hc, ite_eq_right (show ¬(1 ≤ twHeadTop r s + 1 ∧
      twHeadTop r s + 1 ≤ twHeadTop r s) by omega), ite_eq_left (show 1 ≤ twHeadTop r s ∧
      twHeadTop r s ≤ twHeadTop r s by omega), ite_eq_right (show ¬(1 ≤ 0 ∧
      0 ≤ twHeadTop r s) by omega), ite_eq_left (show 1 ≤ 0 + 1 ∧ 0 + 1 ≤ twHeadTop r s by omega),
      edgeMer, prePr_zero]
    group
  · rw [ite_eq_right hc, ite_eq_right hc, one_mul, twcVirtCh, ite_eq_right hc]

/-- The untwisted run on the virtual tuple is the restriction of the twisted run. -/
theorem runTop_twcVirtual {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hnew : ∀ k : Fin (twStrands r s ℓ), pairStrands r s ≤ (k : ℕ) →
      runTop (twStrands r s ℓ) ((twBlocks r s ℓ σ).take (twExtra ℓ + 1)) F k = F k) :
    runTop (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) =
      resTuple (pairStrands_le_twStrands r s ℓ)
        (runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F) := by
  conv_lhs => rw [twcBase_eq_head_cons h σ, runTop_cons, step_twcVirtual_twCVirtual h ℓ σ F hnew]
  rw [twBlocks_eq_chain_append, runTop_append,
    resTuple_runTop _ _ (twcBase_tail_valid_twCVirtual h σ)]

/-- Off the head position the block loops of the virtual run are those of the twisted run. -/
theorem loopAt_twcVirtual {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hnew : ∀ k : Fin (twStrands r s ℓ), pairStrands r s ≤ (k : ℕ) →
      runTop (twStrands r s ℓ) ((twBlocks r s ℓ σ).take (twExtra ℓ + 1)) F k = F k)
    {q : ℕ} (hq : q < 2 * pairC r s + 2) (hq' : q ≠ 0) :
    loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) q = twcLoop r s ℓ σ F q := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq'
  have hlen : q < (twcBase r s σ).tail.length := by
    rw [List.length_tail, twcBase, List.length_map, length_pairBlocks_rev h]
    omega
  rw [twcLoop, ite_eq_right (Nat.succ_ne_zero q), twBlocks_eq_chain_append,
    show q + 1 + twExtra ℓ = (twChain (pairStrands r s) (twHeadTop r s) ℓ).length + q by
      rw [length_twChain]; omega,
    loopAt_append_right, loopAt_resTuple (pairStrands_le_twStrands r s ℓ) _
      (twcBase_tail_valid_twCVirtual h σ) _ hlen, ← step_twcVirtual_twCVirtual h ℓ σ F hnew]
  conv_lhs => rw [twcBase_eq_head_cons h σ]
  simp only [loopAt, List.getD_cons_succ, List.take_succ_cons, runTop_cons]

end AJConjecture
