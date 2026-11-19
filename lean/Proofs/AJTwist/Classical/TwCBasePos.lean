import Mathlib
import AJHandoff.TorusKnot.PairKOrbStrand
import AJHandoff.TorusKnot.PairKPeriHopf
import AJTwist.Classical.TwCBlocks
import AJTwist.Classical.TwCRestrict

/-!
# The untwisted positive-clasp block list: strand loops and Hopf loops (crux)

`twcBase r s false` is `pairBlocks r s` with both Hopf letters `σ_T⁻¹` replaced by `σ_T`
(`T = 2c - 1`; `twClaspBlock false`). The strand map, the gap intervals and all blocks other
than the two letters are unchanged, but a positive letter is carried by the strand at its upper
level `T + 1 = 2c`, a negative one by the strand at `T`. For an arbitrary tuple `f`, with `L`
the block loops:

* `stPerm_twcBase`: the strand map is that of `pairBlocks r s`;
* `stLoop_twcBase_pos`: the strand `T` collects the first Hopf loop in front of its core, the
  strand `2c` the second one, and the strand `pairOrbH1 = 2c - s - 1` nothing:
  `S_T = H₁ · core(T)`, `S_(2c) = H₂ · core(2c)`, `S_(pairOrbH1) = 1`, `S_t = core(t)` otherwise
  (for the negative clasp `S_T = H₂ · core(T)`, `S_(pairOrbH1) = H₁`, `stLoop_pairBlocks_core`);
* `twcHopf_loops_pos`: with `β = e_T`, `α = e_(T+1)` the edge meridians of the bottom tuple,
  `H₁ = α R_0 β⁻¹` and `H₂ = α H₁⁻¹ C R_0 β⁻¹ H₁⁻¹` (negative clasp: `pairHopf_loops`).

Route. All blocks other than the two Hopf letters live on the strands `0, …, T`, so replacing
the single entry `T + 1` of the tuple by a virtual one (`twcClaspVirt`) makes `σ_T⁻¹` act on the
entries `0, …, T` as `σ_T` does on the original tuple (`clasp_compare`). The run of
`pairBlocks r s` on the virtual tuple then has the same loops off the Hopf letters and strand
loops that differ only by the Hopf loops, and the statements follow from the library's theorems
for the negative clasp (`stLoop_pairBlocks_core`, `stPerm_pairBlocks_orb`; the Hopf formula is
an adapted copy of the proof of `pairHopf_loops`). The stage files of the negative clasp are not
copied.

Checked numerically on random unitary tuples for
`(r, s) ∈ {(2,3), (2,5), (3,4), (3,5), (4,5), (5,7)}` (`SCR/C/py/v11_core.py`): both formulas to
`10⁻¹⁵`, next to the library's statements for the negative clasp.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Changing the sign of a Hopf letter does not change its strand map. -/
private theorem perm_twClaspBlock_twCBasePos (σ : Bool) (b : SBlock) (t : ℕ) :
    (twClaspBlock σ b).perm t = b.perm t := by
  cases b with
  | band i j => rfl
  | neg i => cases σ <;> rfl

/-- Changing the sign of the Hopf letters does not change the strand map of a list. -/
private theorem stPerm_map_twClaspBlock_twCBasePos (σ : Bool) (bs : List SBlock) (t : ℕ) :
    stPerm (bs.map (twClaspBlock σ)) t = stPerm bs t := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.map_cons, stPerm, stPerm, ih, perm_twClaspBlock_twCBasePos]

/-- The strand map does not depend on the sign of the Hopf letters. -/
theorem stPerm_twcBase (r s : ℕ) (σ : Bool) (t : ℕ) :
    stPerm (twcBase r s σ) t = stPerm (pairBlocks r s) t :=
  stPerm_map_twClaspBlock_twCBasePos σ (pairBlocks r s) t

/-! ### The virtual tuple of the clasp

The proofs below do not repeat the stage computation. All blocks other than the two Hopf
letters live on the strands `0, …, T`, so their loops and strand loops only read the entries
`0, …, T` of the tuple below them. Replacing the entry `T + 1` of `f` by a suitable element
gives a tuple `g` (`twcClaspVirt_twCBasePos`) such that the negative letter above the lower
blocks run on `g` acts on the entries `0, …, T` as the positive letter does in the run of `f`.
Hence the run of `pairBlocks r s` on `g` has the same loops off the Hopf letters and the same
strand loops up to the loops of the letters (`clasp_compare_twCBasePos`), and
`stLoop_pairBlocks_core` for `g` gives `stLoop_twcBase_pos`. -/

/-! ### Blocks on the lower strands -/

/-- Blocks on the first `n` strands fix the positions `≥ n`. -/
private theorem stPerm_of_ge_twCBasePos {n : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid n)
    {t : ℕ} (ht : n ≤ t) : stPerm bs t = t := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [stPerm, ih hv.2]
    have hb := hv.1
    cases b <;> simp only [SBlock.Valid, SBlock.perm] at hb ⊢ <;> split_ifs <;> omega

/-- Blocks on the first `n` strands collect nothing at the positions `≥ n`. -/
private theorem stLoop_of_ge_twCBasePos {m n : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid n)
    (f : Fin m → G) {t : ℕ} (ht : n ≤ t) : stLoop m bs f t = 1 := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [stLoop, ih hv.2, stPerm_of_ge_twCBasePos bs hv.2 ht, one_mul, SBlock.strandLoop]
    have hb := hv.1
    have hc : b.carries t = false := by
      cases b <;> simp only [SBlock.Valid, SBlock.carries, decide_eq_false_iff_not] at hb ⊢ <;>
        omega
    rw [hc]
    rfl

/-- A tuple is determined by its chamber products. -/
private theorem ext_of_prePr_twCBasePos {m : ℕ} (f f' : Fin m → G)
    (hP : ∀ n, n ≤ m → prePr f n = prePr f' n) : f = f' := by
  funext k
  have h1 := prePr_succ f k k.2
  rw [hP _ k.2, hP _ k.2.le, prePr_succ f' k k.2] at h1
  exact (mul_left_cancel h1).symm

/-! ### The virtual tuple of the clasp -/

/-- The tuple `f` with the entry `T + 1` replaced so that the negative letter `σ_T⁻¹` above a
list `A` on the strands `0, …, T` acts on the entries `0, …, T` as the positive letter `σ_T`
does on the run of `f`. -/
private def twcClaspVirt_twCBasePos {m : ℕ} (T : ℕ) (hT : T + 1 < m) (A : List SBlock)
    (f : Fin m → G) : Fin m → G :=
  Function.update f ⟨T + 1, hT⟩
    ((prePr (runTop m A f) T)⁻¹ * prePr (runTop m A f) (T + 2) *
      (prePr (runTop m A f) (T + 1))⁻¹ * prePr (runTop m A f) T)

/-- The virtual tuple agrees with `f` on the entries `0, …, T`. -/
private theorem resTuple_twcClaspVirt_twCBasePos {m T : ℕ} (hT : T + 1 < m) (A : List SBlock)
    (f : Fin m → G) :
    resTuple hT.le (twcClaspVirt_twCBasePos T hT A f) = resTuple hT.le f := by
  funext k
  have hne : Fin.castLE hT.le k ≠ ⟨T + 1, hT⟩ := fun h ↦ by
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  simp only [resTuple, twcClaspVirt_twCBasePos, Function.update_of_ne hne]

/-- The two letters agree on the entries `0, …, T` of the tuples above `A`. -/
private theorem resTuple_step_twcClaspVirt_twCBasePos {m T : ℕ} (hT : T + 1 < m)
    (A : List SBlock) (hA : ∀ b ∈ A, b.Valid (T + 1)) (f : Fin m → G) :
    resTuple hT.le ((SBlock.neg T).step m (runTop m A (twcClaspVirt_twCBasePos T hT A f))) =
      resTuple hT.le ((SBlock.band T (T + 1)).step m (runTop m A f)) := by
  set g := twcClaspVirt_twCBasePos T hT A f with hg
  have hres : resTuple hT.le (runTop m A g) = resTuple hT.le (runTop m A f) := by
    rw [resTuple_runTop hT.le A hA, resTuple_runTop hT.le A hA,
      resTuple_twcClaspVirt_twCBasePos]
  have hlow : ∀ n, n ≤ T + 1 → prePr (runTop m A g) n = prePr (runTop m A f) n := fun n hn ↦ by
    rw [← prePr_resTuple hT.le _ hn, hres, prePr_resTuple hT.le _ hn]
  have htop : prePr (runTop m A g) (T + 2) = prePr (runTop m A f) (T + 1) *
      ((prePr (runTop m A f) T)⁻¹ * prePr (runTop m A f) (T + 2) *
        (prePr (runTop m A f) (T + 1))⁻¹ * prePr (runTop m A f) T) := by
    rw [show T + 2 = T + 1 + 1 from rfl, prePr_succ _ (T + 1) hT, hlow _ le_rfl,
      runTop_apply_of_ge hT.le A hA g ⟨T + 1, hT⟩ le_rfl, hg, twcClaspVirt_twCBasePos,
      Function.update_self]
  refine ext_of_prePr_twCBasePos _ _ fun n hn ↦ ?_
  rw [prePr_resTuple hT.le _ hn, prePr_resTuple hT.le _ hn,
    SBlock.prePr_step _ (show (SBlock.neg T).Valid m from hT),
    SBlock.prePr_step _ (show (SBlock.band T (T + 1)).Valid m from ⟨Nat.lt_succ_self T, hT⟩)]
  rw [SBlock.gapLoop, SBlock.gapLoop]
  by_cases hn1 : n = T + 1
  · subst hn1
    rw [ite_eq_left (show (SBlock.neg T).lo ≤ T + 1 ∧ T + 1 ≤ (SBlock.neg T).hi from
        ⟨le_rfl, le_rfl⟩),
      ite_eq_left (show (SBlock.band T (T + 1)).lo ≤ T + 1 ∧ T + 1 ≤ (SBlock.band T (T + 1)).hi
        from ⟨le_rfl, le_rfl⟩), SBlock.loop, SBlock.loop, htop, hlow _ le_rfl, hlow T (by omega)]
    group
  · rw [ite_eq_right (show ¬((SBlock.neg T).lo ≤ n ∧ n ≤ (SBlock.neg T).hi) from
        fun h ↦ hn1 (le_antisymm h.2 h.1)),
      ite_eq_right (show ¬((SBlock.band T (T + 1)).lo ≤ n ∧ n ≤ (SBlock.band T (T + 1)).hi) from
        fun h ↦ hn1 (le_antisymm h.2 h.1)), hlow n hn]

/-! ### A list with the same letter at two places -/

/-- The strand loop of a list with the letter `X` at two places, cut at the letters. -/
private theorem stLoop_clasp_split_twCBasePos {m : ℕ} (A Mid : List SBlock) (X : SBlock)
    (u : Fin m → G) (t : ℕ) :
    stLoop m (A ++ ([X] ++ (Mid ++ [X]))) u t =
      X.strandLoop (runTop m Mid (X.step m (runTop m A u))) t *
        stLoop m Mid (X.step m (runTop m A u)) (X.perm t) *
        X.strandLoop (runTop m A u) (stPerm Mid (X.perm t)) *
        stLoop m A u (X.perm (stPerm Mid (X.perm t))) := by
  simp only [stLoop_append, stPerm_append, List.singleton_append, stLoop, stPerm, one_mul,
    mul_assoc]

/-- The strand map of a list with the letter `X` at two places. -/
private theorem stPerm_clasp_split_twCBasePos (A Mid : List SBlock) (X : SBlock) (t : ℕ) :
    stPerm (A ++ ([X] ++ (Mid ++ [X]))) t = stPerm A (X.perm (stPerm Mid (X.perm t))) := by
  simp only [stPerm_append, List.singleton_append, stPerm]

/-- The loop of the first letter `X`. -/
private theorem loopAt_clasp_first_twCBasePos {m : ℕ} (A Mid : List SBlock) (X : SBlock)
    (u : Fin m → G) :
    loopAt m (A ++ ([X] ++ (Mid ++ [X]))) u A.length = X.loop (runTop m A u) := by
  have h := loopAt_append_right m A ([X] ++ (Mid ++ [X])) u 0
  rw [Nat.add_zero] at h
  rw [h]
  simp only [loopAt, List.singleton_append, List.getD_cons_zero, List.take_zero, runTop_nil]

/-- The loops of the blocks between the two letters `X`. -/
private theorem loopAt_clasp_mid_twCBasePos {m : ℕ} (A Mid : List SBlock) (X : SBlock)
    (u : Fin m → G) {j : ℕ} (hj : j < Mid.length) :
    loopAt m (A ++ ([X] ++ (Mid ++ [X]))) u (A.length + (1 + j)) =
      loopAt m Mid (X.step m (runTop m A u)) j := by
  rw [loopAt_append_right, show 1 + j = [X].length + j from rfl, loopAt_append_right,
    loopAt_append_left _ _ _ _ _ hj, runTop_cons, runTop_nil]

/-- The loop of the second letter `X`. -/
private theorem loopAt_clasp_second_twCBasePos {m : ℕ} (A Mid : List SBlock) (X : SBlock)
    (u : Fin m → G) :
    loopAt m (A ++ ([X] ++ (Mid ++ [X]))) u (A.length + (1 + Mid.length)) =
      X.loop (runTop m Mid (X.step m (runTop m A u))) := by
  rw [loopAt_append_right, show 1 + Mid.length = [X].length + (Mid.length + 0) from rfl,
    loopAt_append_right, loopAt_append_right, runTop_cons, runTop_nil]
  simp only [loopAt, List.getD_cons_zero, List.take_zero, runTop_nil]

/-- The loop collected at a negative letter. -/
private theorem strandLoop_neg_twCBasePos {m : ℕ} (T : ℕ) (v : Fin m → G) (p : ℕ) :
    (SBlock.neg T).strandLoop v p = if p = T then (SBlock.neg T).loop v else 1 := by
  simp only [SBlock.strandLoop, SBlock.carries, decide_eq_true_eq]

/-- The loop collected at a positive letter. -/
private theorem strandLoop_pos_twCBasePos {m : ℕ} (T : ℕ) (v : Fin m → G) (p : ℕ) :
    (SBlock.band T (T + 1)).strandLoop v p =
      if p = T + 1 then (SBlock.band T (T + 1)).loop v else 1 := by
  simp only [SBlock.strandLoop, SBlock.carries, decide_eq_true_eq]
  by_cases hp : p = T + 1
  · rw [ite_eq_left hp, ite_eq_left (Or.inl hp)]
  · rw [ite_eq_right hp, ite_eq_right (by omega)]

/-- The strand map of a letter on the levels `T`, `T + 1`. -/
private theorem perm_neg_twCBasePos (T p : ℕ) :
    (SBlock.neg T).perm p = if p = T then T + 1 else if p = T + 1 then T else p := rfl

/-- The strand map of a positive letter on the levels `T`, `T + 1`. -/
private theorem perm_pos_twCBasePos (T p : ℕ) :
    (SBlock.band T (T + 1)).perm p = if p = T then T + 1 else if p = T + 1 then T else p := rfl

/-- The run of the list with positive letters on `f` and the run of the list with negative
letters on the virtual tuple: the same loops off the letters, and strand loops that differ by
the loops of the letters only. -/
private theorem clasp_compare_twCBasePos {m T : ℕ} (hT : T + 1 < m) (A Mid : List SBlock)
    (hA : ∀ b ∈ A, b.Valid (T + 1)) (hMid : ∀ b ∈ Mid, b.Valid (T + 1)) (f : Fin m → G) :
    ∃ g : Fin m → G,
      (∀ q, q < A.length →
        loopAt m (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) g q =
          loopAt m (A ++ ([SBlock.band T (T + 1)] ++ (Mid ++ [SBlock.band T (T + 1)]))) f q) ∧
      (∀ j, j < Mid.length →
        loopAt m (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) g (A.length + (1 + j)) =
          loopAt m (A ++ ([SBlock.band T (T + 1)] ++ (Mid ++ [SBlock.band T (T + 1)]))) f
            (A.length + (1 + j))) ∧
      stLoop m (A ++ ([SBlock.band T (T + 1)] ++ (Mid ++ [SBlock.band T (T + 1)]))) f T =
        loopAt m (A ++ ([SBlock.band T (T + 1)] ++ (Mid ++ [SBlock.band T (T + 1)]))) f
            A.length *
          (loopAt m (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) g
            (A.length + (1 + Mid.length)))⁻¹ *
          stLoop m (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) g T ∧
      (stPerm (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) (T + 1) ≠ T + 1 →
        stLoop m (A ++ ([SBlock.band T (T + 1)] ++ (Mid ++ [SBlock.band T (T + 1)]))) f
            (T + 1) =
          loopAt m (A ++ ([SBlock.band T (T + 1)] ++ (Mid ++ [SBlock.band T (T + 1)]))) f
              (A.length + (1 + Mid.length)) *
            stLoop m (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) g (T + 1)) ∧
      ∀ t, t < T →
        stLoop m (A ++ ([SBlock.band T (T + 1)] ++ (Mid ++ [SBlock.band T (T + 1)]))) f t =
          stLoop m (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) g t *
            if stPerm (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) t = T + 1 then
              (loopAt m (A ++ ([SBlock.neg T] ++ (Mid ++ [SBlock.neg T]))) g A.length)⁻¹
            else 1 := by
  set g := twcClaspVirt_twCBasePos T hT A f with hg
  have hres : resTuple hT.le g = resTuple hT.le f := resTuple_twcClaspVirt_twCBasePos hT A f
  have hres2 := resTuple_step_twcClaspVirt_twCBasePos hT A hA f
  rw [← hg] at hres2
  have hBot : ∀ p, stLoop m A g p = stLoop m A f p := fun p ↦ by
    rw [stLoop_resTuple hT.le A hA, stLoop_resTuple hT.le A hA, hres]
  have hTop : ∀ p, stLoop m Mid ((SBlock.neg T).step m (runTop m A g)) p =
      stLoop m Mid ((SBlock.band T (T + 1)).step m (runTop m A f)) p := fun p ↦ by
    rw [stLoop_resTuple hT.le Mid hMid, stLoop_resTuple hT.le Mid hMid, hres2]
  have hMT : stPerm Mid (T + 1) = T + 1 := stPerm_of_ge_twCBasePos Mid hMid le_rfl
  have hAT : stPerm A (T + 1) = T + 1 := stPerm_of_ge_twCBasePos A hA le_rfl
  have hMl : ∀ v : Fin m → G, stLoop m Mid v (T + 1) = 1 := fun v ↦
    stLoop_of_ge_twCBasePos Mid hMid v le_rfl
  have hAl : ∀ v : Fin m → G, stLoop m A v (T + 1) = 1 := fun v ↦
    stLoop_of_ge_twCBasePos A hA v le_rfl
  have hMle : ∀ p, p ≤ T → stPerm Mid p ≤ T := fun p hp ↦
    Nat.lt_succ_iff.1 (stPerm_lt Mid hMid p (by omega))
  have hAle : ∀ p, p ≤ T → stPerm A p ≤ T := fun p hp ↦
    Nat.lt_succ_iff.1 (stPerm_lt A hA p (by omega))
  refine ⟨g, fun q hq ↦ ?_, fun j hj ↦ ?_, ?_, fun hne ↦ ?_, fun t ht ↦ ?_⟩
  · rw [loopAt_append_left _ _ _ _ _ hq, loopAt_append_left _ _ _ _ _ hq,
      loopAt_resTuple hT.le A hA _ hq, loopAt_resTuple hT.le A hA _ hq, hres]
  · rw [loopAt_clasp_mid_twCBasePos _ _ _ _ hj, loopAt_clasp_mid_twCBasePos _ _ _ _ hj,
      loopAt_resTuple hT.le Mid hMid _ hj, loopAt_resTuple hT.le Mid hMid _ hj, hres2]
  · rw [loopAt_clasp_first_twCBasePos, loopAt_clasp_second_twCBasePos,
      stLoop_clasp_split_twCBasePos, stLoop_clasp_split_twCBasePos]
    simp only [strandLoop_neg_twCBasePos, strandLoop_pos_twCBasePos, perm_neg_twCBasePos,
      perm_pos_twCBasePos, hMT, hMl, hBot, ite_true, ite_eq_right (Nat.succ_ne_self T),
      ite_eq_right (Nat.succ_ne_self T).symm, one_mul, mul_one]
    group
  · have hTT : T + 1 ≠ T := Nat.succ_ne_self T
    have hpT : stPerm Mid T ≠ T := fun h ↦ hne (by
      simp only [stPerm_clasp_split_twCBasePos, perm_neg_twCBasePos, ite_eq_right hTT, ite_true,
        h, hAT])
    have hpT1 : stPerm Mid T ≠ T + 1 := fun h ↦ by
      have := hMle T le_rfl
      omega
    rw [loopAt_clasp_second_twCBasePos, stLoop_clasp_split_twCBasePos,
      stLoop_clasp_split_twCBasePos]
    simp only [strandLoop_neg_twCBasePos, strandLoop_pos_twCBasePos, perm_neg_twCBasePos,
      perm_pos_twCBasePos, hTop, hBot, ite_true, ite_eq_right hTT, ite_eq_right hpT,
      ite_eq_right hpT1, one_mul, mul_one, mul_assoc]
  · have htT : t ≠ T := by omega
    have htT1 : t ≠ T + 1 := by omega
    have hpT1 : stPerm Mid t ≠ T + 1 := fun h ↦ by
      have := hMle t (by omega)
      omega
    rw [stLoop_clasp_split_twCBasePos, stLoop_clasp_split_twCBasePos,
      stPerm_clasp_split_twCBasePos, loopAt_clasp_first_twCBasePos]
    simp only [strandLoop_neg_twCBasePos, strandLoop_pos_twCBasePos, perm_neg_twCBasePos,
      perm_pos_twCBasePos, hTop, hBot, ite_eq_right htT, ite_eq_right htT1, ite_eq_right hpT1,
      one_mul, mul_one]
    by_cases hpT : stPerm Mid t = T
    · simp only [hpT, ite_true, hAT, hAl, mul_one, mul_inv_cancel_right]
    · have hlt : stPerm Mid t < T := lt_of_le_of_ne (hMle t (by omega)) hpT
      have hne : stPerm A (stPerm Mid t) ≠ T + 1 := fun h ↦ by
        have := hAle _ hlt.le
        omega
      simp only [ite_eq_right hpT, ite_eq_right hne, mul_one]

/-! ### The core loops only read the loops off the Hopf letters -/

/-- The core loop of a strand other than `pairOrbH1` only reads the block loops off the two
Hopf letters. -/
private theorem pairOrbCore_congr_twCBasePos {r s : ℕ} (h : IsTorusPair r s) {L L' : ℕ → G}
    (hL : ∀ q, q < pairIdxH2 r s → q ≠ pairIdxH1 r s → L q = L' q) {t : ℕ}
    (ht : t < pairStrands r s) (hne : t ≠ pairOrbH1 r s) :
    pairOrbCore r s L t = pairOrbCore r s L' t := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hH1 : pairOrbH1 r s = 2 * pairC r s - s - 1 := rfl
  have hq : ∀ q, q < 2 * pairC r s + 1 → q ≠ 2 * pairC r s - s - r + 2 → L q = L' q := hL
  have hD : ∀ a n, a + n ≤ r - 2 → descProd (fun j ↦ L (pairIdxDp r s j)) a n =
      descProd (fun j ↦ L' (pairIdxDp r s j)) a n := fun a n han ↦
    descProd_congr_orb _ _ a a n fun i hi ↦ hq _ (by unfold pairIdxDp pairIdxB; omega)
      (by unfold pairIdxDp pairIdxB; omega)
  have hA : ∀ a n, a + n ≤ 2 * pairC r s - s - r → descProd L a n = descProd L' a n :=
    fun a n han ↦ descProd_congr_orb _ _ a a n fun i hi ↦ hq _ (by omega) (by omega)
  have hR : ∀ u, u < s → L (pairIdxR r s u) = L' (pairIdxR r s u) := fun u hu ↦
    hq _ (by unfold pairIdxR pairIdxB; split_ifs <;> omega)
      (by unfold pairIdxR pairIdxB; split_ifs <;> omega)
  have hSkip : ∀ ρ, pairOrbSkip r s L ρ = pairOrbSkip r s L' ρ := fun ρ ↦ by
    unfold pairOrbSkip
    refine congrArg List.prod (List.map_congr_left fun u hu ↦ ?_)
    rw [hR u (List.mem_range.1 (List.mem_reverse.1 hu))]
  have hB : L (pairIdxB r s) = L' (pairIdxB r s) :=
    hq _ (by unfold pairIdxB; omega) (by unfold pairIdxB; omega)
  have hC : L (pairIdxC r s) = L' (pairIdxC r s) :=
    hq _ (by unfold pairIdxC pairIdxB; omega) (by unfold pairIdxC pairIdxB; omega)
  have hr2 : L (r - 2) = L' (r - 2) := hq _ (by omega) (by omega)
  have hRun : t + s ≤ pairC r s → L (pairIdxRun r s t) = L' (pairIdxRun r s t) := fun hts ↦
    hq _ (by unfold pairIdxRun; split_ifs <;> omega) (by unfold pairIdxRun; split_ifs <;> omega)
  have hSuf : ∀ j, j < r → pairOrbSuf r s L j = pairOrbSuf r s L' j := fun j hj ↦ by
    unfold pairOrbSuf
    split_ifs with h1 h2
    · exact hA _ _ (by omega)
    · rw [hB, hr2, hA 0 (r - 2) (by omega),
        hA (r - 2 + pairRunDown r s) (pairRunUp r s) (by unfold pairRunUp; omega)]
    · rfl
  have hSlot : ∀ i, i < r → pairOrbSlotLoop r s L i = pairOrbSlotLoop r s L' i := fun i hi ↦ by
    unfold pairOrbSlotLoop
    rw [hSkip, hSuf (pairOrbNext r s i) (Nat.mod_lt _ (by omega)), hC]
    by_cases hi1 : i + 1 = r
    · rw [ite_eq_left hi1, ite_eq_left hi1]
    · rw [ite_eq_right hi1, ite_eq_right hi1, hD (r - 2 - i) i (by omega)]
  unfold pairOrbCore
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact hSlot _ (by unfold pairOrbLow; split_ifs <;> omega)
  · rw [hD 0 (r - 2) (by omega), hR (s - 1) (by omega), hRun h2, hA 0 (r - 2) (by omega)]
  · rw [hD 0 (r - 2) (by omega), hR (s - 1) (by omega), hA 0 (r - 2) (by omega)]
  · rw [hD _ _ (by unfold pairOrbFoot; omega), hA _ _ (by omega)]
  · omega
  · rw [hC, hR (s - 1) (by omega), hA 0 (r - 2) (by omega)]
  · rw [hC, hR _ (by unfold pairTop; omega), hB, hA 0 (r - 2) (by omega)]
  · rw [hR 0 (by omega), hB, hA 0 (r - 2) (by omega)]

/-- The core loop of `pairOrbH1` is the first Hopf loop. -/
private theorem pairOrbCore_H1_twCBasePos {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G) :
    pairOrbCore r s L (pairOrbH1 r s) = L (pairIdxH1 r s) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  unfold pairOrbCore pairOrbH1
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega)]

/-- Only the strand `pairOrbH1` ends at the bottom position `2c`. -/
private theorem pairOrbPerm_eq_top_twCBasePos {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (ht : t < pairStrands r s) :
    pairOrbPerm r s t = 2 * pairC r s ↔ t = pairOrbH1 r s := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  unfold pairOrbPerm pairOrbH1 pairTop
  generalize pairOrbNext r s (pairOrbLow r s t) = j
  split_ifs <;> omega

/-! ### The base lists around the Hopf letters -/

/-- The blocks of `pairBlocks r s` below the first Hopf letter. -/
private def twcLow_twCBasePos (r s : ℕ) : List SBlock :=
  (List.range (r - 2)).map (fun i ↦ SBlock.band i (pairTop r s - 1 - i)) ++
    ((List.range (pairRunDown r s)).map (fun j ↦ SBlock.band (r + pairRunDown r s - 3 - j)
      (r + pairRunDown r s - 2 - j)) ++
    ((List.range (pairRunUp r s)).map (fun j ↦ SBlock.band (r - 2 + pairRunDown r s + j)
      (r - 1 + pairRunDown r s + j)) ++
    [SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r),
      SBlock.band (pairTop r s - r) (pairTop r s)]))

/-- The blocks of `pairBlocks r s` between the two Hopf letters. -/
private def twcMid_twCBasePos (r s : ℕ) : List SBlock :=
  (List.range (s - 2)).map (fun j ↦ SBlock.band (pairTop r s - r - 1 - j)
      (pairTop r s - 1 - j)) ++
    ([SBlock.band (r - 2) (pairTop r s + 1 - s), SBlock.band (pairTop r s - s) (pairTop r s)] ++
    (List.range (r - 2)).map (fun j ↦ SBlock.band (r - 3 - j) (pairTop r s + 2 - s - r + j)))

/-- `pairBlocks r s` cut at the two Hopf letters. -/
private theorem pairBlocks_clasp_twCBasePos (r s : ℕ) :
    pairBlocks r s = twcLow_twCBasePos r s ++ ([SBlock.neg (pairTop r s)] ++
      (twcMid_twCBasePos r s ++ [SBlock.neg (pairTop r s)])) := by
  simp only [pairBlocks, twcLow_twCBasePos, twcMid_twCBasePos, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The blocks below the first Hopf letter are bands on the strands `0, …, T`. -/
private theorem twcLow_band_twCBasePos {r s : ℕ} (h : IsTorusPair r s) :
    ∀ b ∈ twcLow_twCBasePos r s, ∃ i j, b = SBlock.band i j ∧ i < j ∧ j < pairTop r s + 1 := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  intro b hb
  simp only [twcLow_twCBasePos, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hb
  simp only [pairTop, pairRunUp] at hb ⊢
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | rfl <;>
    exact ⟨_, _, rfl, by omega, by omega⟩

/-- The blocks between the Hopf letters are bands on the strands `0, …, T`. -/
private theorem twcMid_band_twCBasePos {r s : ℕ} (h : IsTorusPair r s) :
    ∀ b ∈ twcMid_twCBasePos r s, ∃ i j, b = SBlock.band i j ∧ i < j ∧ j < pairTop r s + 1 := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  intro b hb
  simp only [twcMid_twCBasePos, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hb
  simp only [pairTop] at hb ⊢
  rcases hb with ⟨j, hj, rfl⟩ | (rfl | rfl) | ⟨j, hj, rfl⟩ <;>
    exact ⟨_, _, rfl, by omega, by omega⟩

/-- Bands are not changed by the clasp sign. -/
private theorem map_twClaspBlock_of_band_twCBasePos (σ : Bool) {n : ℕ} (bs : List SBlock)
    (hb : ∀ b ∈ bs, ∃ i j, b = SBlock.band i j ∧ i < j ∧ j < n) :
    bs.map (twClaspBlock σ) = bs := by
  refine (List.map_congr_left fun b hbm ↦ ?_).trans (List.map_id bs)
  obtain ⟨i, j, rfl, -, -⟩ := hb b hbm
  rfl

/-- Bands with upper end below `n` live on `n` strands. -/
private theorem valid_of_band_twCBasePos {n : ℕ} (bs : List SBlock)
    (hb : ∀ b ∈ bs, ∃ i j, b = SBlock.band i j ∧ i < j ∧ j < n) : ∀ b ∈ bs, b.Valid n := by
  intro b hbm
  obtain ⟨i, j, rfl, hij, hj⟩ := hb b hbm
  exact ⟨hij, hj⟩

/-- The positive-clasp base list cut at the two Hopf letters. -/
private theorem twcBase_false_clasp_twCBasePos {r s : ℕ} (h : IsTorusPair r s) :
    twcBase r s false = twcLow_twCBasePos r s ++
      ([SBlock.band (pairTop r s) (pairTop r s + 1)] ++
        (twcMid_twCBasePos r s ++ [SBlock.band (pairTop r s) (pairTop r s + 1)])) := by
  rw [twcBase, pairBlocks_clasp_twCBasePos, List.map_append, List.map_append, List.map_append,
    map_twClaspBlock_of_band_twCBasePos false _ (twcLow_band_twCBasePos h),
    map_twClaspBlock_of_band_twCBasePos false _ (twcMid_band_twCBasePos h)]
  rfl

/-- The number of blocks below the first Hopf letter. -/
private theorem length_twcLow_twCBasePos {r s : ℕ} (h : IsTorusPair r s) :
    (twcLow_twCBasePos r s).length = pairIdxH1 r s := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  simp only [twcLow_twCBasePos, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil, pairIdxH1, pairIdxB, pairRunUp]
  omega

/-- The number of blocks between the Hopf letters. -/
private theorem length_twcMid_twCBasePos {r s : ℕ} (h : IsTorusPair r s) :
    (twcMid_twCBasePos r s).length = s + r - 2 := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  simp only [twcMid_twCBasePos, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]
  omega

/-- The strand loops of the positive-clasp list on an arbitrary tuple. -/
theorem stLoop_twcBase_pos {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    {t : ℕ} (ht : t < pairStrands r s) :
    stLoop (pairStrands r s) (twcBase r s false) f t =
      (if t = pairTop r s then loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH1 r s)
        else if t = 2 * pairC r s then
          loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH2 r s)
        else 1) *
      (if t = pairOrbH1 r s then 1
        else pairOrbCore r s (loopAt (pairStrands r s) (twcBase r s false) f) t) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hT1 : pairTop r s + 1 = 2 * pairC r s := by omega
  have hH1 : pairOrbH1 r s = 2 * pairC r s - s - 1 := rfl
  have hTm : pairTop r s + 1 < pairStrands r s := by omega
  have hlA := length_twcLow_twCBasePos h
  have hlM := length_twcMid_twCBasePos h
  have hI2 : (twcLow_twCBasePos r s).length + (1 + (twcMid_twCBasePos r s).length) =
      pairIdxH2 r s := by
    rw [hlA, hlM]
    unfold pairIdxH1 pairIdxB pairIdxH2
    omega
  obtain ⟨g, hlow, hmid, hST, hST1, hSt⟩ := clasp_compare_twCBasePos hTm (twcLow_twCBasePos r s)
    (twcMid_twCBasePos r s) (valid_of_band_twCBasePos _ (twcLow_band_twCBasePos h))
    (valid_of_band_twCBasePos _ (twcMid_band_twCBasePos h)) f
  rw [← pairBlocks_clasp_twCBasePos, ← twcBase_false_clasp_twCBasePos h] at hlow hmid hST hSt
  rw [← pairBlocks_clasp_twCBasePos, ← twcBase_false_clasp_twCBasePos h] at hST1
  rw [hI2] at hST hST1
  rw [hlA] at hST hSt hlow
  have hLL : ∀ q, q < pairIdxH2 r s → q ≠ pairIdxH1 r s →
      loopAt (pairStrands r s) (pairBlocks r s) g q =
        loopAt (pairStrands r s) (twcBase r s false) f q := fun q hq hne ↦ by
    rcases Nat.lt_or_ge q (pairIdxH1 r s) with hq1 | hq1
    · exact hlow q hq1
    · obtain ⟨j, rfl⟩ : ∃ j, q = (twcLow_twCBasePos r s).length + (1 + j) :=
        ⟨q - pairIdxH1 r s - 1, by omega⟩
      exact hmid j (by omega)
  have hcore : ∀ t, t < pairStrands r s → t ≠ pairOrbH1 r s →
      pairOrbCore r s (loopAt (pairStrands r s) (pairBlocks r s) g) t =
        pairOrbCore r s (loopAt (pairStrands r s) (twcBase r s false) f) t := fun t ht' hne ↦
    pairOrbCore_congr_twCBasePos h hLL ht' hne
  have hperm : ∀ t, t < pairStrands r s →
      (stPerm (pairBlocks r s) t = pairTop r s + 1 ↔ t = pairOrbH1 r s) := fun t ht' ↦ by
    rw [stPerm_pairBlocks_orb h ht', hT1]
    exact pairOrbPerm_eq_top_twCBasePos h ht'
  rcases Nat.lt_trichotomy t (pairTop r s) with hlt | rfl | hgt
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), one_mul, hSt t hlt,
      stLoop_pairBlocks_core h g ht, ite_eq_right (by omega), one_mul]
    by_cases hH : t = pairOrbH1 r s
    · rw [ite_eq_left ((hperm t ht).2 hH), ite_eq_left hH, hH, pairOrbCore_H1_twCBasePos h,
        mul_inv_cancel]
    · rw [ite_eq_right (fun h' ↦ hH ((hperm t ht).1 h')), ite_eq_right hH, mul_one,
        hcore t ht hH]
  · rw [ite_eq_left rfl, ite_eq_right (by omega), hST, stLoop_pairBlocks_core h g ht,
      ite_eq_left rfl, hcore _ ht (by omega)]
    group
  · have ht2 : t = 2 * pairC r s := by omega
    have hne : stPerm (pairBlocks r s) (pairTop r s + 1) ≠ pairTop r s + 1 := fun h' ↦ by
      have := (hperm _ (by omega)).1 h'
      omega
    rw [ite_eq_right (by omega), ite_eq_left ht2, ite_eq_right (by omega), ht2, ← hT1, hST1 hne,
      stLoop_pairBlocks_core h g (by omega), ite_eq_right (by omega), one_mul,
      hcore _ (by omega) (by omega)]

/-! ### The loops of the positive Hopf letters -/

/-- A block that neither moves nor carries the strand `t` leaves the edge meridian of `t`
unchanged. -/
private theorem edgeMer_step_of_untouched_twCBasePos {m : ℕ} (b : SBlock) (hb : b.Valid m)
    (f : Fin m → G) (t : ℕ) (ht : t < m) (hp : b.perm t = t) (hc : b.carries t = false) :
    edgeMer (b.step m f) t = edgeMer f t := by
  rw [SBlock.edgeMer_step b hb f t ht, SBlock.strandLoop, hc, hp]
  simp

/-- Blocks that neither move nor carry the strand `t` leave the edge meridian of `t`
unchanged. -/
private theorem edgeMer_runTop_of_untouched_twCBasePos {m : ℕ} (bs : List SBlock)
    (f : Fin m → G) (t : ℕ) (ht : t < m)
    (hu : ∀ b ∈ bs, b.Valid m ∧ b.perm t = t ∧ b.carries t = false) :
    edgeMer (runTop m bs f) t = edgeMer f t := by
  induction bs generalizing f with
  | nil => rw [runTop_nil]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hu
    rw [runTop_cons, ih _ hu.2,
      edgeMer_step_of_untouched_twCBasePos b hu.1.1 f t ht hu.1.2.1 hu.1.2.2]

/-- The loop of a band in terms of the edge meridians of its ends. -/
private theorem loop_band_edgeMer_twCBasePos {m : ℕ} (f : Fin m → G) (i j : ℕ) :
    (SBlock.band i j).loop f = edgeMer f j * (edgeMer f i)⁻¹ := by
  simp only [SBlock.loop, edgeMer]
  group

/-- The edge meridian of the upper end `j` above a band `b(i, j)`. -/
private theorem edgeMer_step_band_top_twCBasePos {m : ℕ} (i j : ℕ) (hij : i < j) (hj : j < m)
    (f : Fin m → G) :
    edgeMer ((SBlock.band i j).step m f) j = edgeMer f j * ((SBlock.band i j).loop f)⁻¹ := by
  rw [SBlock.edgeMer_step (SBlock.band i j) (show i < j ∧ j < m from ⟨hij, hj⟩) f j hj]
  simp only [SBlock.strandLoop, SBlock.carries, SBlock.perm, true_or, decide_true, ite_true,
    show j ≠ i by omega, ite_false, loop_band_edgeMer_twCBasePos]
  group

/-- The edge meridian of the lower end `i` above a band `b(i, j)`. -/
private theorem edgeMer_step_band_bot_twCBasePos {m : ℕ} (i j : ℕ) (hij : i < j) (hj : j < m)
    (f : Fin m → G) : edgeMer ((SBlock.band i j).step m f) i = edgeMer f j := by
  rw [SBlock.edgeMer_step (SBlock.band i j) (show i < j ∧ j < m from ⟨hij, hj⟩) f i (by omega)]
  have hc : (SBlock.band i j).carries i = false := by
    simp only [SBlock.carries, decide_eq_false_iff_not]
    omega
  simp only [SBlock.strandLoop, hc, SBlock.perm, ite_true, Bool.false_eq_true, ite_false,
    one_mul, inv_one, mul_one]

/-- The loops of the two positive Hopf letters in terms of the edge meridians of the levels `T`
and `T + 1` of the bottom tuple. -/
theorem twcHopf_loops_pos {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G) :
    loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH1 r s) =
        edgeMer f (pairTop r s + 1) *
          loopAt (pairStrands r s) (twcBase r s false) f (pairIdxR r s 0) *
          (edgeMer f (pairTop r s))⁻¹ ∧
      loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH2 r s) =
        edgeMer f (pairTop r s + 1) *
          (loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH1 r s))⁻¹ *
          loopAt (pairStrands r s) (twcBase r s false) f (pairIdxC r s) *
          loopAt (pairStrands r s) (twcBase r s false) f (pairIdxR r s 0) *
          (edgeMer f (pairTop r s))⁻¹ *
          (loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH1 r s))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  set T := pairTop r s with hT
  set pre : List SBlock := (List.range (r - 2)).map (fun i ↦ SBlock.band i (T - 1 - i)) ++
      ((List.range (pairRunDown r s)).map (fun j ↦ SBlock.band (r + pairRunDown r s - 3 - j)
        (r + pairRunDown r s - 2 - j)) ++
      ((List.range (pairRunUp r s)).map (fun j ↦ SBlock.band (r - 2 + pairRunDown r s + j)
        (r - 1 + pairRunDown r s + j)) ++
      [SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (T + 1 - r)])) with hpre
  set mid : List SBlock := (List.range (s - 2)).map (fun j ↦ SBlock.band (T - r - 1 - j)
      (T - 1 - j)) ++ [SBlock.band (r - 2) (T + 1 - s)] with hmid
  set post : List SBlock := (List.range (r - 2)).map (fun j ↦ SBlock.band (r - 3 - j)
      (T + 2 - s - r + j)) with hpost
  have hsplit : twcBase r s false = pre ++ ([SBlock.band (T - r) T, SBlock.band T (T + 1)] ++
      (mid ++ ([SBlock.band (T - s) T] ++ (post ++ [SBlock.band T (T + 1)])))) := by
    rw [twcBase_false_clasp_twCBasePos h]
    simp only [twcLow_twCBasePos, twcMid_twCBasePos, hpre, hmid, hpost, List.append_assoc,
      List.cons_append, List.nil_append, ← hT]
  have hTm : T + 1 < (pairStrands r s) := by simp only [hT, pairTop, pairStrands]; omega
  have hlpre : pre.length = pairIdxB r s + 1 := by
    simp only [hpre, List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil, pairIdxB, pairRunUp]
    omega
  have hlmid : mid.length = s - 1 := by
    simp only [hmid, List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega
  have hlpost : post.length = r - 2 := by simp [hpost]
  have hu : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ pre ++ mid ++ post,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := by
    intro t ht1 ht2 b hb
    simp only [hpre, hmid, hpost, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    simp only [hT, pairTop, pairStrands, pairRunUp] at ht1 ht2 hb ⊢
    rcases hb with (((⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl) |
      (⟨j, hj, rfl⟩ | rfl)) | ⟨j, hj, rfl⟩) <;>
      simp only [SBlock.Valid, SBlock.perm, SBlock.carries, decide_eq_false_iff_not] <;>
      refine ⟨by omega, by split_ifs <;> omega, by omega⟩
  have hupre : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ pre,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := fun t h1 h2 b hb ↦
    hu t h1 h2 b (List.mem_append_left _ (List.mem_append_left _ hb))
  have humid : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ mid,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := fun t h1 h2 b hb ↦
    hu t h1 h2 b (List.mem_append_left _ (List.mem_append_right _ hb))
  have hupost : ∀ t, T ≤ t → t ≤ T + 1 → ∀ b ∈ post,
      b.Valid (pairStrands r s) ∧ b.perm t = t ∧ b.carries t = false := fun t h1 h2 b hb ↦
    hu t h1 h2 b (List.mem_append_right _ hb)
  set g := runTop (pairStrands r s) pre f with hg
  set R := (SBlock.band (T - r) T).loop g with hR
  set g1 := (SBlock.band (T - r) T).step (pairStrands r s) g with hg1
  set H := (SBlock.band T (T + 1)).loop g1 with hH
  set g2 := (SBlock.band T (T + 1)).step (pairStrands r s) g1 with hg2
  set g3 := runTop (pairStrands r s) mid g2 with hg3
  set Cl := (SBlock.band (T - s) T).loop g3 with hCl
  set g4 := (SBlock.band (T - s) T).step (pairStrands r s) g3 with hg4
  set g5 := runTop (pairStrands r s) post g4 with hg5
  have hLR : loopAt (pairStrands r s) (twcBase r s false) f (pairIdxR r s 0) = R := by
    rw [hsplit, show pairIdxR r s 0 = pre.length + 0 by simp [pairIdxR, hlpre],
      loopAt_append_right, loopAt_append_left _ _ _ _ _ (by simp)]
    simp [loopAt, runTop_nil, hR, hg]
  have hLH1 : loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH1 r s) = H := by
    rw [hsplit, show pairIdxH1 r s = pre.length + 1 by simp [pairIdxH1, hlpre],
      loopAt_append_right, loopAt_append_left _ _ _ _ _ (by simp)]
    simp [loopAt, runTop_cons, runTop_nil, hH, hg1, hg]
  have hLC : loopAt (pairStrands r s) (twcBase r s false) f (pairIdxC r s) = Cl := by
    rw [hsplit, show pairIdxC r s = pre.length +
      ([SBlock.band (T - r) T, SBlock.band T (T + 1)].length + (mid.length + 0)) by
        simp only [pairIdxC, hlpre, hlmid, List.length_cons, List.length_nil]; omega,
      loopAt_append_right, loopAt_append_right, loopAt_append_right,
      loopAt_append_left _ _ _ _ _ (by simp)]
    simp [loopAt, runTop_cons, runTop_nil, hCl, hg3, hg2, hg1, hg]
  have hLH2 : loopAt (pairStrands r s) (twcBase r s false) f (pairIdxH2 r s) =
      (SBlock.band T (T + 1)).loop g5 := by
    rw [hsplit, show pairIdxH2 r s = pre.length +
      ([SBlock.band (T - r) T, SBlock.band T (T + 1)].length +
      (mid.length + ([SBlock.band (T - s) T].length + (post.length + 0)))) by
        simp only [pairIdxH2, hlpre, hlmid, hlpost, List.length_cons, List.length_nil, pairIdxB]
        omega,
      loopAt_append_right, loopAt_append_right, loopAt_append_right, loopAt_append_right,
      loopAt_append_right]
    simp [loopAt, runTop_cons, runTop_nil, hg5, hg4, hg3, hg2, hg1, hg]
  have hTr : T - r < T := by simp only [hT, pairTop]; omega
  have hTs : T - s < T := by simp only [hT, pairTop]; omega
  have hP : (SBlock.band T (T + 1)).Valid (pairStrands r s) := ⟨Nat.lt_succ_self T, hTm⟩
  have e0 : edgeMer g T = edgeMer f T :=
    edgeMer_runTop_of_untouched_twCBasePos pre f T (by omega) (hupre T le_rfl (by omega))
  have e0' : edgeMer g (T + 1) = edgeMer f (T + 1) :=
    edgeMer_runTop_of_untouched_twCBasePos pre f (T + 1) hTm (hupre (T + 1) (by omega) le_rfl)
  have e1 : edgeMer g1 T = edgeMer g T * R⁻¹ :=
    edgeMer_step_band_top_twCBasePos (T - r) T hTr (by omega) g
  have e1' : edgeMer g1 (T + 1) = edgeMer g (T + 1) :=
    edgeMer_step_of_untouched_twCBasePos (SBlock.band (T - r) T)
      (show (SBlock.band (T - r) T).Valid (pairStrands r s) from ⟨hTr, by omega⟩) g (T + 1) hTm
      (by simp only [SBlock.perm]; split_ifs <;> omega)
      (by simp only [SBlock.carries, decide_eq_false_iff_not]; omega)
  have hH1 : H = edgeMer f (T + 1) * R * (edgeMer f T)⁻¹ := by
    rw [hH, loop_band_edgeMer_twCBasePos, e1, e1', e0, e0']
    group
  have e2 : edgeMer g2 T = edgeMer g1 (T + 1) :=
    edgeMer_step_band_bot_twCBasePos T (T + 1) (Nat.lt_succ_self T) hTm g1
  have e2' : edgeMer g2 (T + 1) = edgeMer g1 (T + 1) * H⁻¹ :=
    edgeMer_step_band_top_twCBasePos T (T + 1) (Nat.lt_succ_self T) hTm g1
  have e3 : edgeMer g3 T = edgeMer g2 T :=
    edgeMer_runTop_of_untouched_twCBasePos mid g2 T (by omega) (humid T le_rfl (by omega))
  have e3' : edgeMer g3 (T + 1) = edgeMer g2 (T + 1) :=
    edgeMer_runTop_of_untouched_twCBasePos mid g2 (T + 1) hTm (humid (T + 1) (by omega) le_rfl)
  have e4 : edgeMer g4 T = edgeMer g3 T * Cl⁻¹ :=
    edgeMer_step_band_top_twCBasePos (T - s) T hTs (by omega) g3
  have e4' : edgeMer g4 (T + 1) = edgeMer g3 (T + 1) :=
    edgeMer_step_of_untouched_twCBasePos (SBlock.band (T - s) T)
      (show (SBlock.band (T - s) T).Valid (pairStrands r s) from ⟨hTs, by omega⟩) g3 (T + 1) hTm
      (by simp only [SBlock.perm]; split_ifs <;> omega)
      (by simp only [SBlock.carries, decide_eq_false_iff_not]; omega)
  have e5 : edgeMer g5 T = edgeMer g4 T :=
    edgeMer_runTop_of_untouched_twCBasePos post g4 T (by omega) (hupost T le_rfl (by omega))
  have e5' : edgeMer g5 (T + 1) = edgeMer g4 (T + 1) :=
    edgeMer_runTop_of_untouched_twCBasePos post g4 (T + 1) hTm
      (hupost (T + 1) (by omega) le_rfl)
  rw [hLR, hLH1, hLC, hLH2]
  refine ⟨hH1, ?_⟩
  rw [loop_band_edgeMer_twCBasePos, e5, e5', e4, e4', e3, e3', e2, e2', e1', e0', hH1]
  group

end AJConjecture
