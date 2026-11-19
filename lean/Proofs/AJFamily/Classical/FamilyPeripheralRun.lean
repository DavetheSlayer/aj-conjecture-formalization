import Mathlib
import AJFamily.Classical.BraidRunAppend
import AJFamily.Classical.FamilyPeripheralBlock

/-!
# The run of a list of blocks

The run of the braid word `blocksWord bs` of a list of blocks (the head block acting first, at
the bottom), by recursion over the list. For a level `n`, `gapProd` collects the loops of the
blocks whose gap interval contains `n`; `stPerm`, `stLoop` and `stCount` follow the strand at
top position `t` downwards; `loopAt bs f r` is the loop of the `r`-th block read on the tuple
below it. The chamber products, edge meridians and conjugators of the run are expressed through
these data.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The braid word of a list of blocks (the head block first, i.e. at the bottom). -/
def blocksWord (bs : List SBlock) : BraidWord := bs.flatMap SBlock.word

/-- The tuple above a list of blocks. -/
def runTop (m : ℕ) (bs : List SBlock) (f : Fin m → G) : Fin m → G :=
  (braidRun m (blocksWord bs) f).1

/-- The factor of the chamber product of level `n` collected by a list of blocks. -/
def gapProd (m : ℕ) : List SBlock → (Fin m → G) → ℕ → G
  | [], _, _ => 1
  | b :: bs, f, n => gapProd m bs (b.step m f) n * b.gapLoop f n

/-- The bottom position of the strand at top position `t`. -/
def stPerm : List SBlock → ℕ → ℕ
  | [], t => t
  | b :: bs, t => b.perm (stPerm bs t)

/-- The product of the loops collected by the strand at top position `t`, top to bottom. -/
def stLoop (m : ℕ) : List SBlock → (Fin m → G) → ℕ → G
  | [], _, _ => 1
  | b :: bs, f, t => stLoop m bs (b.step m f) t * b.strandLoop f (stPerm bs t)

/-- The meridian count of the strand at top position `t`. -/
def stCount : List SBlock → ℕ → ℤ
  | [], _ => 0
  | b :: bs, t => stCount bs t + b.count (stPerm bs t)

/-- The loop of the `r`-th block of a list, read on the tuple below it. -/
def loopAt (m : ℕ) (bs : List SBlock) (f : Fin m → G) (r : ℕ) : G :=
  (bs.getD r (SBlock.neg 0)).loop (runTop m (bs.take r) f)

/-- The braid word of a nonempty list of blocks. -/
private theorem blocksWord_cons (b : SBlock) (bs : List SBlock) :
    blocksWord (b :: bs) = b.word ++ blocksWord bs := by
  simp [blocksWord]

theorem runTop_nil (m : ℕ) (f : Fin m → G) : runTop m [] f = f := by
  simp [runTop, blocksWord, braidRun]

theorem runTop_cons (m : ℕ) (b : SBlock) (bs : List SBlock) (f : Fin m → G) :
    runTop m (b :: bs) f = runTop m bs (b.step m f) := by
  simp only [runTop, blocksWord_cons, braidRun_append, SBlock.step]

theorem runTop_append (m : ℕ) (bs cs : List SBlock) (f : Fin m → G) :
    runTop m (bs ++ cs) f = runTop m cs (runTop m bs f) := by
  simp only [runTop, blocksWord, List.flatMap_append, braidRun_append]

theorem stPerm_lt {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m) (t : ℕ) (ht : t < m) :
    stPerm bs t < m := by
  induction bs with
  | nil => simpa [stPerm] using ht
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    exact SBlock.perm_lt b hv.1 _ (ih hv.2)

theorem prePr_runTop {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m) (f : Fin m → G)
    (n : ℕ) : prePr (runTop m bs f) n = gapProd m bs f n * prePr f n := by
  induction bs generalizing f with
  | nil => simp [runTop_nil, gapProd]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [runTop_cons, ih hv.2, SBlock.prePr_step b hv.1, gapProd, mul_assoc]

theorem edgeMer_runTop {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m) (f : Fin m → G)
    (t : ℕ) (ht : t < m) :
    edgeMer (runTop m bs f) t =
      stLoop m bs f t * edgeMer f (stPerm bs t) * (stLoop m bs f t)⁻¹ := by
  induction bs generalizing f with
  | nil => simp [runTop_nil, stLoop, stPerm]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [runTop_cons, ih hv.2, SBlock.edgeMer_step b hv.1 f _ (stPerm_lt bs hv.2 t ht), stLoop,
      stPerm]
    group

theorem artinWord_blocksWord_fst {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m)
    (t : Fin m) : ((artinWord m (blocksWord bs) t).1 : ℕ) = stPerm bs t := by
  induction bs with
  | nil => simp [blocksWord, artinWord, stPerm]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [blocksWord_cons, artinWord_append_fst, SBlock.artinWord_word_fst b hv.1, ih hv.2,
      stPerm]

theorem braidRun_blocksWord_snd {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m)
    (f : Fin m → G) (t : Fin m) :
    (braidRun m (blocksWord bs) f).2 t =
      (prePr (runTop m bs f) t)⁻¹ * edgeMer (runTop m bs f) t ^ stCount bs t *
        stLoop m bs f t * prePr f (stPerm bs t) := by
  induction bs generalizing f with
  | nil => simp [blocksWord, braidRun, runTop_nil, stCount, stLoop, stPerm]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [blocksWord_cons, braidRun_append]
    simp only
    rw [← SBlock.step, ih hv.2, SBlock.braidRun_word_snd b hv.1,
      artinWord_blocksWord_fst bs hv.2, runTop_cons, stCount, stLoop, stPerm, zpow_add]
    have hE := edgeMer_runTop bs hv.2 (b.step m f) t t.2
    set S := stLoop m bs (b.step m f) t
    set e := edgeMer (b.step m f) (stPerm bs t)
    have hc : S * e ^ b.count (stPerm bs t) =
        edgeMer (runTop m bs (b.step m f)) t ^ b.count (stPerm bs t) * S := by
      rw [hE, conj_zpow]
      group
    calc _ = (prePr (runTop m bs (b.step m f)) t)⁻¹ *
          edgeMer (runTop m bs (b.step m f)) t ^ stCount bs t *
          (S * e ^ b.count (stPerm bs t)) * b.strandLoop f (stPerm bs t) *
          prePr f (b.perm (stPerm bs t)) := by group
      _ = _ := by rw [hc]; group

theorem gapProd_append (m : ℕ) (bs cs : List SBlock) (f : Fin m → G) (n : ℕ) :
    gapProd m (bs ++ cs) f n = gapProd m cs (runTop m bs f) n * gapProd m bs f n := by
  induction bs generalizing f with
  | nil => simp [runTop_nil, gapProd]
  | cons b bs ih => rw [List.cons_append, gapProd, ih, gapProd, runTop_cons, mul_assoc]

theorem stPerm_append (bs cs : List SBlock) (t : ℕ) :
    stPerm (bs ++ cs) t = stPerm bs (stPerm cs t) := by
  induction bs with
  | nil => simp [stPerm]
  | cons b bs ih => rw [List.cons_append, stPerm, ih, stPerm]

theorem stLoop_append (m : ℕ) (bs cs : List SBlock) (f : Fin m → G) (t : ℕ) :
    stLoop m (bs ++ cs) f t = stLoop m cs (runTop m bs f) t * stLoop m bs f (stPerm cs t) := by
  induction bs generalizing f with
  | nil => simp [runTop_nil, stLoop]
  | cons b bs ih =>
    rw [List.cons_append, stLoop, ih, stLoop, runTop_cons, stPerm_append, mul_assoc]

theorem stCount_append (bs cs : List SBlock) (t : ℕ) :
    stCount (bs ++ cs) t = stCount cs t + stCount bs (stPerm cs t) := by
  induction bs with
  | nil => simp [stCount]
  | cons b bs ih => rw [List.cons_append, stCount, ih, stCount, stPerm_append, add_assoc]

theorem loopAt_append_left (m : ℕ) (bs cs : List SBlock) (f : Fin m → G) (r : ℕ)
    (hr : r < bs.length) : loopAt m (bs ++ cs) f r = loopAt m bs f r := by
  simp only [loopAt, List.getD_append _ _ _ _ hr, List.take_append_of_le_length hr.le]

theorem loopAt_append_right (m : ℕ) (bs cs : List SBlock) (f : Fin m → G) (r : ℕ) :
    loopAt m (bs ++ cs) f (bs.length + r) = loopAt m cs (runTop m bs f) r := by
  simp only [loopAt, List.getD_eq_getElem?_getD, List.take_append, runTop_append,
    List.take_of_length_le (Nat.le_add_right bs.length r),
    List.getElem?_append_right (Nat.le_add_right bs.length r), Nat.add_sub_cancel_left]

end AJConjecture
