import Mathlib
import AJFamily.Classical.FamilyPeripheralRun

/-!
# Running a block list on a longer tuple

A list of blocks that lives on `m` strands, run on a tuple of `m' ≥ m` group elements, acts on
the first `m` entries as on the restricted tuple and leaves the other entries alone: the loop
of a block only reads the chamber products `prePr f n`, `n ≤ m`. This lets the theorems about
`pairBlocks r s` (on `2c + 1` strands) be used for block lists with additional top strands.

Route: `prePr_resTuple` by `List.take`; one block by `SBlock.prePr_step` on both sides (the
loops agree, hence all chamber products `≤ m`, hence the entries, since
`f n = (prePr f n)⁻¹ * prePr f (n + 1)`); for the entries `≥ m` compare the chamber products
`> m`, which no gap interval contains; lists by induction with `runTop_cons`, `stLoop`,
`gapProd`, `loopAt`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The first `m` entries of a tuple of `m' ≥ m` elements. -/
def resTuple {m m' : ℕ} (hm : m ≤ m') (F : Fin m' → G) : Fin m → G :=
  fun k ↦ F (Fin.castLE hm k)

theorem prePr_resTuple {m m' : ℕ} (hm : m ≤ m') (F : Fin m' → G) {n : ℕ} (hn : n ≤ m) :
    prePr (resTuple hm F) n = prePr F n := by
  induction n with
  | zero => rw [prePr_zero, prePr_zero]
  | succ n ih =>
    rw [prePr_succ _ n (by omega), prePr_succ F n (by omega), ih (by omega)]
    rfl

/-- An entry of a tuple is the ratio of two consecutive chamber products. -/
private theorem apply_eq_prePr_twCRestrict {m : ℕ} (f : Fin m → G) (k : Fin m) :
    f k = (prePr f k)⁻¹ * prePr f (k + 1) := by
  rw [prePr_succ f k k.2, inv_mul_cancel_left]

/-- The loop of a block living on `m` strands only reads the first `m` entries. -/
private theorem loop_resTuple_twCRestrict {m m' : ℕ} (hm : m ≤ m') (b : SBlock)
    (hb : b.Valid m) (F : Fin m' → G) : b.loop (resTuple hm F) = b.loop F := by
  cases b with
  | band i j =>
    obtain ⟨hij, hj⟩ := hb
    simp only [SBlock.loop]
    rw [prePr_resTuple hm F (show j + 1 ≤ m by omega), prePr_resTuple hm F (show j ≤ m by omega),
      prePr_resTuple hm F (show i ≤ m by omega), prePr_resTuple hm F (show i + 1 ≤ m by omega)]
  | neg i =>
    have hi : i + 1 < m := hb
    simp only [SBlock.loop]
    rw [prePr_resTuple hm F (show i ≤ m by omega), prePr_resTuple hm F (show i + 1 ≤ m by omega),
      prePr_resTuple hm F (show i + 2 ≤ m by omega)]

/-- A block living on `m` strands lives on more strands. -/
private theorem valid_mono_twCRestrict {m m' : ℕ} (hm : m ≤ m') (b : SBlock) (hb : b.Valid m) :
    b.Valid m' := by
  cases b <;> simp only [SBlock.Valid] at hb ⊢ <;> omega

/-- The upper end of the gap interval of a block living on `m` strands is below `m`. -/
private theorem hi_lt_twCRestrict {m : ℕ} (b : SBlock) (hb : b.Valid m) : b.hi < m := by
  cases b <;> simp only [SBlock.Valid, SBlock.hi] at hb ⊢ <;> omega

/-- The chamber products above a block living on `m` strands, read on a longer tuple. -/
private theorem prePr_step_resTuple_twCRestrict {m m' : ℕ} (hm : m ≤ m') (b : SBlock)
    (hb : b.Valid m) (F : Fin m' → G) (n : ℕ) :
    prePr (b.step m' F) n = b.gapLoop (resTuple hm F) n * prePr F n := by
  rw [SBlock.prePr_step b (valid_mono_twCRestrict hm b hb), SBlock.gapLoop, SBlock.gapLoop,
    loop_resTuple_twCRestrict hm b hb]

/-- One block living on `m` strands commutes with restriction. -/
private theorem resTuple_step_twCRestrict {m m' : ℕ} (hm : m ≤ m') (b : SBlock)
    (hb : b.Valid m) (F : Fin m' → G) :
    resTuple hm (b.step m' F) = b.step m (resTuple hm F) := by
  funext k
  rw [apply_eq_prePr_twCRestrict (b.step m (resTuple hm F)) k, SBlock.prePr_step b hb,
    SBlock.prePr_step b hb, prePr_resTuple hm F k.2.le, prePr_resTuple hm F (Nat.succ_le_of_lt k.2),
    ← prePr_step_resTuple_twCRestrict hm b hb, ← prePr_step_resTuple_twCRestrict hm b hb]
  exact apply_eq_prePr_twCRestrict (b.step m' F) (Fin.castLE hm k)

/-- One block living on `m` strands does not change the entries `≥ m`. -/
private theorem step_apply_of_ge_twCRestrict {m m' : ℕ} (hm : m ≤ m') (b : SBlock)
    (hb : b.Valid m) (F : Fin m' → G) (k : Fin m') (hk : m ≤ (k : ℕ)) :
    b.step m' F k = F k := by
  have hhi := hi_lt_twCRestrict b hb
  rw [apply_eq_prePr_twCRestrict (b.step m' F) k, apply_eq_prePr_twCRestrict F k,
    SBlock.prePr_step b (valid_mono_twCRestrict hm b hb),
    SBlock.prePr_step b (valid_mono_twCRestrict hm b hb), SBlock.gapLoop, SBlock.gapLoop,
    ite_eq_right (by omega), ite_eq_right (by omega), one_mul, one_mul]

/-- The run of blocks living on `m` strands commutes with restriction. -/
theorem resTuple_runTop {m m' : ℕ} (hm : m ≤ m') (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (F : Fin m' → G) :
    resTuple hm (runTop m' bs F) = runTop m bs (resTuple hm F) := by
  induction bs generalizing F with
  | nil => rw [runTop_nil, runTop_nil]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [runTop_cons, runTop_cons, ih hv.2, resTuple_step_twCRestrict hm b hv.1]

/-- The run of blocks living on `m` strands does not change the entries `≥ m`. -/
theorem runTop_apply_of_ge {m m' : ℕ} (hm : m ≤ m') (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (F : Fin m' → G) (k : Fin m') (hk : m ≤ (k : ℕ)) :
    runTop m' bs F k = F k := by
  induction bs generalizing F with
  | nil => rw [runTop_nil]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [runTop_cons, ih hv.2, step_apply_of_ge_twCRestrict hm b hv.1 F k hk]

theorem loopAt_resTuple {m m' : ℕ} (hm : m ≤ m') (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (F : Fin m' → G) {q : ℕ} (hq : q < bs.length) :
    loopAt m' bs F q = loopAt m bs (resTuple hm F) q := by
  have hb : (bs.getD q (SBlock.neg 0)).Valid m := by
    rw [List.getD_eq_getElem _ _ hq]
    exact hv _ (List.getElem_mem hq)
  rw [loopAt, loopAt, ← resTuple_runTop hm _ (fun b hb ↦ hv b (List.mem_of_mem_take hb)),
    loop_resTuple_twCRestrict hm _ hb]

theorem gapProd_resTuple {m m' : ℕ} (hm : m ≤ m') (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (F : Fin m' → G) (n : ℕ) :
    gapProd m' bs F n = gapProd m bs (resTuple hm F) n := by
  induction bs generalizing F with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [gapProd, gapProd, ih hv.2, resTuple_step_twCRestrict hm b hv.1, SBlock.gapLoop,
      SBlock.gapLoop, loop_resTuple_twCRestrict hm b hv.1]

theorem stLoop_resTuple {m m' : ℕ} (hm : m ≤ m') (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (F : Fin m' → G) (t : ℕ) :
    stLoop m' bs F t = stLoop m bs (resTuple hm F) t := by
  induction bs generalizing F with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [stLoop, stLoop, ih hv.2, resTuple_step_twCRestrict hm b hv.1, SBlock.strandLoop,
      SBlock.strandLoop, loop_resTuple_twCRestrict hm b hv.1]

end AJConjecture
