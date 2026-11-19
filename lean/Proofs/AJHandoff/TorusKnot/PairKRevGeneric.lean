import Mathlib
import AJFamily.Classical.FamilyPeripheralRun

/-!
# Fixed tuples of a block word from prescribed loops

Two generic tools for constructing a tuple fixed by the run of a list of blocks:

* `runTop_eq_self_of_gapProd`: a tuple is fixed by the run as soon as all its gap products are
  `1` (the chamber products determine the tuple);
* `loopAt_eq_of_prescribed`: if values `ℓ q` are prescribed for the block loops and the bottom
  tuple `f` satisfies, for every block, the loop equation `ℓ q = loopPr b_q (G_q · prePr f)`,
  where `G_q n` is the product of the prescribed loops of the earlier blocks whose gap contains
  `n` (`gapPrefix`), then the block loops of `f` are the `ℓ q` and its gap products are the
  products `gapPrefix bs ℓ n` of the prescribed loops.

Together they turn the construction of a fixed tuple into pure algebra: choose the loops `ℓ`
with all `gapPrefix bs ℓ n = 1`, and the bottom edge meridians solving the loop equations.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The loop of a block read on a chamber-product function `P` (`P n` the product below level
`n`). -/
def loopPr (b : SBlock) (P : ℕ → G) : G :=
  match b with
  | .band i j => P (j + 1) * (P j)⁻¹ * P i * (P (i + 1))⁻¹
  | .neg i => P i * (P (i + 1))⁻¹ * P (i + 2) * (P (i + 1))⁻¹

/-- The product of the prescribed loops `ℓ 0, ℓ 1, …` of the blocks of a list whose gap contains
the level `n` (the later blocks on the left), as in `gapProd`. -/
def gapPrefix : List SBlock → (ℕ → G) → ℕ → G
  | [], _, _ => 1
  | b :: bs, ℓ, n => gapPrefix bs (fun q ↦ ℓ (q + 1)) n * (if b.lo ≤ n ∧ n ≤ b.hi then ℓ 0 else 1)

theorem sBlock_loop_eq_loopPr {m : ℕ} (b : SBlock) (f : Fin m → G) :
    b.loop f = loopPr b (prePr f) := by
  cases b <;> rfl

/-- A tuple whose gap products are all `1` is fixed by the run. -/
theorem runTop_eq_self_of_gapProd {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m)
    (f : Fin m → G) (h : ∀ n, gapProd m bs f n = 1) : runTop m bs f = f := by
  have hP : ∀ n, prePr (runTop m bs f) n = prePr f n := fun n ↦ by
    rw [prePr_runTop bs hv, h, one_mul]
  funext t
  have h1 := prePr_succ (runTop m bs f) t t.2
  have h2 := prePr_succ f t t.2
  rw [hP, hP, h2] at h1
  exact (mul_left_cancel h1).symm

/-- Prescribed loops: if every block loop equation holds on the chamber products corrected by
the earlier prescribed loops, the block loops are the prescribed ones and the gap products are
the products of the prescribed loops. -/
theorem loopAt_eq_of_prescribed {m : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid m)
    (f : Fin m → G) (ℓ : ℕ → G)
    (h : ∀ q < bs.length, ℓ q =
      loopPr (bs.getD q (SBlock.neg 0)) (fun n ↦ gapPrefix (bs.take q) ℓ n * prePr f n)) :
    (∀ q < bs.length, loopAt m bs f q = ℓ q) ∧ ∀ n, gapProd m bs f n = gapPrefix bs ℓ n := by
  induction bs generalizing f ℓ with
  | nil => exact ⟨fun q hq ↦ absurd hq (Nat.not_lt_zero q), fun n ↦ rfl⟩
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    have h0 : ℓ 0 = b.loop f := by
      have := h 0 (by simp)
      simp only [List.getD_cons_zero, List.take_zero, gapPrefix, one_mul] at this
      rw [this, sBlock_loop_eq_loopPr]
    have hgl : ∀ n, b.gapLoop f n = if b.lo ≤ n ∧ n ≤ b.hi then ℓ 0 else 1 := fun n ↦ by
      rw [SBlock.gapLoop, h0]
    have hstep : ∀ n, prePr (b.step m f) n =
        (if b.lo ≤ n ∧ n ≤ b.hi then ℓ 0 else 1) * prePr f n := fun n ↦ by
      rw [SBlock.prePr_step b hv.1, hgl]
    obtain ⟨ih1, ih2⟩ := ih hv.2 (b.step m f) (fun q ↦ ℓ (q + 1)) fun q hq ↦ by
      have := h (q + 1) (by simp; omega)
      simp only [List.getD_cons_succ, List.take_succ_cons, gapPrefix] at this
      rw [this]
      congr 1
      funext n
      rw [hstep, mul_assoc]
    refine ⟨fun q hq ↦ ?_, fun n ↦ ?_⟩
    · cases q with
      | zero => simp [loopAt, runTop_nil, h0]
      | succ q =>
        have := ih1 q (by simp at hq; omega)
        simpa [loopAt, runTop_cons] using this
    · rw [gapProd, ih2, gapPrefix, hgl]

end AJConjecture
