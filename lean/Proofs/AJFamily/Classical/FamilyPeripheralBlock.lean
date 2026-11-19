import Mathlib
import AJFamily.Classical.BandWord

/-!
# The run of one block

The run of one block of a braided-surface word, a positive band `bandWord i j true` or a single
negative letter `σ_i⁻¹` (`SBlock`), in terms of the chamber products `prePr f n = f₀ ⋯ f_{n-1}`
and the edge meridians `edgeMer f t = prePr f (t+1) (prePr f t)⁻¹`. A block multiplies the
chamber products of its gap interval on the left by its loop (`prePr_step`), permutes the edge
meridians and conjugates them by the loop (`edgeMer_step`), and its conjugators are ratios of
chamber products (`braidRun_word_snd`).
-/

namespace AJConjecture

section Chamber

variable {G : Type*} [Group G]

/-- The chamber product below level `n`: the product of the first `n` entries of a tuple
(all entries if `n ≥ m`). -/
def prePr {m : ℕ} (f : Fin m → G) (n : ℕ) : G :=
  ((List.ofFn f).take n).prod

/-- The edge meridian of level `t`: `prePr f (t + 1) * (prePr f t)⁻¹`. -/
def edgeMer {m : ℕ} (f : Fin m → G) (t : ℕ) : G :=
  prePr f (t + 1) * (prePr f t)⁻¹

theorem prePr_zero {m : ℕ} (f : Fin m → G) : prePr f 0 = 1 := by
  simp [prePr]

theorem prePr_succ {m : ℕ} (f : Fin m → G) (n : ℕ) (hn : n < m) :
    prePr f (n + 1) = prePr f n * f ⟨n, hn⟩ := by
  simp [prePr, List.take_add_one, hn]

theorem edgeMer_zero {m : ℕ} (f : Fin m → G) (hm : 0 < m) : edgeMer f 0 = f ⟨0, hm⟩ := by
  rw [edgeMer, prePr_succ f 0 hm, prePr_zero]
  simp

/-- The chamber product is constant from `m` on. -/
private theorem prePr_of_length_le {m : ℕ} (f : Fin m → G) {n : ℕ} (hn : m ≤ n) :
    prePr f n = prePr f m := by
  simp [prePr, List.take_of_length_le, hn]

/-- The chamber product does not grow from `m` on. -/
private theorem prePr_succ_of_length_le {m : ℕ} (f : Fin m → G) {n : ℕ} (hn : m ≤ n) :
    prePr f (n + 1) = prePr f n := by
  rw [prePr_of_length_le f hn, prePr_of_length_le f (by omega)]

/-- A tuple `f'` whose chamber products are those of `f` multiplied on the left by `g`, checked
one level at a time. -/
private theorem prePr_eq_of_levelwise {m : ℕ} (f f' : Fin m → G) (g : ℕ → G) (h0 : g 0 = 1)
    (hm : ∀ n, m ≤ n → g (n + 1) = g n)
    (hs : ∀ n (hn : n < m), g n * prePr f n * f' ⟨n, hn⟩ = g (n + 1) * prePr f n * f ⟨n, hn⟩)
    (n : ℕ) : prePr f' n = g n * prePr f n := by
  induction n with
  | zero => rw [prePr_zero, prePr_zero, h0, one_mul]
  | succ n ih =>
    by_cases hn : n < m
    · rw [prePr_succ f' n hn, prePr_succ f n hn, ih, hs n hn, mul_assoc]
    · rw [prePr_succ_of_length_le f' (by omega), prePr_succ_of_length_le f (by omega), ih,
        hm n (by omega)]

/-- The chamber product of level `j` splits at level `i + 1` with the product strictly between
the levels `i` and `j`. -/
private theorem prePr_eq_mul_midProd {m i j : ℕ} (hij : i < j) (hj : j ≤ m) (f : Fin m → G) :
    prePr f j = prePr f (i + 1) * midProd f i j := by
  induction j, hij using Nat.le_induction with
  | base =>
    have h : (List.finRange m).filter (fun l : Fin m ↦ i < (l : ℕ) ∧ (l : ℕ) < i + 1) = [] :=
      List.filter_eq_nil_iff.2 fun x _ ↦ by
        simp only [decide_eq_true_eq, not_and, not_lt]
        omega
    rw [midProd, h]
    simp
  | succ j hij ih =>
    have h := filter_lt_succ_of_pairwise (fun k ↦ i < k) j hj _ (List.pairwise_lt_finRange m)
      (List.mem_finRange _)
    simp only [show i < j by omega, ite_true] at h
    rw [prePr_succ f j hj, ih (by omega), midProd, midProd, h, List.map_append, List.prod_append]
    simp [mul_assoc]

end Chamber

/-- A block of a braided-surface word: a positive band `b(i, j)` or a single negative letter
`σ_i⁻¹`. -/
inductive SBlock where
  | band (i j : ℕ)
  | neg (i : ℕ)
  deriving DecidableEq

namespace SBlock

/-- The braid word of a block. -/
def word : SBlock → BraidWord
  | band i j => bandWord i j true
  | neg i => [(i, false)]

/-- The block lives on `m` strands. -/
def Valid (m : ℕ) : SBlock → Prop
  | band i j => i < j ∧ j < m
  | neg i => i + 1 < m

/-- Lower end of the gap interval (in `prePr` indices). -/
def lo : SBlock → ℕ
  | band i _ => i + 1
  | neg i => i + 1

/-- Upper end of the gap interval (in `prePr` indices). -/
def hi : SBlock → ℕ
  | band _ j => j
  | neg i => i + 1

/-- The bottom position of the strand at top position `t`. -/
def perm : SBlock → ℕ → ℕ
  | band i j, t => if t = i then j else if t = j then i else t
  | neg i, t => if t = i then i + 1 else if t = i + 1 then i else t

/-- Whether the strand at top position `t` collects the loop of the block. -/
def carries : SBlock → ℕ → Bool
  | band i j, t => decide (t = j ∨ (i < t ∧ t < j))
  | neg i, t => decide (t = i)

/-- The meridian count of the strand at top position `t`. -/
def count : SBlock → ℕ → ℤ
  | band _ j, t => if t = j then 1 else 0
  | neg i, t => if t = i then -1 else 0

variable {G : Type*} [Group G]

/-- The loop of a block, read on the tuple `f` below it. -/
def loop {m : ℕ} (f : Fin m → G) : SBlock → G
  | band i j => prePr f (j + 1) * (prePr f j)⁻¹ * prePr f i * (prePr f (i + 1))⁻¹
  | neg i => prePr f i * (prePr f (i + 1))⁻¹ * prePr f (i + 2) * (prePr f (i + 1))⁻¹

/-- The tuple above a block. -/
def step (m : ℕ) (b : SBlock) (f : Fin m → G) : Fin m → G := (braidRun m b.word f).1

/-- The loop collected by the strand at top position `t`. -/
def strandLoop {m : ℕ} (f : Fin m → G) (b : SBlock) (t : ℕ) : G :=
  if b.carries t then b.loop f else 1

/-- The factor of the chamber product of level `n`. -/
def gapLoop {m : ℕ} (f : Fin m → G) (b : SBlock) (n : ℕ) : G :=
  if b.lo ≤ n ∧ n ≤ b.hi then b.loop f else 1

theorem perm_lt {m : ℕ} (b : SBlock) (hb : b.Valid m) (t : ℕ) (ht : t < m) : b.perm t < m := by
  cases b <;> simp only [Valid, perm] at hb ⊢ <;> split_ifs <;> omega

theorem artinWord_word_fst {m : ℕ} (b : SBlock) (hb : b.Valid m) (t : Fin m) :
    ((artinWord m b.word t).1 : ℕ) = b.perm t := by
  cases b with
  | band i j => exact artinWord_bandWord_fst hb.1 hb.2 true t
  | neg i =>
    simp only [Valid] at hb
    simp only [word, artinWord, perm, artinGen, hb, dite_true]
    split_ifs <;> simp_all

/-- The tuple above a band, entrywise. -/
private theorem step_band_apply {m i j : ℕ} (hij : i < j) (hj : j < m) (f : Fin m → G) (n : ℕ)
    (hn : n < m) : (band i j).step m f ⟨n, hn⟩ =
      if n = i then (f ⟨i, by omega⟩ * midProd f i j) * f ⟨j, hj⟩ *
          (f ⟨i, by omega⟩ * midProd f i j)⁻¹
      else if n = j then (midProd f i j)⁻¹ * f ⟨i, by omega⟩ * midProd f i j
      else f ⟨n, hn⟩ := by
  simp [step, word, braidRun_bandWord_fst hij hj]

/-- The tuple above a negative letter, entrywise. -/
private theorem step_neg_apply {m i : ℕ} (hi : i + 1 < m) (f : Fin m → G) (n : ℕ)
    (hn : n < m) : (neg i).step m f ⟨n, hn⟩ =
      if n = i then f ⟨i + 1, hi⟩
      else if n = i + 1 then (f ⟨i + 1, hi⟩)⁻¹ * f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩
      else f ⟨n, hn⟩ := by
  show braidStep m (i, false) f ⟨n, hn⟩ = _
  simp only [braidStep, artinGen, hi, dite_true, Bool.false_eq_true, ite_false]
  split_ifs <;> subst_vars <;> simp

/-- The factor of the chamber products of a band. -/
private theorem gapLoop_band {m : ℕ} (f : Fin m → G) (i j n : ℕ) :
    (band i j).gapLoop f n = if i + 1 ≤ n ∧ n ≤ j then (band i j).loop f else 1 := rfl

/-- The factor of the chamber products of a negative letter. -/
private theorem gapLoop_neg {m : ℕ} (f : Fin m → G) (i n : ℕ) :
    (neg i).gapLoop f n = if n = i + 1 then (neg i).loop f else 1 := by
  simp only [gapLoop, lo, hi]
  congr 1
  apply propext
  omega

/-- The chamber products above a band. -/
private theorem prePr_step_band {m i j : ℕ} (hij : i < j) (hj : j < m) (f : Fin m → G) (n : ℕ) :
    prePr ((band i j).step m f) n = (band i j).gapLoop f n * prePr f n := by
  have hP : prePr f j = prePr f i * f ⟨i, by omega⟩ * midProd f i j := by
    rw [prePr_eq_mul_midProd hij hj.le, prePr_succ f i (by omega)]
  have hL : (band i j).loop f = (prePr f i * f ⟨i, by omega⟩ * midProd f i j) * f ⟨j, hj⟩ *
      (prePr f i * f ⟨i, by omega⟩ * midProd f i j)⁻¹ *
        (prePr f i * (f ⟨i, by omega⟩)⁻¹ * (prePr f i)⁻¹) := by
    rw [loop, prePr_succ f j hj, hP, prePr_succ f i (by omega)]
    group
  refine prePr_eq_of_levelwise f _ _ ?_ ?_ ?_ n
  · rw [gapLoop_band]
    simp
  · intro n hn
    rw [gapLoop_band, gapLoop_band]
    split_ifs <;> first | rfl | omega
  · intro n hn
    rw [step_band_apply hij hj, gapLoop_band, gapLoop_band]
    split_ifs <;> subst_vars <;> first | omega | rfl | (rw [hL]; group; done) | (rw [hL, hP]; group)

/-- The chamber products above a negative letter. -/
private theorem prePr_step_neg {m i : ℕ} (hi : i + 1 < m) (f : Fin m → G) (n : ℕ) :
    prePr ((neg i).step m f) n = (neg i).gapLoop f n * prePr f n := by
  have hL : (neg i).loop f = prePr f i * f ⟨i + 1, hi⟩ * (f ⟨i, by omega⟩)⁻¹ * (prePr f i)⁻¹ := by
    rw [loop, show i + 2 = i + 1 + 1 from rfl, prePr_succ f (i + 1) hi,
      prePr_succ f i (by omega)]
    group
  refine prePr_eq_of_levelwise f _ _ ?_ ?_ ?_ n
  · rw [gapLoop_neg]
    simp
  · intro n hn
    rw [gapLoop_neg, gapLoop_neg]
    split_ifs <;> first | rfl | omega
  · intro n hn
    rw [step_neg_apply hi, gapLoop_neg, gapLoop_neg]
    split_ifs <;> subst_vars <;> first | omega | rfl | (rw [hL]; group; done) |
      (rw [hL, prePr_succ f i (by omega)]; group)

theorem prePr_step {m : ℕ} (b : SBlock) (hb : b.Valid m) (f : Fin m → G) (n : ℕ) :
    prePr (b.step m f) n = b.gapLoop f n * prePr f n := by
  cases b with
  | band i j => exact prePr_step_band hb.1 hb.2 f n
  | neg i => exact prePr_step_neg hb f n

/-- The edge meridians above a block, in terms of the factors of the chamber products. -/
private theorem edgeMer_step_gapLoop {m : ℕ} (b : SBlock) (hb : b.Valid m) (f : Fin m → G)
    (t : ℕ) : edgeMer (b.step m f) t = b.gapLoop f (t + 1) * edgeMer f t * (b.gapLoop f t)⁻¹ := by
  rw [edgeMer, edgeMer, prePr_step b hb, prePr_step b hb]
  group

/-- The loop of a band in terms of edge meridians. -/
private theorem loop_band_eq_edgeMer {m : ℕ} (f : Fin m → G) (i j : ℕ) :
    (band i j).loop f = edgeMer f j * (edgeMer f i)⁻¹ := by
  simp only [loop, edgeMer]
  group

/-- The loop of a negative letter in terms of edge meridians. -/
private theorem loop_neg_eq_edgeMer {m : ℕ} (f : Fin m → G) (i : ℕ) :
    (neg i).loop f = (edgeMer f i)⁻¹ * edgeMer f (i + 1) := by
  simp only [loop, edgeMer]
  group

theorem edgeMer_step {m : ℕ} (b : SBlock) (hb : b.Valid m) (f : Fin m → G) (t : ℕ) (ht : t < m) :
    edgeMer (b.step m f) t = b.strandLoop f t * edgeMer f (b.perm t) * (b.strandLoop f t)⁻¹ := by
  rw [edgeMer_step_gapLoop b hb]
  cases b with
  | band i j =>
    have hL := loop_band_eq_edgeMer f i j
    have hij : i < j := hb.1
    simp only [gapLoop_band, strandLoop, carries, perm, decide_eq_true_eq]
    split_ifs <;> subst_vars <;> first | omega | (simp only [hL]; group) | group
  | neg i =>
    have hL := loop_neg_eq_edgeMer f i
    simp only [gapLoop_neg, strandLoop, carries, perm, decide_eq_true_eq]
    split_ifs <;> subst_vars <;> first | omega | (simp only [hL]; group) | group

/-- The conjugators of a negative letter. -/
private theorem braidRun_neg_snd {m i : ℕ} (hi : i + 1 < m) (f : Fin m → G) (t : Fin m) :
    (braidRun m (neg i).word f).2 t = if (t : ℕ) = i + 1 then (f ⟨i + 1, hi⟩)⁻¹ else 1 := by
  obtain ⟨n, hn⟩ := t
  show FreeGroup.lift f (artinGen m (i, false) ⟨n, hn⟩).2 * 1 = _
  simp only [artinGen, hi, dite_true, Bool.false_eq_true, ite_false]
  split_ifs <;> first | omega | simp_all

theorem braidRun_word_snd {m : ℕ} (b : SBlock) (hb : b.Valid m) (f : Fin m → G) (t : Fin m) :
    (braidRun m b.word f).2 t =
      (prePr (b.step m f) t)⁻¹ * edgeMer (b.step m f) t ^ b.count t * b.strandLoop f t *
        prePr f (b.perm t) := by
  rw [prePr_step b hb, edgeMer_step_gapLoop b hb]
  cases b with
  | band i j =>
    obtain ⟨hij, hj⟩ := hb
    have hPi : prePr f (i + 1) = prePr f i * f ⟨i, by omega⟩ := prePr_succ f i (by omega)
    have hP : prePr f j = prePr f i * f ⟨i, by omega⟩ * midProd f i j := by
      rw [prePr_eq_mul_midProd hij hj.le, hPi]
    rw [word, braidRun_bandWord_snd hij hj]
    simp only [gapLoop_band, strandLoop, carries, perm, count, decide_eq_true_eq, ite_true, loop,
      edgeMer]
    split_ifs <;> subst_vars <;> first | omega | ((try simp only [hP, hPi]); group)
  | neg i =>
    have hi : i + 1 < m := hb
    have hPi : prePr f (i + 1) = prePr f i * f ⟨i, by omega⟩ := prePr_succ f i (by omega)
    have h2 : prePr f (i + 2) = prePr f i * f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩ := by
      rw [show i + 2 = i + 1 + 1 from rfl, prePr_succ f (i + 1) hi, hPi]
    rw [braidRun_neg_snd hi]
    obtain ⟨n, hn⟩ := t
    simp only [gapLoop_neg, strandLoop, carries, perm, count, decide_eq_true_eq, loop, edgeMer]
    split_ifs <;> subst_vars <;> first | omega | ((try simp only [h2, hPi]); group)

end SBlock

end AJConjecture
