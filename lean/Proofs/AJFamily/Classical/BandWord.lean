import Mathlib
import AJFamily.Classical.BraidRunAppend
import AJConjecture.BraidRun

/-!
# Band words

The band generator between the levels `i < j` of a braid, the letter `σ_i^{±1}` conjugated by
`σ_{j-1} ⋯ σ_{i+1}`, as a braid word (`bandWord`). Its Artin action swaps the strands `i` and
`j`, and its run on a tuple of colours is given in closed form through the product `midProd`
of the colours strictly between the two levels.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The band generator between the levels `i < j` with sign `b`. -/
def bandWord (i j : ℕ) (b : Bool) : BraidWord :=
  ((List.range (j - 1 - i)).map fun t ↦ (j - 1 - t, true)) ++ [(i, b)] ++
    ((List.range (j - 1 - i)).map fun t ↦ (i + 1 + t, false))

/-- The band word of span one is a single letter. -/
private theorem bandWord_self_succ (i : ℕ) (b : Bool) : bandWord i (i + 1) b = [(i, b)] := by
  simp [bandWord]

/-- The band word of span `j + 1 - i` is the band word of span `j - i` conjugated by `σ_j`. -/
private theorem bandWord_succ_right {i j : ℕ} (hij : i < j) (b : Bool) :
    bandWord i (j + 1) b = (j, true) :: (bandWord i j b ++ [(j, false)]) := by
  obtain ⟨k, hk⟩ : ∃ k, j - 1 - i = k := ⟨_, rfl⟩
  have hk' : j + 1 - 1 - i = k + 1 := by omega
  have h1 : (List.range (k + 1)).map (fun t ↦ (j + 1 - 1 - t, true)) =
      (j, true) :: (List.range k).map (fun t ↦ (j - 1 - t, true)) := by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.cons.injEq]
    refine ⟨by simp, List.map_congr_left fun t _ ↦ ?_⟩
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    omega
  have h2 : (List.range (k + 1)).map (fun t ↦ (i + 1 + t, false)) =
      (List.range k).map (fun t ↦ (i + 1 + t, false)) ++ [(j, false)] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    congr 3
    omega
  rw [bandWord, bandWord, hk, hk', h1, h2]
  simp

/-- The product of the colours strictly between the levels `i` and `j`. -/
def midProd {G : Type*} [Group G] {m : ℕ} (f : Fin m → G) (i j : ℕ) : G :=
  (((List.finRange m).filter fun l : Fin m ↦ i < (l : ℕ) ∧ (l : ℕ) < j).map f).prod

/-- In a strictly increasing list containing `n`, the entries below `n + 1` satisfying `p` are
those below `n` followed by `n` itself if it satisfies `p`. -/
theorem filter_lt_succ_of_pairwise {m : ℕ} (p : ℕ → Prop) [DecidablePred p] (n : ℕ)
    (hn : n < m) (L : List (Fin m)) (hL : L.Pairwise (· < ·)) (hmem : (⟨n, hn⟩ : Fin m) ∈ L) :
    L.filter (fun t : Fin m ↦ p t ∧ (t : ℕ) < n + 1) =
      L.filter (fun t : Fin m ↦ p t ∧ (t : ℕ) < n) ++ (if p n then [⟨n, hn⟩] else []) := by
  induction L with
  | nil => simp at hmem
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    by_cases ha : a = ⟨n, hn⟩
    · subst ha
      have h1 : L.filter (fun t : Fin m ↦ p t ∧ (t : ℕ) < n + 1) = [] :=
        List.filter_eq_nil_iff.2 fun x hx ↦ by
          have := hL.1 x hx
          simp only [Fin.lt_def] at this
          simp only [decide_eq_true_eq, not_and, not_lt]
          omega
      have h2 : L.filter (fun t : Fin m ↦ p t ∧ (t : ℕ) < n) = [] :=
        List.filter_eq_nil_iff.2 fun x hx ↦ by
          have := hL.1 x hx
          simp only [Fin.lt_def] at this
          simp only [decide_eq_true_eq, not_and, not_lt]
          omega
      rw [List.filter_cons, List.filter_cons, h1, h2]
      by_cases hp : p n <;> simp [hp]
    · have hmem' : (⟨n, hn⟩ : Fin m) ∈ L := by
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h.symm ha
        · exact h
      have hlt : (a : ℕ) < n := by
        have := hL.1 _ hmem'
        simpa [Fin.lt_def] using this
      rw [List.filter_cons, List.filter_cons, ih hL.2 hmem']
      by_cases hpa : p a <;> simp [hpa, hlt, Nat.lt_succ_of_lt hlt]

/-- The entries of `Fin m` below `n + 1` satisfying `p`. -/
private theorem filter_finRange_lt_succ {m : ℕ} (p : ℕ → Prop) [DecidablePred p] (n : ℕ)
    (hn : n < m) :
    (List.finRange m).filter (fun t : Fin m ↦ p t ∧ (t : ℕ) < n + 1) =
      (List.finRange m).filter (fun t : Fin m ↦ p t ∧ (t : ℕ) < n) ++
        (if p n then [⟨n, hn⟩] else []) :=
  filter_lt_succ_of_pairwise p n hn _ (List.pairwise_lt_finRange m) (List.mem_finRange _)

/-- The product between `i` and `j + 1` is the product between `i` and `j` times `f_j`. -/
private theorem midProd_succ_right {G : Type*} [Group G] {m i j : ℕ} (hij : i < j)
    (hj : j < m) (f : Fin m → G) : midProd f i (j + 1) = midProd f i j * f ⟨j, hj⟩ := by
  have h := filter_finRange_lt_succ (fun k ↦ i < k) j hj
  simp only [hij, ite_true] at h
  rw [midProd, midProd, h, List.map_append, List.prod_append]
  simp

/-- The product between two adjacent levels is trivial. -/
private theorem midProd_self_succ {G : Type*} [Group G] {m : ℕ} (i : ℕ) (f : Fin m → G) :
    midProd f i (i + 1) = 1 := by
  have h : (List.finRange m).filter (fun l : Fin m ↦ i < (l : ℕ) ∧ (l : ℕ) < i + 1) = [] :=
    List.filter_eq_nil_iff.2 fun x _ ↦ by
      simp only [decide_eq_true_eq, not_and, not_lt]
      omega
  rw [midProd, h]
  simp

/-- The product between `i` and `j` only depends on the colours strictly between them. -/
private theorem midProd_congr {G : Type*} [Group G] {m : ℕ} (i j : ℕ) (f f' : Fin m → G)
    (h : ∀ l : Fin m, i < (l : ℕ) → (l : ℕ) < j → f l = f' l) :
    midProd f i j = midProd f' i j := by
  rw [midProd, midProd, List.map_congr_left fun l hl ↦ ?_]
  simp only [List.mem_filter, decide_eq_true_eq] at hl
  exact h l hl.2.1 hl.2.2

/-- The strand reached by one letter, as a natural number. -/
private theorem artinGen_fst_val (m : ℕ) (g : ℕ × Bool) (k : Fin m) :
    ((artinGen m g k).1 : ℕ) =
      if g.1 + 1 < m then
        (if (k : ℕ) = g.1 then g.1 + 1 else if (k : ℕ) = g.1 + 1 then g.1 else k)
      else k := by
  unfold artinGen
  split_ifs <;> simp_all

/-- One letter at the lower one of its two strands. -/
private theorem artinGen_of_val_eq {m g : ℕ} (b : Bool) (h : g + 1 < m) {k : Fin m}
    (hk : (k : ℕ) = g) : artinGen m (g, b) k = (⟨g + 1, h⟩, if b then FreeGroup.of k else 1) := by
  simp [artinGen, h, hk]

/-- One letter at the upper one of its two strands. -/
private theorem artinGen_of_val_eq_succ {m g : ℕ} (b : Bool) {k : Fin m}
    (hk : (k : ℕ) = g + 1) :
    artinGen m (g, b) k = (⟨g, by omega⟩, if b then 1 else (FreeGroup.of k)⁻¹) := by
  have h : g + 1 < m := hk ▸ k.2
  simp [artinGen, h, hk]

/-- One letter away from its two strands. -/
private theorem artinGen_of_val_ne {m g : ℕ} (b : Bool) {k : Fin m} (h1 : (k : ℕ) ≠ g)
    (h2 : (k : ℕ) ≠ g + 1) : artinGen m (g, b) k = (k, 1) := by
  simp [artinGen, h1, h2]

/-- One letter on a tuple, at the lower one of its two strands. -/
private theorem braidStep_of_val_eq {G : Type*} [Group G] {m g : ℕ} (b : Bool) (h : g + 1 < m)
    (f : Fin m → G) {k : Fin m} (hk : (k : ℕ) = g) :
    braidStep m (g, b) f k = if b then f k * f ⟨g + 1, h⟩ * (f k)⁻¹ else f ⟨g + 1, h⟩ := by
  cases b <;> simp [braidStep, artinGen_of_val_eq _ h hk]

/-- One letter on a tuple, at the upper one of its two strands. -/
private theorem braidStep_of_val_eq_succ {G : Type*} [Group G] {m g : ℕ} (b : Bool)
    (f : Fin m → G) {k : Fin m} (hk : (k : ℕ) = g + 1) :
    braidStep m (g, b) f k = if b then f ⟨g, by omega⟩ else (f k)⁻¹ * f ⟨g, by omega⟩ * f k := by
  cases b <;> simp [braidStep, artinGen_of_val_eq_succ _ hk]

/-- One letter on a tuple, away from its two strands. -/
private theorem braidStep_of_val_ne {G : Type*} [Group G] {m g : ℕ} (b : Bool) (f : Fin m → G)
    {k : Fin m} (h1 : (k : ℕ) ≠ g) (h2 : (k : ℕ) ≠ g + 1) : braidStep m (g, b) f k = f k := by
  simp [braidStep, artinGen_of_val_ne _ h1 h2]

/-- The strand of Artin's action of a concatenation. -/
theorem artinWord_append_fst (m : ℕ) (u v : BraidWord) (k : Fin m) :
    (artinWord m (u ++ v) k).1 = (artinWord m u (artinWord m v k).1).1 := by
  induction u with
  | nil => simp [artinWord]
  | cons g u ih => simp only [List.cons_append, artinWord, ih]

/-- The strand map of a band word: it swaps the strands `i` and `j`. -/
private theorem artinWord_bandWord_fst_val {m i j : ℕ} (hij : i < j) (hj : j < m) (b : Bool)
    (l : Fin m) : ((artinWord m (bandWord i j b) l).1 : ℕ) =
      if (l : ℕ) = i then j else if (l : ℕ) = j then i else l := by
  induction j, hij using Nat.le_induction generalizing l with
  | base =>
    rw [bandWord_self_succ]
    simp only [artinWord, artinGen_fst_val]
    split_ifs <;> omega
  | succ j hij ih =>
    rw [bandWord_succ_right hij]
    simp only [artinWord]
    rw [artinWord_append_fst]
    simp only [artinWord, artinGen_fst_val, ih (by omega)]
    split_ifs <;> omega

/-- The fold of `braidRunStep` from an arbitrary start is the run on the colours of the start,
with the conjugators of the start appended. -/
private theorem foldl_braidRunStep_eq_band {G : Type*} [Group G] (m : ℕ) (w : BraidWord)
    (s : (Fin m → G) × (Fin m → G)) :
    w.foldl (braidRunStep m) s =
      ((braidRun m w s.1).1, fun k ↦ (braidRun m w s.1).2 k * s.2 (artinWord m w k).1) := by
  refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)
  · rw [(foldl_braidRunStep_apply m w s k).2, braidRun_fst_apply, lift_artinWord_snd]
  · rw [(foldl_braidRunStep_apply m w s k).1, lift_artinWord_snd]

/-- The run of a word with one letter in front. -/
private theorem braidRun_cons_band {G : Type*} [Group G] (m : ℕ) (g : ℕ × Bool)
    (w : BraidWord) (f : Fin m → G) :
    braidRun m (g :: w) f =
      ((braidRun m w (braidStep m g f)).1, fun k ↦
        (braidRun m w (braidStep m g f)).2 k *
          FreeGroup.lift f (artinGen m g (artinWord m w k).1).2) := by
  rw [braidRun, List.foldl_cons, foldl_braidRunStep_eq_band]
  simp [braidRunStep]

/-- The run of a word with one letter at the end. -/
private theorem braidRun_append_singleton_band {G : Type*} [Group G] (m : ℕ) (w : BraidWord)
    (g : ℕ × Bool) (f : Fin m → G) :
    braidRun m (w ++ [g]) f = braidRunStep m (braidRun m w f) g := by
  simp [braidRun, List.foldl_append]

/-- The conjugators of the run of a band word. -/
private theorem braidRun_bandWord_snd_aux {G : Type*} [Group G] {m i j : ℕ} (hij : i < j)
    (hj : j < m) (b : Bool) (f : Fin m → G) :
    (braidRun m (bandWord i j b) f).2 = fun l : Fin m ↦
      if (l : ℕ) = i then (if b then f ⟨i, by omega⟩ * midProd f i j else midProd f i j)
      else if (l : ℕ) = j then
        (if b then (midProd f i j)⁻¹ else (midProd f i j * f ⟨j, hj⟩)⁻¹)
      else 1 := by
  induction j, hij using Nat.le_induction generalizing f with
  | base =>
    funext l
    rw [bandWord_self_succ, midProd_self_succ]
    simp only [braidRun, List.foldl_cons, List.foldl_nil, braidRunStep, mul_one]
    by_cases h1 : (l : ℕ) = i
    · rw [artinGen_of_val_eq b hj h1, ite_eq_left h1]
      subst h1
      cases b <;> simp
    · by_cases h2 : (l : ℕ) = i + 1
      · rw [artinGen_of_val_eq_succ b h2, ite_eq_right h1, ite_eq_left h2]
        have : l = ⟨i + 1, hj⟩ := Fin.ext h2
        subst this
        cases b <;> simp
      · rw [artinGen_of_val_ne b h1 h2, ite_eq_right h1, ite_eq_right h2]
        simp
  | succ j hij ih =>
    have hj' : j < m := by omega
    have hij' : i < j := hij
    funext l
    rw [bandWord_succ_right hij', ← List.cons_append, braidRun_append_singleton_band,
      braidRun_cons_band]
    simp only [braidRunStep]
    set f' := braidStep m (j, true) f with hf'
    have ih' := ih hj' f'
    have hM : midProd f' i j = midProd f i j :=
      midProd_congr i j f' f fun l h1 h2 ↦ braidStep_of_val_ne true f (by omega) (by omega)
    have hfi : f' ⟨i, by omega⟩ = f ⟨i, by omega⟩ :=
      braidStep_of_val_ne true f (by simp; omega) (by simp; omega)
    have hfj : f' ⟨j, hj'⟩ = f ⟨j, hj'⟩ * f ⟨j + 1, hj⟩ * (f ⟨j, hj'⟩)⁻¹ :=
      braidStep_of_val_eq true hj f rfl
    have hfj1 : f' ⟨j + 1, hj⟩ = f ⟨j, hj'⟩ := braidStep_of_val_eq_succ true f rfl
    rw [hM, hfi, hfj] at ih'
    rw [midProd_succ_right hij' hj']
    have hi : i < m := by omega
    have awi : (artinWord m (bandWord i j b) ⟨i, hi⟩).1 = ⟨j, hj'⟩ :=
      Fin.ext (by simp [artinWord_bandWord_fst_val hij' hj'])
    have awj : (artinWord m (bandWord i j b) ⟨j, hj'⟩).1 = ⟨i, hi⟩ :=
      Fin.ext (by simp [artinWord_bandWord_fst_val hij' hj', hij'.ne'])
    have awj1 : (artinWord m (bandWord i j b) ⟨j + 1, hj⟩).1 = ⟨j + 1, hj⟩ :=
      Fin.ext (by simp [artinWord_bandWord_fst_val hij' hj', show j + 1 ≠ i by omega])
    by_cases h1 : (l : ℕ) = i
    · obtain rfl : l = ⟨i, hi⟩ := Fin.ext h1
      simp only [ih', awi,
        artinGen_of_val_ne (k := ⟨i, hi⟩) false (show i ≠ j by omega) (show i ≠ j + 1 by omega),
        artinGen_of_val_eq true hj (rfl : ((⟨j, hj'⟩ : Fin m) : ℕ) = j)]
      cases b <;> simp [mul_assoc]
    by_cases h2 : (l : ℕ) = j + 1
    · obtain rfl : l = ⟨j + 1, hj⟩ := Fin.ext h2
      simp only [artinGen_of_val_eq_succ false (rfl : ((⟨j + 1, hj⟩ : Fin m) : ℕ) = j + 1), ih',
        awj, artinGen_of_val_ne (k := ⟨i, hi⟩) true (show i ≠ j by omega) (show i ≠ j + 1 by omega),
        Bool.false_eq_true, ite_false, map_inv, FreeGroup.lift_apply_of, braidRun_fst_apply,
        awj1, hfj1]
      cases b <;> simp [mul_assoc, show j + 1 ≠ i by omega, hij'.ne']
    by_cases h3 : (l : ℕ) = j
    · obtain rfl : l = ⟨j, hj'⟩ := Fin.ext h3
      simp only [artinGen_of_val_eq false hj (rfl : ((⟨j, hj'⟩ : Fin m) : ℕ) = j), ih', awj1,
        artinGen_of_val_eq_succ true (rfl : ((⟨j + 1, hj⟩ : Fin m) : ℕ) = j + 1)]
      simp [show j + 1 ≠ i by omega, hij'.ne']
    · have awl : (artinWord m (bandWord i j b) l).1 = l :=
        Fin.ext (by rw [artinWord_bandWord_fst_val hij' hj', ite_eq_right h1, ite_eq_right h3])
      simp only [artinGen_of_val_ne false h3 h2, ih', awl, artinGen_of_val_ne true h3 h2, h1, h2,
        h3, ite_false]
      simp

theorem braidRun_bandWord_fst {G : Type*} [Group G] {m i j : ℕ} (hij : i < j) (hj : j < m)
    (b : Bool) (f : Fin m → G) :
    (braidRun m (bandWord i j b) f).1 = fun l : Fin m ↦
      if (l : ℕ) = i then
        (if b then (f ⟨i, by omega⟩ * midProd f i j) * f ⟨j, hj⟩ *
            (f ⟨i, by omega⟩ * midProd f i j)⁻¹
          else midProd f i j * f ⟨j, hj⟩ * (midProd f i j)⁻¹)
      else if (l : ℕ) = j then
        (if b then (midProd f i j)⁻¹ * f ⟨i, by omega⟩ * midProd f i j
          else (midProd f i j * f ⟨j, hj⟩)⁻¹ * f ⟨i, by omega⟩ * (midProd f i j * f ⟨j, hj⟩))
      else f l := by
  have hi : i < m := by omega
  funext l
  rw [braidRun_fst_apply, braidRun_bandWord_snd_aux hij hj]
  by_cases h1 : (l : ℕ) = i
  · obtain rfl : l = ⟨i, hi⟩ := Fin.ext h1
    have aw : (artinWord m (bandWord i j b) ⟨i, hi⟩).1 = ⟨j, hj⟩ :=
      Fin.ext (by simp [artinWord_bandWord_fst_val hij hj])
    cases b <;> simp [aw]
  by_cases h2 : (l : ℕ) = j
  · obtain rfl : l = ⟨j, hj⟩ := Fin.ext h2
    have aw : (artinWord m (bandWord i j b) ⟨j, hj⟩).1 = ⟨i, hi⟩ :=
      Fin.ext (by simp [artinWord_bandWord_fst_val hij hj, hij.ne'])
    cases b <;> simp [aw, hij.ne']
  · have aw : (artinWord m (bandWord i j b) l).1 = l :=
      Fin.ext (by rw [artinWord_bandWord_fst_val hij hj, ite_eq_right h1, ite_eq_right h2])
    simp [aw, h1, h2]

theorem braidRun_bandWord_snd {G : Type*} [Group G] {m i j : ℕ} (hij : i < j) (hj : j < m)
    (b : Bool) (f : Fin m → G) :
    (braidRun m (bandWord i j b) f).2 = fun l : Fin m ↦
      if (l : ℕ) = i then (if b then f ⟨i, by omega⟩ * midProd f i j else midProd f i j)
      else if (l : ℕ) = j then
        (if b then (midProd f i j)⁻¹ else (midProd f i j * f ⟨j, hj⟩)⁻¹)
      else 1 :=
  braidRun_bandWord_snd_aux hij hj b f

theorem artinWord_bandWord_fst {m i j : ℕ} (hij : i < j) (hj : j < m) (b : Bool) (l : Fin m) :
    ((artinWord m (bandWord i j b) l).1 : ℕ) =
      if (l : ℕ) = i then j else if (l : ℕ) = j then i else l :=
  artinWord_bandWord_fst_val hij hj b l

end AJConjecture
