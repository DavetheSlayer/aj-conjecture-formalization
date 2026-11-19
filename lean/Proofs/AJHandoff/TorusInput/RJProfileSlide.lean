import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinProfileBasic
import AJConjecture.SkeinThickCableBasic
import AJConjecture.SkeinJwThickCross
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinPlaceNest
import AJConjecture.SkeinPlaceMul

/-!
# Profile cables: concatenation and sliding projectors (node RA5.ii.1)

The profile cable of `u ++ v` is the cable of `u` followed by the cable of `v` with the profile
reached at the top of `u`; a word on `n` strands fixes the columns `≥ n` and preserves the total
thickness of the columns `< n`; and the column projectors slide from the bottom to the top of a
profile cable, each to the column where its strand ends.

Route. The first two statements by induction on `u` (definitions of `thickCable`, `profileEnd`).
The third and fourth by induction on `w`: one letter swaps two adjacent columns
(`profileSwap`, `Finset.sum_range_succ`). Sliding: for one letter `(i, s)`, the projectors of the
columns `i`, `i + 1` pass the thick crossing by (N2) `jwAt_mul_braidMatrix_thickCross_fst`,
`_snd`, and the others commute with its letters (disjoint windows: `jwAt_commute_tlGenF`,
transport principle); the product over the columns is reordered (the factors commute). The
constant-profile case is `jwAt_mul_braidMatrix_cable` (`AJConjecture.SkeinCableNatural`).
Estimate 150–220 lines.
-/

noncomputable section

namespace AJConjecture

/-- The profile cable of a concatenation. -/
theorem rj_thickCable_append (κ : ℕ → ℕ) (u v : BraidWord) :
    thickCable κ (u ++ v) = thickCable κ u ++ thickCable (profileEnd κ u) v := by
  induction u generalizing κ with
  | nil => rfl
  | cons g u ih => simp only [List.cons_append, thickCable, profileEnd, ih, List.append_assoc]

/-- The top profile of a concatenation. -/
theorem rj_profileEnd_append (κ : ℕ → ℕ) (u v : BraidWord) :
    profileEnd κ (u ++ v) = profileEnd (profileEnd κ u) v := by
  induction u generalizing κ with
  | nil => rfl
  | cons g u ih => simp only [List.cons_append, profileEnd, ih]

/-- A word on `n` strands fixes the columns `≥ n`. -/
theorem rj_profileEnd_of_le (κ : ℕ → ℕ) (n : ℕ) (w : BraidWord) (hw : IsOnStrands n w) (x : ℕ)
    (hx : n ≤ x) : profileEnd κ w x = κ x := by
  induction w generalizing κ with
  | nil => rfl
  | cons g w ih =>
    have hg : g.1 + 1 < n := hw g List.mem_cons_self
    rw [profileEnd, ih (profileSwap κ g.1) fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg'),
      profileSwap, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

/-- Swapping two adjacent columns below `n` does not change the offset of the column `n`. -/
private theorem rj_profileOffset_profileSwap_of_lt_slide (κ : ℕ → ℕ) (i n : ℕ) (h : i + 1 < n) :
    profileOffset (profileSwap κ i) n = profileOffset κ n := by
  unfold profileOffset profileSwap
  refine Finset.sum_nbij' (Equiv.swap i (i + 1)) (Equiv.swap i (i + 1)) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_range] at hy ⊢
    rw [Equiv.swap_apply_def]
    split_ifs <;> omega
  · intro y hy
    rw [Finset.mem_range] at hy ⊢
    rw [Equiv.swap_apply_def]
    split_ifs <;> omega
  · intro y _
    exact Equiv.swap_apply_self _ _ _
  · intro y _
    exact Equiv.swap_apply_self _ _ _
  · intro y _
    rfl

/-- Swapping two adjacent columns does not change the offsets of the columns up to the first. -/
private theorem rj_profileOffset_profileSwap_of_le_slide (κ : ℕ → ℕ) (i x : ℕ) (h : x ≤ i) :
    profileOffset (profileSwap κ i) x = profileOffset κ x := by
  unfold profileOffset profileSwap
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [Finset.mem_range] at hy
  rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

/-- The offset of the column `i + 1` after swapping the columns `i`, `i + 1`. -/
private theorem rj_profileOffset_profileSwap_succ_slide (κ : ℕ → ℕ) (i : ℕ) :
    profileOffset (profileSwap κ i) (i + 1) = profileOffset κ i + κ (i + 1) := by
  rw [profileOffset, Finset.sum_range_succ, ← profileOffset,
    rj_profileOffset_profileSwap_of_le_slide κ i i le_rfl, profileSwap, Equiv.swap_apply_left]

/-- The offset of the next column. -/
private theorem rj_profileOffset_succ_slide (κ : ℕ → ℕ) (x : ℕ) :
    profileOffset κ (x + 1) = profileOffset κ x + κ x := by
  rw [profileOffset, Finset.sum_range_succ, ← profileOffset]

/-- The offsets are monotone. -/
private theorem rj_profileOffset_mono_slide (κ : ℕ → ℕ) {x y : ℕ} (h : x ≤ y) :
    profileOffset κ x ≤ profileOffset κ y :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- A word on `n` strands preserves the total thickness of the columns `< n`. -/
theorem rj_profileOffset_profileEnd (κ : ℕ → ℕ) (n : ℕ) (w : BraidWord) (hw : IsOnStrands n w) :
    profileOffset (profileEnd κ w) n = profileOffset κ n := by
  induction w generalizing κ with
  | nil => rfl
  | cons g w ih =>
    rw [profileEnd, ih (profileSwap κ g.1) fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg'),
      rj_profileOffset_profileSwap_of_lt_slide κ g.1 n (hw g List.mem_cons_self)]

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem rj_mem_thickCross_slide {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
    (hg : g ∈ thickCross a b off s) : off ≤ g.1 ∧ g.1 + 2 ≤ off + a + b := by
  cases s
  · simp only [thickCross, thickGen, Bool.false_eq_true, ite_false, List.mem_flatMap,
      List.mem_reverse, List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    exact ⟨by omega, by omega⟩
  · simp only [thickCross, thickGen, ite_true, List.mem_flatMap, List.mem_reverse,
      List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    exact ⟨by omega, by omega⟩

/-- A projector commutes with the matrix of a word whose letters avoid its block. -/
private theorem rj_commute_jwAt_braidMatrix_of_far_slide (n o k : ℕ) (w : BraidWord)
    (h : ∀ g ∈ w, g.1 + 1 < o ∨ o + k ≤ g.1) : Commute (jwAt n o k) (braidMatrix n w) := by
  induction w with
  | nil =>
    rw [braidMatrix_nil]
    exact Commute.one_right _
  | cons g w ih =>
    obtain ⟨l, s⟩ := g
    have hl : Commute (jwAt n o k) (tlGenF n l) :=
      jwAt_commute_tlGenF n o k l (h (l, s) List.mem_cons_self)
    have hg : Commute (jwAt n o k) (crossingF n (l, s)) := by
      cases s
      · rw [crossingF_neg]
        exact ((Commute.one_right _).smul_right _).add_right (hl.smul_right _)
      · rw [crossingF_pos]
        exact ((Commute.one_right _).smul_right _).add_right (hl.smul_right _)
    rw [show braidMatrix n ((l, s) :: w) = crossingF n (l, s) * braidMatrix n w from by
      simp only [braidMatrix, List.map_cons, List.prod_cons]]
    exact hg.mul_right (ih fun g hg ↦ h g (List.mem_cons_of_mem _ hg))

/-- A product of factors that each pass `B` passes `B`. -/
private theorem rj_list_prod_map_mul_of_forall_slide {M : Type*} [Monoid M] (l : List ℕ)
    (F H : ℕ → M) (B : M)
    (h : ∀ x ∈ l, F x * B = B * H x) : (l.map F).prod * B = B * (l.map H).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_mul, mul_one]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_assoc,
      ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy), ← mul_assoc, h x List.mem_cons_self,
      mul_assoc]

/-- Two projectors on disjoint blocks commute. -/
private theorem rj_jwAt_mul_jwAt_comm_of_le_slide (n i k i' k' : ℕ) (h : i + k ≤ i') :
    jwAt n i k * jwAt n i' k' = jwAt n i' k' * jwAt n i k :=
  (jwAt_mul_eq_mul_jwAt n n i' i' (jwAt n i k) k' fun l _ ↦
    (jwAt_commute_tlGenF n i k (i' + l) (Or.inr (by omega))).eq.symm).symm

/-- A product over `range n` is unchanged by exchanging two adjacent commuting factors. -/
private theorem rj_list_prod_map_swap_slide {M : Type*} [Monoid M] (G : ℕ → M) (i n : ℕ)
    (h : i + 1 < n)
    (hc : G i * G (i + 1) = G (i + 1) * G i) :
    ((List.range n).map fun x ↦ G (Equiv.swap i (i + 1) x)).prod =
      ((List.range n).map G).prod := by
  obtain ⟨d, rfl⟩ : ∃ d, n = i + 2 + d := ⟨n - (i + 2), by omega⟩
  have hfix : ∀ x, x ≠ i → x ≠ i + 1 → G (Equiv.swap i (i + 1) x) = G x := fun x h1 h2 ↦ by
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  rw [List.range_add, List.map_append, List.map_append, List.prod_append, List.prod_append,
    List.range_succ, List.range_succ, List.map_append, List.map_append, List.map_append,
    List.map_append, List.prod_append, List.prod_append, List.prod_append, List.prod_append]
  have h1 : ((List.range i).map fun x ↦ G (Equiv.swap i (i + 1) x)) = (List.range i).map G :=
    List.map_congr_left fun x hx ↦ by
      rw [List.mem_range] at hx
      exact hfix x (by omega) (by omega)
  have h2 : ((List.range d).map (fun x ↦ i + 2 + x)).map
      (fun x ↦ G (Equiv.swap i (i + 1) x)) = ((List.range d).map (fun x ↦ i + 2 + x)).map G :=
    List.map_congr_left fun x hx ↦ by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact hfix _ (by omega) (by omega)
  rw [h1, h2]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  congr 1
  rw [mul_assoc, mul_assoc, hc]

/-- The column projectors pass one thick crossing of a profile cable. -/
private theorem rj_profileProj_mul_braidMatrix_thickCross_slide (N : ℕ) (κ : ℕ → ℕ) (n i : ℕ)
    (s : Bool)
    (hi : i + 1 < n) (hN : profileOffset κ n ≤ N) :
    rjProfileProj N κ n *
        braidMatrix N (thickCross (κ i) (κ (i + 1)) (profileOffset κ i) s) =
      braidMatrix N (thickCross (κ i) (κ (i + 1)) (profileOffset κ i) s) *
        rjProfileProj N (profileSwap κ i) n := by
  set κ' := profileSwap κ i with hκ'
  set B := braidMatrix N (thickCross (κ i) (κ (i + 1)) (profileOffset κ i) s) with hB
  have hoff2 : profileOffset κ i + κ i + κ (i + 1) = profileOffset κ (i + 2) := by
    rw [rj_profileOffset_succ_slide, rj_profileOffset_succ_slide]
  have hle2 : profileOffset κ (i + 2) ≤ N :=
    le_trans (rj_profileOffset_mono_slide κ (show i + 2 ≤ n by omega)) hN
  have hmem : ∀ g ∈ thickCross (κ i) (κ (i + 1)) (profileOffset κ i) s,
      profileOffset κ i ≤ g.1 ∧ g.1 + 2 ≤ profileOffset κ (i + 2) := fun g hg ↦ by
    have := rj_mem_thickCross_slide hg
    omega
  have key : ∀ x ∈ List.range n, jwAt N (profileOffset κ x) (κ x) * B =
      B * (fun y ↦ jwAt N (profileOffset κ' y) (κ' y)) (Equiv.swap i (i + 1) x) := by
    intro x hx
    rw [List.mem_range] at hx
    simp only
    rcases lt_trichotomy x i with hxi | rfl | hxi
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), hκ',
        rj_profileOffset_profileSwap_of_le_slide κ i x hxi.le, profileSwap,
        Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      refine (rj_commute_jwAt_braidMatrix_of_far_slide N _ _ _ fun g hg ↦ Or.inr ?_).eq
      have := (hmem g hg).1
      have := rj_profileOffset_mono_slide κ (show x + 1 ≤ i by omega)
      rw [rj_profileOffset_succ_slide] at this
      omega
    · rw [Equiv.swap_apply_left, hκ', rj_profileOffset_profileSwap_succ_slide, profileSwap,
        Equiv.swap_apply_right, hB]
      exact jwAt_mul_braidMatrix_thickCross_fst N _ _ _ s (by omega)
    · rcases Nat.lt_or_ge (i + 1) x with hxi' | hxi'
      · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), hκ',
          rj_profileOffset_profileSwap_of_lt_slide κ i x hxi', profileSwap,
          Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
        refine (rj_commute_jwAt_braidMatrix_of_far_slide N _ _ _ fun g hg ↦ Or.inl ?_).eq
        have := (hmem g hg).2
        have := rj_profileOffset_mono_slide κ (show i + 2 ≤ x by omega)
        omega
      · obtain rfl : x = i + 1 := by omega
        rw [Equiv.swap_apply_right, hκ', rj_profileOffset_profileSwap_of_le_slide κ i i le_rfl,
          profileSwap, Equiv.swap_apply_left, rj_profileOffset_succ_slide, hB]
        exact jwAt_mul_braidMatrix_thickCross_snd N _ _ _ s (by omega)
  rw [rjProfileProj, rj_list_prod_map_mul_of_forall_slide _ _ _ B key, rjProfileProj]
  congr 1
  refine rj_list_prod_map_swap_slide (fun y ↦ jwAt N (profileOffset κ' y) (κ' y)) i n hi ?_
  exact rj_jwAt_mul_jwAt_comm_of_le_slide N _ _ _ _ (by rw [rj_profileOffset_succ_slide])

/-- The column projectors slide from the bottom to the top of a profile cable. -/
theorem rj_profileProj_mul_braidMatrix (N : ℕ) (κ : ℕ → ℕ) (n : ℕ) (w : BraidWord)
    (hw : IsOnStrands n w) (hN : profileOffset κ n ≤ N) :
    rjProfileProj N κ n * braidMatrix N (thickCable κ w) =
      braidMatrix N (thickCable κ w) * rjProfileProj N (profileEnd κ w) n := by
  induction w generalizing κ with
  | nil => rw [thickCable, braidMatrix_nil, Matrix.mul_one, Matrix.one_mul, profileEnd]
  | cons g w ih =>
    have hg : g.1 + 1 < n := hw g List.mem_cons_self
    have hw' : IsOnStrands n w := fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg')
    rw [thickCable, braidMatrix_append, ← Matrix.mul_assoc,
      rj_profileProj_mul_braidMatrix_thickCross_slide N κ n g.1 g.2 hg hN, Matrix.mul_assoc,
      ih (profileSwap κ g.1) hw'
        (by rw [rj_profileOffset_profileSwap_of_lt_slide κ g.1 n hg]; exact hN),
      profileEnd, Matrix.mul_assoc]

/-- The offset of the next column. -/
theorem rj_profileOffset_succ (κ : ℕ → ℕ) (x : ℕ) :
    profileOffset κ (x + 1) = profileOffset κ x + κ x :=
  rj_profileOffset_succ_slide κ x

/-- The offsets are monotone. -/
theorem rj_profileOffset_mono (κ : ℕ → ℕ) {x y : ℕ} (h : x ≤ y) :
    profileOffset κ x ≤ profileOffset κ y :=
  rj_profileOffset_mono_slide κ h

/-- Swapping two adjacent columns below `n` does not change the offset of the column `n`. -/
theorem rj_profileOffset_profileSwap_of_lt (κ : ℕ → ℕ) (i n : ℕ) (h : i + 1 < n) :
    profileOffset (profileSwap κ i) n = profileOffset κ n :=
  rj_profileOffset_profileSwap_of_lt_slide κ i n h

/-- Swapping two adjacent columns does not change the offsets of the columns up to the first. -/
theorem rj_profileOffset_profileSwap_of_le (κ : ℕ → ℕ) (i x : ℕ) (h : x ≤ i) :
    profileOffset (profileSwap κ i) x = profileOffset κ x :=
  rj_profileOffset_profileSwap_of_le_slide κ i x h

/-- The letters of a thick crossing act on the strands of its two bundles. -/
theorem rj_mem_thickCross {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
    (hg : g ∈ thickCross a b off s) : off ≤ g.1 ∧ g.1 + 2 ≤ off + a + b :=
  rj_mem_thickCross_slide hg

/-- A projector commutes with the matrix of a word whose letters avoid its block. -/
theorem rj_commute_jwAt_braidMatrix_of_far (n o k : ℕ) (w : BraidWord)
    (h : ∀ g ∈ w, g.1 + 1 < o ∨ o + k ≤ g.1) : Commute (jwAt n o k) (braidMatrix n w) :=
  rj_commute_jwAt_braidMatrix_of_far_slide n o k w h

/-- Two projectors on disjoint blocks commute. -/
theorem rj_jwAt_mul_jwAt_comm_of_le (n i k i' k' : ℕ) (h : i + k ≤ i') :
    jwAt n i k * jwAt n i' k' = jwAt n i' k' * jwAt n i k :=
  rj_jwAt_mul_jwAt_comm_of_le_slide n i k i' k' h

/-- The profile projectors of `n + 1` columns. -/
theorem rj_profileProj_succ (N : ℕ) (κ : ℕ → ℕ) (n : ℕ) :
    rjProfileProj N κ (n + 1) =
      rjProfileProj N κ n * jwAt N (profileOffset κ n) (κ n) := by
  rw [rjProfileProj, List.range_succ, List.map_append, List.prod_append, ← rjProfileProj,
    List.map_singleton, List.prod_singleton]

/-- The profile projectors depend only on the columns `< n`. -/
theorem rj_profileProj_congr (N : ℕ) (κ κ' : ℕ → ℕ) (n : ℕ)
    (h : ∀ x < n, κ x = κ' x) : rjProfileProj N κ n = rjProfileProj N κ' n := by
  unfold rjProfileProj
  congr 1
  refine List.map_congr_left fun x hx ↦ ?_
  rw [List.mem_range] at hx
  have ho : profileOffset κ x = profileOffset κ' x :=
    Finset.sum_congr rfl fun y hy ↦ h y (by rw [Finset.mem_range] at hy; omega)
  rw [ho, h x hx]

/-- The profile projectors intertwine the weights. -/
theorem rj_skWeight_mul_profileProj (N : ℕ) (κ : ℕ → ℕ) (n : ℕ) :
    skWeight N * rjProfileProj N κ n = rjProfileProj N κ n * skWeight N := by
  induction n with
  | zero => simp only [rjProfileProj, List.range_zero, List.map_nil, List.prod_nil,
      Matrix.mul_one, Matrix.one_mul]
  | succ n ih =>
    rw [rj_profileProj_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
      skWeight_mul_jwAt, Matrix.mul_assoc]

/-- A projector at or after the column `n` commutes with the profile projectors of the columns
`< n`. -/
theorem rj_commute_jwAt_profileProj (N : ℕ) (κ : ℕ → ℕ) (n i k : ℕ)
    (hi : profileOffset κ n ≤ i) : Commute (jwAt N i k) (rjProfileProj N κ n) := by
  refine Commute.list_prod_right _ _ fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  rw [List.mem_range] at hx
  have h1 := rj_profileOffset_mono κ (show x + 1 ≤ n by omega)
  rw [rj_profileOffset_succ] at h1
  exact (rj_jwAt_mul_jwAt_comm_of_le N _ _ _ _ (by omega)).symm

/-- The profile projectors form an idempotent. -/
theorem rj_profileProj_mul_self (N : ℕ) (κ : ℕ → ℕ) (n : ℕ) :
    rjProfileProj N κ n * rjProfileProj N κ n = rjProfileProj N κ n := by
  induction n with
  | zero => simp only [rjProfileProj, List.range_zero, List.map_nil, List.prod_nil,
      Matrix.mul_one]
  | succ n ih =>
    have hc := rj_commute_jwAt_profileProj N κ n (profileOffset κ n) (κ n) le_rfl
    rw [rj_profileProj_succ, Matrix.mul_assoc, ← Matrix.mul_assoc (jwAt _ _ _), hc.eq,
      Matrix.mul_assoc _ (jwAt _ _ _), jwAt_mul_self, ← Matrix.mul_assoc, ih]

/-- A braid word whose letters lie after the column `n` commutes with the profile projectors
of the columns `< n`. -/
theorem rj_commute_profileProj_braidMatrix (N : ℕ) (κ : ℕ → ℕ) (n : ℕ)
    (v : BraidWord) (hv : ∀ g ∈ v, profileOffset κ n ≤ g.1) :
    Commute (rjProfileProj N κ n) (braidMatrix N v) := by
  refine Commute.list_prod_left _ _ fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  rw [List.mem_range] at hx
  have h1 := rj_profileOffset_mono κ (show x + 1 ≤ n by omega)
  rw [rj_profileOffset_succ] at h1
  exact rj_commute_jwAt_braidMatrix_of_far N _ _ v fun g hg ↦ Or.inr (by
    have := hv g hg
    omega)

/-- A projector inside the first `M` strands is placed at `0`. -/
theorem rj_jwAt_eq_skPlace_zero (N M i k : ℕ) (hk : i + k ≤ M) (hM : M ≤ N) :
    jwAt N i k = skPlace N N 0 (jwAt M i k) := by
  rw [jwAt_eq_skPlace N i k (by omega), jwAt_eq_skPlace M i k hk,
    skPlace_skPlace N N 0 i _ hk rfl (by omega) rfl, Nat.zero_add]

/-- The profile projectors inside the first `M` strands are placed at `0`. -/
theorem rj_profileProj_eq_skPlace_zero (N M : ℕ) (κ : ℕ → ℕ) (n : ℕ)
    (hn : profileOffset κ n ≤ M) (hM : M ≤ N) :
    rjProfileProj N κ n = skPlace N N 0 (rjProfileProj M κ n) := by
  induction n with
  | zero =>
    simp only [rjProfileProj, List.range_zero, List.map_nil, List.prod_nil]
    rw [skPlace_one N 0 M (by omega)]
  | succ n ih =>
    have h1 := rj_profileOffset_succ κ n
    rw [rj_profileProj_succ, rj_profileProj_succ, ih (by omega),
      skPlace_mul N N N 0 _ _ (by omega) rfl rfl,
      rj_jwAt_eq_skPlace_zero N M _ _ (by omega) hM]

/-- The letters of a profile cable of a word on `n` strands lie inside the first
`profileOffset κ n` strands. -/
theorem rj_mem_thickCable (κ : ℕ → ℕ) (n : ℕ) (w : BraidWord)
    (hw : IsOnStrands n w) : ∀ g ∈ thickCable κ w, g.1 + 2 ≤ profileOffset κ n := by
  induction w generalizing κ with
  | nil => intro g hg; simp [thickCable] at hg
  | cons g w ih =>
    intro g' hg'
    have hg : g.1 + 1 < n := hw g List.mem_cons_self
    rw [thickCable, List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · have h1 := rj_mem_thickCross hg'
      have h2 := rj_profileOffset_mono κ (show g.1 + 2 ≤ n by omega)
      rw [rj_profileOffset_succ, rj_profileOffset_succ] at h2
      omega
    · have := ih (profileSwap κ g.1) (fun g'' hg'' ↦ hw g'' (List.mem_cons_of_mem _ hg''))
        g' hg'
      rwa [rj_profileOffset_profileSwap_of_lt κ g.1 n hg] at this

/-- The profile cable of a word on `n` strands is placed at `0`. -/
theorem rj_braidMatrix_thickCable_eq_skPlace (N M : ℕ) (κ : ℕ → ℕ) (n : ℕ)
    (w : BraidWord) (hw : IsOnStrands n w) (hn : profileOffset κ n ≤ M) (hM : M ≤ N) :
    braidMatrix N (thickCable κ w) = skPlace N N 0 (braidMatrix M (thickCable κ w)) := by
  have h := braidMatrix_map_add_eq_skPlace M N 0 (thickCable κ w) (fun g hg ↦ by
    have := rj_mem_thickCable κ n w hw g hg
    omega) (by omega)
  simpa only [Nat.add_zero, Prod.mk.eta, List.map_id'] using h

end AJConjecture
