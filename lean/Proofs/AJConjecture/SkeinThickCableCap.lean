import Mathlib
import AJConjecture.SkeinCableNatural
import AJConjecture.SkeinThickCrossCap
import AJConjecture.SkeinTraceCyclic

/-!
# A cap slides along a strand of a cabled braid

One lap: a cap on the strands `j`, `j + 1` of the bundle in the column `p` at the bottom of a
cabled braid word equals the cap at the top, on the same strands of the bundle in the column
where the strand ends, with the bundle thicker by two along the whole strand. Induction on the
word: each letter is a thick crossing, and the cap is on its first bundle
(`AJConjecture.capAt_mul_braidMatrix_thickCross_fst`), on its second bundle
(`AJConjecture.capAt_mul_braidMatrix_thickCross_snd`), or on a bundle that the letter does not
touch (`AJConjecture.capAt_mul_braidMatrix_of_lt`, `AJConjecture.capAt_mul_braidMatrix_of_le` with
`AJConjecture.thickCross_add_off`); the profiles are followed through
`AJConjecture.profileEnd`. The second statement is the same lap under the quantum trace.
-/

namespace AJConjecture

/-- The offset of the next column. -/
private theorem profileOffset_succ_thickCableCap (κ : ℕ → ℕ) (x : ℕ) :
    profileOffset κ (x + 1) = profileOffset κ x + κ x := by
  rw [profileOffset, profileOffset, Finset.sum_range_succ]

/-- The offsets increase with the column. -/
private theorem profileOffset_mono_thickCableCap (κ : ℕ → ℕ) {x y : ℕ} (h : x ≤ y) :
    profileOffset κ x ≤ profileOffset κ y :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- A change of the profile in the column `p` does not move the columns up to `p`. -/
private theorem profileOffset_update_of_le_thickCableCap (κ : ℕ → ℕ) (p v x : ℕ) (h : x ≤ p) :
    profileOffset (Function.update κ p v) x = profileOffset κ x := by
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [Finset.mem_range] at hy
  exact Function.update_of_ne (by omega) _ _

/-- A thicker bundle in the column `p` moves the columns behind `p`. -/
private theorem profileOffset_update_of_lt_thickCableCap (κ : ℕ → ℕ) (p d x : ℕ) (h : p < x) :
    profileOffset (Function.update κ p (κ p + d)) x = profileOffset κ x + d := by
  induction x with
  | zero => omega
  | succ x ih =>
    rw [profileOffset_succ_thickCableCap, profileOffset_succ_thickCableCap]
    rcases Nat.lt_or_ge p x with hpx | hpx
    · rw [ih hpx, Function.update_of_ne (by omega)]
      omega
    · obtain rfl : p = x := by omega
      rw [profileOffset_update_of_le_thickCableCap κ p _ p le_rfl, Function.update_self]
      omega

/-- A crossing of the columns `i`, `i + 1` does not move the columns up to `i`. -/
private theorem profileOffset_profileSwap_of_le_thickCableCap (κ : ℕ → ℕ) (i x : ℕ)
    (h : x ≤ i) : profileOffset (profileSwap κ i) x = profileOffset κ x := by
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [Finset.mem_range] at hy
  rw [profileSwap, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

/-- A crossing of the columns `i`, `i + 1` does not move the columns from `i + 2` on. -/
private theorem profileOffset_profileSwap_of_ge_thickCableCap (κ : ℕ → ℕ) (i x : ℕ)
    (h : i + 2 ≤ x) : profileOffset (profileSwap κ i) x = profileOffset κ x := by
  refine Finset.sum_equiv (Equiv.swap i (i + 1)) (fun y ↦ ?_) (fun y _ ↦ rfl)
  simp only [Finset.mem_range]
  rw [Equiv.swap_apply_def]
  split_ifs <;> omega

/-- The swap of a profile changed in one column. -/
private theorem profileSwap_update_thickCableCap (κ : ℕ → ℕ) (i p v : ℕ) :
    profileSwap (Function.update κ p v) i =
      Function.update (profileSwap κ i) (Equiv.swap i (i + 1) p) v := by
  funext x
  simp only [profileSwap, Function.update_apply, Equiv.swap_apply_eq_iff]

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem mem_thickCross_thickCableCap {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
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

/-- A cap on the bundle in the column `p` slides through the thick crossing of the columns
`i`, `i + 1`. -/
private theorem capAt_mul_braidMatrix_thickCross_profile_thickCableCap (N : ℕ) (κ : ℕ → ℕ)
    (i p j : ℕ) (s : Bool) (hj : j ≤ κ p) (hN : profileOffset κ (i + 2) ≤ N) :
    capAt N (profileOffset κ p + j) *
        braidMatrix N (thickCross (κ i) (κ (i + 1)) (profileOffset κ i) s) =
      braidMatrix (N + 2) (thickCross (Function.update κ p (κ p + 2) i)
          (Function.update κ p (κ p + 2) (i + 1))
          (profileOffset (Function.update κ p (κ p + 2)) i) s) *
        capAt N (profileOffset (profileSwap κ i) (Equiv.swap i (i + 1) p) + j) := by
  have h2 : profileOffset κ (i + 2) = profileOffset κ i + κ i + κ (i + 1) := by
    rw [profileOffset_succ_thickCableCap, profileOffset_succ_thickCableCap]
  rcases Nat.lt_trichotomy p i with hpi | rfl | hpi
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      profileOffset_update_of_lt_thickCableCap κ p 2 i hpi,
      Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
      profileOffset_profileSwap_of_le_thickCableCap κ i p (by omega), thickCross_add_off]
    refine capAt_mul_braidMatrix_of_le N _ _ fun g hg ↦ ?_
    have h1 := (mem_thickCross_thickCableCap hg).1
    have h3 := profileOffset_add_le κ p i hpi
    omega
  · rw [Function.update_self, Function.update_of_ne (by omega),
      profileOffset_update_of_le_thickCableCap κ p _ p le_rfl, Equiv.swap_apply_left,
      profileOffset_succ_thickCableCap,
      profileOffset_profileSwap_of_le_thickCableCap κ p p le_rfl]
    have h3 : profileSwap κ p p = κ (p + 1) := by rw [profileSwap, Equiv.swap_apply_left]
    rw [h3]
    exact capAt_mul_braidMatrix_thickCross_fst N (κ p) (κ (p + 1)) (profileOffset κ p) j s
      (by omega) hj
  · rcases Nat.eq_or_lt_of_le hpi with rfl | hpi'
    · rw [Function.update_self, Function.update_of_ne (by omega),
        profileOffset_update_of_le_thickCableCap κ (i + 1) _ i (by omega),
        Equiv.swap_apply_right, profileOffset_succ_thickCableCap,
        profileOffset_profileSwap_of_le_thickCableCap κ i i le_rfl]
      exact capAt_mul_braidMatrix_thickCross_snd N (κ i) (κ (i + 1)) (profileOffset κ i) j s
        (by omega) hj
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        profileOffset_update_of_le_thickCableCap κ p _ i (by omega),
        Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
        profileOffset_profileSwap_of_ge_thickCableCap κ i p (by omega)]
      refine capAt_mul_braidMatrix_of_lt N _ _ fun g hg ↦ ?_
      have h1 := (mem_thickCross_thickCableCap hg).2
      have h3 := profileOffset_mono_thickCableCap κ (show i + 2 ≤ p from by omega)
      omega

/-- One lap of a cap along a strand of a cabled braid with a thickness profile. -/
theorem capAt_mul_braidMatrix_thickCable (m N : ℕ) (κ : ℕ → ℕ) (w : BraidWord) (p j : ℕ)
    (hw : IsOnStrands m w) (hp : p < m) (hj : j ≤ κ p) (hN : profileOffset κ m ≤ N) :
    capAt N (profileOffset κ p + j) * braidMatrix N (thickCable κ w) =
      braidMatrix (N + 2) (thickCable (Function.update κ p (κ p + 2)) w) *
        capAt N (profileOffset (profileEnd κ w) (strandEnd w p) + j) := by
  induction w generalizing κ p with
  | nil => simp only [thickCable, profileEnd, strandEnd, braidMatrix_nil, Matrix.mul_one,
      Matrix.one_mul]
  | cons g w ih =>
    obtain ⟨i, s⟩ := g
    have hi : i + 1 < m := hw (i, s) List.mem_cons_self
    have hw' : IsOnStrands m w := fun g hg ↦ hw g (List.mem_cons_of_mem _ hg)
    have hκ : profileSwap κ i (Equiv.swap i (i + 1) p) = κ p := by
      rw [profileSwap, Equiv.swap_apply_self]
    have hp' : Equiv.swap i (i + 1) p < m := by
      rw [Equiv.swap_apply_def]
      split_ifs <;> omega
    have hN' : profileOffset (profileSwap κ i) m ≤ N := by
      rw [profileOffset_profileSwap_of_ge_thickCableCap κ i m (by omega)]
      exact hN
    have hN2 : profileOffset κ (i + 2) ≤ N :=
      (profileOffset_mono_thickCableCap κ (by omega)).trans hN
    have h := ih (profileSwap κ i) (Equiv.swap i (i + 1) p) hw' hp' (by rw [hκ]; exact hj) hN'
    rw [hκ] at h
    simp only [thickCable, profileEnd, strandEnd]
    rw [braidMatrix_append, braidMatrix_append, profileSwap_update_thickCableCap,
      ← Matrix.mul_assoc,
      capAt_mul_braidMatrix_thickCross_profile_thickCableCap N κ i p j s hj hN2,
      Matrix.mul_assoc, h, Matrix.mul_assoc]

/-- One lap under the quantum trace, against an arbitrary matrix. -/
theorem qtr_thickCable_capAt (m N : ℕ) (κ : ℕ → ℕ) (w : BraidWord) (p j : ℕ)
    (hw : IsOnStrands m w) (hp : p < m) (hj : j ≤ κ p) (hN : profileOffset κ m ≤ N)
    (R : SkMat N (N + 2)) :
    qtr (N + 2) (braidMatrix (N + 2) (thickCable (Function.update κ p (κ p + 2)) w) *
        capAt N (profileOffset (profileEnd κ w) (strandEnd w p) + j) * R) =
      qtr N (braidMatrix N (thickCable κ w) * R * capAt N (profileOffset κ p + j)) := by
  rw [← capAt_mul_braidMatrix_thickCable m N κ w p j hw hp hj hN, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc (braidMatrix N _)]
  exact qtr_mul_comm_of_weight (N + 2) N _ _ (skWeight_mul_capAt N _)

end AJConjecture
