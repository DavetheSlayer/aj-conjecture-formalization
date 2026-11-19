import Mathlib
import AJConjecture.SkeinJwThickCross

/-!
# Operators on a bundle slide along a cabled braid

A Temperley–Lieb generator, or the Jones–Wenzl projector, on the bundle in the column `p` at
the bottom of a cabled braid word equals the same operator on the bundle in the column where
the strand ends, at the top. Induction on the word with the naturality of thick crossings and
far commutation.
-/

namespace AJConjecture

/-- An operator that commutes with the generators of the letters of a word commutes with the
matrix of the word. -/
private theorem commute_braidMatrix_of_commute_tlGenF_cableNatural (n : ℕ) (X : SkMat n n)
    (w : BraidWord) (h : ∀ g ∈ w, Commute X (tlGenF n g.1)) : Commute X (braidMatrix n w) := by
  induction w with
  | nil =>
    rw [braidMatrix_nil]
    exact Commute.one_right X
  | cons g w ih =>
    obtain ⟨l, s⟩ := g
    have hl : Commute X (tlGenF n l) := h (l, s) List.mem_cons_self
    have hg : Commute X (crossingF n (l, s)) := by
      cases s
      · rw [crossingF_neg]
        exact ((Commute.one_right X).smul_right _).add_right (hl.smul_right _)
      · rw [crossingF_pos]
        exact ((Commute.one_right X).smul_right _).add_right (hl.smul_right _)
    rw [show braidMatrix n ((l, s) :: w) = crossingF n (l, s) * braidMatrix n w from by
      simp only [braidMatrix, List.map_cons, List.prod_cons]]
    exact hg.mul_right (ih fun g hg ↦ h g (List.mem_cons_of_mem _ hg))

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem mem_thickCross_cableNatural {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
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

/-- A family of operators on the columns that slides through every cabled letter slides along
the cabled word. -/
private theorem mul_braidMatrix_cable_of_slide_cableNatural (m c : ℕ)
    (X : ℕ → SkMat (c * m) (c * m))
    (hX : ∀ (i : ℕ) (s : Bool) (p : ℕ), i + 1 < m →
      X p * braidMatrix (c * m) (thickCross c c (c * i) s) =
        braidMatrix (c * m) (thickCross c c (c * i) s) * X (Equiv.swap i (i + 1) p))
    (w : BraidWord) (hw : IsOnStrands m w) (p : ℕ) :
    X p * braidMatrix (c * m) (cable c w) =
      braidMatrix (c * m) (cable c w) * X (strandEnd w p) := by
  induction w generalizing p with
  | nil =>
    simp only [cable, List.flatMap_nil, braidMatrix_nil, strandEnd, Matrix.mul_one,
      Matrix.one_mul]
  | cons g w ih =>
    have hw' : IsOnStrands m w := fun g hg ↦ hw g (List.mem_cons_of_mem _ hg)
    rw [show cable c (g :: w) = thickCross c c (c * g.1) g.2 ++ cable c w from by
        rw [← cableGen_eq_thickCross, cable, List.flatMap_cons, cable],
      show strandEnd (g :: w) p = strandEnd w (Equiv.swap g.1 (g.1 + 1) p) from rfl,
      braidMatrix_append, ← Matrix.mul_assoc, hX g.1 g.2 p (hw g List.mem_cons_self),
      Matrix.mul_assoc, ih hw', Matrix.mul_assoc]

/-- A generator on the bundle of the column `p` slides through a cabled letter. -/
private theorem tlGenF_mul_braidMatrix_thickCross_column_cableNatural (m c i p j : ℕ) (s : Bool)
    (hi : i + 1 < m) (hj : j + 1 < c) :
    tlGenF (c * m) (c * p + j) * braidMatrix (c * m) (thickCross c c (c * i) s) =
      braidMatrix (c * m) (thickCross c c (c * i) s) *
        tlGenF (c * m) (c * Equiv.swap i (i + 1) p + j) := by
  have hn : c * i + c + c ≤ c * m := by
    have := Nat.mul_le_mul_left c (show i + 2 ≤ m from by omega)
    rw [Nat.mul_add] at this
    omega
  rcases Nat.lt_trichotomy p i with hpi | rfl | hpi
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    refine (commute_braidMatrix_of_commute_tlGenF_cableNatural _ _ _ fun g hg ↦
      tlGenF_commute _ _ _ ?_).eq
    have h1 := (mem_thickCross_cableNatural hg).1
    have h2 := Nat.mul_le_mul_left c (show p + 1 ≤ i from hpi)
    rw [Nat.mul_add_one] at h2
    omega
  · rw [Equiv.swap_apply_left, Nat.mul_add_one]
    exact tlGenF_mul_braidMatrix_thickCross_fst (c * m) c c (c * p) j s hn hj
  · rcases Nat.eq_or_lt_of_le hpi with rfl | hpi'
    · rw [Equiv.swap_apply_right, Nat.mul_add_one]
      exact tlGenF_mul_braidMatrix_thickCross_snd (c * m) c c (c * i) j s hn hj
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      refine (commute_braidMatrix_of_commute_tlGenF_cableNatural _ _ _ fun g hg ↦
        (tlGenF_commute _ _ _ ?_).symm).eq
      have h1 := (mem_thickCross_cableNatural hg).2
      have h2 := Nat.mul_le_mul_left c (show i + 2 ≤ p from by omega)
      rw [Nat.mul_add] at h2
      omega

/-- The projector on the factors `i, …, i + k - 1` commutes with the generators that do not
touch these factors. -/
private theorem jwAt_commute_tlGenF_cableNatural (n i k l : ℕ) (h : l + 1 < i ∨ i + k ≤ l) :
    Commute (jwAt n i k) (tlGenF n l) := by
  rcases k with _ | k
  · exact Commute.one_left _
  · induction k with
    | zero => exact Commute.one_left _
    | succ k ih =>
      have h1 : Commute (jwAt n i (k + 1)) (tlGenF n l) := ih (by omega)
      have h2 : Commute (tlGenF n (i + k)) (tlGenF n l) := by
        rcases h with h | h
        · exact (tlGenF_commute n l (i + k) (by omega)).symm
        · exact tlGenF_commute n (i + k) l (by omega)
      rw [jwAt]
      exact h1.add_left (((h1.mul_left h2).mul_left h1).smul_left _)

/-- The projector on the bundle of the column `p` slides through a cabled letter. -/
private theorem jwAt_mul_braidMatrix_thickCross_column_cableNatural (m c i p : ℕ) (s : Bool)
    (hi : i + 1 < m) :
    jwAt (c * m) (c * p) c * braidMatrix (c * m) (thickCross c c (c * i) s) =
      braidMatrix (c * m) (thickCross c c (c * i) s) *
        jwAt (c * m) (c * Equiv.swap i (i + 1) p) c := by
  have hn : c * i + c + c ≤ c * m := by
    have := Nat.mul_le_mul_left c (show i + 2 ≤ m from by omega)
    rw [Nat.mul_add] at this
    omega
  rcases Nat.lt_trichotomy p i with hpi | rfl | hpi
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    refine (commute_braidMatrix_of_commute_tlGenF_cableNatural _ _ _ fun g hg ↦
      jwAt_commute_tlGenF_cableNatural _ _ _ _ (Or.inr ?_)).eq
    have h1 := (mem_thickCross_cableNatural hg).1
    have h2 := Nat.mul_le_mul_left c (show p + 1 ≤ i from hpi)
    rw [Nat.mul_add_one] at h2
    omega
  · rw [Equiv.swap_apply_left, Nat.mul_add_one]
    exact jwAt_mul_braidMatrix_thickCross_fst (c * m) c c (c * p) s hn
  · rcases Nat.eq_or_lt_of_le hpi with rfl | hpi'
    · rw [Equiv.swap_apply_right, Nat.mul_add_one]
      exact jwAt_mul_braidMatrix_thickCross_snd (c * m) c c (c * i) s hn
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      refine (commute_braidMatrix_of_commute_tlGenF_cableNatural _ _ _ fun g hg ↦
        jwAt_commute_tlGenF_cableNatural _ _ _ _ (Or.inl ?_)).eq
      have h1 := (mem_thickCross_cableNatural hg).2
      have h2 := Nat.mul_le_mul_left c (show i + 2 ≤ p from by omega)
      rw [Nat.mul_add] at h2
      omega

set_option linter.unusedVariables false in
/-- A generator on a bundle slides along a cabled braid. -/
theorem tlGenF_mul_braidMatrix_cable (m c : ℕ) (w : BraidWord) (p j : ℕ) (hw : IsOnStrands m w)
    (hp : p < m) (hj : j + 1 < c) :
    tlGenF (c * m) (c * p + j) * braidMatrix (c * m) (cable c w) =
      braidMatrix (c * m) (cable c w) * tlGenF (c * m) (c * strandEnd w p + j) :=
  mul_braidMatrix_cable_of_slide_cableNatural m c (fun q ↦ tlGenF (c * m) (c * q + j))
    (fun i s q hi ↦ tlGenF_mul_braidMatrix_thickCross_column_cableNatural m c i q j s hi hj)
    w hw p

set_option linter.unusedVariables false in
/-- The Jones–Wenzl projector on a bundle slides along a cabled braid. -/
theorem jwAt_mul_braidMatrix_cable (m c : ℕ) (w : BraidWord) (p : ℕ) (hw : IsOnStrands m w)
    (hp : p < m) :
    jwAt (c * m) (c * p) c * braidMatrix (c * m) (cable c w) =
      braidMatrix (c * m) (cable c w) * jwAt (c * m) (c * strandEnd w p) c :=
  mul_braidMatrix_cable_of_slide_cableNatural m c (fun q ↦ jwAt (c * m) (c * q) c)
    (fun i s q hi ↦ jwAt_mul_braidMatrix_thickCross_column_cableNatural m c i q s hi) w hw p

end AJConjecture
