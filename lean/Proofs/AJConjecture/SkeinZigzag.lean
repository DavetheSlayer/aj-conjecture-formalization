import Mathlib
import AJConjecture.SkeinPlaceBasic
import AJConjecture.SkeinPlaceMul
import AJConjecture.SkeinPlaceNest

/-!
# Zig-zag and loop value

A cup followed by a cap on the neighbouring pair of strands is a straight strand, and a cup
followed by the cap on the same pair is a closed loop, of value `δ = -t² - t⁻²`. On one strand
these are the scalar identities `∑_b cup(a, b) cap(b, a') = δ_{a a'}` and
`∑ cup(a, b) cap(a, b) = δ`; the general case follows by functoriality of the placement.
-/

namespace AJConjecture

/-- The states of three factors are the triples of Booleans. -/
private def boolTripleEquiv_zigzag : Bool × Bool × Bool ≃ (Fin 3 → Bool) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun c := (c 0, c 1, c 2)
  left_inv _ := rfl
  right_inv c := by
    funext x
    fin_cases x <;> rfl

/-- A sum over the states of three factors, written out. -/
private theorem sum_fin_three_zigzag (f : (Fin 3 → Bool) → RatFunc ℚ) :
    ∑ c, f c = ∑ x : Bool, ∑ y : Bool, ∑ z : Bool, f ![x, y, z] := by
  rw [← boolTripleEquiv_zigzag.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Fintype.sum_prod_type]
  rfl

/-- The entries of a cup created on the right of one strand. -/
private theorem skPlace_cup_right_apply_zigzag (a : Fin 1 → Bool) (c : Fin 3 → Bool) :
    skPlace 1 3 1 skCup a c = if a 0 = c 0 then cupEntry (c 1) (c 2) else 0 := by
  unfold skPlace
  rw [Matrix.of_apply, dite_eq_left (by omega)]
  refine if_congr ⟨fun hP ↦ hP.1 0 Nat.zero_lt_one, fun hQ ↦ ⟨fun x hx ↦ ?_, fun x hx ↦ by omega⟩⟩
    rfl rfl
  obtain rfl : x = 0 := Subsingleton.elim _ _
  exact hQ

/-- The entries of a cup created on the left of one strand. -/
private theorem skPlace_cup_left_apply_zigzag (a : Fin 1 → Bool) (c : Fin 3 → Bool) :
    skPlace 1 3 0 skCup a c = if a 0 = c 2 then cupEntry (c 0) (c 1) else 0 := by
  unfold skPlace
  rw [Matrix.of_apply, dite_eq_left (by omega)]
  refine if_congr ⟨fun hP ↦ hP.2 0 (Nat.le_refl _), fun hQ ↦ ⟨fun x hx ↦ by omega, fun x hx ↦ ?_⟩⟩
    rfl rfl
  obtain rfl : x = 0 := Subsingleton.elim _ _
  exact hQ

/-- The entries of a cap on the first two of three strands. -/
private theorem skPlace_cap_left_apply_zigzag (c : Fin 3 → Bool) (b : Fin 1 → Bool) :
    skPlace 3 1 0 skCap c b = if c 2 = b 0 then capEntry (c 0) (c 1) else 0 := by
  unfold skPlace
  rw [Matrix.of_apply, dite_eq_left (by omega)]
  refine if_congr ⟨fun hP ↦ hP.2 2 (Nat.le_refl _), fun hQ ↦ ⟨fun x hx ↦ by omega, fun x hx ↦ ?_⟩⟩
    rfl rfl
  rcases x with ⟨x, hx₃⟩
  dsimp only at hx
  obtain rfl : x = 2 := by omega
  exact hQ

/-- The entries of a cap on the last two of three strands. -/
private theorem skPlace_cap_right_apply_zigzag (c : Fin 3 → Bool) (b : Fin 1 → Bool) :
    skPlace 3 1 1 skCap c b = if c 0 = b 0 then capEntry (c 1) (c 2) else 0 := by
  unfold skPlace
  rw [Matrix.of_apply, dite_eq_left (by omega)]
  refine if_congr ⟨fun hP ↦ hP.1 0 Nat.zero_lt_one, fun hQ ↦ ⟨fun x hx ↦ ?_, fun x hx ↦ by omega⟩⟩
    rfl rfl
  rcases x with ⟨x, hx₃⟩
  dsimp only at hx
  obtain rfl : x = 0 := by omega
  exact hQ

/-- Two states of one factor are equal when their values are. -/
private theorem state_one_eq_iff_zigzag (a b : Fin 1 → Bool) : a = b ↔ a 0 = b 0 :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ funext fun x ↦ by rw [Subsingleton.elim x 0]; exact h⟩

/-- The zig-zag identity on one strand, with the cup on the right. -/
private theorem skPlace_cup_mul_skPlace_cap_right_zigzag :
    skPlace 1 3 1 skCup * skPlace 3 1 0 skCap = 1 := by
  ext a b
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  rw [Matrix.mul_apply, sum_fin_three_zigzag, Matrix.one_apply,
    if_congr (state_one_eq_iff_zigzag a b) rfl rfl]
  simp only [skPlace_cup_right_apply_zigzag, skPlace_cap_left_apply_zigzag]
  generalize a 0 = x
  generalize b 0 = y
  cases x <;> cases y <;> simp [cupEntry, capEntry, hX]

/-- The zig-zag identity on one strand, with the cup on the left. -/
private theorem skPlace_cup_mul_skPlace_cap_left_zigzag :
    skPlace 1 3 0 skCup * skPlace 3 1 1 skCap = 1 := by
  ext a b
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  rw [Matrix.mul_apply, sum_fin_three_zigzag, Matrix.one_apply,
    if_congr (state_one_eq_iff_zigzag a b) rfl rfl]
  simp only [skPlace_cup_left_apply_zigzag, skPlace_cap_right_apply_zigzag]
  generalize a 0 = x
  generalize b 0 = y
  cases x <;> cases y <;> simp [cupEntry, capEntry, hX]

/-- A cup followed by a cap is a loop: the scalar `-t² - t⁻²`. -/
private theorem skCup_mul_skCap_zigzag :
    skCup * skCap =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • (1 : SkMat 0 0) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ite_eq_left (Subsingleton.elim a b),
    ← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [skCup, skCap, cupEntry, capEntry]
  ring

/-- Zig-zag: the cap joins a strand with the left leg of a cup created on its right. -/
theorem cupAt_succ_mul_capAt (n i : ℕ) (h : i < n) : cupAt n (i + 1) * capAt n i = 1 := by
  have h₁ : skPlace n (n + 2) (i + 1) skCup = skPlace n (n + 2) i (skPlace 1 3 1 skCup) :=
    (skPlace_skPlace n (n + 2) i 1 skCup (by omega) (by omega) (by omega) (by omega)).symm
  have h₂ : skPlace (n + 2) n i skCap = skPlace (n + 2) n i (skPlace 3 1 0 skCap) :=
    (skPlace_skPlace (n + 2) n i 0 skCap (by omega) (by omega) (by omega) (by omega)).symm
  rw [cupAt, capAt, h₁, h₂, ← skPlace_mul n (n + 2) n i _ _ (by omega) (by omega) (by omega),
    skPlace_cup_mul_skPlace_cap_right_zigzag, skPlace_one n i 1 (by omega)]

/-- Zig-zag: the cap joins the right leg of a cup with the strand on its right. -/
theorem cupAt_mul_capAt_succ (n i : ℕ) (h : i < n) : cupAt n i * capAt n (i + 1) = 1 := by
  have h₁ : skPlace n (n + 2) i skCup = skPlace n (n + 2) i (skPlace 1 3 0 skCup) :=
    (skPlace_skPlace n (n + 2) i 0 skCup (by omega) (by omega) (by omega) (by omega)).symm
  have h₂ : skPlace (n + 2) n (i + 1) skCap = skPlace (n + 2) n i (skPlace 3 1 1 skCap) :=
    (skPlace_skPlace (n + 2) n i 1 skCap (by omega) (by omega) (by omega) (by omega)).symm
  rw [cupAt, capAt, h₁, h₂, ← skPlace_mul n (n + 2) n i _ _ (by omega) (by omega) (by omega),
    skPlace_cup_mul_skPlace_cap_left_zigzag, skPlace_one n i 1 (by omega)]

/-- A cup followed by the cap on the same two strands is a loop: the scalar `-t² - t⁻²`. -/
theorem cupAt_mul_capAt (n i : ℕ) (h : i ≤ n) :
    cupAt n i * capAt n i =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • (1 : SkMat n n) := by
  rw [cupAt, capAt, ← skPlace_mul n (n + 2) n i skCup skCap (by omega) (by omega) (by omega),
    skCup_mul_skCap_zigzag, skPlace_smul, skPlace_one n i 0 (by omega)]

end AJConjecture
