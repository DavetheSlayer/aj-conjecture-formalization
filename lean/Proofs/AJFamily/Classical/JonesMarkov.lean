import Mathlib
import AJConjecture.ColoredJones
import AJConjecture.SkeinBracketCyclic
import AJConjecture.SkeinCrossingRelations
import AJFamily.MarkovEquiv

/-!
# Markov invariance of the colour-2 Jones polynomial

`jones2` is the colour-2 coloured Jones polynomial of an arbitrary closed braid, built from the
writhe and the Kauffman bracket. It is invariant under every elementary Markov move, hence under
`MarkovEquiv`; so braid knots with pairwise distinct `coloredJones K 2` are pairwise not Markov
equivalent.
-/

open Polynomial
open LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The colour-2 coloured Jones polynomial of a closed braid. -/
def jones2 (p : ClosedBraid) : ℤ[T;T⁻¹] :=
  ((-1 : ℤ) ^ (1 + (writhe p.2).natAbs)) • (T (-(3 * writhe p.2)) * bracket p.1 p.2)

/-- Cabling with one strand does nothing. -/
theorem cable_one (w : BraidWord) : cable 1 w = w := by
  unfold cable
  have h : ∀ g : ℕ × Bool, cableGen 1 g = [g] := by
    rintro ⟨i, b⟩
    cases b <;> simp [cableGen]
  rw [show cableGen 1 = fun g ↦ [g] from funext h]
  exact List.flatMap_singleton' w

/-- The colour-2 coloured Jones polynomial of a braid knot is `jones2` of its closed braid. -/
theorem coloredJones_two_eq_jones2 (K : BraidKnot) :
    coloredJones K 2 = jones2 (K.strands, K.word) := by
  simp only [coloredJones, coloredJonesPos, chebyshevBracket, jones2]
  norm_num
  rw [cable_one, mul_comm (writhe K.word), mul_comm]

/-- The writhe is additive under concatenation. -/
theorem writhe_append (u v : BraidWord) : writhe (u ++ v) = writhe u + writhe v := by
  simp [writhe, List.map_append, List.sum_append]

/-- Replacing a middle subword by one with the same braid matrix keeps the bracket. -/
private theorem bracket_append_mid_congr (m : ℕ) (u v x y : BraidWord)
    (h : braidMatrix m x = braidMatrix m y) :
    bracket m (u ++ x ++ v) = bracket m (u ++ y ++ v) := by
  apply laurentToField_injective
  rw [laurentToField_bracket, laurentToField_bracket, braidMatrix_append, braidMatrix_append,
    braidMatrix_append, braidMatrix_append, h]

/-- The braid matrix of a two-letter word. -/
private theorem braidMatrix_pair (m : ℕ) (g h : ℕ × Bool) :
    braidMatrix m [g, h] = crossingF m g * crossingF m h := by
  simp [braidMatrix]

/-- The braid matrix of a three-letter word. -/
private theorem braidMatrix_triple (m : ℕ) (g h k : ℕ × Bool) :
    braidMatrix m [g, h, k] = crossingF m g * crossingF m h * crossingF m k := by
  simp [braidMatrix, mul_assoc]

/-- Cancelling a letter against its inverse keeps the bracket. -/
theorem bracket_cancel (m : ℕ) (u v : BraidWord) (i : ℕ) (b : Bool) :
    bracket m (u ++ (i, b) :: (i, !b) :: v) = bracket m (u ++ v) := by
  have h := bracket_append_mid_congr m u v [(i, b), (i, !b)] [] (by
    rw [braidMatrix_pair, braidMatrix_nil]
    cases b
    · exact crossingF_inv_mul m i
    · exact crossingF_mul_inv m i)
  simpa using h

/-- Far commutation keeps the bracket. -/
theorem bracket_farComm (m : ℕ) (u v : BraidWord) (i j : ℕ) (b c : Bool) (hij : i + 2 ≤ j) :
    bracket m (u ++ (i, b) :: (j, c) :: v) = bracket m (u ++ (j, c) :: (i, b) :: v) := by
  have h := bracket_append_mid_congr m u v [(i, b), (j, c)] [(j, c), (i, b)] (by
    rw [braidMatrix_pair, braidMatrix_pair]
    exact (crossingF_commute m i j b c (by omega)).eq)
  simpa using h

/-- The braid relation keeps the bracket. -/
theorem bracket_braidRel (m : ℕ) (u v : BraidWord) (i : ℕ) (h : i + 2 < m) :
    bracket m (u ++ (i, true) :: (i + 1, true) :: (i, true) :: v) =
      bracket m (u ++ (i + 1, true) :: (i, true) :: (i + 1, true) :: v) := by
  have h' := bracket_append_mid_congr m u v [(i, true), (i + 1, true), (i, true)]
    [(i + 1, true), (i, true), (i + 1, true)] (by
    rw [braidMatrix_triple, braidMatrix_triple]
    exact crossingF_braid m i true h)
  simpa using h'

/-- Markov stabilisation multiplies the bracket by the kink factor `-T (±3)`. -/
theorem bracket_stabilize (m : ℕ) (w : BraidWord) (b : Bool) (hm : 0 < m)
    (hw : IsOnStrands m w) :
    bracket (m + 1) (w ++ [(m - 1, b)]) = -T (if b then 3 else -3) * bracket m w := by
  apply laurentToField_injective
  rw [map_mul, laurentToField_bracket, laurentToField_bracket,
    qtr_braidMatrix_stabilise m w b hw hm]
  congr 1
  rw [map_neg, laurentToField, LaurentPolynomial.eval₂_T]
  split_ifs <;> simp

/-- Adding one to an integer flips the parity of its absolute value. -/
private theorem neg_one_pow_natAbs_add_one (z : ℤ) :
    (-1 : ℤ) ^ (z + 1).natAbs = -((-1 : ℤ) ^ z.natAbs) := by
  rcases Int.even_or_odd z with h | h
  · rw [(Int.natAbs_even.mpr h).neg_one_pow, (Int.natAbs_odd.mpr h.add_one).neg_one_pow]
  · rw [(Int.natAbs_odd.mpr h).neg_one_pow, (Int.natAbs_even.mpr h.add_one).neg_one_pow]
    norm_num

/-- `jones2` is invariant under Markov stabilisation. -/
private theorem jones2_stabilize (m : ℕ) (w : BraidWord) (b : Bool) (hm : 0 < m)
    (hw : IsOnStrands m w) : jones2 (m + 1, w ++ [(m - 1, b)]) = jones2 (m, w) := by
  simp only [jones2]
  rw [bracket_stabilize m w b hm hw, writhe_append]
  have hw1 : writhe [(m - 1, b)] = if b then 1 else -1 := by cases b <;> simp [writhe]
  rw [hw1]
  have hs1 : ∀ z : ℤ, ((-1 : ℤ) ^ (1 + (z + 1).natAbs)) = -((-1 : ℤ) ^ (1 + z.natAbs)) := by
    intro z
    rw [pow_add, pow_add, neg_one_pow_natAbs_add_one]
    ring
  have hs2 : ∀ z : ℤ,
      ((-1 : ℤ) ^ (1 + (z + -1).natAbs)) = -((-1 : ℤ) ^ (1 + z.natAbs)) := by
    intro z
    have h := neg_one_pow_natAbs_add_one (z + -1)
    rw [show z + -1 + 1 = z by ring] at h
    rw [pow_add, pow_add, h]
    ring
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [hs2]
    have hT : T (-(3 * (writhe w + -1))) * (-T (-3) * bracket m w) =
        -(T (-(3 * writhe w)) * bracket m w) := by
      rw [show -(3 * (writhe w + -1)) = -(3 * writhe w) + 3 by ring, T_add]
      have : T (3 : ℤ) * T (-3 : ℤ) = (1 : ℤ[T;T⁻¹]) := by rw [← T_add]; simp
      linear_combination (-(T (-(3 * writhe w)) * bracket m w)) * this
    rw [hT, smul_neg, neg_smul, neg_neg]
  · simp only [ite_true]
    rw [hs1]
    have hT : T (-(3 * (writhe w + 1))) * (-T 3 * bracket m w) =
        -(T (-(3 * writhe w)) * bracket m w) := by
      rw [show -(3 * (writhe w + 1)) = -(3 * writhe w) + -3 by ring, T_add]
      have : T (-3 : ℤ) * T (3 : ℤ) = (1 : ℤ[T;T⁻¹]) := by rw [← T_add]; simp
      linear_combination (-(T (-(3 * writhe w)) * bracket m w)) * this
    rw [hT, smul_neg, neg_smul, neg_neg]

/-- `jones2` is invariant under each elementary Markov move. -/
theorem jones2_of_markovStep {p q : ClosedBraid} (h : MarkovStep p q) : jones2 p = jones2 q := by
  cases h with
  | cancel u v i b h =>
    have hw : writhe (u ++ (i, b) :: (i, !b) :: v) = writhe (u ++ v) := by
      rw [show u ++ (i, b) :: (i, !b) :: v = u ++ ([(i, b), (i, !b)] ++ v) by simp,
        writhe_append, writhe_append, writhe_append]
      cases b <;> simp [writhe]
    simp only [jones2, hw, bracket_cancel]
  | farComm u v i j b c hij h =>
    have hw : writhe (u ++ (i, b) :: (j, c) :: v) = writhe (u ++ (j, c) :: (i, b) :: v) := by
      simp only [writhe, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      ring
    simp only [jones2, hw, bracket_farComm _ u v i j b c hij]
  | braidRel u v i h =>
    have hw : writhe (u ++ (i, true) :: (i + 1, true) :: (i, true) :: v) =
        writhe (u ++ (i + 1, true) :: (i, true) :: (i + 1, true) :: v) := by
      simp [writhe]
    simp only [jones2, hw, bracket_braidRel _ u v i h]
  | @rotate m w g =>
    have hw : writhe (g :: w) = writhe (w ++ [g]) := by
      rw [show g :: w = [g] ++ w from rfl, writhe_append, writhe_append, add_comm]
    have hb : bracket m (g :: w) = bracket m (w ++ [g]) := bracket_append_comm m [g] w
    simp only [jones2, hw, hb]
  | stabilize w b hm hw => exact (jones2_stabilize _ w b hm hw).symm

/-- `jones2` is invariant under Markov equivalence of closed braids. -/
theorem jones2_of_eqvGen {p q : ClosedBraid} (h : Relation.EqvGen MarkovStep p q) :
    jones2 p = jones2 q := by
  induction h with
  | rel p q h => exact jones2_of_markovStep h
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih1 ih2 => exact ih1.trans ih2

/-- Markov equivalent braid knots have the same colour-2 coloured Jones polynomial. -/
theorem coloredJones_two_eq_of_markovEquiv {K K' : BraidKnot} (h : MarkovEquiv K K') :
    coloredJones K 2 = coloredJones K' 2 := by
  rw [coloredJones_two_eq_jones2, coloredJones_two_eq_jones2]
  exact jones2_of_eqvGen h

/-- Braid knots with pairwise distinct colour-2 coloured Jones polynomials are pairwise not
Markov equivalent. -/
theorem pairwise_not_markovEquiv_of_injective (K : ℕ → BraidKnot)
    (h : Function.Injective fun n ↦ coloredJones (K n) 2) :
    Pairwise fun i j ↦ ¬ MarkovEquiv (K i) (K j) :=
  fun _ _ hij hK ↦ hij (h (coloredJones_two_eq_of_markovEquiv hK))

end AJConjecture
