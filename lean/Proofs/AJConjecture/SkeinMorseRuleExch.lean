import Mathlib
import AJConjecture.SkeinMorseRule
import AJConjecture.SkeinPlaceComm

/-!
# Soundness of the rule `exch`

Two letters with disjoint supports exchange their heights: if the letter `a` at the position `i`
lies to the left of the letter `b` at the position `j` (`i + in a ≤ j`), then "first `a`, then `b`
shifted by `out a - in a`" is "first `b`, then `a`".

Proof: one application of `AJConjecture.skPlace_mul_skPlace_comm` for each of the nine pairs of
kinds (the local operators are `cupThick c`, `capThick c`, `halfTwist c s`, of sizes `0 → 2c`,
`2c → 0`, `2c → 2c`), with the offsets `c * i`, `c * j`; the hypotheses of that lemma are the two
fitting conditions multiplied by `c`.
-/

namespace AJConjecture

/-- Two placements on disjoint windows exchange, each side followed by the operator of the
empty word, with free intermediate sizes. -/
private theorem skPlace_mul_skPlace_comm_sized_morseRuleExch (N N₁ N₂ P P' N' i j j' : ℕ)
    {k l k' l' : ℕ} (A : SkMat k l) (B : SkMat k' l') (hij : i + k ≤ j) (hj : j + k' ≤ N)
    (hj' : j' = j + l - k) (h₁ : N + l = N₁ + k) (h₂ : N + l' = N₂ + k')
    (hP : N₁ + l' = P + k') (hP' : P' = P) :
    skPlace N N₁ i A * (skPlace N₁ P j' B * skPlace P N' 0 (1 : SkMat 0 0)) =
      skPlace N N₂ j B * (skPlace N₂ P' i A * skPlace P' N' 0 (1 : SkMat 0 0)) := by
  subst hj' hP'
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    skPlace_mul_skPlace_comm N N₁ N₂ _ i j A B hij hj h₁ h₂ hP]

/-- The exchange of two letters with disjoint supports is sound. -/
theorem morseRuleSound_exch (a b : MorseLetter) : MorseRuleSound (.exch a b) := by
  intro c n N N' hN hok _ hr
  obtain ⟨ka, i⟩ := a
  obtain ⟨kb, j⟩ := b
  simp only [morseRuleOk, decide_eq_true_eq] at hok
  simp only [morseRuleRhs, morseFits, Bool.and_eq_true, decide_eq_true_eq] at hr
  have m₁ := Nat.mul_le_mul_left c hok
  have m₂ := Nat.mul_le_mul_left c hr.1
  have m₃ : c * (j + morseKindOut ka - morseKindIn ka) =
      c * j + c * morseKindOut ka - c * morseKindIn ka := by
    rw [Nat.mul_sub, Nat.mul_add]
  rw [Nat.mul_add] at m₁ m₂
  subst hN
  cases ka <;> cases kb <;> dsimp only [morseKindIn, morseKindOut] at m₁ m₂ m₃ <;>
    refine skPlace_mul_skPlace_comm_sized_morseRuleExch _ _ _ _ _ N' (c * i) (c * j) _ _ _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try dsimp only [morseKindIn, morseKindOut]) <;> omega

end AJConjecture
