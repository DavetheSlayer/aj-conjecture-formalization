import Mathlib
import AJHandoff.TorusKnot.PairKWhDOrientExch

/-!
# Every rule of the checker preserves oriented states

`orientStates_rule_perm`: for every rule of `AJConjecture.MorseRule` whose two sides fit on `n`
strands, and every label list of length `n`, the two sides have the same oriented states up to
order. In particular every move preserves the oriented writhe (the framed first Reidemeister move
`kink` cancels a positive and a negative curl, whose oriented signs are `+1` and `-1`; a strand
sliding over a cup or a cap crosses its two legs, of opposite directions, with opposite oriented
signs).

Route: `exch` is `orientStates_exch_perm`. Every other rule at the position `i` is the shift by
`i` of the same rule at the position `0` (`orientStates_rule_shift`, from `orientStates_frame`
and `orientStates_add`); at the position `0` it is a finite check on its `1`, `2` or `3` strands
and all signs (`decide`).
-/

namespace AJConjecture

/-- A pair of words with the same oriented states on `m` strands keeps them when shifted by `i`
inside any longer label list. -/
private theorem orientStates_rule_shift (u v : MorseWord) (m i n : ℕ)
    (hu : morseFits m u = true) (hv : morseFits m v = true)
    (hbase : ∀ A : List Bool, A.length = m →
      (orientStates u [(A, 0)]).Perm (orientStates v [(A, 0)]))
    (hn : i + m ≤ n) (L : List Bool) (hL : L.length = n) (x : ℤ) :
    (orientStates (morseShiftWord i u) [(L, x)]).Perm
      (orientStates (morseShiftWord i v) [(L, x)]) := by
  have hsplit : L = L.take i ++ (L.drop i).take m ++ (L.drop i).drop m := by
    simp
  have hP : (L.take i).length = i := by simp; omega
  have hA : ((L.drop i).take m).length = m := by simp; omega
  rw [hsplit, orientStates_frame m i u hu _ _ _ hP hA, orientStates_frame m i v hv _ _ _ hP hA,
    orientStates_add u, orientStates_add v, List.map_map, List.map_map]
  exact ((hbase _ hA).map _)

/-- A statement about all lists of length one. -/
private theorem forall_length_one {P : List Bool → Prop} (h : ∀ b₀, P [b₀]) :
    ∀ A : List Bool, A.length = 1 → P A := by
  intro A hA
  rcases A with _ | ⟨b₀, _ | ⟨_, _⟩⟩ <;> simp at hA
  exact h b₀

/-- A statement about all lists of length two. -/
private theorem forall_length_two {P : List Bool → Prop} (h : ∀ b₀ b₁, P [b₀, b₁]) :
    ∀ A : List Bool, A.length = 2 → P A := by
  intro A hA
  rcases A with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨_, _⟩⟩⟩ <;> simp at hA
  exact h b₀ b₁

/-- A statement about all lists of length three. -/
private theorem forall_length_three {P : List Bool → Prop}
    (h : ∀ b₀ b₁ b₂, P [b₀, b₁, b₂]) :
    ∀ A : List Bool, A.length = 3 → P A := by
  intro A hA
  rcases A with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hA
  exact h b₀ b₁ b₂

/-! The rules at the position `0`: finite checks. -/

private theorem base_zig : ∀ r b₀ : Bool,
    (orientStates (morseRuleLhs (.zig 0 r)) [([b₀], 0)]).Perm
      (orientStates (morseRuleRhs (.zig 0 r)) [([b₀], 0)]) := by decide

private theorem base_r2 : ∀ s b₀ b₁ : Bool,
    (orientStates (morseRuleLhs (.r2 0 s)) [([b₀, b₁], 0)]).Perm
      (orientStates (morseRuleRhs (.r2 0 s)) [([b₀, b₁], 0)]) := by decide

private theorem base_r3 : ∀ s b₀ b₁ b₂ : Bool,
    (orientStates (morseRuleLhs (.r3 0 s)) [([b₀, b₁, b₂], 0)]).Perm
      (orientStates (morseRuleRhs (.r3 0 s)) [([b₀, b₁, b₂], 0)]) := by decide

private theorem base_cupSlide : ∀ s r b₀ : Bool,
    (orientStates (morseRuleLhs (.cupSlide 0 s r)) [([b₀], 0)]).Perm
      (orientStates (morseRuleRhs (.cupSlide 0 s r)) [([b₀], 0)]) := by decide

private theorem base_capSlide : ∀ s r b₀ b₁ b₂ : Bool,
    (orientStates (morseRuleLhs (.capSlide 0 s r)) [([b₀, b₁, b₂], 0)]).Perm
      (orientStates (morseRuleRhs (.capSlide 0 s r)) [([b₀, b₁, b₂], 0)]) := by decide

private theorem base_kink : ∀ s b₀ : Bool,
    (orientStates (morseRuleLhs (.kink 0 s)) [([b₀], 0)]).Perm
      (orientStates (morseRuleRhs (.kink 0 s)) [([b₀], 0)]) := by decide

/-- **Every rule of the checker preserves the oriented states up to order.** -/
theorem orientStates_rule_perm (R : MorseRule) (n : ℕ) (hR : morseRuleOk R = true)
    (hl : morseFits n (morseRuleLhs R) = true) (hr : morseFits n (morseRuleRhs R) = true)
    (L : List Bool) (hL : L.length = n) (x : ℤ) :
    (orientStates (morseRuleLhs R) [(L, x)]).Perm (orientStates (morseRuleRhs R) [(L, x)]) := by
  cases R with
  | exch a b =>
    simp only [morseRuleOk, decide_eq_true_eq] at hR
    exact orientStates_exch_perm a b hR n hl L hL x
  | zig i r =>
    have e1 : morseRuleLhs (.zig i r) = morseShiftWord i (morseRuleLhs (.zig 0 r)) := by
      cases r <;> simp [morseRuleLhs, morseShiftWord, shiftLetter] <;> omega
    have e2 : morseRuleRhs (.zig i r) = morseShiftWord i (morseRuleRhs (.zig 0 r)) := rfl
    rw [e1, e2] at *
    refine orientStates_rule_shift _ _ 1 i n (by cases r <;> rfl) rfl
      (forall_length_one (base_zig r)) ?_ L hL x
    cases r <;> simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn,
      morseKindOut] at hl <;> omega
  | r2 i s =>
    have e1 : morseRuleLhs (.r2 i s) = morseShiftWord i (morseRuleLhs (.r2 0 s)) := by
      simp [morseRuleLhs, morseShiftWord, shiftLetter]
    have e2 : morseRuleRhs (.r2 i s) = morseShiftWord i (morseRuleRhs (.r2 0 s)) := rfl
    rw [e1, e2] at *
    refine orientStates_rule_shift _ _ 2 i n (by cases s <;> rfl) rfl
      (forall_length_two (base_r2 s)) ?_ L hL x
    simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn,
      morseKindOut] at hl
    omega
  | r3 i s =>
    have e1 : morseRuleLhs (.r3 i s) = morseShiftWord i (morseRuleLhs (.r3 0 s)) := by
      simp [morseRuleLhs, morseShiftWord, shiftLetter]; omega
    have e2 : morseRuleRhs (.r3 i s) = morseShiftWord i (morseRuleRhs (.r3 0 s)) := by
      simp [morseRuleRhs, morseShiftWord, shiftLetter]; omega
    rw [e1, e2] at *
    refine orientStates_rule_shift _ _ 3 i n (by cases s <;> rfl) (by cases s <;> rfl)
      (forall_length_three (base_r3 s)) ?_ L hL x
    simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn,
      morseKindOut] at hl
    omega
  | cupSlide i s r =>
    have e1 : morseRuleLhs (.cupSlide i s r) =
        morseShiftWord i (morseRuleLhs (.cupSlide 0 s r)) := by
      cases r <;> simp [morseRuleLhs, morseShiftWord, shiftLetter] <;> omega
    have e2 : morseRuleRhs (.cupSlide i s r) =
        morseShiftWord i (morseRuleRhs (.cupSlide 0 s r)) := by
      cases r <;> simp [morseRuleRhs, morseShiftWord, shiftLetter]; omega
    rw [e1, e2] at *
    refine orientStates_rule_shift _ _ 1 i n (by cases s <;> cases r <;> rfl)
      (by cases r <;> rfl) (forall_length_one (base_cupSlide s r)) ?_ L hL x
    cases r <;> simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn,
      morseKindOut] at hl <;> omega
  | capSlide i s r =>
    have e1 : morseRuleLhs (.capSlide i s r) =
        morseShiftWord i (morseRuleLhs (.capSlide 0 s r)) := by
      cases r <;> simp [morseRuleLhs, morseShiftWord, shiftLetter] <;> omega
    have e2 : morseRuleRhs (.capSlide i s r) =
        morseShiftWord i (morseRuleRhs (.capSlide 0 s r)) := by
      cases r <;> simp [morseRuleRhs, morseShiftWord, shiftLetter]; omega
    rw [e1, e2] at *
    refine orientStates_rule_shift _ _ 3 i n (by cases s <;> cases r <;> rfl)
      (by cases r <;> rfl) (forall_length_three (base_capSlide s r)) ?_ L hL x
    cases r <;> simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn,
      morseKindOut] at hl <;> omega
  | kink i s =>
    have e1 : morseRuleLhs (.kink i s) = morseShiftWord i (morseRuleLhs (.kink 0 s)) := by
      simp [morseRuleLhs, morseShiftWord, shiftLetter]; omega
    have e2 : morseRuleRhs (.kink i s) = morseShiftWord i (morseRuleRhs (.kink 0 s)) := rfl
    rw [e1, e2] at *
    refine orientStates_rule_shift _ _ 1 i n (by cases s <;> rfl) rfl
      (forall_length_one (base_kink s)) ?_ L hL x
    simp [morseRuleLhs, morseFits, morseLetterOut, morseKindIn,
      morseKindOut] at hl
    omega

end AJConjecture
