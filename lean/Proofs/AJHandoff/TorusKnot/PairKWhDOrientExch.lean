import Mathlib
import AJHandoff.TorusKnot.PairKWhDOrientBasic

/-!
# The exchange rule preserves oriented states

`orientStates_exch_perm`: two letters with disjoint supports act on disjoint segments of the label
list, so performing them in either order gives the same oriented states, up to order (a cup
doubles the states, and the two orders interleave the doublings differently).

Route: write the label list as `P ++ A ++ M ++ B ++ Q` with `P.length = a.2`,
`A.length = morseKindIn a.1`, `(P ++ A ++ M).length = b.2`, `B.length = morseKindIn b.1`; each
letter is a shifted letter at the position `0` (`orientStates_frame` with `m = morseKindIn`);
the two composites are the two orders of a product of two lists (`List.Perm` of the swapped
`flatMap`), with the writhes added in both orders (`orientStates_add`). Case analysis on the
kinds is not needed beyond `morseKindOut`, `morseKindIn`.
-/

namespace AJConjecture

/-- The exchange of two letters with disjoint supports preserves the oriented states up to
order. -/
theorem orientStates_exch_perm (a b : MorseLetter) (h : a.2 + morseKindIn a.1 ≤ b.2) (n : ℕ)
    (hl : morseFits n (morseRuleLhs (.exch a b)) = true) (L : List Bool) (hL : L.length = n)
    (x : ℤ) :
    (orientStates (morseRuleLhs (.exch a b)) [(L, x)]).Perm
      (orientStates (morseRuleRhs (.exch a b)) [(L, x)]) := by
  obtain ⟨ka, i⟩ := a
  obtain ⟨kb, j⟩ := b
  simp only at h
  simp only [morseRuleLhs, morseFits, morseLetterOut, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hl
  obtain ⟨hl1, hl2⟩ := hl
  have hl2' := of_decide_eq_true hl2
  have hjn : j + morseKindIn kb ≤ n := by omega
  -- one letter at the position `P.length` acts on the segment after `P`
  have key : ∀ (k : MorseKind) (P A R : List Bool) (y : ℤ), A.length = morseKindIn k →
      orientLetter (k, P.length) (P ++ A ++ R, y) =
        ((orientLetter (k, 0) (A, 0)).map fun st ↦ (P ++ st.1 ++ R, st.2 + y)) := by
    intro k P A R y hA
    have h1 := orientLetter_frame (morseKindIn k) (k, 0) (by simp) P A R hA y
    have h2 := orientLetter_add (k, 0) A 0 y
    simp only [shiftLetter, zero_add] at h1 h2
    rw [h1, h2, List.map_map]
    rfl
  have hout : ∀ (k : MorseKind) (A : List Bool), A.length = morseKindIn k →
      ∀ st ∈ orientLetter (k, 0) (A, 0), st.1.length = morseKindOut k := by
    intro k A hA st hst
    have := orientLetter_length (morseKindIn k) (k, 0) (by simp) (A, 0) hA st hst
    simpa [morseLetterOut] using this
  -- the segments
  set P := L.take i with hP
  set A := (L.drop i).take (morseKindIn ka) with hA
  set M := (L.drop (i + morseKindIn ka)).take (j - (i + morseKindIn ka)) with hM
  set B := (L.drop j).take (morseKindIn kb) with hB
  set Q := L.drop (j + morseKindIn kb) with hQ
  have hPl : P.length = i := by simp [hP]; omega
  have hAl : A.length = morseKindIn ka := by simp [hA]; omega
  have hMl : M.length = j - (i + morseKindIn ka) := by simp [hM]; omega
  have hBl : B.length = morseKindIn kb := by simp [hB]; omega
  have hsplit : L = P ++ A ++ M ++ B ++ Q := by
    apply List.ext_getElem
    · simp [hP, hA, hM, hB, hQ]; omega
    · intro t h1 h2
      simp only [hP, hA, hM, hB, hQ, List.getElem_append, List.length_append, List.length_take,
        List.length_drop, List.getElem_take, List.getElem_drop]
      split_ifs <;> congr 1 <;> omega
  -- the two sides
  have hlhs : orientStates [(ka, i), (kb, j + morseKindOut ka - morseKindIn ka)] [(L, x)] =
      (orientLetter (ka, 0) (A, 0)).flatMap fun sa ↦
        (orientLetter (kb, 0) (B, 0)).map fun sb ↦
          (P ++ sa.1 ++ M ++ sb.1 ++ Q, sb.2 + (sa.2 + x)) := by
    simp only [orientStates, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hsplit, show P ++ A ++ M ++ B ++ Q = P ++ A ++ (M ++ B ++ Q) by simp, ← hPl,
      key ka P A _ x hAl, List.flatMap_map]
    refine List.flatMap_congr fun sa hsa ↦ ?_
    have hsa' := hout ka A hAl sa hsa
    have hpos : j + morseKindOut ka - morseKindIn ka = (P ++ sa.1 ++ M).length := by
      simp [hPl, hsa', hMl]; omega
    rw [hpos, show P ++ sa.1 ++ (M ++ B ++ Q) = P ++ sa.1 ++ M ++ B ++ Q by simp,
      key kb _ B Q _ hBl]
  have hrhs : orientStates [(kb, j), (ka, i)] [(L, x)] =
      (orientLetter (kb, 0) (B, 0)).flatMap fun sb ↦
        (orientLetter (ka, 0) (A, 0)).map fun sa ↦
          (P ++ sa.1 ++ M ++ sb.1 ++ Q, sa.2 + (sb.2 + x)) := by
    simp only [orientStates, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hpos : j = (P ++ A ++ M).length := by simp [hPl, hAl, hMl]; omega
    rw [hsplit, hpos, key kb _ B Q x hBl, List.flatMap_map]
    refine List.flatMap_congr fun sb _ ↦ ?_
    rw [show P ++ A ++ M ++ sb.1 ++ Q = P ++ A ++ (M ++ sb.1 ++ Q) by simp, ← hPl,
      key ka P A _ _ hAl]
    simp [List.append_assoc]
  simp only [morseRuleLhs, morseRuleRhs]
  rw [hlhs, hrhs, ← Multiset.coe_eq_coe, ← Multiset.coe_bind, ← Multiset.coe_bind]
  simp only [← Multiset.map_coe]
  rw [Multiset.bind_map_comm]
  refine Multiset.bind_congr fun sb _ ↦ Multiset.map_congr rfl fun sa _ ↦ ?_
  simp only [Prod.mk.injEq, true_and]
  ring

end AJConjecture
