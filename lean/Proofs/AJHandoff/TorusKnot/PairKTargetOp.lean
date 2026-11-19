import Mathlib
import AJHandoff.TorusKnot.PairKTargetWord
import AJConjecture.SkeinLongKnot
import AJConjecture.SkeinMorseOpBasic

/-!
# The operator of the target word

`morseOp_pairTargetWord`: at every thickness `c` the operator of `pairTargetWord r s` is the
partial trace over the second bundle of the long-knot operator of `T(r, s)` at thickness `2c`,
followed by `2(r - 1)s` negative half twists and the clasp. Route (generalising
`AJFamily.Skein.TorusTargetOp`, with the word-specific doubling step replaced by
`morseOp_morseDouble`): split the word with `morseOp_append`; the first cup and the last cap
give the closure formula `ptrTail_eq_cupThick_capThick`; the doubled long closure is
`morseOp (2c) (morseLongClosure r _) = longKnotOp (torusPairKnot r s h) (2c)` placed at offset
`0` (`morseOp_morseDouble`, `morseOp_morseLongClosure_eq_longKnotOp`); the twists and the clasp
word are placed at offset `0` on `3c` factors (as in `TorusTargetOp`).
-/

namespace AJConjecture

/-- The number of strands after a concatenation. -/
private theorem morseOut_append_target (n : ℕ) (u v : MorseWord) :
    morseOut n (u ++ v) = morseOut (morseOut n u) v := by
  induction u generalizing n with
  | nil => rfl
  | cons l u ih => exact ih _

/-- A concatenation fits if both pieces fit in turn. -/
private theorem morseFits_append_target {n : ℕ} {u v : MorseWord} (hu : morseFits n u = true)
    (hv : morseFits (morseOut n u) v = true) : morseFits n (u ++ v) = true := by
  induction u generalizing n with
  | nil => exact hv
  | cons l u ih =>
    simp only [morseFits, Bool.and_eq_true] at hu
    simp only [List.cons_append, morseFits, Bool.and_eq_true]
    exact ⟨hu.1, ih hu.2 hv⟩

/-- The cups of a long closure fit on `n ≥ 1` strands and add `2p` strands. -/
private theorem morseFits_cups_target (p n : ℕ) (hn : 1 ≤ n) :
    morseFits n ((List.range p).map fun j ↦ (MorseKind.cup, j + 1)) = true ∧
      morseOut n ((List.range p).map fun j ↦ (MorseKind.cup, j + 1)) = n + 2 * p := by
  induction p with
  | zero => exact ⟨rfl, rfl⟩
  | succ p ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine ⟨morseFits_append_target ih.1 ?_, ?_⟩
    · rw [ih.2]
      simp only [morseFits, morseKindIn, Bool.and_true]
      exact decide_eq_true (by omega)
    · rw [morseOut_append_target, ih.2]
      simp only [morseOut, morseLetterOut, morseKindOut, morseKindIn]
      omega

/-- The caps of a long closure fit on `1 + 2p` strands and leave one strand. -/
private theorem morseFits_caps_target (p : ℕ) :
    morseFits (1 + 2 * p) ((List.range p).reverse.map fun j ↦ (MorseKind.cap, j + 1)) = true ∧
      morseOut (1 + 2 * p) ((List.range p).reverse.map fun j ↦ (MorseKind.cap, j + 1)) = 1 := by
  induction p with
  | zero => exact ⟨rfl, rfl⟩
  | succ p ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons]
    have e : morseLetterOut (1 + 2 * (p + 1)) (MorseKind.cap, p + 1) = 1 + 2 * p := by
      simp only [morseLetterOut, morseKindOut, morseKindIn]
      omega
    refine ⟨?_, ?_⟩
    · simp only [morseFits, Bool.and_eq_true, e, ih.1, and_true, morseKindIn]
      exact decide_eq_true (by omega)
    · simp only [morseOut, e, ih.2]

/-- A braid word on `m ≤ n` strands fits on `n` strands and keeps their number. -/
private theorem morseFits_morseOfBraid_target (n m : ℕ) (w : BraidWord) (hw : IsOnStrands m w)
    (hmn : m ≤ n) : morseFits n (morseOfBraid w) = true ∧ morseOut n (morseOfBraid w) = n := by
  induction w with
  | nil => exact ⟨rfl, rfl⟩
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg')
    have e : morseLetterOut n (MorseKind.cross g.2, g.1) = n := by
      simp only [morseLetterOut, morseKindOut, morseKindIn]
      omega
    refine ⟨?_, ?_⟩
    · change (decide (g.1 + morseKindIn (MorseKind.cross g.2) ≤ n) &&
        morseFits (morseLetterOut n (MorseKind.cross g.2, g.1)) (morseOfBraid w)) = true
      simp only [e, h1, Bool.and_true, morseKindIn]
      exact decide_eq_true (by omega)
    · change morseOut (morseLetterOut n (MorseKind.cross g.2, g.1)) (morseOfBraid w) = n
      rw [e, h2]

/-- The long closure of a braid on `m ≥ 1` strands fits on one strand and ends on one strand. -/
private theorem morseFits_morseLongClosure_target (m : ℕ) (w : BraidWord) (hm : 1 ≤ m)
    (hw : IsOnStrands m w) :
    morseFits 1 (morseLongClosure m w) = true ∧ morseOut 1 (morseLongClosure m w) = 1 := by
  obtain ⟨hc1, hc2⟩ := morseFits_cups_target (m - 1) 1 le_rfl
  obtain ⟨hb1, hb2⟩ := morseFits_morseOfBraid_target (1 + 2 * (m - 1)) m w hw (by omega)
  obtain ⟨hp1, hp2⟩ := morseFits_caps_target (m - 1)
  refine ⟨?_, ?_⟩
  · refine morseFits_append_target (morseFits_append_target hc1 ?_) ?_
    · rw [hc2]; exact hb1
    · rw [morseOut_append_target, hc2, hb2]; exact hp1
  · rw [morseLongClosure, morseOut_append_target, morseOut_append_target, hc2, hb2, hp2]

/-- The operator of a word that begins with a cup, with free sizes. -/
private theorem morseOp_cons_cup_target (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N + 2 * c) :
    morseOp c ((MorseKind.cup, i) :: u) N N' =
      skPlace N M (c * i) (cupThick c) * morseOp c u M N' := by
  have e : N + c * 2 - c * 0 = M := by rw [hM]; ring_nf; omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a cap, with free sizes. -/
private theorem morseOp_cons_cap_target (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hN : N = M + 2 * c) :
    morseOp c ((MorseKind.cap, i) :: u) N N' =
      skPlace N M (c * i) (capThick c) * morseOp c u M N' := by
  have e : N + c * 0 - c * 2 = M := by rw [hN]; ring_nf; omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a crossing, with free sizes. -/
private theorem morseOp_cons_cross_target (c i : ℕ) (s : Bool) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N) :
    morseOp c ((MorseKind.cross s, i) :: u) N N' =
      skPlace N M (c * i) (halfTwist c s) * morseOp c u M N' := by
  have e : N + c * 2 - c * 2 = M := by omega
  rw [← e]
  rfl

/-- A placed letter, placed again at `0` with `e` extra factors on the right. -/
private theorem skPlace_zero_mul_target {k l : ℕ} (N M O e j : ℕ) (A : SkMat k l)
    (B : SkMat M O) (hj : j + k ≤ N) (hkl : N + l = M + k) :
    skPlace (N + e) (M + e) j A * skPlace (M + e) (O + e) 0 B =
      skPlace (N + e) (O + e) 0 (skPlace N M j A * B) := by
  rw [skPlace_mul (N + e) (M + e) (O + e) 0 _ B (by omega) (by omega) (by omega),
    skPlace_skPlace (N + e) (M + e) 0 j A hj hkl (by omega) (by omega), Nat.zero_add]

/-- Extra tensor factors on the right of a word that fits pass through its operator. -/
private theorem morseOp_add_right_target (d e n : ℕ) (u : MorseWord)
    (hu : morseFits n u = true) :
    morseOp d u (d * n + e) (d * morseOut n u + e) =
      skPlace (d * n + e) (d * morseOut n u + e) 0 (morseOp d u (d * n) (d * morseOut n u)) := by
  induction u generalizing n with
  | nil =>
    change morseOp d [] (d * n + e) (d * n + e) =
      skPlace (d * n + e) (d * n + e) 0 (morseOp d [] (d * n) (d * n))
    rw [morseOp_nil, morseOp_nil, skPlace_one _ 0 _ (by omega)]
  | cons l u ih =>
    obtain ⟨k, i⟩ := l
    simp only [morseFits, Bool.and_eq_true, decide_eq_true_eq] at hu
    obtain ⟨hi, hu⟩ := hu
    have hdi : d * i ≤ d * n := Nat.mul_le_mul_left d (by omega)
    cases k with
    | cup =>
      have hu' : morseFits (n + 2) u = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hu
      change morseOp d ((MorseKind.cup, i) :: u) (d * n + e) (d * morseOut (n + 2 - 0) u + e) =
        skPlace (d * n + e) (d * morseOut (n + 2 - 0) u + e) 0
          (morseOp d ((MorseKind.cup, i) :: u) (d * n) (d * morseOut (n + 2 - 0) u))
      have hn2 : d * (n + 2) = d * n + 2 * d := by ring
      rw [Nat.sub_zero, morseOp_cons_cup_target d i u _ (d * (n + 2) + e) _ (by omega),
        morseOp_cons_cup_target d i u _ (d * (n + 2)) _ hn2, ih (n + 2) hu',
        skPlace_zero_mul_target _ _ _ e _ _ _ (by omega) (by omega)]
    | cap =>
      simp only [morseKindIn] at hi
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hu' : morseFits m u = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hu
      change morseOp d ((MorseKind.cap, i) :: u) (d * (m + 2) + e)
          (d * morseOut (m + 2 + 0 - 2) u + e) =
        skPlace (d * (m + 2) + e) (d * morseOut (m + 2 + 0 - 2) u + e) 0
          (morseOp d ((MorseKind.cap, i) :: u) (d * (m + 2)) (d * morseOut (m + 2 + 0 - 2) u))
      have hn2 : d * (m + 2) = d * m + 2 * d := by ring
      have hdi' : d * i ≤ d * m := Nat.mul_le_mul_left d (by omega)
      rw [show m + 2 + 0 - 2 = m by omega,
        morseOp_cons_cap_target d i u _ (d * m + e) _ (by omega),
        morseOp_cons_cap_target d i u _ (d * m) _ hn2, ih m hu', hn2,
        skPlace_zero_mul_target _ _ _ e _ _ _ (by omega) (by omega)]
    | cross s =>
      simp only [morseKindIn] at hi
      have hu' : morseFits n u = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hu
      change morseOp d ((MorseKind.cross s, i) :: u) (d * n + e)
          (d * morseOut (n + 2 - 2) u + e) =
        skPlace (d * n + e) (d * morseOut (n + 2 - 2) u + e) 0
          (morseOp d ((MorseKind.cross s, i) :: u) (d * n) (d * morseOut (n + 2 - 2) u))
      have hdi' : d * (i + 2) ≤ d * n := Nat.mul_le_mul_left d (by omega)
      rw [Nat.mul_add] at hdi'
      rw [Nat.add_sub_cancel, morseOp_cons_cross_target d i s u _ _ _ rfl,
        morseOp_cons_cross_target d i s u _ _ _ rfl, ih n hu',
        skPlace_zero_mul_target _ _ _ e _ _ _ (by omega) (by omega)]

/-- The number of tensor factors after a concatenation. -/
private theorem morseThickOut_append_target (c N : ℕ) (u v : MorseWord) :
    morseThickOut c N (u ++ v) = morseThickOut c (morseThickOut c N u) v := by
  induction u generalizing N with
  | nil => rfl
  | cons l u ih => exact ih _

/-- A braid word does not change the number of tensor factors. -/
private theorem morseThickOut_morseOfBraid_target (c : ℕ) (w : BraidWord) (N : ℕ) :
    morseThickOut c N (morseOfBraid w) = N := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    change morseThickOut c (N + c * 2 - c * 2) (morseOfBraid w) = N
    rw [Nat.add_sub_cancel, ih]

/-- The double of a word changes the number of factors at thickness `c` as the word does at
thickness `2c`. -/
private theorem morseThickOut_morseDouble_target (c N : ℕ) (w : MorseWord) :
    morseThickOut c N (morseDouble w) = morseThickOut (2 * c) N w := by
  induction w generalizing N with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨k, i⟩ := l
    change morseThickOut c N (morseDoubleLetter (k, i) ++ morseDouble w) = _
    rw [morseThickOut_append_target, ih]
    cases k with
    | cup =>
      change morseThickOut (2 * c) (N + c * 2 - c * 0 + c * 2 - c * 0) w =
        morseThickOut (2 * c) (N + 2 * c * 2 - 2 * c * 0) w
      congr 1
      omega
    | cap =>
      change morseThickOut (2 * c) (N + c * 0 - c * 2 + c * 0 - c * 2) w =
        morseThickOut (2 * c) (N + 2 * c * 0 - 2 * c * 2) w
      congr 1
      omega
    | cross s =>
      change morseThickOut (2 * c) (morseThickOut c N (morseOfBraid (cable 2 [(i, s)]))) w =
        morseThickOut (2 * c) (N + 2 * c * 2 - 2 * c * 2) w
      rw [morseThickOut_morseOfBraid_target, Nat.add_sub_cancel]

/-- A word that fits on `n` strands ends, for the thickness `d` and `e` extra factors, on
`d` times the number of strands at its end plus `e`. -/
private theorem morseThickOut_add_target (d e n : ℕ) (w : MorseWord)
    (hw : morseFits n w = true) :
    morseThickOut d (d * n + e) w = d * morseOut n w + e := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨k, i⟩ := l
    simp only [morseFits, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hi, hw⟩ := hw
    change morseFits (n + morseKindOut k - morseKindIn k) w = true at hw
    change morseThickOut d (d * n + e + d * morseKindOut k - d * morseKindIn k) w =
      d * morseOut (n + morseKindOut k - morseKindIn k) w + e
    rw [← ih _ hw]
    congr 1
    cases k with
    | cup =>
      simp only [morseKindOut, morseKindIn, Nat.sub_zero, Nat.mul_zero, Nat.mul_add]
      omega
    | cap =>
      simp only [morseKindOut, morseKindIn] at hi ⊢
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [show m + 2 + 0 - 2 = m by omega, Nat.mul_add]
      omega
    | cross s =>
      simp only [morseKindOut, morseKindIn, Nat.add_sub_cancel]

/-- The operator of a concatenation, with a free intermediate size. -/
private theorem morseOp_append_target (c : ℕ) (u v : MorseWord) (N M N' : ℕ)
    (hM : M = morseThickOut c N u) :
    morseOp c (u ++ v) N N' = morseOp c u N M * morseOp c v M N' := by
  subst hM
  exact morseOp_append c u v N N'

/-- Repeated crossings do not change the number of tensor factors. -/
private theorem morseThickOut_replicate_cross_target (c n i : ℕ) (s : Bool) (N : ℕ) :
    morseThickOut c N (List.replicate n (MorseKind.cross s, i)) = N := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change morseThickOut c (N + c * 2 - c * 2) (List.replicate n (MorseKind.cross s, i)) = N
    rw [Nat.add_sub_cancel, ih]

/-- A placement placed at the position `0`. -/
private theorem skPlace_zero_skPlace_target (n n' j : ℕ) {k l k' l' : ℕ}
    (A : SkMat k l) (hj : j + k ≤ k') (hkl : k' + l = l' + k) (h : k' ≤ n)
    (h' : n + l' = n' + k') :
    skPlace n n' 0 (skPlace k' l' j A) = skPlace n n' j A := by
  have e := skPlace_skPlace n n' 0 j A hj hkl (by omega) h'
  rwa [Nat.zero_add] at e

/-- The thick operator of `n` negative crossings of the first two bundles. -/
private theorem morseOp_replicate_cross_target (c n N : ℕ) (hN : 2 * c ≤ N) :
    morseOp c (List.replicate n (MorseKind.cross false, 0)) N N =
      skPlace N N 0 (halfTwist c false ^ n) := by
  induction n with
  | zero =>
    rw [List.replicate_zero, morseOp_nil, pow_zero, skPlace_one N 0 (2 * c) (by omega)]
  | succ n ih =>
    rw [List.replicate_succ, morseOp_cons_cross_target c 0 false _ N N N rfl, Nat.mul_zero, ih,
      pow_succ', skPlace_mul N N N 0 (halfTwist c false) (halfTwist c false ^ n) (by omega)
        rfl rfl]

/-- The four letters of the clasp word on at least two bundles, with free intermediate sizes. -/
private theorem pairTarget_clasp (c N N₁ N₂ N₃ N₄ i₁ i₂ i₄ : ℕ)
    (hN : 2 * c ≤ N) (h₁ : N₁ = N + 2 * c) (h₂ : N₂ = N + 2 * c) (h₃ : N₃ = N + 2 * c)
    (h₄ : N = N₄) (hi₁ : i₁ = 2 * c) (hi₂ : c = i₂) (hi₄ : i₄ = 0) :
    skPlace N N₁ i₁ (cupThick c) * (skPlace N₁ N₂ i₂ (halfTwist c true) *
      (skPlace N₂ N₃ i₂ (halfTwist c true) * (skPlace N₃ N₄ i₄ (capThick c) *
        skPlace N₄ N 0 (1 : SkMat 0 0)))) = skPlace N N 0 (claspOp c) := by
  subst h₁ h₂ h₃ h₄ hi₁ hi₂ hi₄
  rw [skPlace_one N 0 0 (Nat.zero_le _), Matrix.mul_one, claspOp,
    skPlace_mul N (N + 2 * c) N 0 _ (skPlace (4 * c) (2 * c) 0 (capThick c))
      (by omega) (by omega) (by omega),
    skPlace_mul N (N + 2 * c) (N + 2 * c) 0 (skPlace (2 * c) (4 * c) (2 * c) (cupThick c))
      (skPlace (4 * c) (4 * c) c (halfTwist c true * halfTwist c true))
      (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_target N (N + 2 * c) (2 * c) (cupThick c)
      (by omega) (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_target (N + 2 * c) (N + 2 * c) c
      (halfTwist c true * halfTwist c true) (by omega) (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_target (N + 2 * c) N 0 (capThick c)
      (by omega) (by omega) (by omega) (by omega),
    skPlace_mul (N + 2 * c) (N + 2 * c) (N + 2 * c) c (halfTwist c true) (halfTwist c true)
      (by omega) (by omega) (by omega)]
  simp only [Matrix.mul_assoc]

/-- The thick operator of the clasp word on three bundles is the clasp on the first two. -/
private theorem morseOp_claspWord_target (c : ℕ) :
    morseOp c claspWord (3 * c) (3 * c) = skPlace (3 * c) (3 * c) 0 (claspOp c) := by
  simp only [claspWord, morseOp, morseLetterOp, morseKindOut, morseKindIn]
  exact pairTarget_clasp c (3 * c) _ _ _ _ _ _ _ (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The partial trace over the second of two bundles, with free sizes. -/
private theorem ptrTail_eq_cupThick_capThick_target (c N M : ℕ) (hN : N = c + c)
    (hM : M = c + 2 * c) (A : SkMat N N) :
    ptrTail c N A =
      skPlace c M c (cupThick c) * skPlace M M 0 A * skPlace M c c (capThick c) := by
  subst hN hM
  exact ptrTail_eq_cupThick_capThick c c A

/-- The doubled long closure on three bundles: the long-knot operator of `T(r, s)` at
thickness `2c` on the first two. -/
private theorem morseOp_morseDouble_longClosure_target {r s : ℕ} (h : IsTorusPair r s)
    (c : ℕ) :
    morseOp c (morseDouble (morseLongClosure r (torusPairWord r s))) (3 * c) (3 * c) =
      skPlace (3 * c) (3 * c) 0 (longKnotOp (torusPairKnot r s h) (2 * c)) := by
  obtain ⟨hf, ho⟩ := morseFits_morseLongClosure_target r (torusPairWord r s) (by
    obtain ⟨hr, -⟩ := h; omega) (isOnStrands_torusPairWord r s)
  have e3 : 3 * c = 2 * c * 1 + c := by ring
  have hext := morseOp_add_right_target (2 * c) c 1 _ hf
  rw [ho] at hext
  have hK : morseOp (2 * c) (morseLongClosure r (torusPairWord r s)) (2 * c) (2 * c) =
      longKnotOp (torusPairKnot r s h) (2 * c) :=
    morseOp_morseLongClosure_eq_longKnotOp (torusPairKnot r s h) (2 * c)
  rw [e3, morseOp_morseDouble_add c c 1 _ _ hf, hext, Nat.mul_one, hK]

/-- The operator of the band-and-clasp target word. -/
theorem morseOp_pairTargetWord {r s : ℕ} (h : IsTorusPair r s) (c : ℕ) :
    morseOp c (pairTargetWord r s) c c =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwist c false ^ (2 * ((r - 1) * s)) * claspOp c)) := by
  obtain ⟨hf, ho⟩ := morseFits_morseLongClosure_target r (torusPairWord r s) (by
    obtain ⟨hr, -⟩ := h; omega) (isOnStrands_torusPairWord r s)
  have hw : pairTargetWord r s = [(MorseKind.cup, 1)] ++
      (morseDouble (morseLongClosure r (torusPairWord r s)) ++
        (List.replicate (2 * ((r - 1) * s)) (MorseKind.cross false, 0) ++
          (claspWord ++ [(MorseKind.cap, 1)]))) := by
    simp only [pairTargetWord, List.append_assoc]
  have h₁ : 3 * c = morseThickOut c c [(MorseKind.cup, 1)] := by
    simp only [morseThickOut, morseKindOut, morseKindIn]
    omega
  have h₂ : 3 * c = morseThickOut c (3 * c)
      (morseDouble (morseLongClosure r (torusPairWord r s))) := by
    rw [morseThickOut_morseDouble_target, show 3 * c = 2 * c * 1 + c by ring,
      morseThickOut_add_target _ _ _ _ hf, ho]
  have h₅ : 3 * c = morseThickOut c (3 * c) claspWord := by
    simp only [claspWord, morseThickOut, morseKindOut, morseKindIn]
    omega
  have hcup : morseOp c [(MorseKind.cup, 1)] c (3 * c) =
      skPlace c (3 * c) (c * 1) (cupThick c) := by
    rw [morseOp_cons_cup_target c 1 [] c (3 * c) (3 * c) (by omega), morseOp_nil,
      Matrix.mul_one]
  have hcap : morseOp c [(MorseKind.cap, 1)] (3 * c) c =
      skPlace (3 * c) c (c * 1) (capThick c) := by
    rw [morseOp_cons_cap_target c 1 [] (3 * c) c c (by omega), morseOp_nil, Matrix.mul_one]
  rw [hw, morseOp_append_target c _ _ c (3 * c) c h₁,
    morseOp_append_target c _ _ (3 * c) (3 * c) c h₂,
    morseOp_append_target c _ _ (3 * c) (3 * c) c
      (morseThickOut_replicate_cross_target c _ 0 false _).symm,
    morseOp_append_target c _ _ (3 * c) (3 * c) c h₅,
    hcup, morseOp_morseDouble_longClosure_target h c,
    morseOp_replicate_cross_target c _ (3 * c) (by omega),
    morseOp_claspWord_target, hcap,
    ptrTail_eq_cupThick_capThick_target c (2 * c) (3 * c) (by omega) (by omega),
    skPlace_mul (3 * c) (3 * c) (3 * c) 0 (longKnotOp (torusPairKnot r s h) (2 * c)) _
      (by omega) (by omega) (by omega),
    skPlace_mul (3 * c) (3 * c) (3 * c) 0 (halfTwist c false ^ (2 * ((r - 1) * s)))
      (claspOp c) (by omega) (by omega) (by omega), Nat.mul_one]
  simp only [Matrix.mul_assoc]

end AJConjecture
