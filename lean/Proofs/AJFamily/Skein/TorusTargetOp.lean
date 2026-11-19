import Mathlib
import AJConjecture.SkeinMorseOpBasic
import AJConjecture.SkeinThickGenInv
import AJFamily.Skein.TorusTargetWord

/-!
# The operator of the target word

`morseOp_torusTargetWord`: the thick operator of `torusTargetWord k` at colour `c` is the partial
trace `ptrTail c (2c)` of `longKnotOp (torusKnot k) (2c)` followed by `2(2k+1)` negative half twists
and the clasp. The word-specific step is that the `c`-cable of the blackboard double of `σ_0^(2k+1)`
has the matrix of its `2c`-cable.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The operator of a concatenation, with a free intermediate size. -/
private theorem morseOp_append_torusTargetOp (c : ℕ) (u v : MorseWord) (N M N' : ℕ)
    (hM : M = morseThickOut c N u) :
    morseOp c (u ++ v) N N' = morseOp c u N M * morseOp c v M N' := by
  subst hM
  exact morseOp_append c u v N N'

/-- A braid word does not change the number of tensor factors. -/
private theorem morseThickOut_morseOfBraid_torusTargetOp (c : ℕ) (w : BraidWord) (N : ℕ) :
    morseThickOut c N (morseOfBraid w) = N := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    change morseThickOut c (N + c * 2 - c * 2) (morseOfBraid w) = N
    rw [Nat.add_sub_cancel, ih]

/-- Repeated crossings do not change the number of tensor factors. -/
private theorem morseThickOut_replicate_cross_torusTargetOp (c n i : ℕ) (s : Bool) (N : ℕ) :
    morseThickOut c N (List.replicate n (MorseKind.cross s, i)) = N := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change morseThickOut c (N + c * 2 - c * 2) (List.replicate n (MorseKind.cross s, i)) = N
    rw [Nat.add_sub_cancel, ih]

/-- A placement placed at the position `0`. -/
private theorem skPlace_zero_skPlace_torusTargetOp (n n' j : ℕ) {k l k' l' : ℕ}
    (A : SkMat k l) (hj : j + k ≤ k') (hkl : k' + l = l' + k) (h : k' ≤ n)
    (h' : n + l' = n' + k') :
    skPlace n n' 0 (skPlace k' l' j A) = skPlace n n' j A := by
  have e := skPlace_skPlace n n' 0 j A hj hkl (by omega) h'
  rwa [Nat.zero_add] at e

/-- The three closing cups, with free intermediate sizes: a cup of `c` strands and, inside it,
a nest of `2 * c` cups. -/
private theorem targetWord_cups (c N₁ N₂ N₃ i₁ i₂ i₃ : ℕ) (h₁ : N₁ = 3 * c)
    (h₂ : N₂ = 5 * c) (h₃ : N₃ = 7 * c) (hi₁ : i₁ = 1 * c) (hi₂ : i₂ = 2 * c)
    (hi₃ : i₃ = 3 * c) :
    skPlace c N₁ i₁ (cupThick c) * (skPlace N₁ N₂ i₂ (cupThick c) *
      (skPlace N₂ N₃ i₃ (cupThick c) * skPlace N₃ (7 * c) 0 (1 : SkMat 0 0))) =
      skPlace c (3 * c) (1 * c) (cupThick c) *
        skPlace (3 * c) (7 * c) (2 * c) (cupThick (2 * c)) := by
  subst h₁ h₂ h₃ hi₁ hi₂ hi₃
  rw [skPlace_one (7 * c) 0 0 (Nat.zero_le _), Matrix.mul_one,
    skPlace_cupThick_mul c c (2 * c) (3 * c) (5 * c) (7 * c) (2 * c) (3 * c)
      (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- The thick operator of the three closing cups. -/
private theorem morseOp_cups_torusTargetOp (c : ℕ) :
    morseOp c [(MorseKind.cup, 1), (MorseKind.cup, 2), (MorseKind.cup, 3)] c (7 * c) =
      skPlace c (3 * c) (1 * c) (cupThick c) *
        skPlace (3 * c) (7 * c) (2 * c) (cupThick (2 * c)) := by
  simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
  exact targetWord_cups c _ _ _ _ _ _ (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

/-- The two caps that close the second copy of the band, with free intermediate sizes. -/
private theorem targetWord_caps (c N₁ N₂ i₁ i₂ : ℕ) (h₁ : N₁ = 5 * c)
    (h₂ : N₂ = 3 * c) (hi₁ : i₁ = 3 * c) (hi₂ : i₂ = 2 * c) :
    skPlace (7 * c) N₁ i₁ (capThick c) * (skPlace N₁ N₂ i₂ (capThick c) *
      skPlace N₂ (3 * c) 0 (1 : SkMat 0 0)) =
      skPlace (7 * c) (3 * c) (2 * c) (capThick (2 * c)) := by
  subst h₁ h₂ hi₁ hi₂
  rw [skPlace_one (3 * c) 0 0 (Nat.zero_le _), Matrix.mul_one,
    skPlace_capThick_mul c c (2 * c) (3 * c) (5 * c) (7 * c) (2 * c) (3 * c)
      (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- The thick operator of the two caps that close the second copy of the band. -/
private theorem morseOp_caps_torusTargetOp (c : ℕ) :
    morseOp c [(MorseKind.cap, 3), (MorseKind.cap, 2)] (7 * c) (3 * c) =
      skPlace (7 * c) (3 * c) (2 * c) (capThick (2 * c)) := by
  simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
  exact targetWord_caps c _ _ _ _ (by omega) (by omega) (by omega) (by omega)

/-- The last cap, with a free intermediate size. -/
private theorem targetWord_lastCap (c N₁ i : ℕ) (h₁ : c = N₁)
    (hi : i = 1 * c) :
    skPlace (3 * c) N₁ i (capThick c) * skPlace N₁ c 0 (1 : SkMat 0 0) =
      skPlace (3 * c) c (1 * c) (capThick c) := by
  subst h₁ hi
  rw [skPlace_one c 0 0 (Nat.zero_le _), Matrix.mul_one]

/-- The thick operator of the last cap. -/
private theorem morseOp_lastCap_torusTargetOp (c : ℕ) :
    morseOp c [(MorseKind.cap, 1)] (3 * c) c = skPlace (3 * c) c (1 * c) (capThick c) := by
  simp only [morseOp, morseLetterOp, morseKindOut, morseKindIn]
  exact targetWord_lastCap c _ _ (by omega) (by omega)

/-- The operator of a word that begins with a crossing, with a free offset. -/
private theorem morseOp_cons_cross_torusTargetOp (c i j : ℕ) (s : Bool) (u : MorseWord)
    (N M N' : ℕ) (hM : M = N) (hj : j = c * i) :
    morseOp c ((MorseKind.cross s, i) :: u) N N' =
      skPlace N M j (halfTwist c s) * morseOp c u M N' := by
  subst hj
  have e : N + c * 2 - c * 2 = M := by omega
  rw [← e]
  rfl

/-- The thick operator of `n` negative crossings of the first two bundles. -/
private theorem morseOp_replicate_cross_torusTargetOp (c n N : ℕ) (hN : 2 * c ≤ N) :
    morseOp c (List.replicate n (MorseKind.cross false, 0)) N N =
      skPlace N N 0 (halfTwist c false ^ n) := by
  induction n with
  | zero =>
    rw [List.replicate_zero, morseOp_nil, pow_zero, skPlace_one N 0 (2 * c) (by omega)]
  | succ n ih =>
    rw [List.replicate_succ, morseOp_cons_cross_torusTargetOp c 0 0 false _ N N N rfl rfl,
      ih,
      pow_succ', skPlace_mul N N N 0 (halfTwist c false) (halfTwist c false ^ n) (by omega)
        rfl rfl]

/-- The four letters of the clasp word on at least two bundles, with free intermediate sizes. -/
private theorem targetWord_clasp (c N N₁ N₂ N₃ N₄ i₁ i₂ i₄ : ℕ)
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
    skPlace_zero_skPlace_torusTargetOp N (N + 2 * c) (2 * c) (cupThick c)
      (by omega) (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_torusTargetOp (N + 2 * c) (N + 2 * c) c
      (halfTwist c true * halfTwist c true) (by omega) (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_torusTargetOp (N + 2 * c) N 0 (capThick c)
      (by omega) (by omega) (by omega) (by omega),
    skPlace_mul (N + 2 * c) (N + 2 * c) (N + 2 * c) c (halfTwist c true) (halfTwist c true)
      (by omega) (by omega) (by omega)]
  simp only [Matrix.mul_assoc]

/-- The thick operator of the clasp word on three bundles is the clasp on the first two. -/
private theorem morseOp_claspWord_torusTargetOp (c : ℕ) :
    morseOp c claspWord (3 * c) (3 * c) = skPlace (3 * c) (3 * c) 0 (claspOp c) := by
  simp only [claspWord, morseOp, morseLetterOp, morseKindOut, morseKindIn]
  exact targetWord_clasp c (3 * c) _ _ _ _ _ _ _ (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- A crossing of two bundles of `2 * c` strands is four crossings of bundles of `c` strands,
with free sizes. -/
private theorem braidMatrix_thickGen_double_torusTargetOp (N c A o₀ o₁ o₂ : ℕ)
    (hA : A = c + c) (h₁ : o₁ = o₀ + c) (h₂ : o₂ = o₀ + c + c) :
    braidMatrix N (thickGen A A o₀ true) =
      braidMatrix N (thickGen c c o₁ true) * (braidMatrix N (thickGen c c o₂ true) *
        (braidMatrix N (thickGen c c o₀ true) * braidMatrix N (thickGen c c o₁ true))) := by
  subst hA h₁ h₂
  rw [thickGen_add_left c c (c + c) o₀, braidMatrix_append,
    braidMatrix_thickGen_add_right N c c c (o₀ + c), braidMatrix_thickGen_add_right N c c c o₀,
    Matrix.mul_assoc]

/-- The cabled generator of the double of `σ_0`: the matrix of the `2 * c`-cable of `σ_0` is the
matrix of the `c`-cable of the `2`-cable of `σ_0`. -/
private theorem braidMatrix_cableGen_double_torusTargetOp (N c : ℕ) :
    braidMatrix N (cableGen (2 * c) (0, true)) =
      braidMatrix N (cableGen c (1, true)) * (braidMatrix N (cableGen c (2, true)) *
        (braidMatrix N (cableGen c (0, true)) * braidMatrix N (cableGen c (1, true)))) :=
  braidMatrix_thickGen_double_torusTargetOp N c (2 * c) (2 * c * 0) (c * 1) (c * 2)
    (by omega) (by omega) (by omega)

/-- The `2`-cable of the generator `σ_0`. -/
private theorem cableGen_two_zero_torusTargetOp :
    cableGen 2 (0, true) = [(1, true), (2, true), (0, true), (1, true)] := by
  decide

/-- The `c`-cable of the double of `σ_0^m` has the matrix of the `2 * c`-cable of `σ_0^m`. -/
private theorem braidMatrix_cable_cable_replicate_torusTargetOp (N c m : ℕ) :
    braidMatrix N (cable c (cable 2 (List.replicate m (0, true)))) =
      braidMatrix N (cable (2 * c) (List.replicate m (0, true))) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, cable, List.flatMap_cons, List.flatMap_append,
      cableGen_two_zero_torusTargetOp, List.flatMap_nil, List.append_nil,
      braidMatrix_append] at ih ⊢
    rw [ih, braidMatrix_cableGen_double_torusTargetOp N c]

/-- The cable of the torus braid is a braid word on two bundles. -/
private theorem isOnStrands_cable_torusWord_torusTargetOp (k a n : ℕ) (hn : n = 2 * a) :
    IsOnStrands n (cable a (torusWord k)) := by
  intro g hg
  simp only [cable, torusWord, List.mem_flatMap, List.mem_replicate] at hg
  obtain ⟨x, ⟨-, rfl⟩, hg⟩ := hg
  simp only [cableGen, ite_true, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  dsimp only
  omega

/-- The double of the torus braid is a braid word on seven strands. -/
private theorem isOnStrands_cable_two_torusWord_torusTargetOp (k : ℕ) :
    IsOnStrands 7 (cable 2 (torusWord k)) :=
  fun g hg ↦ by
    have := isOnStrands_cable_torusWord_torusTargetOp k 2 4 rfl g hg
    omega

/-- The thick operator of the double of the torus braid on seven bundles: the matrix of the
`2 * c`-cable of the torus braid on the first four. -/
private theorem morseOp_braid_torusTargetOp (k c N n : ℕ) (hN : N = c * 7)
    (hn : n = 2 * (2 * c)) :
    morseOp c (morseOfBraid (cable 2 (torusWord k))) N N =
      skPlace N N 0 (braidMatrix n (cable (2 * c) (torusWord k))) := by
  subst hN
  have h := braidMatrix_map_add_eq_skPlace n (c * 7) 0 _
    (isOnStrands_cable_torusWord_torusTargetOp k (2 * c) n hn) (by omega)
  have hmap : ((cable (2 * c) (torusWord k)).map fun g ↦ (g.1 + 0, g.2)) =
      cable (2 * c) (torusWord k) := List.map_id _
  rw [hmap] at h
  rw [morseOp_morseOfBraid c 7 _ (isOnStrands_cable_two_torusWord_torusTargetOp k), torusWord,
    braidMatrix_cable_cable_replicate_torusTargetOp, ← torusWord, h]

/-- The partial trace over the second of two bundles, written with a thick cup and a thick cap,
with free sizes. -/
private theorem ptrTail_eq_cupThick_capThick_torusTargetOp (c N M : ℕ) (hN : N = c + c)
    (hM : M = c + 2 * c) (A : SkMat N N) :
    ptrTail c N A =
      skPlace c M c (cupThick c) * skPlace M M 0 A * skPlace M c c (capThick c) := by
  subst hN hM
  exact ptrTail_eq_cupThick_capThick c c A

/-- A partial trace placed at the position `0`: the cups and the caps are placed after the
factors that are kept. -/
private theorem skPlace_zero_ptrTail_torusTargetOp (k r n N M : ℕ) (hk : k ≤ n)
    (hN : N = k + r) (hM : M = n + 2 * r) (A : SkMat N N) :
    skPlace n n 0 (ptrTail k N A) =
      skPlace n M k (cupThick r) * skPlace M M 0 A * skPlace M n k (capThick r) := by
  subst hN hM
  rw [ptrTail_eq_cupThick_capThick k r A,
    skPlace_mul n (n + 2 * r) n 0 _ (skPlace (k + 2 * r) k k (capThick r))
      (by omega) (by omega) (by omega),
    skPlace_mul n (n + 2 * r) (n + 2 * r) 0 (skPlace k (k + 2 * r) k (cupThick r))
      (skPlace (k + 2 * r) (k + 2 * r) 0 A) (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_torusTargetOp n (n + 2 * r) k (cupThick r)
      (by omega) (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_torusTargetOp (n + 2 * r) (n + 2 * r) 0 A
      (by omega) (by omega) (by omega) (by omega),
    skPlace_zero_skPlace_torusTargetOp (n + 2 * r) n k (capThick r)
      (by omega) (by omega) (by omega) (by omega)]

/-- The six pieces of the band-and-clasp word are the two nested partial traces. -/
private theorem targetWord_assemble (c n : ℕ) (hn : n = 2 * (2 * c))
    (B : SkMat n n) (X Y : SkMat (2 * c) (2 * c)) :
    skPlace c (3 * c) (1 * c) (cupThick c) * skPlace (3 * c) (7 * c) (2 * c) (cupThick (2 * c)) *
      (skPlace (7 * c) (7 * c) 0 B * (skPlace (7 * c) (3 * c) (2 * c) (capThick (2 * c)) *
        (skPlace (3 * c) (3 * c) 0 X * (skPlace (3 * c) (3 * c) 0 Y *
          skPlace (3 * c) c (1 * c) (capThick c))))) =
      ptrTail c (2 * c) (ptrTail (2 * c) n B * (X * Y)) := by
  rw [ptrTail_eq_cupThick_capThick_torusTargetOp c (2 * c) (3 * c) (by omega) (by omega) _,
    skPlace_mul (3 * c) (3 * c) (3 * c) 0 (ptrTail (2 * c) n B) (X * Y)
      (by omega) (by omega) (by omega),
    skPlace_mul (3 * c) (3 * c) (3 * c) 0 X Y (by omega) (by omega) (by omega),
    skPlace_zero_ptrTail_torusTargetOp (2 * c) (2 * c) (3 * c) n (7 * c) (by omega)
      (by omega) (by omega) B, Nat.one_mul]
  simp only [Matrix.mul_assoc]

/-- The thick operator of the band-and-clasp word of `Wh⁻₀(T(2, 2k+1))`. -/
theorem morseOp_torusTargetWord (k c : ℕ) :
    morseOp c (torusTargetWord k) c c =
      ptrTail c (2 * c)
        (longKnotOp (torusKnot k) (2 * c) * (halfTwist c false ^ (2 * (2 * k + 1)) * claspOp c)) := by
  have hΛ : longKnotOp (torusKnot k) (2 * c) =
      ptrTail (2 * c) (2 * c * 2) (braidMatrix (2 * c * 2) (cable (2 * c) (torusWord k))) := rfl
  have hw : torusTargetWord k =
      [(MorseKind.cup, 1), (MorseKind.cup, 2), (MorseKind.cup, 3)] ++
        (morseOfBraid (cable 2 (torusWord k)) ++ ([(MorseKind.cap, 3), (MorseKind.cap, 2)] ++
          (List.replicate (2 * (2 * k + 1)) (MorseKind.cross false, 0) ++
            (claspWord ++ [(MorseKind.cap, 1)])))) := by
    simp only [torusTargetWord, List.append_assoc]
  have h₁ : 7 * c = morseThickOut c c
      [(MorseKind.cup, 1), (MorseKind.cup, 2), (MorseKind.cup, 3)] := by
    simp only [morseThickOut, morseKindOut, morseKindIn]
    omega
  have h₃ : 3 * c = morseThickOut c (7 * c) [(MorseKind.cap, 3), (MorseKind.cap, 2)] := by
    simp only [morseThickOut, morseKindOut, morseKindIn]
    omega
  have h₅ : 3 * c = morseThickOut c (3 * c) claspWord := by
    simp only [claspWord, morseThickOut, morseKindOut, morseKindIn]
    omega
  rw [hΛ, hw, morseOp_append_torusTargetOp c _ _ c (7 * c) c h₁,
    morseOp_append_torusTargetOp c _ _ (7 * c) (7 * c) c
      (morseThickOut_morseOfBraid_torusTargetOp c _ _).symm,
    morseOp_append_torusTargetOp c _ _ (7 * c) (3 * c) c h₃,
    morseOp_append_torusTargetOp c _ _ (3 * c) (3 * c) c
      (morseThickOut_replicate_cross_torusTargetOp c _ 0 false _).symm,
    morseOp_append_torusTargetOp c _ _ (3 * c) (3 * c) c h₅,
    morseOp_cups_torusTargetOp, morseOp_braid_torusTargetOp k c (7 * c) (2 * c * 2)
      (by omega) (by omega), morseOp_caps_torusTargetOp,
    morseOp_replicate_cross_torusTargetOp c _ (3 * c) (by omega),
    morseOp_claspWord_torusTargetOp, morseOp_lastCap_torusTargetOp]
  exact targetWord_assemble c (2 * c * 2) (by omega) _ _ _

end AJConjecture
