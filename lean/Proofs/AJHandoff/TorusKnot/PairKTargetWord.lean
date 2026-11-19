import Mathlib
import AJHandoff.TorusKnot.PairKBlocks
import AJConjecture.SkeinMorseBraid
import AJConjecture.SkeinUFormClasp
import AJFamily.Skein.TorusTargetWord
import AJConjecture.SkeinThickGenInv

/-!
# The band-and-clasp target word over `T(r, s)`

`morseDouble w` is the blackboard double of a Morse word (every strand replaced by two parallel
strands): a cup or cap at `i` becomes a nest of two at `2i`, a crossing at `i` the four crossings
of `cable 2 [(i, s)]`. Its thick operator at thickness `c` is the operator of `w` at thickness
`2c` (`morseOp_morseDouble`): this is the generic form of the word-specific step of
`AJFamily.Skein.TorusTargetOp`.

`pairTargetWord r s` is the satellite diagram of `Wh⁻₀(T(r, s))` cut open on one edge of the
band: the first cup, the blackboard double of the long closure of `(σ_0 ⋯ σ_(r-2))^s`,
`2(r - 1)s` negative crossings of the two edges at the base point (they cancel the `(r - 1)s`
positive full twists that the blackboard double of a diagram of writhe `(r - 1)s` puts into the
band), the clasp, the last cap. For `r = 2` it is the library's `torusTargetWord k`.
-/

namespace AJConjecture

/-- The blackboard double of one Morse letter. -/
def morseDoubleLetter : MorseLetter → MorseWord
  | (.cup, i) => [(.cup, 2 * i), (.cup, 2 * i + 1)]
  | (.cap, i) => [(.cap, 2 * i + 1), (.cap, 2 * i)]
  | (.cross s, i) => morseOfBraid (cable 2 [(i, s)])

/-- The blackboard double of a Morse word. -/
def morseDouble (w : MorseWord) : MorseWord := w.flatMap morseDoubleLetter

/-- The band-and-clasp diagram of `Wh⁻₀(T(r, s))` cut open on one edge of the band. -/
def pairTargetWord (r s : ℕ) : MorseWord :=
  [(.cup, 1)] ++ morseDouble (morseLongClosure r (torusPairWord r s)) ++
    List.replicate (2 * ((r - 1) * s)) (.cross false, 0) ++ claspWord ++ [(.cap, 1)]

/-- Doubling a braid word as a Morse word is cabling it by `2`. -/
theorem morseDouble_morseOfBraid (w : BraidWord) :
    morseDouble (morseOfBraid w) = morseOfBraid (cable 2 w) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    change morseDoubleLetter (MorseKind.cross g.2, g.1) ++ morseDouble (morseOfBraid w) =
      morseOfBraid (cableGen 2 g ++ cable 2 w)
    rw [ih]
    simp only [morseDoubleLetter, morseOfBraid, cable, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append]

/-- The operator of a word that begins with a cup. -/
private theorem morseOp_cons_cup_double (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N + 2 * c) :
    morseOp c ((MorseKind.cup, i) :: u) N N' =
      skPlace N M (c * i) (cupThick c) * morseOp c u M N' := by
  have e : N + c * 2 - c * 0 = M := by rw [hM]; ring_nf; omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a cap. -/
private theorem morseOp_cons_cap_double (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hN : N = M + 2 * c) :
    morseOp c ((MorseKind.cap, i) :: u) N N' =
      skPlace N M (c * i) (capThick c) * morseOp c u M N' := by
  have e : N + c * 0 - c * 2 = M := by rw [hN]; ring_nf; omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a crossing. -/
private theorem morseOp_cons_cross_double (c i : ℕ) (s : Bool) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N) :
    morseOp c ((MorseKind.cross s, i) :: u) N N' =
      skPlace N M (c * i) (halfTwist c s) * morseOp c u M N' := by
  have e : N + c * 2 - c * 2 = M := by omega
  rw [← e]
  rfl

/-- The operator of a braid word followed by another word, on at least `c * m` tensor factors. -/
private theorem morseOp_morseOfBraid_append_double (c m : ℕ) (w : BraidWord)
    (hw : IsOnStrands m w) (rest : MorseWord) (N N' : ℕ) (hN : c * m ≤ N) :
    morseOp c (morseOfBraid w ++ rest) N N' =
      braidMatrix N (cable c w) * morseOp c rest N N' := by
  induction w with
  | nil =>
    rw [show morseOfBraid [] = [] from rfl, List.nil_append, show cable c [] = [] from rfl,
      braidMatrix_nil, Matrix.one_mul]
  | cons g w ih =>
    have hg : g.1 + 1 < m := hw g List.mem_cons_self
    have hg' : c * (g.1 + 2) ≤ c * m := Nat.mul_le_mul_left c hg
    rw [Nat.mul_add] at hg'
    have hcable : cable c (g :: w) = cableGen c g ++ cable c w := by
      rw [cable, List.flatMap_cons, cable]
    rw [show morseOfBraid (g :: w) = (MorseKind.cross g.2, g.1) :: morseOfBraid w from rfl,
      List.cons_append, morseOp_cons_cross_double c g.1 g.2 _ N N N' rfl,
      ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg'), hcable, braidMatrix_append,
      cableGen_eq_thickCross,
      skPlace_halfTwist_eq_braidMatrix c N (c * g.1) g.2 (by omega), Matrix.mul_assoc]

/-- A positive crossing of two bundles of `2c` strands is four crossings of bundles of `c`
strands. -/
private theorem braidMatrix_thickGen_double (N c A o₀ o₁ o₂ : ℕ)
    (hA : A = c + c) (h₁ : o₁ = o₀ + c) (h₂ : o₂ = o₀ + c + c) :
    braidMatrix N (thickGen A A o₀ true) =
      braidMatrix N (thickGen c c o₁ true) * (braidMatrix N (thickGen c c o₂ true) *
        (braidMatrix N (thickGen c c o₀ true) * braidMatrix N (thickGen c c o₁ true))) := by
  subst hA h₁ h₂
  rw [thickGen_add_left c c (c + c) o₀, braidMatrix_append,
    braidMatrix_thickGen_add_right N c c c (o₀ + c), braidMatrix_thickGen_add_right N c c c o₀,
    Matrix.mul_assoc]

/-- The double of a positive generator. -/
private theorem cable_two_single_true (i : ℕ) :
    cable 2 [(i, true)] =
      [(2 * i + 1, true), (2 * i + 2, true), (2 * i, true), (2 * i + 1, true)] := by
  simp only [cable, cableGen, List.flatMap_cons, List.flatMap_nil, List.append_nil, ite_true]
  simp [List.range_succ]

/-- The double of a negative generator. -/
private theorem cable_two_single_false (i : ℕ) :
    cable 2 [(i, false)] =
      [(2 * i + 1, false), (2 * i, false), (2 * i + 2, false), (2 * i + 1, false)] := by
  simp only [cable, cableGen, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [List.range_succ]

/-- The matrix of the `c`-cable of a braid word, letter by letter. -/
private theorem braidMatrix_cable_cons (N c : ℕ) (g : ℕ × Bool) (w : BraidWord) :
    braidMatrix N (cable c (g :: w)) =
      braidMatrix N (thickCross c c (c * g.1) g.2) * braidMatrix N (cable c w) := by
  rw [cable, List.flatMap_cons, braidMatrix_append, cableGen_eq_thickCross, ← cable]

/-- The `c`-cable of the double of a generator has the matrix of its `2c`-cable. -/
private theorem braidMatrix_cable_cable_two_single (N c i : ℕ) (s : Bool) :
    braidMatrix N (cable c (cable 2 [(i, s)])) =
      braidMatrix N (thickCross (2 * c) (2 * c) (2 * c * i) s) := by
  have hP := braidMatrix_thickGen_double N c (2 * c) (2 * c * i) (c * (2 * i + 1))
    (c * (2 * i + 2)) (by ring) (by ring) (by ring)
  have hnil : braidMatrix N (cable c []) = 1 := braidMatrix_nil N
  cases s with
  | true =>
    rw [cable_two_single_true]
    simp only [braidMatrix_cable_cons, hnil, Matrix.mul_one]
    rw [show thickCross (2 * c) (2 * c) (2 * c * i) true = thickGen (2 * c) (2 * c) (2 * c * i) true
      from rfl, hP, show 2 * c * i = c * (2 * i) by ring]
    rfl
  | false =>
    rw [cable_two_single_false]
    simp only [braidMatrix_cable_cons, hnil, Matrix.mul_one]
    rw [show thickCross (2 * c) (2 * c) (2 * c * i) false =
      thickGen (2 * c) (2 * c) (2 * c * i) false from rfl]
    have hcancel : ∀ (x : ℕ) (X : SkMat N N), braidMatrix N (thickGen c c x true) *
        (braidMatrix N (thickCross c c x false) * X) = X := by
      intro x X
      rw [← Matrix.mul_assoc, show thickCross c c x false = thickGen c c x false from rfl,
        braidMatrix_thickGen_mul_inv, Matrix.one_mul]
    set L := braidMatrix N (thickCross c c (c * (2 * i + 1)) false) *
      (braidMatrix N (thickCross c c (c * (2 * i)) false) *
        (braidMatrix N (thickCross c c (c * (2 * i + 2)) false) *
          braidMatrix N (thickCross c c (c * (2 * i + 1)) false))) with hLdef
    have hL : braidMatrix N (thickGen (2 * c) (2 * c) (2 * c * i) true) * L = 1 := by
      rw [hP, show 2 * c * i = c * (2 * i) by ring]
      simp only [Matrix.mul_assoc]
      rw [hLdef, hcancel, hcancel, hcancel]
      rw [show thickCross c c (c * (2 * i + 1)) false = thickGen c c (c * (2 * i + 1)) false
        from rfl, braidMatrix_thickGen_mul_inv]
    have hL' := mul_eq_one_comm.mp hL
    calc L = L * (braidMatrix N (thickGen (2 * c) (2 * c) (2 * c * i) true) *
          braidMatrix N (thickGen (2 * c) (2 * c) (2 * c * i) false)) := by
          rw [braidMatrix_thickGen_mul_inv, Matrix.mul_one]
      _ = braidMatrix N (thickGen (2 * c) (2 * c) (2 * c * i) false) := by
          rw [← Matrix.mul_assoc, hL', Matrix.one_mul]

/-- The double of a generator acts on the strands up to `2i + 3`. -/
private theorem isOnStrands_cable_two_single (i : ℕ) (s : Bool) :
    IsOnStrands (2 * i + 4) (cable 2 [(i, s)]) := by
  intro g hg
  cases s
  · rw [cable_two_single_false] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · rw [cable_two_single_true] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- The doubling identity with `e` extra tensor factors on the right. -/
private theorem morseOp_morseDouble_aux (c e n N' : ℕ) (w : MorseWord)
    (hw : morseFits n w = true) :
    morseOp c (morseDouble w) (2 * c * n + e) N' = morseOp (2 * c) w (2 * c * n + e) N' := by
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨k, i⟩ := l
    simp only [morseFits, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hi, hw⟩ := hw
    cases k with
    | cup =>
      simp only [morseKindIn, Nat.add_zero] at hi
      have hw' : morseFits (n + 2) w = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hw
      change morseOp c ((MorseKind.cup, 2 * i) :: (MorseKind.cup, 2 * i + 1) :: morseDouble w)
        (2 * c * n + e) N' = morseOp (2 * c) ((MorseKind.cup, i) :: w) (2 * c * n + e) N'
      rw [morseOp_cons_cup_double c (2 * i) _ _ (2 * c * n + e + 2 * c) _ rfl,
        morseOp_cons_cup_double c (2 * i + 1) _ _ (2 * c * (n + 2) + e) _ (by ring),
        morseOp_cons_cup_double (2 * c) i _ _ (2 * c * (n + 2) + e) _ (by ring), ih (n + 2) hw',
        ← Matrix.mul_assoc,
        skPlace_cupThick_mul c c (2 * c) (2 * c * n + e) (2 * c * n + e + 2 * c)
          (2 * c * (n + 2) + e) (c * (2 * i)) (c * (2 * i + 1)) (by ring) rfl (by ring)
          (by ring) (by nlinarith),
        show c * (2 * i) = 2 * c * i by ring]
    | cap =>
      simp only [morseKindIn] at hi
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      have hw' : morseFits n w = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hw
      change morseOp c ((MorseKind.cap, 2 * i + 1) :: (MorseKind.cap, 2 * i) :: morseDouble w)
        (2 * c * (n + 2) + e) N' =
          morseOp (2 * c) ((MorseKind.cap, i) :: w) (2 * c * (n + 2) + e) N'
      rw [morseOp_cons_cap_double c (2 * i + 1) _ _ (2 * c * n + e + 2 * c) _ (by ring),
        morseOp_cons_cap_double c (2 * i) _ _ (2 * c * n + e) _ rfl,
        morseOp_cons_cap_double (2 * c) i _ _ (2 * c * n + e) _ (by ring), ih n hw',
        ← Matrix.mul_assoc,
        skPlace_capThick_mul c c (2 * c) (2 * c * n + e) (2 * c * n + e + 2 * c)
          (2 * c * (n + 2) + e) (c * (2 * i)) (c * (2 * i + 1)) (by ring) rfl (by ring)
          (by ring) (by nlinarith),
        show c * (2 * i) = 2 * c * i by ring]
    | cross s =>
      simp only [morseKindIn] at hi
      have hw' : morseFits n w = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hw
      change morseOp c (morseOfBraid (cable 2 [(i, s)]) ++ morseDouble w) (2 * c * n + e) N' =
        morseOp (2 * c) ((MorseKind.cross s, i) :: w) (2 * c * n + e) N'
      rw [morseOp_morseOfBraid_append_double c (2 * i + 4) _ (isOnStrands_cable_two_single i s)
          _ _ _ (by nlinarith),
        morseOp_cons_cross_double (2 * c) i s _ _ _ _ rfl, ih n hw',
        braidMatrix_cable_cable_two_single,
        skPlace_halfTwist_eq_braidMatrix (2 * c) (2 * c * n + e) (2 * c * i) s (by nlinarith)]

/-- The thick operator of the double of a word at thickness `c` is the thick operator of the
word at thickness `2c` (a nest of `2c` cups is two nests of `c` cups, a crossing of two bundles
of `2c` strands is four crossings of bundles of `c` strands). -/
theorem morseOp_morseDouble (c n N' : ℕ) (w : MorseWord) (hw : morseFits n w = true) :
    morseOp c (morseDouble w) (2 * c * n) N' = morseOp (2 * c) w (2 * c * n) N' :=
  morseOp_morseDouble_aux c 0 n N' w hw

/-- For `r = 2` the torus braid is the library's `σ_0^(2k+1)`. -/
private theorem torusPairWord_two (k : ℕ) : torusPairWord 2 (2 * k + 1) = torusWord k := by
  simp only [torusPairWord, torusWord, show 2 - 1 = 1 from rfl, List.range_one, List.map_singleton]
  induction 2 * k + 1 with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_succ]; rfl

/-- For `r = 2`, `s = 2k + 1` the target word is the library's `torusTargetWord k`. -/
theorem pairTargetWord_two (k : ℕ) : pairTargetWord 2 (2 * k + 1) = torusTargetWord k := by
  have hc : 2 * ((2 - 1) * (2 * k + 1)) = 2 * (2 * k + 1) := by omega
  rw [pairTargetWord, torusTargetWord, morseLongClosure, torusPairWord_two, hc]
  simp only [show 2 - 1 = 1 from rfl, List.range_one, List.map_singleton, List.reverse_singleton,
    morseDouble, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← morseDouble, morseDouble_morseOfBraid]
  simp only [morseDoubleLetter, List.append_assoc, List.cons_append,
    List.nil_append]

/-- The doubling identity `AJConjecture.morseOp_morseDouble` with `e` extra tensor factors on
the right of the word. -/
theorem morseOp_morseDouble_add (c e n N' : ℕ) (w : MorseWord) (hw : morseFits n w = true) :
    morseOp c (morseDouble w) (2 * c * n + e) N' = morseOp (2 * c) w (2 * c * n + e) N' :=
  morseOp_morseDouble_aux c e n N' w hw

end AJConjecture
