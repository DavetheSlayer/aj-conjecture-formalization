import Mathlib
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinLongKnot
import AJConjecture.SkeinMorseWord
import AJConjecture.SkeinProfileBasic
import AJConjecture.SkeinPtrTailCyclic
import AJConjecture.SkeinThickCableBasic
import AJConjecture.SkeinThickCupAdd

/-!
# Braids and long closures as Morse words

A braid word is a Morse word of crossings, and its thick operator is the matrix of its cable.
The long closure of a braid on `m` strands — cups at the positions `1, …, m - 1`, the braid, caps
at the positions `m - 1, …, 1` — is the diagram of the closed braid cut open in the first column,
a tangle from one strand to one strand; its thick operator is the partial trace of the cabled
braid over all bundles but the first, that is, the long knot operator.

Proofs: `morseOp_morseOfBraid` by induction on the word with
`AJConjecture.braidMatrix_map_add_eq_skPlace` (`halfTwist c s` is the matrix of
`cableGen c (0, s)` and `cableGen c (i, s)` is its shift by `c * i`). `morseOp_morseLongClosure`
is `AJConjecture.ptrTail_eq_cupThick_capThick` with `k = c`, `r = c * (m - 1)`, after writing
the thick cup of `c * (m - 1)` strands as `m - 1` nested thick cups of `c` strands
(`AJConjecture.cupThick_succ`, `AJConjecture.cupThick_succ_inner`) and the same for the caps.
-/

namespace AJConjecture

/-- A braid word as a Morse word. -/
def morseOfBraid (w : BraidWord) : MorseWord :=
  w.map fun g ↦ (MorseKind.cross g.2, g.1)

/-- The closed braid on `m` strands cut open in the first column: cups, the braid, caps. -/
def morseLongClosure (m : ℕ) (w : BraidWord) : MorseWord :=
  ((List.range (m - 1)).map fun j ↦ (MorseKind.cup, j + 1)) ++ morseOfBraid w ++
    ((List.range (m - 1)).reverse.map fun j ↦ (MorseKind.cap, j + 1))

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem mem_thickCross_morseBraid {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
    (hg : g ∈ thickCross a b off s) : g.1 + 2 ≤ off + a + b := by
  cases s
  · simp only [thickCross, thickGen, Bool.false_eq_true, ite_false, List.mem_flatMap,
      List.mem_reverse, List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    dsimp only
    omega
  · simp only [thickCross, thickGen, ite_true, List.mem_flatMap, List.mem_reverse,
      List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    dsimp only
    omega

/-- The half twist placed at the offset `d` is the matrix of the thick crossing at `d`. -/
theorem skPlace_halfTwist_eq_braidMatrix (c N d : ℕ) (s : Bool)
    (h : d + 2 * c ≤ N) :
    skPlace N N d (halfTwist c s) = braidMatrix N (thickCross c c d s) := by
  have hw : IsOnStrands (2 * c) (thickCross c c 0 s) := fun g hg ↦ by
    have := mem_thickCross_morseBraid hg
    omega
  have e : halfTwist c s = braidMatrix (2 * c) (thickCross c c 0 s) := by
    rw [halfTwist, cableGen_eq_thickCross]
    rfl
  have e' := thickCross_add_off c c 0 d s
  rw [Nat.zero_add] at e'
  rw [e, ← braidMatrix_map_add_eq_skPlace (2 * c) N d _ hw h, e']

/-- The cable of a braid word on `m` strands is a braid word on `c * m` strands. -/
private theorem isOnStrands_cable_morseBraid (c m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) :
    IsOnStrands (c * m) (cable c w) := by
  intro g hg
  rw [cable, List.mem_flatMap] at hg
  obtain ⟨g₀, hg₀, hg⟩ := hg
  rw [cableGen_eq_thickCross] at hg
  have h₁ := mem_thickCross_morseBraid hg
  have h₂ : c * (g₀.1 + 2) ≤ c * m := Nat.mul_le_mul_left c (hw g₀ hg₀)
  rw [Nat.mul_add] at h₂
  omega

/-- The operator of the empty word is the identity. -/
private theorem morseOp_nil_morseBraid (c N : ℕ) : morseOp c [] N N = 1 :=
  skPlace_one N 0 0 (Nat.zero_le N)

/-- The operator of a word that begins with a cup. -/
private theorem morseOp_cons_cup_morseBraid (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N + 2 * c) :
    morseOp c ((MorseKind.cup, i) :: u) N N' =
      skPlace N M (c * i) (cupThick c) * morseOp c u M N' := by
  have e : N + c * 2 - c * 0 = M := by omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a cap. -/
private theorem morseOp_cons_cap_morseBraid (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hN : N = M + 2 * c) :
    morseOp c ((MorseKind.cap, i) :: u) N N' =
      skPlace N M (c * i) (capThick c) * morseOp c u M N' := by
  have e : N + c * 0 - c * 2 = M := by omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a crossing. -/
private theorem morseOp_cons_cross_morseBraid (c i : ℕ) (s : Bool) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N) :
    morseOp c ((MorseKind.cross s, i) :: u) N N' =
      skPlace N M (c * i) (halfTwist c s) * morseOp c u M N' := by
  have e : N + c * 2 - c * 2 = M := by omega
  rw [← e]
  rfl

/-- The thick cup on no strands, placed anywhere, is the identity. -/
private theorem skPlace_cupThick_zero_morseBraid (c r : ℕ) (hr : r = 0) :
    skPlace c c c (cupThick r) = 1 := by
  subst hr
  have h : cupThick 0 = (1 : SkMat 0 0) := by
    ext a b
    have hab : a = b := Subsingleton.elim (α := Fin 0 → Bool) a b
    simp only [cupThick, Matrix.of_apply, Finset.univ_eq_empty, Finset.prod_empty,
      Matrix.one_apply, hab, ↓reduceIte]
  exact (congrArg (fun A : SkMat 0 0 ↦ skPlace c c c A) h).trans
    (skPlace_one c c 0 (Nat.le_refl c))

/-- The thick cap on no strands, placed anywhere, is the identity. -/
private theorem skPlace_capThick_zero_morseBraid (c r : ℕ) (hr : r = 0) :
    skPlace c c c (capThick r) = 1 := by
  subst hr
  have h : capThick 0 = (1 : SkMat 0 0) := by
    ext a b
    have hab : a = b := Subsingleton.elim (α := Fin 0 → Bool) a b
    simp only [capThick, Matrix.of_apply, Finset.univ_eq_empty, Finset.prod_empty,
      Matrix.one_apply, hab, ↓reduceIte]
  exact (congrArg (fun A : SkMat 0 0 ↦ skPlace c c c A) h).trans
    (skPlace_one c c 0 (Nat.le_refl c))

/-- A nest of `r` cups followed by `c` cups inside it is a nest of `r + c` cups. -/
theorem skPlace_cupThick_mul (c r R N M M' i j : ℕ) (hR : R = r + c)
    (hM : M = N + 2 * r) (hM' : M' = M + 2 * c) (hj : j = i + r) (hi : i ≤ N) :
    skPlace N M i (cupThick r) * skPlace M M' j (cupThick c) = skPlace N M' i (cupThick R) := by
  subst hR hM hM' hj
  rw [cupThick_add r c, skPlace_mul N (N + 2 * r) (N + 2 * r + 2 * c) i (cupThick r) _
    (by omega) (by omega) (by omega),
    skPlace_skPlace _ _ i r (cupThick c) (by omega) (by omega) (by omega) (by omega)]

/-- The `c` inner caps of a nest followed by the `r` outer caps are a nest of `r + c` caps. -/
theorem skPlace_capThick_mul (c r R N M M' i j : ℕ) (hR : R = r + c)
    (hM : M = N + 2 * r) (hM' : M' = M + 2 * c) (hj : j = i + r) (hi : i ≤ N) :
    skPlace M' M j (capThick c) * skPlace M N i (capThick r) = skPlace M' N i (capThick R) := by
  subst hR hM hM' hj
  rw [capThick_add r c, skPlace_mul (N + 2 * r + 2 * c) (N + 2 * r) N i _ (capThick r)
    (by omega) (by omega) (by omega),
    skPlace_skPlace _ _ i r (capThick c) (by omega) (by omega) (by omega) (by omega)]

/-- The operator of a braid word followed by another word, on at least `c * m` tensor factors. -/
private theorem morseOp_morseOfBraid_append_morseBraid (c m : ℕ) (w : BraidWord)
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
      List.cons_append, morseOp_cons_cross_morseBraid c g.1 g.2 _ N N N' rfl,
      ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem g hg'), hcable, braidMatrix_append,
      cableGen_eq_thickCross,
      skPlace_halfTwist_eq_braidMatrix c N (c * g.1) g.2 (by omega), Matrix.mul_assoc]

/-- The cups of the long closure are a thick cup of `c * p` strands on the right of the first
bundle. -/
private theorem morseOp_cups_append_morseBraid (c p : ℕ) :
    ∀ (rest : MorseWord) (M N' : ℕ), M = c + 2 * (c * p) →
      morseOp c (((List.range p).map fun j ↦ (MorseKind.cup, j + 1)) ++ rest) c N' =
        skPlace c M c (cupThick (c * p)) * morseOp c rest M N' := by
  induction p with
  | zero =>
    intro rest M N' hM
    have hM' : c = M := by omega
    subst hM'
    rw [List.range_zero, List.map_nil, List.nil_append,
      skPlace_cupThick_zero_morseBraid c (c * 0) rfl, Matrix.one_mul]
  | succ p ih =>
    intro rest M N' hM
    have hmul : c * (p + 1) = c * p + c := Nat.mul_succ c p
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc,
      List.singleton_append, ih _ (c + 2 * (c * p)) N' rfl,
      morseOp_cons_cup_morseBraid c (p + 1) rest (c + 2 * (c * p)) M N' (by omega),
      ← Matrix.mul_assoc,
      skPlace_cupThick_mul c (c * p) (c * (p + 1)) c (c + 2 * (c * p)) M c
        (c * (p + 1)) hmul rfl (by omega) (by omega) le_rfl]

/-- The caps of the long closure are a thick cap of `c * p` strands on the right of the first
bundle. -/
private theorem morseOp_caps_morseBraid (c p : ℕ) :
    ∀ N : ℕ, N = c + 2 * (c * p) →
      morseOp c ((List.range p).reverse.map fun j ↦ (MorseKind.cap, j + 1)) N c =
        skPlace N c c (capThick (c * p)) := by
  induction p with
  | zero =>
    intro N hN
    have hN' : c = N := by omega
    subst hN'
    rw [List.range_zero, List.reverse_nil, List.map_nil, morseOp_nil_morseBraid,
      skPlace_capThick_zero_morseBraid c (c * 0) rfl]
  | succ p ih =>
    intro N hN
    have hmul : c * (p + 1) = c * p + c := Nat.mul_succ c p
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, morseOp_cons_cap_morseBraid c (p + 1) _ N (c + 2 * (c * p)) c (by omega),
      ih _ rfl,
      skPlace_capThick_mul c (c * p) (c * (p + 1)) c (c + 2 * (c * p)) N c
        (c * (p + 1)) hmul rfl (by omega) (by omega) le_rfl]

/-- The partial trace of a braid matrix over the last `r` factors, written with a thick cup and
a thick cap. -/
private theorem ptrTail_braidMatrix_eq_morseBraid (c r N : ℕ) (hN : N = c + r) (v : BraidWord)
    (hv : IsOnStrands N v) :
    ptrTail c N (braidMatrix N v) =
      skPlace c (c + 2 * r) c (cupThick r) * (braidMatrix (c + 2 * r) v *
        skPlace (c + 2 * r) c c (capThick r)) := by
  subst hN
  have h := braidMatrix_map_add_eq_skPlace (c + r) (c + 2 * r) 0 v hv (by omega)
  have hmap : (v.map fun g ↦ (g.1 + 0, g.2)) = v := List.map_id v
  rw [hmap] at h
  rw [ptrTail_eq_cupThick_capThick c r, h, Matrix.mul_assoc]

/-- The thick operator of a braid word is the matrix of its cable. -/
theorem morseOp_morseOfBraid (c m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) :
    morseOp c (morseOfBraid w) (c * m) (c * m) = braidMatrix (c * m) (cable c w) := by
  have h := morseOp_morseOfBraid_append_morseBraid c m w hw [] (c * m) (c * m) le_rfl
  rw [List.append_nil, morseOp_nil_morseBraid, Matrix.mul_one] at h
  exact h

/-- The thick operator of the long closure of a braid is the partial trace of its cable over all
bundles but the first. -/
theorem morseOp_morseLongClosure (c m : ℕ) (w : BraidWord) (hm : 0 < m) (hw : IsOnStrands m w) :
    morseOp c (morseLongClosure m w) c c = ptrTail c (c * m) (braidMatrix (c * m) (cable c w)) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hmul : c * (p + 1) = c * p + c := Nat.mul_succ c p
  rw [morseLongClosure, Nat.add_sub_cancel, List.append_assoc,
    morseOp_cups_append_morseBraid c p _ (c + 2 * (c * p)) c rfl,
    morseOp_morseOfBraid_append_morseBraid c (p + 1) w hw _ _ c (by omega),
    morseOp_caps_morseBraid c p _ rfl,
    ptrTail_braidMatrix_eq_morseBraid c (c * p) (c * (p + 1)) (by omega) (cable c w)
      (isOnStrands_cable_morseBraid c (p + 1) w hw)]

/-- The thick operator of the long closure of a closed braid is its long knot operator. -/
theorem morseOp_morseLongClosure_eq_longKnotOp (K : BraidKnot) (c : ℕ) :
    morseOp c (morseLongClosure K.strands K.word) c c = longKnotOp K c := by
  rw [longKnotOp]
  exact morseOp_morseLongClosure c K.strands K.word K.strands_pos K.isOnStrands

end AJConjecture
