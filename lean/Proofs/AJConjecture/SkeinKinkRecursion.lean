import Mathlib
import AJConjecture.SkeinCableNatural
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinHalfTwist
import AJConjecture.SkeinProfileBasic
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinPtrTailPlace
import AJConjecture.SkeinThickYangBaxter

/-!
# The kink of a bundle, one strand at a time

The ribbon identity `θ_{A ⊗ a} = c_{A,a} (θ_a ⊗ θ_A) c_{a,A}` for a bundle `A` of `c` strands and
a single strand `a`: the kink of `c + 1` strands is the kink `-t^{±3}` of the last strand, the
kink of the first `c` strands, and the full twist of the strand around the bundle.

Route (positive sign; the negative sign is the same computation with the inverse words). The
half twist of two bundles of `c + 1` strands is, by `AJConjecture.cableGen_eq_thickCross`,
`AJConjecture.thickGen_add_left` and `AJConjecture.braidMatrix_thickGen_add_right`,
`X(1,c)_c · σ_{2c} · X(c,c)_0 · X(c,1)_c`, where `X(x,y)_o` is the matrix of
`thickGen x y o true`. Only `σ_{2c}` touches the last strand; the other factors are placements
at `0` of matrices on `2c + 1` strands (`AJConjecture.braidMatrix_map_add_eq_skPlace`), so the
partial trace over the last strand is `-t³ · X(1,c)_c · X(c,c)_0 · X(c,1)_c`
(`AJConjecture.ptrTail_ptrTail`, `AJConjecture.ptrTail_skPlace_mul`,
`AJConjecture.ptrTail_mul_skPlace`, `AJConjecture.ptrTail_crossingF_last`). By the Yang–Baxter
relation for the bundles of `c`, `1`, `c` strands (`AJConjecture.braidMatrix_thickCross_yangBaxter`)
this product is `X(c,1)_0 · X(c,c)_1 · X(1,c)_0`; the outer factors act on the `c + 1` factors that
are kept, and the partial trace of the middle one is the kink of `c` strands placed at the
position `1` (`AJConjecture.ptrTail_skPlace_shift`).
-/

namespace AJConjecture

/-- The letters of a thick crossing act on the strands of its two bundles. -/
private theorem mem_thickCross_kinkRec {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
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

/-- A thick crossing of bundles inside the first `n` strands, shifted by `d`, is the placement at
`d` of its matrix on `n` strands. -/
private theorem braidMatrix_thickCross_add_eq_skPlace_kinkRec (n n' a b off d : ℕ) (s : Bool)
    (h : off + a + b ≤ n) (h' : d + n ≤ n') :
    braidMatrix n' (thickCross a b (off + d) s) =
      skPlace n' n' d (braidMatrix n (thickCross a b off s)) := by
  rw [thickCross_add_off]
  refine braidMatrix_map_add_eq_skPlace n n' d _ (fun g hg ↦ ?_) h'
  have := mem_thickCross_kinkRec hg
  omega

/-- A thick crossing of bundles inside the first `n` strands is the placement at `0` of its
matrix on `n` strands. -/
private theorem braidMatrix_thickCross_eq_skPlace_kinkRec (n n' a b off : ℕ) (s : Bool)
    (h : off + a + b ≤ n) (h' : n ≤ n') :
    braidMatrix n' (thickCross a b off s) =
      skPlace n' n' 0 (braidMatrix n (thickCross a b off s)) :=
  braidMatrix_thickCross_add_eq_skPlace_kinkRec n n' a b off 0 s h (by omega)

/-- The crossing of two single strands is one letter. -/
private theorem braidMatrix_thickGen_one_one_kinkRec (n off : ℕ) (s : Bool) :
    braidMatrix n (thickGen 1 1 off s) = crossingF n (off, s) := by
  cases s <;> simp [thickGen, braidMatrix]

/-- The positive half twist of two bundles of `c + 1` strands, with the last strand split off. -/
private theorem braidMatrix_thickGen_succ_succ_kinkRec (n c : ℕ) :
    braidMatrix n (thickGen (c + 1) (c + 1) 0 true) =
      braidMatrix n (thickGen 1 c c true) * braidMatrix n (thickGen 1 1 (2 * c) true) *
        (braidMatrix n (thickGen c c 0 true) * braidMatrix n (thickGen c 1 c true)) := by
  rw [thickGen_add_left c 1 (c + 1) 0, braidMatrix_append,
    braidMatrix_thickGen_add_right n 1 c 1 (0 + c), braidMatrix_thickGen_add_right n c c 1 0,
    Nat.zero_add, show c + c = 2 * c by omega]

/-- The inverse of a product of four invertible factors. -/
private theorem eq_inv_of_mul_eq_one_kinkRec {M : Type*} [Monoid M] {x z a t b d a' t' b' d' : M}
    (hx : x = a * t * (b * d)) (hxz : x * z = 1) (ha : a' * a = 1) (ht : t' * t = 1)
    (hb : b' * b = 1) (hd : d' * d = 1) : z = d' * b' * t' * a' := by
  have h : d' * b' * t' * a' * (a * t * (b * d)) = 1 := by
    calc d' * b' * t' * a' * (a * t * (b * d))
        = d' * (b' * (t' * (a' * a) * t) * b) * d := by simp only [mul_assoc]
      _ = 1 := by rw [ha, mul_one, ht, mul_one, hb, mul_one, hd]
  calc z = d' * b' * t' * a' * (a * t * (b * d)) * z := by rw [h, one_mul]
    _ = d' * b' * t' * a' := by rw [← hx, mul_assoc, hxz, mul_one]

/-- The negative half twist of two bundles of `c + 1` strands, with the last strand split off. -/
private theorem braidMatrix_thickGen_succ_succ_false_kinkRec (n c : ℕ) :
    braidMatrix n (thickGen (c + 1) (c + 1) 0 false) =
      braidMatrix n (thickGen c 1 c false) * braidMatrix n (thickGen c c 0 false) *
        braidMatrix n (thickGen 1 1 (2 * c) false) * braidMatrix n (thickGen 1 c c false) :=
  eq_inv_of_mul_eq_one_kinkRec (braidMatrix_thickGen_succ_succ_kinkRec n c)
    (braidMatrix_thickGen_mul_inv n _ _ _) (braidMatrix_thickGen_inv_mul n _ _ _)
    (braidMatrix_thickGen_inv_mul n _ _ _) (braidMatrix_thickGen_inv_mul n _ _ _)
    (braidMatrix_thickGen_inv_mul n _ _ _)

/-- The partial trace over the last strand of the half twist of two bundles of `c + 1`
strands. -/
private theorem ptrTail_last_halfTwist_kinkRec (c : ℕ) (s : Bool) :
    ptrTail (2 * c + 1) (2 * c + 2) (braidMatrix (2 * c + 2) (thickCross (c + 1) (c + 1) 0 s)) =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) •
        (braidMatrix (2 * c + 1) (thickCross 1 c c s) *
          braidMatrix (2 * c + 1) (thickCross c c 0 s) *
          braidMatrix (2 * c + 1) (thickCross c 1 c s)) := by
  have p1 := braidMatrix_thickCross_eq_skPlace_kinkRec (2 * c + 1) (2 * c + 2) 1 c c s
    (by omega) (by omega)
  have p2 := braidMatrix_thickCross_eq_skPlace_kinkRec (2 * c + 1) (2 * c + 2) c c 0 s
    (by omega) (by omega)
  have p3 := braidMatrix_thickCross_eq_skPlace_kinkRec (2 * c + 1) (2 * c + 2) c 1 c s
    (by omega) (by omega)
  cases s
  · simp only [thickCross, Bool.false_eq_true, ite_false] at p1 p2 p3 ⊢
    rw [braidMatrix_thickGen_succ_succ_false_kinkRec, braidMatrix_thickGen_one_one_kinkRec,
      p1, p2, p3, ptrTail_mul_skPlace _ _ (by omega), Matrix.mul_assoc,
      ptrTail_skPlace_mul _ _ (by omega), ptrTail_skPlace_mul _ _ (by omega),
      ptrTail_crossingF_last]
    simp only [Bool.false_eq_true, ite_false, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  · simp only [thickCross, ite_true] at p1 p2 p3 ⊢
    rw [braidMatrix_thickGen_succ_succ_kinkRec, braidMatrix_thickGen_one_one_kinkRec,
      p1, p2, p3, ← Matrix.mul_assoc, ptrTail_mul_skPlace _ _ (by omega),
      ptrTail_mul_skPlace _ _ (by omega), ptrTail_skPlace_mul _ _ (by omega),
      ptrTail_crossingF_last]
    simp only [ite_true, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- The partial trace of a placement at `i`, for sizes given up to equality. -/
private theorem ptrTail_skPlace_shift_of_eq_kinkRec (i k n K N : ℕ) (hK : K = i + k)
    (hN : N = i + n) (h : k ≤ n) (A : SkMat n n) :
    ptrTail K N (skPlace N N i A) = skPlace K K i (ptrTail k n A) := by
  subst hK hN
  exact ptrTail_skPlace_shift i k n h A

/-- The kink of `c` strands is the partial trace of the thick crossing of two bundles. -/
private theorem kinkOp_eq_ptrTail_thickCross_kinkRec (c : ℕ) (s : Bool) :
    kinkOp c s = ptrTail c (2 * c) (braidMatrix (2 * c) (thickCross c c 0 s)) := by
  rw [kinkOp, halfTwist, cableGen_eq_thickCross]
  rfl

/-- The partial trace over the second bundle of the three crossings left after the removal of
the last strand: Yang–Baxter, then the outer crossings come out of the trace. -/
private theorem ptrTail_thickCross_triple_kinkRec (c : ℕ) (s : Bool) :
    ptrTail (c + 1) (2 * c + 1) (braidMatrix (2 * c + 1) (thickCross 1 c c s) *
        braidMatrix (2 * c + 1) (thickCross c c 0 s) *
        braidMatrix (2 * c + 1) (thickCross c 1 c s)) =
      braidMatrix (c + 1) (thickCross c 1 0 s) * skPlace (c + 1) (c + 1) 1 (kinkOp c s) *
        braidMatrix (c + 1) (thickCross 1 c 0 s) := by
  have yb := braidMatrix_thickCross_yangBaxter (2 * c + 1) c 1 c 0 s (by omega)
  simp only [Nat.zero_add] at yb
  have p1 := braidMatrix_thickCross_eq_skPlace_kinkRec (c + 1) (2 * c + 1) c 1 0 s
    (by omega) (by omega)
  have p2 := braidMatrix_thickCross_add_eq_skPlace_kinkRec (2 * c) (2 * c + 1) c c 0 1 s
    (by omega) (by omega)
  have p3 := braidMatrix_thickCross_eq_skPlace_kinkRec (c + 1) (2 * c + 1) 1 c 0 s
    (by omega) (by omega)
  rw [Nat.zero_add] at p2
  rw [← yb, p1, p2, p3, ptrTail_mul_skPlace _ _ (by omega), Matrix.mul_assoc,
    ptrTail_skPlace_mul _ _ (by omega),
    ptrTail_skPlace_shift_of_eq_kinkRec 1 c (2 * c) (c + 1) (2 * c + 1) (by omega) (by omega)
      (by omega),
    ← kinkOp_eq_ptrTail_thickCross_kinkRec, Matrix.mul_assoc]

/-- The kink of `c + 1` strands in terms of the kink of `c` strands. -/
theorem kinkOp_succ (c : ℕ) (s : Bool) :
    kinkOp (c + 1) s =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) •
        (braidMatrix (c + 1) (thickCross c 1 0 s) * skPlace (c + 1) (c + 1) 1 (kinkOp c s) *
          braidMatrix (c + 1) (thickCross 1 c 0 s)) := by
  have h : kinkOp (c + 1) s = ptrTail (c + 1) (2 * c + 2)
      (braidMatrix (2 * c + 2) (thickCross (c + 1) (c + 1) 0 s)) :=
    kinkOp_eq_ptrTail_thickCross_kinkRec (c + 1) s
  rw [h, ← ptrTail_ptrTail (c + 1) (2 * c + 1) (2 * c + 2) (by omega) (by omega),
    ptrTail_last_halfTwist_kinkRec, ptrTail_smul, ptrTail_thickCross_triple_kinkRec]

end AJConjecture
