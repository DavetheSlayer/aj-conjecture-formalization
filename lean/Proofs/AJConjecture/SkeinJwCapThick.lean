import Mathlib
import AJConjecture.SkeinJwCapComm
import AJConjecture.SkeinTurnbackBasic
import AJConjecture.SkeinJwMirror
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinThickCupAdd

/-!
# A projector passes to the other leg of a nest of caps

The nest of `c` caps joins the strand `x` with the strand `2c - 1 - x`. A generator on the strands
`j`, `j + 1` of the first leg followed by the nest is the generator on the mirror strands
`2c - 2 - j`, `2c - 1 - j` of the second leg followed by the nest: for the two caps involved this is
a planar isotopy (two zig-zags, `AJConjecture.cupAt_mul_capAt_succ` and its companion, after
writing the nest with `AJConjecture.capThick_succ_inner`); the other caps are spectators. The
projector `f_c` on the first leg is built from these generators by Wenzl's recursion and the
projector on the second leg from the mirror generators by the recursion from the left
(`AJConjecture.jwAt_succ_succ_left`); induction on the size of the projector. The statements for
cups are the transposes.
-/

namespace AJConjecture

/-- On the nest of two caps, the generator on the first two strands is the generator on the
last two strands. -/
private theorem tlGenF_mul_capThick_two_jwCapThick :
    tlGenF (2 * 2) 0 * capThick 2 = tlGenF (2 * 2) 2 * capThick 2 := by
  have hcap : capThick 2 = capAt 2 1 * skCap := by
    have h : capThick 2 = skPlace (2 * (1 + 1)) (2 * 1) 1 skCap * capThick 1 :=
      capThick_succ_inner 1
    rw [capThick_one] at h
    exact h
  have h0 : tlGenF (2 * 2) 0 = capAt 2 0 * cupAt 2 0 := (capAt_mul_cupAt 2 0 (by omega)).symm
  have h2 : tlGenF (2 * 2) 2 = capAt 2 2 * cupAt 2 2 := (capAt_mul_cupAt 2 2 (by omega)).symm
  have hz0 : cupAt 2 0 * capAt 2 1 = 1 := cupAt_mul_capAt_succ 2 0 (by omega)
  have hz2 : cupAt 2 2 * capAt 2 1 = 1 := cupAt_succ_mul_capAt 2 1 (by omega)
  have hcomm : capAt 2 0 * skCap = capAt 2 2 * skCap := by
    have h := skPlace_mul_skPlace_comm 4 2 2 0 0 2 skCap skCap (by omega) (by omega) (by omega)
      (by omega) (by omega)
    rw [skPlace_self] at h
    exact h
  rw [hcap, h0, h2, Matrix.mul_assoc, ← Matrix.mul_assoc (cupAt 2 0), hz0, Matrix.one_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc (cupAt 2 2), hz2, Matrix.one_mul, hcomm]

/-- On a nest of at least two caps, the generator on the first two strands is the generator on
the last two strands. -/
private theorem tlGenF_zero_mul_capThick_jwCapThick (d : ℕ) :
    tlGenF (2 * (2 + d)) 0 * capThick (2 + d) =
      tlGenF (2 * (2 + d)) (2 * d + 2) * capThick (2 + d) := by
  have h1 := tlGenF_mul_skPlace_of_lt (2 * (2 + d)) (2 * 2) 0 2 (capThick d)
    (by omega) (by omega) (by omega)
  have h2 := tlGenF_mul_skPlace_of_ge (2 * (2 + d)) (2 * 2) (2 * d + 2) 2 (capThick d)
    (by omega) (by omega) (by omega)
  rw [show 2 * d + 2 + 0 - 2 * d = 2 from by omega] at h2
  rw [capThick_add 2 d, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.mul_assoc,
    Matrix.mul_assoc, tlGenF_mul_capThick_two_jwCapThick]

/-- A generator on the first leg of a nest of caps is the mirror generator on the second leg. -/
theorem tlGenF_mul_capThick (c j : ℕ) (hj : j + 1 < c) :
    tlGenF (2 * c) j * capThick c = tlGenF (2 * c) (2 * c - 2 - j) * capThick c := by
  obtain ⟨d, rfl⟩ : ∃ d, c = j + (2 + d) := ⟨c - j - 2, by omega⟩
  have h1 : tlGenF (2 * (j + (2 + d))) j =
      skPlace (2 * (j + (2 + d))) (2 * (j + (2 + d))) j (tlGenF (2 * (2 + d)) 0) := by
    rw [tlGenF_eq_skPlace (2 * (j + (2 + d))) j, tlGenF_eq_skPlace (2 * (2 + d)) 0,
      skPlace_skPlace _ _ j 0 _ (by omega) (by omega) (by omega) (by omega), Nat.add_zero]
  have h2 : tlGenF (2 * (j + (2 + d))) (j + (2 * d + 2)) =
      skPlace (2 * (j + (2 + d))) (2 * (j + (2 + d))) j (tlGenF (2 * (2 + d)) (2 * d + 2)) := by
    rw [tlGenF_eq_skPlace (2 * (j + (2 + d))) (j + (2 * d + 2)),
      tlGenF_eq_skPlace (2 * (2 + d)) (2 * d + 2),
      skPlace_skPlace _ _ j (2 * d + 2) _ (by omega) (by omega) (by omega) (by omega)]
  rw [show 2 * (j + (2 + d)) - 2 - j = j + (2 * d + 2) from by omega, capThick_add j (2 + d),
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2,
    ← skPlace_mul _ _ _ j _ _ (by omega) (by omega) (by omega),
    ← skPlace_mul _ _ _ j _ _ (by omega) (by omega) (by omega),
    tlGenF_zero_mul_capThick_jwCapThick]

/-- The step of Wenzl's recursion for the passage of a projector to the mirror block. -/
private theorem wenzl_mirror_step_jwCapThick {n : ℕ} (P Q e e' : SkMat n n) (Z : SkMat n 0)
    (x : RatFunc ℚ) (hPZ : P * Z = Q * Z) (heZ : e * Z = e' * Z) (heQ : e * Q = Q * e)
    (hPQ : P * Q = Q * P) (hPe' : P * e' = e' * P) :
    (P + x • (P * e * P)) * Z = (Q + x • (Q * e' * Q)) * Z := by
  have h : P * e * P * Z = Q * e' * Q * Z := by
    calc P * e * P * Z = P * (e * (P * Z)) := by simp only [Matrix.mul_assoc]
      _ = P * (e * Q) * Z := by rw [hPZ]; simp only [Matrix.mul_assoc]
      _ = P * Q * (e * Z) := by rw [heQ]; simp only [Matrix.mul_assoc]
      _ = Q * (P * e') * Z := by rw [heZ, hPQ]; simp only [Matrix.mul_assoc]
      _ = Q * e' * (P * Z) := by rw [hPe']; simp only [Matrix.mul_assoc]
      _ = Q * e' * Q * Z := by rw [hPZ]; simp only [Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hPZ, h]

/-- The projector on the first `k` strands of a nest of caps is the projector on the last `k`
strands. -/
private theorem jwAt_mul_capThick_mirror_jwCapThick (c : ℕ) :
    ∀ k : ℕ, k ≤ c → jwAt (2 * c) 0 k * capThick c = jwAt (2 * c) (2 * c - k) k * capThick c
  | 0, _ => by rw [jwAt, jwAt]
  | 1, _ => by rw [jwAt, jwAt]
  | k + 2, hk => by
    have ih := jwAt_mul_capThick_mirror_jwCapThick c (k + 1) (by omega)
    have he := tlGenF_mul_capThick c k (by omega)
    rw [show 2 * c - 2 - k = 2 * c - (k + 2) from by omega] at he
    have heQ := (jwAt_commute_tlGenF (2 * c) (2 * c - (k + 1)) (k + 1) k (Or.inl (by omega))).eq
    have hPe := (jwAt_commute_tlGenF (2 * c) 0 (k + 1) (2 * c - (k + 2)) (Or.inr (by omega))).eq
    have hPQ : jwAt (2 * c) 0 (k + 1) * jwAt (2 * c) (2 * c - (k + 1)) (k + 1) =
        jwAt (2 * c) (2 * c - (k + 1)) (k + 1) * jwAt (2 * c) 0 (k + 1) :=
      (jwAt_mul_eq_mul_jwAt (2 * c) (2 * c) (2 * c - (k + 1)) (2 * c - (k + 1))
        (jwAt (2 * c) 0 (k + 1)) (k + 1) fun l _ ↦
        (jwAt_commute_tlGenF (2 * c) 0 (k + 1) (2 * c - (k + 1) + l)
          (Or.inr (by omega))).eq.symm).symm
    rw [jwAt_succ_succ_left (2 * c) (2 * c - (k + 2)) k (by omega),
      show 2 * c - (k + 2) + 1 = 2 * c - (k + 1) from by omega, jwAt, Nat.zero_add]
    exact wenzl_mirror_step_jwCapThick _ _ _ _ _ _ ih he heQ.symm hPQ hPe

/-- A projector on the first leg of a nest of caps is the projector on the second leg. -/
theorem jwAt_mul_capThick (c : ℕ) :
    jwAt (2 * c) 0 c * capThick c = jwAt (2 * c) c c * capThick c := by
  have h := jwAt_mul_capThick_mirror_jwCapThick c c le_rfl
  rw [show 2 * c - c = c from by omega] at h
  exact h

/-- The entries of the cup are `-t²` times the entries of the cap. -/
private theorem cupEntry_eq_mul_capEntry_jwCapThick (a b : Bool) :
    cupEntry a b = -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) * capEntry a b := by
  cases a <;> cases b
  · simp only [cupEntry, capEntry, mul_zero]
  · simp only [cupEntry, capEntry, mul_one]
  · simp only [cupEntry, capEntry]
    rw [neg_mul_neg, ← zpow_add₀ RatFunc.X_ne_zero]
    norm_num
  · simp only [cupEntry, capEntry, mul_zero]

/-- The thick cup is a multiple of the transpose of the thick cap. -/
private theorem cupThick_eq_smul_transpose_jwCapThick (m : ℕ) :
    cupThick m = (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)) ^ m • (capThick m).transpose := by
  ext a b
  simp only [cupThick, capThick, Matrix.of_apply, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, cupEntry_eq_mul_capEntry_jwCapThick, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- A projector on the first leg of a nest of cups is the projector on the second leg. -/
theorem cupThick_mul_jwAt (c : ℕ) :
    cupThick c * jwAt (2 * c) 0 c = cupThick c * jwAt (2 * c) c c := by
  have h := congrArg Matrix.transpose (jwAt_mul_capThick c)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, jwAt_transpose, jwAt_transpose] at h
  rw [cupThick_eq_smul_transpose_jwCapThick, Matrix.smul_mul, Matrix.smul_mul, h]

end AJConjecture
