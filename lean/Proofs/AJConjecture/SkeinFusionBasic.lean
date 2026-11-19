import Mathlib
import AJConjecture.SkeinThickCupAdd
import AJConjecture.SkeinJwCapKill
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinTurnbackEigenBasic
import AJConjecture.SkeinTurnbackOneSided
import AJConjecture.SkeinWeightPlace

/-!
# Fusion: the maps between two bundles and a channel

For two bundles of `c = n + m` strands and the channel of colour `2n`:

* `ι π = d_{m,n} f_{2n}`. Induction on `m`: the innermost cup and cap around `f ⊗ f` are a bubble
  (`AJConjecture.skCup_mul_twoBundleProj_mul_skCap`), `x g + y g e g`; the term `g e g` against the
  remaining nest of caps is the one-sided recursion
  (`AJConjecture.turnback_one_mul_capThick_place`), whose second term ends with a cup followed by
  `f_{2n}` and vanishes (`AJConjecture.cupAt_mul_jwAt`), so each step contributes the factor
  `x + y β' = -[i][2n+i+1]/[n+i]²`, and the product of these is `d_{m,n}`.
* `D_1 π = d_{1,n} π`: the one-sided recursion again, with the same vanishing; `β_m = d_{1,n}`. The
  statement for `ι` is its transpose.
* Hence `Q_n π = π` and `ι Q_n = ι`: each factor `(D_1 - d_{1,m'}) / (d_{1,n} - d_{1,m'})` of `Q_n`
  acts on `π` as `1`.
* `π` intertwines the weights (`AJConjecture.skWeight_mul_skPlace`,
  `AJConjecture.skWeight_mul_capThick`, `AJConjecture.skWeight_mul_jwAt`).
-/

namespace AJConjecture

/-- `f ⊗ f` is absorbed by `f_{2c}` on its right. -/
private theorem twoBundleProj_mul_jwAt_fusionBasic (c : ℕ) :
    twoBundleProj c * jwAt (2 * c) 0 (2 * c) = jwAt (2 * c) 0 (2 * c) := by
  rw [twoBundleProj, Matrix.mul_assoc,
    jwAt_mul_jwAt_of_ge (2 * c) 0 (2 * c) c c (by omega) (by omega),
    jwAt_mul_jwAt_of_ge (2 * c) 0 (2 * c) 0 c (by omega) (by omega)]

/-- `f ⊗ f` is absorbed by `f_{2c}` on its left. -/
private theorem jwAt_mul_twoBundleProj_fusionBasic (c : ℕ) :
    jwAt (2 * c) 0 (2 * c) * twoBundleProj c = jwAt (2 * c) 0 (2 * c) := by
  rw [twoBundleProj, ← Matrix.mul_assoc,
    jwAt_mul_jwAt_of_le (2 * c) 0 (2 * c) 0 c (by omega) (by omega),
    jwAt_mul_jwAt_of_le (2 * c) 0 (2 * c) c c (by omega) (by omega)]

/-- `D_1 π = d_{1,n} π`, with a free bundle size. -/
private theorem turnback_one_mul_fusionProj_fusionBasic (c n m : ℕ) (hc : c = n + m) :
    turnback c 1 *
        (twoBundleProj c * skPlace (2 * c) (2 * n) n (capThick m) * jwAt (2 * n) 0 (2 * n)) =
      claspAlgTurnbackEigen c 1 n •
        (twoBundleProj c * skPlace (2 * c) (2 * n) n (capThick m) * jwAt (2 * n) 0 (2 * n)) := by
  rcases n with _ | a
  · obtain rfl : c = m := by omega
    have e1 : skPlace (2 * c) (2 * 0) 0 (capThick c) = capThick c :=
      skPlace_self (2 * c) 0 (capThick c)
    have e2 : jwAt (2 * 0) 0 (2 * 0) = 1 := rfl
    have hd : claspAlgTurnbackEigen c 1 0 =
        -(quantumInt (c : ℤ) * quantumInt ((c : ℤ) + 1)) / quantumInt (c : ℤ) ^ 2 := by
      rw [claspAlgTurnbackEigen, Finset.prod_range_one]
      simp only [Nat.cast_zero, sub_zero, add_zero]
    rw [e1, e2, Matrix.mul_one, ← Matrix.mul_assoc, turnback_mul_twoBundleProj,
      turnback_one_mul_capThick, hd]
  · obtain rfl : c = a + 1 + m := hc
    have h0 : skPlace (2 * a) (2 * (a + 1)) a skCup * jwAt (2 * (a + 1)) 0 (2 * (a + 1)) = 0 :=
      cupAt_mul_jwAt (2 * a) 0 (2 * a + 2) a (by omega) (by omega)
    have hd : claspAlgTurnbackEigen (a + 1 + m) 1 (a + 1) =
        -(quantumInt (m : ℤ) * quantumInt (2 * (a : ℤ) + m + 3)) /
          quantumInt ((a : ℤ) + 1 + m) ^ 2 := by
      rw [claspAlgTurnbackEigen, Finset.prod_range_one]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
      rw [show (a : ℤ) + 1 + m - (a + 1) = m from by ring,
        show (a : ℤ) + 1 + m + (a + 1) + 1 = 2 * a + m + 3 from by ring]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, turnback_mul_twoBundleProj,
      turnback_one_mul_capThick_place, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_assoc _ (twoBundleProj (a + 1)) _, twoBundleProj_mul_jwAt_fusionBasic,
      Matrix.mul_assoc _ (skPlace (2 * a) (2 * (a + 1)) a skCup) _, h0, Matrix.mul_zero,
      smul_zero, add_zero, hd]

/-- The eigenvalue `d_{m+1,n}` of the larger bundles from `d_{m,n}` of the smaller ones: the
factor of one step of the bubble recursion. -/
private theorem turnbackEigen_succ_succ_fusionBasic (c m n : ℕ) (hn : n ≤ c) :
    (-(quantumInt (2 * (c : ℤ) + 2)) / quantumInt ((c : ℤ) + 1) ^ 2 +
        quantumInt (c : ℤ) ^ 2 / quantumInt ((c : ℤ) + 1) ^ 2 * claspAlgTurnbackEigen c 1 n) *
      claspAlgTurnbackEigen c m n = claspAlgTurnbackEigen (c + 1) (m + 1) n := by
  have hstep : claspAlgTurnbackEigen (c + 1) (m + 1) n =
      (-(quantumInt ((c : ℤ) + 1 - n) * quantumInt ((c : ℤ) + n + 2)) /
        quantumInt ((c : ℤ) + 1) ^ 2) * claspAlgTurnbackEigen c m n := by
    unfold claspAlgTurnbackEigen
    rw [Finset.prod_range_succ', mul_comm]
    congr 1
    · simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
      rw [show (c : ℤ) + 1 + n + 1 = c + n + 2 from by ring]
    · refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [show ((c + 1 : ℕ) : ℤ) - n - ((i + 1 : ℕ) : ℤ) = (c : ℤ) - n - i from by push_cast; ring,
        show ((c + 1 : ℕ) : ℤ) + n + 1 - ((i + 1 : ℕ) : ℤ) = (c : ℤ) + n + 1 - i from by
          push_cast; ring,
        show ((c + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) = (c : ℤ) - i from by push_cast; ring]
  have hfac : -(quantumInt (2 * (c : ℤ) + 2)) / quantumInt ((c : ℤ) + 1) ^ 2 +
      quantumInt (c : ℤ) ^ 2 / quantumInt ((c : ℤ) + 1) ^ 2 * claspAlgTurnbackEigen c 1 n =
        -(quantumInt ((c : ℤ) + 1 - n) * quantumInt ((c : ℤ) + n + 2)) /
          quantumInt ((c : ℤ) + 1) ^ 2 := by
    have h1 : quantumInt 1 = 1 := by
      rw [quantumInt]
      exact div_self (by simpa using claspAlg_ratFuncX_sq_sub_ne_zero)
    have key := quantumInt_mul_shift_sub ((c : ℤ) - n) ((c : ℤ) + n + 1) 1
    rw [h1, one_mul, show (c : ℤ) - n + 1 = (c : ℤ) + 1 - n from by ring,
      show (c : ℤ) + n + 1 + 1 = (c : ℤ) + n + 2 from by ring,
      show (c : ℤ) - n + ((c : ℤ) + n + 1) + 1 = 2 * (c : ℤ) + 2 from by ring] at key
    unfold claspAlgTurnbackEigen
    rw [Finset.prod_range_one]
    simp only [Nat.cast_zero, sub_zero]
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · obtain rfl : n = 0 := by omega
      have h0 : quantumInt 0 = 0 := by simp [quantumInt]
      simp [h0, h1]
    · have hc0 : quantumInt (c : ℤ) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
      have hc1 : quantumInt ((c : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
      field_simp
      linear_combination key
  rw [hstep, hfac]

/-- One step of the bubble recursion for `ι π`, for abstract rectangular matrices. -/
private theorem bubble_step_fusionBasic {p q r : ℕ} (f : SkMat p p) (C : SkMat p q)
    (U : SkMat q r) (P' : SkMat r r) (V : SkMat r q) (K : SkMat q p) (P T : SkMat q q)
    (x y d1 dm : RatFunc ℚ) (hP' : P' * P' = P') (hbub : U * P' * V = x • P + y • T)
    (hP : P * P = P) (hPT : P * T = T) (hTP : T * P = T)
    (ih : f * C * P * (P * K * f) = dm • f) (hD : T * (P * K * f) = d1 • (P * K * f)) :
    f * (C * U) * P' * (P' * (V * K) * f) = ((x + y * d1) * dm) • f := by
  have h1 : f * (C * U) * P' * (P' * (V * K) * f) = f * C * (U * (P' * P') * V) * (K * f) := by
    simp only [Matrix.mul_assoc]
  have h2 : f * C * P * (K * f) = dm • f := by
    rw [← ih]
    conv_lhs => rw [← hP]
    simp only [Matrix.mul_assoc]
  have h3 : f * C * T * (K * f) = (d1 * dm) • f := by
    calc f * C * T * (K * f) = f * C * (P * (T * P)) * (K * f) := by rw [hTP, hPT]
      _ = f * C * P * (T * (P * K * f)) := by simp only [Matrix.mul_assoc]
      _ = (d1 * dm) • f := by rw [hD, Matrix.mul_smul, ih, smul_smul]
  rw [h1, hP', hbub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, h2, h3, smul_smul, smul_smul, ← add_smul]
  congr 1
  ring

/-- `ι π = d_{m,n} f_{2n}`. -/
theorem fusionIncl_mul_fusionProj (n m : ℕ) :
    fusionIncl n m * fusionProj n m =
      claspAlgTurnbackEigen (n + m) m n • jwAt (2 * n) 0 (2 * n) := by
  induction m with
  | zero =>
    change jwAt (2 * n) 0 (2 * n) * skPlace (2 * n) (2 * n) n (cupThick 0) * twoBundleProj n *
      (twoBundleProj n * skPlace (2 * n) (2 * n) n (capThick 0) * jwAt (2 * n) 0 (2 * n)) =
        claspAlgTurnbackEigen n 0 n • jwAt (2 * n) 0 (2 * n)
    rw [cupThick_zero, capThick_zero, skPlace_one (2 * n) n 0 (by omega),
      Matrix.mul_one, Matrix.mul_one, jwAt_mul_twoBundleProj_fusionBasic,
      twoBundleProj_mul_jwAt_fusionBasic, jwAt_mul_self, turnbackEigen_zero, one_smul]
  | succ m ih =>
    have hι : fusionIncl n (m + 1) = jwAt (2 * n) 0 (2 * n) *
        (skPlace (2 * n) (2 * (n + m)) n (cupThick m) *
          skPlace (2 * (n + m)) (2 * (n + m + 1)) (n + m) skCup) * twoBundleProj (n + m + 1) := by
      rw [fusionIncl, cupThick_succ_inner,
        skPlace_mul (2 * n) (2 * (n + m)) (2 * (n + (m + 1))) n (cupThick m) _ (by omega)
          (by omega) (by omega),
        skPlace_skPlace (2 * (n + m)) (2 * (n + (m + 1))) n m skCup (by omega) (by omega)
          (by omega) (by omega)]
      rfl
    have hπ : fusionProj n (m + 1) = twoBundleProj (n + m + 1) *
        (skPlace (2 * (n + m + 1)) (2 * (n + m)) (n + m) skCap *
          skPlace (2 * (n + m)) (2 * n) n (capThick m)) * jwAt (2 * n) 0 (2 * n) := by
      rw [fusionProj, capThick_succ_inner,
        skPlace_mul (2 * (n + (m + 1))) (2 * (n + m)) (2 * n) n _ (capThick m) (by omega)
          (by omega) (by omega),
        skPlace_skPlace (2 * (n + (m + 1))) (2 * (n + m)) n m skCap (by omega) (by omega)
          (by omega) (by omega)]
      rfl
    have hbub := skCup_mul_twoBundleProj_mul_skCap (n + m)
    rw [← turnback_one (n + m)] at hbub
    rw [fusionIncl, fusionProj] at ih
    rw [hι, hπ, bubble_step_fusionBasic _ _ _ _ _ _ _ _ _ _ _ _ (twoBundleProj_mul_self _) hbub
      (twoBundleProj_mul_self _) (twoBundleProj_mul_turnback _ 1) (turnback_mul_twoBundleProj _ 1)
      ih (turnback_one_mul_fusionProj_fusionBasic (n + m) n m rfl)]
    congr 1
    exact turnbackEigen_succ_succ_fusionBasic (n + m) m n (by omega)

/-- `D_1 π = d_{1,n} π`. -/
theorem turnback_one_mul_fusionProj (n m : ℕ) :
    turnback (n + m) 1 * fusionProj n m = claspAlgTurnbackEigen (n + m) 1 n • fusionProj n m :=
  turnback_one_mul_fusionProj_fusionBasic (n + m) n m rfl

/-- A product of normalised factors `(D_1 - d_{1,m'}) / (d_{1,n} - d_{1,m'})` acts as `1` on an
eigenvector of `D_1` for the eigenvalue `d_{1,n}`. -/
private theorem prod_mul_of_turnback_one_mul_fusionBasic (c n : ℕ) (hn : n ≤ c) {l : ℕ}
    (Y : SkMat (2 * c) l) (hY : turnback c 1 * Y = claspAlgTurnbackEigen c 1 n • Y)
    (L : List ℕ) (hL : ∀ m' ∈ L, m' ≤ c ∧ m' ≠ n) :
    (L.map fun m' ↦ (claspAlgTurnbackEigen c 1 n - claspAlgTurnbackEigen c 1 m')⁻¹ •
      (turnback c 1 - claspAlgTurnbackEigen c 1 m' • (1 : SkMat (2 * c) (2 * c)))).prod * Y =
        Y := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, Matrix.one_mul]
  | cons a L ih =>
    have ha := hL a List.mem_cons_self
    have hne : claspAlgTurnbackEigen c 1 n - claspAlgTurnbackEigen c 1 a ≠ 0 :=
      sub_ne_zero.mpr fun h ↦ ha.2 (turnbackEigen_one_injective c n a hn ha.1 h).symm
    rw [List.map_cons, List.prod_cons, Matrix.mul_assoc,
      ih fun m' hm' ↦ hL m' (List.mem_cons_of_mem _ hm'), Matrix.smul_mul, Matrix.sub_mul, hY,
      Matrix.smul_mul, Matrix.one_mul, ← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The indices of the factors of `Q_n`. -/
private theorem mem_filter_range_fusionBasic (c n : ℕ) :
    ∀ m' ∈ (List.range (c + 1)).filter (· ≠ n), m' ≤ c ∧ m' ≠ n := by
  intro m' hm'
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hm'
  exact ⟨by omega, hm'.2⟩

/-- `Q_n π = π`. -/
theorem channelIdem_mul_fusionProj (n m : ℕ) :
    channelIdem (n + m) n * fusionProj n m = fusionProj n m := by
  rw [channelIdem, Matrix.mul_assoc,
    prod_mul_of_turnback_one_mul_fusionBasic (n + m) n (by omega) _
      (turnback_one_mul_fusionProj n m) _ (mem_filter_range_fusionBasic (n + m) n),
    fusionProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, twoBundleProj_mul_self]

/-- The fusion map `π` intertwines the weights. -/
theorem skWeight_mul_fusionProj (n m : ℕ) :
    skWeight (2 * (n + m)) * fusionProj n m = fusionProj n m * skWeight (2 * n) := by
  have h1 : skWeight (2 * (n + m)) * twoBundleProj (n + m) =
      twoBundleProj (n + m) * skWeight (2 * (n + m)) := by
    rw [twoBundleProj, ← Matrix.mul_assoc, skWeight_mul_jwAt, Matrix.mul_assoc, skWeight_mul_jwAt,
      Matrix.mul_assoc]
  have h2 := skWeight_mul_skPlace (2 * (n + m)) (2 * n) n (capThick m) (skWeight_mul_capThick m)
  rw [fusionProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
    Matrix.mul_assoc (twoBundleProj (n + m)), h2, Matrix.mul_assoc, Matrix.mul_assoc,
    skWeight_mul_jwAt]
  simp only [Matrix.mul_assoc]

end AJConjecture
