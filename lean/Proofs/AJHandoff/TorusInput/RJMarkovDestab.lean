import Mathlib
import AJHandoff.TorusInput.RJKinkProj
import AJHandoff.TorusInput.RJProfileSlide
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinPtrTailPlace
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinTraceCyclic
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinTurnbackBasic

/-!
# Thick Markov destabilization (node RA5.ii.6)

If the last two columns have the same thickness `c` and the last letter is the only one touching
the last column, closing that column removes one positive crossing and multiplies the coloured
closure by `θ_c`: `⟨w σ_m⟩_κ (m + 2 columns) = θ_c ⟨w⟩_κ (m + 1 columns)`.

Route. Let `N` be the total size and `o = profileOffset κ m`. The cable of `w` lives on the first
`N - c` strands (`braidMatrix_map_add_eq_skPlace` style: a word whose letters avoid the last
bundle is a placement at `0`); the last letter is `X_(c,c)(o)`. Slide the projector of the bottom
column `m` up through the cable of `w` to the top column `m`
(`rj_profileProj_mul_braidMatrix`). Close the last `c` strands first (`qtr_eq_qtr_ptrTail`):
`ptrTail_skPlace_mul`, `ptrTail_mul_skPlace` take everything else out, and
`ptr_c((f_c ⊗ f_c) X_(c,c)) = f_c kink⁺_c f_c = θ_c f_c` (`ptrTail_skPlace_shift`, the definition of
`kinkOp`, N2 to move `1 ⊗ f_c` across `X_(c,c)`, and `rj_jwAt_mul_kinkOp_mul_jwAt`).
Estimate 150–220 lines.
-/

noncomputable section

namespace AJConjecture

/-- Reassociation of a commutation relation. -/
private theorem rj_mul_mul_of_mul_eq_destab {M : Type*} [Semigroup M] {a b c d : M}
    (h : a * b = c * d) (y : M) : a * (b * y) = c * (d * y) := by
  rw [← mul_assoc, h, mul_assoc]

/-- The partial trace of a placement at `i`, for sizes given up to equality. -/
private theorem rj_ptrTail_skPlace_shift_of_eq_destab (i k n K N : ℕ) (hK : K = i + k)
    (hN : N = i + n) (h : k ≤ n) (A : SkMat n n) :
    ptrTail K N (skPlace N N i A) = skPlace K K i (ptrTail k n A) := by
  subst hK hN
  exact ptrTail_skPlace_shift i k n h A

/-- The positive thick crossing of two bundles of `c` strands at `o` is placed at `o`. -/
private theorem rj_braidMatrix_thickCross_eq_skPlace_destab (N o c : ℕ) (h : o + 2 * c ≤ N) :
    braidMatrix N (thickCross c c o true) =
      skPlace N N o (braidMatrix (2 * c) (thickCross c c 0 true)) := by
  rw [← braidMatrix_map_add_eq_skPlace (2 * c) N o _ (fun g hg ↦ by
    have := rj_mem_thickCross hg
    omega) (by omega), ← thickCross_add_off, Nat.zero_add]

/-- The core of the destabilization: closing the last bundle of
`(f_c ⊗ f_c) X_(c,c) (f_c ⊗ f_c)`, with the other projectors and the braid on the left. -/
private theorem rj_ptrTail_destab_core (o c O1 O2 : ℕ) (hO1 : O1 = o + c) (hO2 : O2 = o + 2 * c)
    (B Q : SkMat O1 O1) :
    ptrTail O1 O2 (skPlace O2 O2 0 B * (skPlace O2 O2 0 Q * (skPlace O2 O2 0 (jwAt O1 o c) *
        (braidMatrix O2 (thickCross c c o true) * skPlace O2 O2 0 (jwAt O1 o c))))) =
      kinkScalar c • (B * (Q * jwAt O1 o c)) := by
  rw [ptrTail_skPlace_mul _ _ (by omega), ptrTail_skPlace_mul _ _ (by omega),
    ptrTail_skPlace_mul _ _ (by omega), ptrTail_mul_skPlace _ _ (by omega),
    rj_braidMatrix_thickCross_eq_skPlace_destab O2 o c (by omega),
    rj_ptrTail_skPlace_shift_of_eq_destab o c (2 * c) O1 O2 hO1 hO2 (by omega),
    ← halfTwist_eq_braidMatrix_thickCross, ← kinkOp, jwAt_eq_skPlace O1 o c (by omega),
    ← skPlace_mul O1 O1 O1 o _ _ (by omega) rfl rfl,
    ← skPlace_mul O1 O1 O1 o _ _ (by omega) rfl rfl, ← Matrix.mul_assoc (jwAt c 0 c),
    rj_jwAt_mul_kinkOp_mul_jwAt, skPlace_smul, Matrix.mul_smul, Matrix.mul_smul]

/-- Thick Markov destabilization of a positive crossing between two equal bundles. -/
theorem rj_colorTrace_destab (κ : ℕ → ℕ) (m : ℕ) (w : BraidWord) (hw : IsOnStrands (m + 1) w)
    (hκ : κ m = κ (m + 1)) (hend : ∀ x ≤ m, profileEnd κ w x = κ x) :
    rjColorTrace κ (m + 2) (w ++ [(m, true)]) = kinkScalar (κ m) * rjColorTrace κ (m + 1) w := by
  set c := κ m with hc
  set o := profileOffset κ m with ho
  have hO1 : profileOffset κ (m + 1) = o + c := rj_profileOffset_succ κ m
  have hO2 : profileOffset κ (m + 2) = o + 2 * c := by
    rw [rj_profileOffset_succ, hO1, ← hκ]
    ring
  set O1 := profileOffset κ (m + 1) with hO1def
  set O2 := profileOffset κ (m + 2) with hO2def
  -- the cable of the last letter
  have hlast : thickCable (profileEnd κ w) [(m, true)] = thickCross c c o true := by
    have h1 : profileEnd κ w m = c := hend m le_rfl
    have h2 : profileEnd κ w (m + 1) = c := by
      rw [rj_profileEnd_of_le κ (m + 1) w hw (m + 1) le_rfl, ← hκ]
    have h3 : profileOffset (profileEnd κ w) m = o :=
      Finset.sum_congr rfl fun y hy ↦ hend y (by rw [Finset.mem_range] at hy; omega)
    rw [thickCable, thickCable, List.append_nil]
    simp only
    rw [h1, h2, h3]
  -- the projectors
  set P1 := rjProfileProj O2 κ (m + 1) with hP1
  set Q2 := rjProfileProj O2 κ m with hQ2
  set Jm := jwAt O2 o c with hJm
  set Fl := jwAt O2 O1 c with hFl
  set Bw := braidMatrix O2 (thickCable κ w) with hBw
  set X := braidMatrix O2 (thickCross c c o true) with hX
  have hP2 : rjProfileProj O2 κ (m + 2) = P1 * Fl := by
    rw [rj_profileProj_succ, ← hκ]
  have hP1' : P1 = Q2 * Jm := rj_profileProj_succ O2 κ m
  have hmemw := rj_mem_thickCable κ (m + 1) w hw
  have hFlB : Fl * Bw = Bw * Fl := (rj_commute_jwAt_braidMatrix_of_far O2 O1 c _ fun g hg ↦
    Or.inl (by have := hmemw g hg; omega)).eq
  have hFlX : Fl * X = X * Jm := by
    rw [hFl, hX, hJm, hO1]
    exact jwAt_mul_braidMatrix_thickCross_snd O2 c c o true (by omega)
  have hJQ : Jm * Q2 = Q2 * Jm := (rj_commute_jwAt_profileProj O2 κ m o c le_rfl).eq
  have hJP : Jm * P1 = P1 := by
    rw [hP1', ← Matrix.mul_assoc, hJQ, Matrix.mul_assoc, hJm, jwAt_mul_self]
  have hQX : Q2 * X = X * Q2 := (rj_commute_profileProj_braidMatrix O2 κ m _ fun g hg ↦
    (rj_mem_thickCross hg).1).eq
  have hslide : P1 * Bw = Bw * P1 := by
    rw [hP1, hBw, rj_profileProj_mul_braidMatrix O2 κ (m + 1) w hw
      (rj_profileOffset_mono κ (by omega)),
      rj_profileProj_congr O2 (profileEnd κ w) κ (m + 1) fun x hx ↦ hend x (by omega)]
  have hPP : P1 * P1 = P1 := rj_profileProj_mul_self O2 κ (m + 1)
  have hQQ : Q2 * Q2 = Q2 := rj_profileProj_mul_self O2 κ m
  -- the closure, rearranged
  have hmain : qtr O2 (Bw * X * (P1 * Fl)) = qtr O2 (Bw * (Q2 * (Jm * (X * Jm)))) := by
    calc qtr O2 (Bw * X * (P1 * Fl)) = qtr O2 (Fl * (Bw * X * P1)) := by
          rw [qtr_mul_comm_of_weight _ _ Fl _ (skWeight_mul_jwAt _ _ _)]
          simp only [Matrix.mul_assoc]
      _ = qtr O2 (Bw * X * P1 * P1) := by
          simp only [Matrix.mul_assoc]
          rw [rj_mul_mul_of_mul_eq_destab hFlB, rj_mul_mul_of_mul_eq_destab hFlX, hJP, hPP]
      _ = qtr O2 (P1 * (Bw * X * P1)) := by
          rw [qtr_mul_comm_of_weight _ _ P1 _ (rj_skWeight_mul_profileProj O2 κ (m + 1))]
      _ = qtr O2 (Bw * (Q2 * (Jm * (X * Jm)))) := by
          simp only [Matrix.mul_assoc]
          rw [rj_mul_mul_of_mul_eq_destab hslide, hP1']
          simp only [Matrix.mul_assoc]
          rw [rj_mul_mul_of_mul_eq_destab hQX.symm, rj_mul_mul_of_mul_eq_destab hJQ,
            ← Matrix.mul_assoc Q2 Q2, hQQ]
  unfold rjColorTrace
  rw [← hO2def, rj_thickCable_append, braidMatrix_append, hlast, hP2, ← hBw, ← hX, hmain,
    hBw, rj_braidMatrix_thickCable_eq_skPlace O2 O1 κ (m + 1) w hw le_rfl
      (rj_profileOffset_mono κ (by omega)),
    hQ2, rj_profileProj_eq_skPlace_zero O2 O1 κ m (rj_profileOffset_mono κ (by omega))
      (rj_profileOffset_mono κ (by omega)),
    hJm, rj_jwAt_eq_skPlace_zero O2 O1 o c (by omega) (rj_profileOffset_mono κ (by omega)),
    qtr_eq_qtr_ptrTail O1 O2 (rj_profileOffset_mono κ (by omega)),
    rj_ptrTail_destab_core o c O1 O2 hO1 hO2, ← rj_profileProj_succ, qtr, qtr,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

end AJConjecture
