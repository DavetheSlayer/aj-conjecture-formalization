import Mathlib
import AJHandoff.TorusInput.RJMarkovConj
import AJHandoff.TorusInput.RJCycleCols
import AJConjecture.SkeinThickCableBasic
import AJConjecture.SkeinThickGenInv
import AJConjecture.SkeinPlaceComm

/-!
# The two ends of the isotopy as coloured closures (node RA5.ii.8)

Start: the trace of the cabled cyclic braid on `r` bundles of `b` strands with their projectors,
followed by the full twist with an axis bundle of `k` strands carrying `f_k`, is the coloured
closure of `β(r, 0) = FT_r · c_r` with the profile `(b, …, b, k)`. End: the coloured closure of
`β(1, p) = σ_0^(2p+2)` with the profile `(b, k)` is the trace of `J_(b,k)^(p+1) (f_b ⊗ f_k)`.

Route. Start: `profileOffset (rjAxisProfile b k r) (r + 1) = b r + k`; the cable of `c_r` with
the profile is `cable b c_r` (`thickCable_congr`, `thickCable_const`), placed at `0`
(`braidMatrix_map_add_eq_skPlace`); the cable of `FT_r` (at the same profile, `c_r` permutes
only the `b`-columns) composes to `ρ(X_(br,k)(0)) ρ(X_(k,br)(0)) = J_(br,k)`
(`thickGen_add_left`, `braidMatrix_thickGen_add_right`, induction on `r` with the recursion of
`rjAxisWord`); the profile projectors are `f_b^{⊗ r} ⊗ f_k` (`rjColsProj`, `jwAt_eq_skPlace`);
reorder the projectors (they commute with `J`, N2) and conjugate `c_r · FT_r` to `FT_r · c_r`
(`rj_colorTrace_append_comm`). End: unfold; the word alternates `X_(b,k)(0)`, `X_(k,b)(0)`.
Estimate 150–220 lines.
-/

noncomputable section

namespace AJConjecture

/-- The offsets of a profile that is constant below `m`. -/
private theorem rj_profileOffset_of_const_ends (κ : ℕ → ℕ) (b m : ℕ) (h : ∀ x < m, κ x = b) :
    profileOffset κ m = b * m := by
  rw [profileOffset, Finset.sum_congr rfl fun x hx ↦ h x (Finset.mem_range.mp hx),
    Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- Swapping the same two columns twice restores the profile. -/
private theorem rj_profileSwap_profileSwap_ends (κ : ℕ → ℕ) (i : ℕ) :
    profileSwap (profileSwap κ i) i = κ := by
  funext x
  simp only [profileSwap, Equiv.swap_apply_self]

/-- The full twist of the last strand around the others does not permute the columns. -/
private theorem rj_profileEnd_axisWord_ends (m : ℕ) (κ : ℕ → ℕ) :
    profileEnd κ (rjAxisWord m) = κ := by
  induction m generalizing κ with
  | zero => rfl
  | succ m ih =>
    rw [rjAxisWord, profileEnd, rj_profileEnd_append, ih, profileEnd, profileEnd,
      rj_profileSwap_profileSwap_ends]

/-- The profile cable of the axis word is the full twist of the bundle of the first `m` columns
with the axis bundle. -/
private theorem rj_braidMatrix_axisWord_ends (N b k m : ℕ) (κ : ℕ → ℕ) (hb : ∀ x < m, κ x = b)
    (hk : κ m = k) :
    braidMatrix N (thickCable κ (rjAxisWord m)) =
      braidMatrix N (thickCross (b * m) k 0 true) *
        braidMatrix N (thickCross k (b * m) 0 true) := by
  induction m generalizing κ with
  | zero =>
    have h1 : thickCross 0 k 0 true = [] := rfl
    have h2 : thickCross k 0 0 true = [] := by
      simp [thickCross, thickGen]
    rw [rjAxisWord, thickCable, Nat.mul_zero, h1, h2, braidMatrix_nil, Matrix.one_mul]
  | succ m ih =>
    have hm : κ m = b := hb m (by omega)
    have hoff : profileOffset κ m = b * m :=
      rj_profileOffset_of_const_ends κ b m fun x hx ↦ hb x (by omega)
    have ih' := ih (profileSwap κ m) (fun x hx ↦ by
      rw [profileSwap, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      exact hb x (by omega)) (by rw [profileSwap, Equiv.swap_apply_left, hk])
    have hoff' : profileOffset (profileSwap κ m) m = b * m := by
      rw [rj_profileOffset_profileSwap_of_le κ m m le_rfl, hoff]
    rw [rjAxisWord, thickCable, rj_thickCable_append, rj_profileEnd_axisWord_ends, thickCable,
      thickCable, List.append_nil]
    simp only [braidMatrix_append]
    rw [ih', hm, hk, hoff, hoff']
    simp only [profileSwap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [hk, hm, Nat.mul_succ]
    simp only [thickCross, ite_true]
    rw [thickGen_add_left, braidMatrix_append, braidMatrix_thickGen_add_right, Nat.zero_add]
    simp only [Matrix.mul_assoc]

/-- The column projectors are the profile projectors of a profile constant below `r`. -/
private theorem rj_colsProj_eq_profileProj_ends (b r : ℕ) (κ : ℕ → ℕ)
    (h : ∀ x < r, κ x = b) : rjColsProj b r = rjProfileProj (b * r) κ r := by
  unfold rjColsProj rjProfileProj
  congr 1
  refine List.map_congr_left fun x hx ↦ ?_
  rw [List.mem_range] at hx
  rw [rj_profileOffset_of_const_ends κ b x fun y hy ↦ h y (by omega), h x hx]

/-- The cyclic word is a word on `r` strands. -/
private theorem rj_isOnStrands_cycleWord_ends (r : ℕ) : IsOnStrands r (rjCycleWord r) :=
  fun g hg ↦ by
    simp only [rjCycleWord, List.mem_map, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    simp only
    omega

set_option linter.unusedVariables false in
/-- The start of the isotopy. -/
theorem rj_colorTrace_start (b k r : ℕ) (hr : 1 ≤ r) :
    qtr (b * r + k) (skPlace (b * r + k) (b * r + k) 0 (rjCycleMat b r * rjColsProj b r) *
        rjFullTwist (b * r) k * jwAt (b * r + k) (b * r) k) =
      rjColorTrace (rjAxisProfile b k r) (r + 1) (rjBetaWord r 0) := by
  set κ := rjAxisProfile b k r with hκ
  have hb : ∀ x < r, κ x = b := fun x hx ↦ by simp [hκ, rjAxisProfile, hx]
  have hk : κ r = k := by simp only [hκ, rjAxisProfile, lt_irrefl, ite_false]
  have hoffr : profileOffset κ r = b * r := rj_profileOffset_of_const_ends κ b r hb
  have hN : profileOffset κ (r + 1) = b * r + k := by
    rw [rj_profileOffset_succ, hoffr, hk]
  have hcw := rj_isOnStrands_cycleWord_ends r
  have hword : rjBetaWord r 0 = rjAxisWord r ++ rjCycleWord r := by
    simp only [rjBetaWord, Nat.mul_zero, List.replicate_zero, List.nil_append]
  unfold rjColorTrace
  rw [hword, hN, rj_thickCable_append, rj_profileEnd_axisWord_ends, braidMatrix_append,
    rj_braidMatrix_axisWord_ends _ b k r κ hb hk,
    rj_braidMatrix_thickCable_eq_skPlace (b * r + k) (b * r) κ r _ hcw hoffr.le (by omega),
    thickCable_congr r κ (fun _ ↦ b) _ hcw hb, thickCable_const, rj_profileProj_succ, hk, hoffr,
    rj_profileProj_eq_skPlace_zero (b * r + k) (b * r) κ r hoffr.le (by omega),
    ← rj_colsProj_eq_profileProj_ends b r κ hb, ← rjCycleMat,
    skPlace_mul _ _ _ 0 _ _ (by omega) rfl rfl, ← braidMatrix_append]
  set J := braidMatrix (b * r + k) (thickCross (b * r) k 0 true ++ thickCross k (b * r) 0 true)
    with hJ
  set F := jwAt (b * r + k) (b * r) k with hF
  have e1 := jwAt_mul_braidMatrix_thickCross_snd (b * r + k) (b * r) k 0 true (by omega)
  have e2 := jwAt_mul_braidMatrix_thickCross_fst (b * r + k) k (b * r) 0 true (by omega)
  rw [Nat.zero_add] at e1 e2
  have hFJ : F * J = J * F := by
    rw [hF, hJ, braidMatrix_append, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, e2,
      Matrix.mul_assoc]
  have hrfl : rjFullTwist (b * r) k = J := rfl
  rw [hrfl]
  simp only [Matrix.mul_assoc]
  rw [qtr_mul_comm_of_weight _ _ J _ (skWeight_mul_braidMatrix _ _)]
  simp only [Matrix.mul_assoc]
  rw [hFJ]

/-- The profile cable of an even power of the first generator, with the profile `(b, k)`. -/
private theorem rj_braidMatrix_replicate_ends (b k q : ℕ) :
    braidMatrix (b + k) (thickCable (rjAxisProfile b k 1) (List.replicate (2 * q) (0, true))) =
      rjFullTwist b k ^ q := by
  induction q with
  | zero => rw [Nat.mul_zero, List.replicate_zero, thickCable, braidMatrix_nil, pow_zero]
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, List.replicate_succ, List.replicate_succ,
      thickCable, thickCable]
    simp only
    rw [rj_profileSwap_profileSwap_ends, braidMatrix_append, braidMatrix_append, ih, pow_succ',
      rjFullTwist, braidMatrix_append, Matrix.mul_assoc]
    simp [profileSwap, rjAxisProfile, profileOffset]

/-- The end of the isotopy: the coloured torus link `T(2, 2(p+1))`. -/
theorem rj_colorTrace_end (b k p : ℕ) :
    rjColorTrace (rjAxisProfile b k 1) 2 (rjBetaWord 1 p) =
      qtr (b + k) (rjFullTwist b k ^ (p + 1) * rjBundleProj b k) := by
  have hword : rjBetaWord 1 p = List.replicate (2 * (p + 1)) (0, true) := by
    rw [rjBetaWord]
    simp only [rjAxisWord, rjCycleWord, Nat.sub_self, List.range_zero, List.map_nil,
      List.append_nil, List.nil_append]
    rw [show 2 * (p + 1) = 2 * p + 2 by ring, List.replicate_add]
    rfl
  have hN : profileOffset (rjAxisProfile b k 1) 2 = b + k := by
    simp [profileOffset, Finset.sum_range_succ, rjAxisProfile]
  have hP : rjProfileProj (b + k) (rjAxisProfile b k 1) 2 = rjBundleProj b k := by
    simp [rjProfileProj, List.range_succ, rjAxisProfile, profileOffset, rjBundleProj]
  unfold rjColorTrace
  rw [hword, hN, rj_braidMatrix_replicate_ends, hP]

end AJConjecture
