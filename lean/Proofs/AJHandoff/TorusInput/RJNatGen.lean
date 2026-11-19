import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinJwThickCross
import AJConjecture.SkeinThickCrossTl
import AJConjecture.SkeinThickCrossCap
import AJConjecture.SkeinThickCrossCup
import AJConjecture.SkeinThickCrossBraid
import AJConjecture.SkeinThickCupInner
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinWeightPlace
import AJConjecture.SkeinTraceCyclic
import AJConjecture.SkeinBubble
import AJHandoff.TorusInput.RJNatClosure
import AJConjecture.SkeinThickCup
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinTranspose

/-!
# Naturality: the generators (node RN2)

Projectors on a window inside the bundle, nested caps and cups inside the bundle, and braids on
the bundle are natural (`RJNat`).

Route. Write `J_(m,k) = ρ(X_(m,k)(0)) ρ(X_(k,m)(0))`.
* Projector `f^{(m)}_(i,l)` (`i + l ≤ m`): it passes `X_(m,k)(0)` to the window `k + i` and back
  through `X_(k,m)(0)` to `i`: the generators inside the moving bundle slide
  (`tlGenF_mul_braidMatrix_thickCross_fst`, `_snd`), then the transport principle
  (`jwAt_mul_eq_mul_jwAt`, `commute_jwAt_of_commute_tlGenF`); the projector placed in the bigger
  space is `jwAt_eq_skPlace`.
* Nested caps `skPlace m n p (capThick j)` with `p + 2j ≤ m`, `m = n + 2j`: peel the nest one cap
  at a time (`capThick_succ_inner`, `skPlace_skPlace`); each cap passes the two crossings by (N3)
  `capAt_mul_braidMatrix_thickCross_fst`, `_snd`, which change the thickness of the moving
  bundle by `2`. Cups: (N4) `braidMatrix_thickCross_mul_cupAt_fst`, `_snd`, or transpose the cap
  statement (`rjNat_transpose`, `cupAt_eq_smul_transpose_capAt`).
* Braid words on `m` strands: `braidMatrix_mul_thickCross_fst`, `_snd` (N2).
* Weights: `skWeight_mul_jwAt`, `skWeight_mul_capThick`, `skWeight_mul_braidMatrix`,
  `skWeight_mul_skPlace`.
Estimate 180–250 lines.
-/

noncomputable section

namespace AJConjecture

/-- The full twist as the product of its two thick crossings. -/
private theorem rj_fullTwist_eq_mul_natGen (a b : ℕ) :
    rjFullTwist a b = braidMatrix (a + b) (thickCross a b 0 true) *
      braidMatrix (a + b) (thickCross b a 0 true) := by
  rw [rjFullTwist, braidMatrix_append]

/-- A projector on a window inside the bundle is natural. -/
theorem rjNat_jwAt (m i l : ℕ) (h : i + l ≤ m) : RJNat (jwAt m i l) := by
  refine ⟨skWeight_mul_jwAt m i l, fun k ↦ ?_⟩
  have hP : skPlace (m + k) (m + k) 0 (jwAt m i l) = jwAt (m + k) i l := by
    rw [jwAt_eq_skPlace m i l h, skPlace_skPlace (m + k) (m + k) 0 i _ (by omega) rfl
      (by omega) rfl, Nat.zero_add, jwAt_eq_skPlace (m + k) i l (by omega)]
  have h1 : jwAt (m + k) i l * braidMatrix (m + k) (thickCross m k 0 true) =
      braidMatrix (m + k) (thickCross m k 0 true) * jwAt (m + k) (k + i) l :=
    jwAt_mul_eq_mul_jwAt _ _ _ _ _ l fun l' hl' ↦ by
      have e := tlGenF_mul_braidMatrix_thickCross_fst (m + k) m k 0 (i + l') true (by omega)
        (by omega)
      rwa [Nat.zero_add, Nat.zero_add, ← Nat.add_assoc] at e
  have h2 : jwAt (m + k) (k + i) l * braidMatrix (m + k) (thickCross k m 0 true) =
      braidMatrix (m + k) (thickCross k m 0 true) * jwAt (m + k) i l :=
    jwAt_mul_eq_mul_jwAt _ _ _ _ _ l fun l' hl' ↦ by
      have e := tlGenF_mul_braidMatrix_thickCross_snd (m + k) k m 0 (i + l') true
        (by omega) (by omega)
      rwa [Nat.zero_add, Nat.zero_add, ← Nat.add_assoc] at e
  rw [hP, rj_fullTwist_eq_mul_natGen, Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, ← h1,
    Matrix.mul_assoc]

/-- A cap on the first bundle slides through a thick crossing at `0` (free sizes). -/
private theorem rj_cap_slide_fst_natGen (N M a b A j : ℕ) (s : Bool) (hM : M = N + 2)
    (hA : A = a + 2) (hn : a + b ≤ N) (hj : j ≤ a) :
    skPlace M N j skCap * braidMatrix N (thickCross a b 0 s) =
      braidMatrix M (thickCross A b 0 s) * skPlace M N (b + j) skCap := by
  subst hM hA
  have e := capAt_mul_braidMatrix_thickCross_fst N a b 0 j s (by omega) hj
  rw [Nat.zero_add, Nat.zero_add] at e
  exact e

/-- A cap on the second bundle slides through a thick crossing at `0` (free sizes). -/
private theorem rj_cap_slide_snd_natGen (N M a b B j : ℕ) (s : Bool) (hM : M = N + 2)
    (hB : B = b + 2) (hn : a + b ≤ N) (hj : j ≤ b) :
    skPlace M N (a + j) skCap * braidMatrix N (thickCross a b 0 s) =
      braidMatrix M (thickCross a B 0 s) * skPlace M N j skCap := by
  subst hM hB
  have e := capAt_mul_braidMatrix_thickCross_snd N a b 0 j s (by omega) hj
  rw [Nat.zero_add, Nat.zero_add] at e
  exact e

/-- A single cap inside the bundle is natural. -/
private theorem rjNat_skCap_natGen (m n p : ℕ) (hm : m = n + 2) (hp : p ≤ n) :
    RJNat (skPlace m n p skCap) := by
  subst hm
  refine ⟨skWeight_mul_skPlace _ _ _ _ skWeight_mul_skCap, fun k ↦ ?_⟩
  have hP : skPlace (n + 2 + k) (n + k) 0 (skPlace (n + 2) n p skCap) =
      skPlace (n + 2 + k) (n + k) p skCap := by
    rw [skPlace_skPlace (n + 2 + k) (n + k) 0 p skCap (k' := n + 2) (l' := n) (by omega) rfl
      (by omega) (by omega),
      Nat.zero_add]
  have h1 := rj_cap_slide_fst_natGen (n + k) (n + 2 + k) n k (n + 2) p true (by omega) rfl
    le_rfl hp
  have h2 := rj_cap_slide_snd_natGen (n + k) (n + 2 + k) k n (n + 2) p true (by omega) rfl
    (by omega) hp
  rw [hP, rj_fullTwist_eq_mul_natGen, rj_fullTwist_eq_mul_natGen, Matrix.mul_assoc, ← h2,
    ← Matrix.mul_assoc, ← h1, Matrix.mul_assoc]

/-- A nest of caps with free source size is natural. -/
private theorem rjNat_capThick_aux_natGen (j : ℕ) :
    ∀ n p M : ℕ, p ≤ n → M = n + 2 * j → RJNat (skPlace M n p (capThick j)) := by
  induction j with
  | zero =>
    intro n p M hp hM
    obtain rfl : M = n := by omega
    rw [show skPlace M M p (capThick 0) = 1 from by
      rw [capThick_zero]
      exact skPlace_one M p 0 (by omega)]
    exact rjNat_one _
  | succ j ih =>
    intro n p M hp hM
    rw [skPlace_capThick_succ M n p j (by omega) hM]
    exact rjNat_mul (ih (n + 2) (p + 1) M (by omega) (by omega))
      (rjNat_skCap_natGen (n + 2) n p rfl hp)

/-- A nest of `j` caps inside the bundle, at the position `p`, is natural. -/
theorem rjNat_capThick (n p j : ℕ) (h : p ≤ n) :
    RJNat (skPlace (n + 2 * j) n p (capThick j)) :=
  rjNat_capThick_aux_natGen j n p _ h rfl

/-- The entries of the cup are `-t²` times the entries of the cap. -/
private theorem rj_cupEntry_eq_mul_capEntry_natGen (a b : Bool) :
    cupEntry a b = -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) * capEntry a b := by
  cases a <;> cases b
  · simp only [cupEntry, capEntry, mul_zero]
  · simp only [cupEntry, capEntry, mul_one]
  · simp only [cupEntry, capEntry]
    rw [neg_mul_neg, ← zpow_add₀ RatFunc.X_ne_zero]
    norm_num
  · simp only [cupEntry, capEntry, mul_zero]

/-- The thick cup is a multiple of the transpose of the thick cap. -/
private theorem rj_cupThick_eq_smul_transpose_natGen (m : ℕ) :
    cupThick m = (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)) ^ m • (capThick m).transpose := by
  ext a b
  simp only [cupThick, capThick, Matrix.of_apply, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, rj_cupEntry_eq_mul_capEntry_natGen, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- A nest of `j` cups inside the bundle, at the position `p`, is natural. -/
theorem rjNat_cupThick (n p j : ℕ) (h : p ≤ n) :
    RJNat (skPlace n (n + 2 * j) p (cupThick j)) := by
  rw [rj_cupThick_eq_smul_transpose_natGen, skPlace_smul, ← skPlace_transpose]
  exact rjNat_smul _ (rjNat_transpose (rjNat_capThick n p j h))

/-- A braid on the bundle is natural. -/
theorem rjNat_braidMatrix (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) :
    RJNat (braidMatrix m w) := by
  refine ⟨skWeight_mul_braidMatrix m w, fun k ↦ ?_⟩
  have hP : skPlace (m + k) (m + k) 0 (braidMatrix m w) =
      braidMatrix (m + k) (w.map fun g ↦ (g.1 + 0, g.2)) :=
    (braidMatrix_map_add_eq_skPlace m (m + k) 0 w hw (by omega)).symm
  have h1 := braidMatrix_mul_thickCross_fst (m + k) m k 0 true w (by omega) hw
  have h2 := braidMatrix_mul_thickCross_snd (m + k) k m 0 true w (by omega) hw
  rw [Nat.zero_add] at h1 h2
  rw [hP, rj_fullTwist_eq_mul_natGen, Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, ← h1,
    Matrix.mul_assoc]

end AJConjecture
