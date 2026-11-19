import Mathlib
import AJConjecture.SkeinBubble
import AJConjecture.SkeinCableNatural
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinJwWeight
import AJConjecture.SkeinLapCol
import AJConjecture.SkeinLongKnot

/-!
# One projector on a cabled knot is a projector on every bundle

Let `F` commute with the projectors `f_c` of all the columns of the `c`-cable. Then
`v(x) = qtr(ρ F f_x)` does not depend on the column `x`: the projector slides along the braid
(`AJConjecture.jwAt_mul_braidMatrix_cable`), so
`v(strandEnd w x) = qtr(ρ f_{strandEnd w x} F) = qtr(f_x ρ F) = qtr(ρ F f_x) = v(x)` by the
cyclicity of the trace (`AJConjecture.skWeight_mul_jwAt`), and the columns `lapCol w ℓ` are all
the columns (`AJConjecture.lapCol_eq_iff`). Consequently the knot trace of `f_c` equals the cabled
bracket
with `f_c` inserted on any list of columns: projectors of different columns commute, and
`f_x f_x = f_x`.
-/

namespace AJConjecture

/-- The projectors of two columns commute. -/
private theorem jwAt_col_commute_jwCols (n c x y : ℕ) :
    Commute (jwAt n (c * x) c) (jwAt n (c * y) c) := by
  rcases lt_trichotomy x y with h | rfl | h
  · refine commute_jwAt_of_commute_tlGenF n (c * y) _ c fun l _ ↦ ?_
    refine jwAt_commute_tlGenF n (c * x) c (c * y + l) (Or.inr ?_)
    have := Nat.mul_le_mul_left c (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this
    omega
  · exact Commute.refl _
  · refine commute_jwAt_of_commute_tlGenF n (c * y) _ c fun l hl ↦ ?_
    refine jwAt_commute_tlGenF n (c * x) c (c * y + l) (Or.inl ?_)
    have := Nat.mul_le_mul_left c (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this
    omega

/-- A product of projectors of columns commutes with the projector of any column. -/
private theorem prod_jwAt_col_commute_jwCols (n c x : ℕ) (ps : List ℕ) :
    Commute (ps.map fun p ↦ jwAt n (c * p) c).prod (jwAt n (c * x) c) := by
  induction ps with
  | nil => exact Commute.one_left _
  | cons p ps ih =>
    rw [List.map_cons, List.prod_cons]
    exact (jwAt_col_commute_jwCols n c p x).mul_left ih

/-- Under the trace, the projector moves from the column of the cap after `ℓ` laps to the next
one. -/
private theorem qtr_cable_mul_jwAt_lapCol_succ_jwCols (K : BraidKnot) (c : ℕ)
    (F : SkMat (c * K.strands) (c * K.strands))
    (hF : ∀ x < K.strands, Commute F (jwAt (c * K.strands) (c * x) c)) (ℓ : ℕ) :
    qtr (c * K.strands) (braidMatrix (c * K.strands) (cable c K.word) *
        (F * jwAt (c * K.strands) (c * lapCol K.word ℓ) c)) =
      qtr (c * K.strands) (braidMatrix (c * K.strands) (cable c K.word) *
        (F * jwAt (c * K.strands) (c * lapCol K.word (ℓ + 1)) c)) := by
  have hs := jwAt_mul_braidMatrix_cable K.strands c K.word (lapCol K.word (ℓ + 1)) K.isOnStrands
    (lapCol_lt K (ℓ + 1))
  rw [strandEnd_lapCol_succ] at hs
  rw [(hF _ (lapCol_lt K ℓ)).eq, ← Matrix.mul_assoc, ← hs, Matrix.mul_assoc]
  exact qtr_mul_comm_of_weight _ _ _ _ (skWeight_mul_jwAt _ _ _) |>.trans
    (by rw [Matrix.mul_assoc])

/-- Under the trace, a projector on the bundle of the column `p` can be moved to the column `0`. -/
theorem qtr_cable_mul_jwAt_col (K : BraidKnot) (c p : ℕ) (hp : p < K.strands)
    (F : SkMat (c * K.strands) (c * K.strands))
    (hF : ∀ x < K.strands, Commute F (jwAt (c * K.strands) (c * x) c)) :
    qtr (c * K.strands) (braidMatrix (c * K.strands) (cable c K.word) *
        (F * jwAt (c * K.strands) (c * p) c)) =
      qtr (c * K.strands) (braidMatrix (c * K.strands) (cable c K.word) *
        (F * jwAt (c * K.strands) 0 c)) := by
  have hall : ∀ ℓ : ℕ, qtr (c * K.strands) (braidMatrix (c * K.strands) (cable c K.word) *
        (F * jwAt (c * K.strands) (c * lapCol K.word ℓ) c)) =
      qtr (c * K.strands) (braidMatrix (c * K.strands) (cable c K.word) *
        (F * jwAt (c * K.strands) 0 c)) := by
    intro ℓ
    induction ℓ with
    | zero => rw [show lapCol K.word 0 = 0 from rfl, Nat.mul_zero]
    | succ ℓ ih => rw [← qtr_cable_mul_jwAt_lapCol_succ_jwCols K c F hF ℓ, ih]
  obtain ⟨ℓ, hℓ⟩ := K.connected ⟨0, K.strands_pos⟩ ⟨p, hp⟩
  have hlap : lapCol K.word ℓ = p := by rw [lapCol_eq_strandPerm_pow, hℓ]
  rw [← hlap]
  exact hall ℓ

/-- The knot trace of `f_c` equals the cabled bracket with `f_c` on the bundle of the column `0`
and on the bundles of any list of columns. -/
theorem knotTrace_jwAt_eq_qtr_cols (K : BraidKnot) (c : ℕ) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p < K.strands) :
    knotTrace K c (jwAt c 0 c) =
      qtr (c * K.strands) (braidMatrix (c * K.strands) (cable c K.word) *
        (jwAt (c * K.strands) 0 c * (ps.map fun p ↦ jwAt (c * K.strands) (c * p) c).prod)) := by
  induction ps with
  | nil =>
    have hc : 0 + c ≤ c * K.strands := by
      have := Nat.mul_le_mul_left c K.strands_pos
      omega
    rw [List.map_nil, List.prod_nil, Matrix.mul_one, knotTrace, jwAt_eq_skPlace _ 0 c hc]
  | cons p ps ih =>
    have hp : p < K.strands := hps p List.mem_cons_self
    have h0 := jwAt_col_commute_jwCols (c * K.strands) c 0
    rw [Nat.mul_zero] at h0
    have hP := fun x ↦ prod_jwAt_col_commute_jwCols (c * K.strands) c x ps
    have hP0 := hP 0
    rw [Nat.mul_zero] at hP0
    have e1 : jwAt (c * K.strands) 0 c * (jwAt (c * K.strands) (c * p) c *
        (ps.map fun p ↦ jwAt (c * K.strands) (c * p) c).prod) =
        jwAt (c * K.strands) 0 c * (ps.map fun p ↦ jwAt (c * K.strands) (c * p) c).prod *
          jwAt (c * K.strands) (c * p) c := by
      rw [← (hP p).eq, Matrix.mul_assoc]
    have e2 : jwAt (c * K.strands) 0 c * (ps.map fun p ↦ jwAt (c * K.strands) (c * p) c).prod *
        jwAt (c * K.strands) 0 c =
        jwAt (c * K.strands) 0 c * (ps.map fun p ↦ jwAt (c * K.strands) (c * p) c).prod := by
      rw [Matrix.mul_assoc, hP0.eq, ← Matrix.mul_assoc, jwAt_mul_self]
    rw [ih fun q hq ↦ hps q (List.mem_cons_of_mem p hq), List.map_cons, List.prod_cons, e1,
      qtr_cable_mul_jwAt_col K c p hp _ fun x _ ↦ (h0 x).mul_left (hP x), e2]

end AJConjecture
