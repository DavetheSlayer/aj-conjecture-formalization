import Mathlib
import AJConjecture.SkeinCableNatural
import AJConjecture.SkeinCableOrbit
import AJConjecture.SkeinKnotTraceBasic
import AJConjecture.SkeinTracePairing

/-!
# The long knot commutes with the Temperley–Lieb generators

A generator `e_j` on two strands of the first bundle slides along the cabled braid without
changing the thickness (`AJConjecture.tlGenF_mul_braidMatrix_cable`), so
`AJConjecture.qtr_cable_orbit` applies with `X p = e_{k p + j}` and `Z = Y ⊗ 1`
(`AJConjecture.skPlace_mul_skPlace_comm`: `e_{k p + j}` and `Y ⊗ 1` are on disjoint windows for
`p ≠ 0`): `Tr_{K,k}(e_j Y) = Tr_{K,k}(Y e_j)`. For `k ≤ j + 1` both sides vanish. The operator form
follows from `AJConjecture.knotTrace_eq_qtr_longKnotOp`, the cyclicity of the trace and
`AJConjecture.eq_of_forall_qtr_mul_eq`. No cup is needed here.
-/

namespace AJConjecture

/-- A generator on the first bundle is a generator of the whole diagram. -/
private theorem skPlace_tlGenF_longKnotTl (n k j : ℕ) (hk : k ≤ n) (hj : j + 1 < k) :
    skPlace n n 0 (tlGenF k j) = tlGenF n (k * 0 + j) := by
  rw [tlGenF_eq_skPlace k j, skPlace_skPlace n n 0 j (tlGenF 2 0) (by omega) (by omega)
    (by omega) (by omega), tlGenF_eq_skPlace n (k * 0 + j), Nat.mul_zero]

/-- A generator on a bundle other than the first commutes with an operator on the first
bundle. -/
private theorem tlGenF_mul_skPlace_comm_longKnotTl (n k i : ℕ) (Y : SkMat k k) (hi : k ≤ i)
    (hn : i + 2 ≤ n) :
    tlGenF n i * skPlace n n 0 Y = skPlace n n 0 Y * tlGenF n i := by
  have h := skPlace_mul_skPlace_comm n n n n 0 i Y (tlGenF 2 0) (by omega) hn (by omega)
    (by omega) (by omega)
  rw [show i + k - k = i from by omega] at h
  rw [tlGenF_eq_skPlace n i]
  exact h.symm

/-- The knot trace is cyclic with respect to the generators on the first bundle. -/
theorem knotTrace_tlGenF_mul (K : BraidKnot) (k j : ℕ) (Y : SkMat k k) :
    knotTrace K k (tlGenF k j * Y) = knotTrace K k (Y * tlGenF k j) := by
  rcases Nat.lt_or_ge (j + 1) k with hj | hj
  · have hk : k ≤ k * K.strands := Nat.le_mul_of_pos_right _ K.strands_pos
    have horbit := qtr_cable_orbit K k (fun p ↦ tlGenF (k * K.strands) (k * p + j))
      (skPlace (k * K.strands) (k * K.strands) 0 Y)
      (fun p hp ↦ tlGenF_mul_braidMatrix_cable K.strands k K.word p j K.isOnStrands hp hj)
      (fun p _ ↦ skWeight_mul_tlGenF _ _)
      (fun p hp hp0 ↦ by
        have h1 : k * 1 ≤ k * p := Nat.mul_le_mul_left k (by omega)
        have h2 : k * (p + 1) ≤ k * K.strands := Nat.mul_le_mul_left k hp
        rw [Nat.mul_succ] at h2
        exact tlGenF_mul_skPlace_comm_longKnotTl _ k _ Y (by omega) (by omega))
    rw [knotTrace, knotTrace, skPlace_mul _ _ _ 0 (tlGenF k j) Y (by omega) rfl rfl,
      skPlace_mul _ _ _ 0 Y (tlGenF k j) (by omega) rfl rfl,
      skPlace_tlGenF_longKnotTl _ k j hk hj]
    exact horbit
  · rw [tlGenF_eq_zero k j hj, Matrix.zero_mul, Matrix.mul_zero]

/-- The long knot commutes with the Temperley–Lieb generators. -/
theorem longKnotOp_commute_tlGenF (K : BraidKnot) (k j : ℕ) :
    Commute (longKnotOp K k) (tlGenF k j) := by
  refine eq_of_forall_qtr_mul_eq k k _ _ fun G ↦ ?_
  rw [Matrix.mul_assoc, ← knotTrace_eq_qtr_longKnotOp, knotTrace_tlGenF_mul,
    knotTrace_eq_qtr_longKnotOp, ← Matrix.mul_assoc,
    ← qtr_mul_comm_of_weight k k (tlGenF k j) (longKnotOp K k * G) (skWeight_mul_tlGenF k j),
    Matrix.mul_assoc]

end AJConjecture
