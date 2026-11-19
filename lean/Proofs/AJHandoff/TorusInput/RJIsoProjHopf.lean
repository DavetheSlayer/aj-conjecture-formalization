import Mathlib
import AJHandoff.TorusInput.RJSpectral
import AJHandoff.TorusInput.RJLoopHopf
import AJHandoff.TorusInput.RJNatTwist

/-!
# The axis loop on an isotypic part (node RA2.6)

`P_N Ω_k = h_k(N) P_N`: a loop coloured `f_k` around the `b r` strands acts on the isotypic part
of colour `N` by the Hopf scalar.

Route. `P_N = ∑_(N_x = N) π_x ι_x` (`rj_isoProj_eq_sum`, `rj_goodFamily_exists`);
`ι_x Ω^{(br)}_k = Ω^{(N)}_k ι_x` (`rjAxisLoop_mul_of_rjNat`, `ι_x` natural), and
`Ω^{(N)}_k f_N = h_k(N) f_N` (`rj_axisLoop_mul_jwAt`) with `f_N ι_x = ι_x`. Estimate 40–70
lines.
-/

noncomputable section

namespace AJConjecture

/-- The axis loop acts on the inclusion of a member of a good family by the Hopf scalar. -/
private theorem rj_incl_mul_axisLoop_isoProjHopf (b r k : ℕ) (L : List (RJFusionPair (b * r)))
    (hL : RJGoodFamily b r L) (x : RJFusionPair (b * r)) (hx : x ∈ L) :
    x.2.2 * rjAxisLoop (b * r) k = rjHopf x.1 k • x.2.2 := by
  have hfι := (hL.2 x hx).2.2.2.2.2.1
  rw [← rjAxisLoop_mul_of_rjNat k (hL.2 x hx).2.2.1, ← hfι, ← Matrix.mul_assoc,
    rj_axisLoop_mul_jwAt, Matrix.smul_mul]

/-- The axis loop on a partial sum of a good family of one colour. -/
private theorem rj_sum_mul_axisLoop_isoProjHopf (b r N k : ℕ) (L : List (RJFusionPair (b * r)))
    (hL : RJGoodFamily b r L) (L' : List (RJFusionPair (b * r))) (hL' : ∀ x ∈ L', x ∈ L) :
    ((L'.filter fun x ↦ x.1 = N).map fun x ↦ x.2.1 * x.2.2).sum * rjAxisLoop (b * r) k =
      rjHopf N k • ((L'.filter fun x ↦ x.1 = N).map fun x ↦ x.2.1 * x.2.2).sum := by
  induction L' with
  | nil => rw [List.filter_nil, List.map_nil, List.sum_nil, Matrix.zero_mul, smul_zero]
  | cons x L' ih =>
    have ih' := ih fun y hy ↦ hL' y (List.mem_cons_of_mem _ hy)
    rw [List.filter_cons]
    by_cases h : x.1 = N
    · simp only [decide_eq_true h, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [Matrix.add_mul, ih', smul_add, Matrix.mul_assoc,
        rj_incl_mul_axisLoop_isoProjHopf b r k L hL x (hL' x List.mem_cons_self),
        Matrix.mul_smul, ← h]
    · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      exact ih'

/-- The axis loop acts on the isotypic part of colour `N` by the Hopf scalar. -/
theorem rj_isoProj_mul_axisLoop (b r N k : ℕ) (hr : 1 ≤ r) (hN : N ∈ rjSpec b r) :
    rjIsoProj b r N * rjAxisLoop (b * r) k = rjHopf N k • rjIsoProj b r N := by
  obtain ⟨L, hL⟩ := rj_goodFamily_exists b r hr
  rw [rj_isoProj_eq_sum b r N L hL hN]
  exact rj_sum_mul_axisLoop_isoProjHopf b r N k L hL L fun x hx ↦ hx

end AJConjecture
