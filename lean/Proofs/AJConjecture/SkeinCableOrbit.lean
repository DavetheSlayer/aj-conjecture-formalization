import Mathlib
import AJConjecture.SkeinLapCol
import AJConjecture.SkeinTraceCyclic

/-!
# Transport of an operator around a cabled knot under the trace

Let `X p` be an operator attached to the column `p` of a cabled closed braid that slides along
the braid (`X p * ρ = ρ * X (strandEnd w p)`), intertwines the weight, and commutes with a fixed
operator `Z` unless `p = 0`. Then `qtr(ρ X_0 Z) = qtr(ρ Z X_0)`: with `q_ℓ = lapCol w ℓ`,
`qtr(ρ X_{q_ℓ} Z) = qtr(X_{q_{ℓ+1}} ρ Z) = qtr(ρ Z X_{q_{ℓ+1}})` by the sliding and the cyclicity of
the trace, and `Z X_{q_{ℓ+1}} = X_{q_{ℓ+1}} Z` as long as `q_{ℓ+1} ≠ 0`, that is for `ℓ + 1 < m`;
`q_m = 0` (`AJConjecture.lapCol_eq_iff`). Induction on the number of laps.
-/

namespace AJConjecture

/-- One lap: the operator on the column of the lap `ℓ`, before `Z`, becomes the operator on the
column of the lap `ℓ + 1`, after `Z`. -/
private theorem qtr_cable_orbit_lap (K : BraidKnot) (k : ℕ)
    (X : ℕ → SkMat (k * K.strands) (k * K.strands))
    (Z : SkMat (k * K.strands) (k * K.strands))
    (hslide : ∀ p < K.strands, X p * braidMatrix (k * K.strands) (cable k K.word) =
      braidMatrix (k * K.strands) (cable k K.word) * X (strandEnd K.word p))
    (hweight : ∀ p < K.strands,
      skWeight (k * K.strands) * X p = X p * skWeight (k * K.strands)) (ℓ : ℕ) :
    qtr (k * K.strands)
        (braidMatrix (k * K.strands) (cable k K.word) * (X (lapCol K.word ℓ) * Z)) =
      qtr (k * K.strands)
        (braidMatrix (k * K.strands) (cable k K.word) * (Z * X (lapCol K.word (ℓ + 1)))) := by
  have hs := hslide (lapCol K.word (ℓ + 1)) (lapCol_lt K (ℓ + 1))
  rw [strandEnd_lapCol_succ] at hs
  rw [← mul_assoc, ← hs, mul_assoc,
    qtr_mul_comm_of_weight _ _ _ _ (hweight _ (lapCol_lt K (ℓ + 1))), mul_assoc]

/-- An operator that slides along the cabled braid can be moved around the knot under the trace. -/
theorem qtr_cable_orbit (K : BraidKnot) (k : ℕ) (X : ℕ → SkMat (k * K.strands) (k * K.strands))
    (Z : SkMat (k * K.strands) (k * K.strands))
    (hslide : ∀ p < K.strands, X p * braidMatrix (k * K.strands) (cable k K.word) =
      braidMatrix (k * K.strands) (cable k K.word) * X (strandEnd K.word p))
    (hweight : ∀ p < K.strands,
      skWeight (k * K.strands) * X p = X p * skWeight (k * K.strands))
    (hZ : ∀ p < K.strands, p ≠ 0 → X p * Z = Z * X p) :
    qtr (k * K.strands) (braidMatrix (k * K.strands) (cable k K.word) * (X 0 * Z)) =
      qtr (k * K.strands) (braidMatrix (k * K.strands) (cable k K.word) * (Z * X 0)) := by
  have hlap := qtr_cable_orbit_lap K k X Z hslide hweight
  have hind : ∀ ℓ, ℓ < K.strands →
      qtr (k * K.strands) (braidMatrix (k * K.strands) (cable k K.word) * (X 0 * Z)) =
        qtr (k * K.strands)
          (braidMatrix (k * K.strands) (cable k K.word) * (X (lapCol K.word ℓ) * Z)) := by
    intro ℓ
    induction ℓ with
    | zero => exact fun _ ↦ rfl
    | succ ℓ ih =>
      intro hℓ
      have hne : lapCol K.word (ℓ + 1) ≠ 0 := by
        intro h0
        have hmod := (lapCol_eq_iff K (ℓ + 1) 0).mp h0
        rw [Nat.ModEq, Nat.mod_eq_of_lt hℓ, Nat.zero_mod] at hmod
        omega
      rw [ih (by omega), hlap ℓ, hZ _ (lapCol_lt K (ℓ + 1)) hne]
  obtain ⟨r, hr⟩ : ∃ r, K.strands = r + 1 := ⟨K.strands - 1, by have := K.strands_pos; omega⟩
  have hlast : lapCol K.word (r + 1) = 0 := by
    have h0 : lapCol K.word (r + 1) = lapCol K.word 0 := by
      rw [lapCol_eq_iff, ← hr, Nat.ModEq, Nat.mod_self, Nat.zero_mod]
    exact h0
  rw [hind r (by omega), hlap r, hlast]

end AJConjecture
