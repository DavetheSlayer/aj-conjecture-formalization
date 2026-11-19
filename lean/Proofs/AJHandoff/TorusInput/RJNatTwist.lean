import Mathlib
import AJHandoff.TorusInput.RJNatClosure
import AJHandoff.TorusInput.RJNatGen
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinPtrTailCyclic
import AJConjecture.SkeinPtrTailPlace
import AJConjecture.SkeinTracePairing

/-!
# Naturality of the axis loop (node RN3)

A natural map commutes with the axis loop: `Ω^{(m)} X = X Ω^{(n)}` for `X : m → n` natural, and
more generally for any loop operator `rjLoopWith`.

Route. By `ptrTail_eq_cupThick_capThick`, `rjLoopWith m k Y` is
`cups(k) · (J_(m,k) · (1_m ⊗ Y)) · caps(k)` on the right of the bundle. `X ⊗ 1_k` slides through
`J_(m,k)` (`RJNat`), commutes with `1_m ⊗ Y` (interchange, `skPlace_mul_skPlace_comm`), and passes
the cups and caps on the right (interchange). Alternatively test against every `G`
(`eq_of_forall_qtr_mul_eq`, `qtr_eq_qtr_ptrTail`, `ptrTail_mul_skPlace`) and use cyclicity
(`qtr_mul_comm_of_weight`). Estimate 80–140 lines.
-/

noncomputable section

namespace AJConjecture

/-- A natural map slides through any loop encircling its bundle. -/
theorem rjLoopWith_mul_of_rjNat {m n : ℕ} (k : ℕ) (Y : SkMat k k) {X : SkMat m n}
    (hX : RJNat X) : rjLoopWith m k Y * X = X * rjLoopWith n k Y := by
  have hcap : skPlace (m + 2 * k) m m (capThick k) * X =
      skPlace (m + 2 * k) (n + 2 * k) 0 X * skPlace (n + 2 * k) n n (capThick k) := by
    have h := skPlace_mul_skPlace_comm (m + 2 * k) (n + 2 * k) m n 0 m X (capThick k)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show m + n - m = n from by omega, skPlace_self] at h
    exact h.symm
  have hcup : X * skPlace n (n + 2 * k) n (cupThick k) =
      skPlace m (m + 2 * k) m (cupThick k) * skPlace (m + 2 * k) (n + 2 * k) 0 X := by
    have h := skPlace_mul_skPlace_comm m n (m + 2 * k) (n + 2 * k) 0 m X (cupThick k)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show m + n - m = n from by omega, skPlace_self] at h
    exact h
  have hY : skPlace (m + k) (m + k) m Y * skPlace (m + k) (n + k) 0 X =
      skPlace (m + k) (n + k) 0 X * skPlace (n + k) (n + k) n Y := by
    have h := skPlace_mul_skPlace_comm (m + k) (n + k) (m + k) (n + k) 0 m X Y
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show m + n - m = n from by omega] at h
    exact h.symm
  have hA : rjFullTwist m k * skPlace (m + k) (m + k) m Y * skPlace (m + k) (n + k) 0 X =
      skPlace (m + k) (n + k) 0 X * (rjFullTwist n k * skPlace (n + k) (n + k) n Y) := by
    rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX.2 k, Matrix.mul_assoc]
  have hmid : skPlace (m + 2 * k) (m + 2 * k) 0
        (rjFullTwist m k * skPlace (m + k) (m + k) m Y) * skPlace (m + 2 * k) (n + 2 * k) 0 X =
      skPlace (m + 2 * k) (n + 2 * k) 0 X *
        skPlace (n + 2 * k) (n + 2 * k) 0 (rjFullTwist n k * skPlace (n + k) (n + k) n Y) := by
    have h := congrArg (skPlace (m + 2 * k) (n + 2 * k) 0) hA
    rw [skPlace_mul (m + 2 * k) (m + 2 * k) (n + 2 * k) 0 _ _ (by omega) (by omega) (by omega),
      skPlace_mul (m + 2 * k) (n + 2 * k) (n + 2 * k) 0 _ _ (by omega) (by omega) (by omega),
      skPlace_skPlace (m + 2 * k) (n + 2 * k) 0 0 X (by omega) (by omega) (by omega)
        (by omega)] at h
    exact h
  rw [rjLoopWith, rjLoopWith, ptrTail_eq_cupThick_capThick, ptrTail_eq_cupThick_capThick,
    Matrix.mul_assoc, hcap, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _
      (skPlace (m + 2 * k) (n + 2 * k) 0 X), hmid, ← Matrix.mul_assoc, ← hcup]
  simp only [Matrix.mul_assoc]

/-- A natural map slides through the axis loop. -/
theorem rjAxisLoop_mul_of_rjNat {m n : ℕ} (k : ℕ) {X : SkMat m n} (hX : RJNat X) :
    rjAxisLoop m k * X = X * rjAxisLoop n k :=
  rjLoopWith_mul_of_rjNat k (jwAt k 0 k) hX

end AJConjecture
