import Mathlib
import AJConjecture.SkeinThickCupAdd
import AJConjecture.SkeinTurnbackBasic

/-!
# Nests of caps composed with fusion maps

A nest of `k` caps on two bundles of `n + m + k` strands followed by the fusion map `π` of two
bundles of `n + m` strands is the fusion map of the larger bundles: the projectors on the
strands that are left are absorbed (`AJConjecture.twoBundleProj_mul_capThick_mul_twoBundleProj`)
and the two nests compose (`AJConjecture.capThick_add`, placed with `AJConjecture.skPlace_mul` and
`AJConjecture.skPlace_skPlace`). The mirror statement holds for `ι`. In the same way the turnback
element `D_m` of two bundles of `n + m` strands is the nest of `m` caps followed by the nest of
`m` cups, each with `f ⊗ f` (`AJConjecture.twoBundleProj_mul_self`, and `(n + m) - m = n`).
Sizes are written `n + (m + k)` so that no cast is needed.
-/

namespace AJConjecture

/-- Nested caps below `f ⊗ f` absorb the projectors on the strands that are left, with a free
bundle size. -/
private theorem twoBundleProj_mul_capThick_mul_twoBundleProj_fusionNest (N a k : ℕ)
    (hN : N = a + k) :
    twoBundleProj N * skPlace (2 * N) (2 * a) a (capThick k) * twoBundleProj a =
      twoBundleProj N * skPlace (2 * N) (2 * a) a (capThick k) := by
  subst hN
  exact twoBundleProj_mul_capThick_mul_twoBundleProj a k

/-- A nest of caps followed by a fusion map `π` is the fusion map of the larger bundles. -/
theorem twoBundleProj_mul_capThick_mul_fusionProj (n m k : ℕ) :
    twoBundleProj (n + (m + k)) *
        skPlace (2 * (n + (m + k))) (2 * (n + m)) (n + m) (capThick k) * fusionProj n m =
      fusionProj n (m + k) := by
  rw [fusionProj, fusionProj, capThick_add m k,
    skPlace_mul (2 * (n + (m + k))) (2 * (n + m)) (2 * n) n _ (capThick m) (by omega) (by omega)
      (by omega),
    skPlace_skPlace (2 * (n + (m + k))) (2 * (n + m)) n m (capThick k) (by omega) (by omega)
      (by omega) (by omega),
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    twoBundleProj_mul_capThick_mul_twoBundleProj_fusionNest (n + (m + k)) (n + m) k (by omega)]

/-- The turnback element `D_m` is a nest of caps followed by a nest of cups. -/
theorem turnback_eq_capThick_mul_cupThick (n m : ℕ) :
    turnback (n + m) m =
      twoBundleProj (n + m) * skPlace (2 * (n + m)) (2 * n) n (capThick m) *
        (skPlace (2 * n) (2 * (n + m)) n (cupThick m) * twoBundleProj (n + m)) := by
  rw [turnback, Nat.add_sub_cancel,
    skPlace_mul (2 * (n + m)) (2 * n) (2 * (n + m)) n (capThick m) (cupThick m) (by omega)
      (by omega) (by omega)]
  simp only [Matrix.mul_assoc]

end AJConjecture
