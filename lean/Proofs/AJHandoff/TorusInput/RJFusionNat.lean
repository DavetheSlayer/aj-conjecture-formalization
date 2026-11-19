import Mathlib
import AJHandoff.TorusInput.RJNatClosure
import AJHandoff.TorusInput.RJNatGen
import AJHandoff.TorusInput.RJFusionBasic

/-!
# The fusion maps are natural (node RA1.13)

`f_a ⊗ f_b`, `π_j` and `ι_j` are natural (`RJNat`).

Route. Products (`rjNat_mul`) of projectors on windows (`rjNat_jwAt`) and of the nest of caps,
resp. cups, in the middle (`rjNat_capThick`, `rjNat_cupThick`, after rewriting
`a + b = (a + b - 2j) + 2j` and `a - j ≤ a + b - 2j` by `omega`). Estimate 40–70 lines.
-/

noncomputable section

namespace AJConjecture

/-- `f_a ⊗ f_b` is natural. -/
theorem rjNat_bundleProj (a b : ℕ) : RJNat (rjBundleProj a b) :=
  rjNat_mul (rjNat_jwAt (a + b) 0 a (by omega)) (rjNat_jwAt (a + b) a b le_rfl)

/-- A nest of caps in the middle, in a dimension given by a hypothesis. -/
private theorem rjNat_capThick_of_eq_fusionNat (m p q j : ℕ) (hm : m = p + q + 2 * j) :
    RJNat (skPlace m (p + q) p (capThick j)) := by
  subst hm
  exact rjNat_capThick (p + q) p j (by omega)

/-- A nest of cups in the middle, in a dimension given by a hypothesis. -/
private theorem rjNat_cupThick_of_eq_fusionNat (m p q j : ℕ) (hm : m = p + q + 2 * j) :
    RJNat (skPlace (p + q) m p (cupThick j)) := by
  subst hm
  exact rjNat_cupThick (p + q) p j (by omega)

/-- The fusion map of a channel is natural. -/
theorem rjNat_fusionProj (a b j : ℕ) (hj : j ≤ min a b) : RJNat (rjFusionProj a b j) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = p + j := ⟨a - j, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = q + j := ⟨b - j, by omega⟩
  rw [rjFusionProj, show p + j + (q + j) - 2 * j = p + q from by omega,
    show p + j - j = p from by omega]
  exact rjNat_mul (rjNat_mul (rjNat_bundleProj _ _)
    (rjNat_capThick_of_eq_fusionNat _ p q j (by omega))) (rjNat_jwAt (p + q) 0 (p + q) (by omega))

/-- The fusion inclusion of a channel is natural. -/
theorem rjNat_fusionIncl (a b j : ℕ) (hj : j ≤ min a b) : RJNat (rjFusionIncl a b j) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = p + j := ⟨a - j, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = q + j := ⟨b - j, by omega⟩
  rw [rjFusionIncl, show p + j + (q + j) - 2 * j = p + q from by omega,
    show p + j - j = p from by omega]
  exact rjNat_mul (rjNat_mul (rjNat_jwAt (p + q) 0 (p + q) (by omega))
    (rjNat_cupThick_of_eq_fusionNat _ p q j (by omega))) (rjNat_bundleProj _ _)

end AJConjecture
