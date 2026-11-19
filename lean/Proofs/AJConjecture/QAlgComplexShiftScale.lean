import Mathlib
import AJConjecture.QAlgNodeJet

/-!
# The shift `M ↦ t² M` is surjective up to powers of `t`

For `f = ∑_e a_e M^e` of degree `n` in `M`, the polynomial `g = ∑_e t^(2(n - e)) a_e M^e`
satisfies `g(t, t² M) = t^(2n) f`. Since `t` does not vanish at `t = -1`, this makes the shift
surjective on the local ring of a point `(-1, m₀)`.
-/

open Polynomial

namespace AJConjecture

/-- Every `f ∈ ℂ[t][M]` of degree at most `N` in `M` is, up to the factor `t^(2N)`, in the image
of the shift. -/
private theorem exists_complexShift_eq_of_natDegree_le (N : ℕ) (f : ℂ[X][X])
    (hf : f.natDegree ≤ N) : ∃ g : ℂ[X][X], complexShift g = C (X ^ (2 * N)) * f := by
  refine Polynomial.induction_with_natDegree_le
    (fun f : ℂ[X][X] ↦ ∃ g : ℂ[X][X], complexShift g = C (X ^ (2 * N)) * f) N ?_ ?_ ?_ f hf
  · exact ⟨0, by rw [map_zero, mul_zero]⟩
  · intro n r _ hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    refine ⟨C (X ^ (2 * k) * r) * X ^ n, ?_⟩
    have hcomp : complexShift (C (X ^ (2 * k) * r) * X ^ n) =
        (C (X ^ (2 * k) * r) * X ^ n : ℂ[X][X]).comp (C (X ^ 2) * X) := rfl
    rw [hcomp, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow, ← pow_mul, hk, mul_add,
      pow_add, C_mul, C_mul]
    ring
  · rintro p q _ _ ⟨gp, hgp⟩ ⟨gq, hgq⟩
    refine ⟨gp + gq, ?_⟩
    rw [map_add, hgp, hgq, mul_add]

/-- Every `f ∈ ℂ[t][M]` is, up to the factor `t^(2 deg_M f)`, in the image of the shift. -/
theorem exists_complexShift_eq_C_X_pow_mul (f : ℂ[X][X]) :
    ∃ g : ℂ[X][X], complexShift g = C (X ^ (2 * f.natDegree)) * f :=
  exists_complexShift_eq_of_natDegree_le f.natDegree f le_rfl

end AJConjecture
