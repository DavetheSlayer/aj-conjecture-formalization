import Mathlib
import AJHandoff.Geometry.GeoBlochWignerInvolution

/-!
# The signed volume of an oriented ideal tetrahedron (G-VOL, orientation)

The shape of the oriented ideal tetrahedron with vertices `v₀, v₁, v₂, v₃ ∈ ℂ` is the cross-ratio
`(v₂ - v₀)(v₃ - v₁)/((v₃ - v₀)(v₂ - v₁))` (`geoCrossRatio`; the tetrahedron `(∞, 0, 1, z)` has
shape `z`), and its signed volume is `D` of the shape. Reordering the vertices by a permutation `σ`
multiplies the signed volume by `sign σ`: even permutations act on the shape through
`z ↦ 1/(1 - z) ↦ 1 - 1/z`, odd ones through `z ↦ 1/z, 1 - z, z/(z - 1)`. In particular reversing
the orientation (a transposition) negates the signed volume; this is the sign rule behind the
mirror pullback in `GeoVolumeSigned`.

Route. The Klein four-group fixes the cross-ratio and `S₄ → S₃` preserves the sign; it suffices to
check the generators `(0 1)`, `(1 2)`, `(2 3)` (`Equiv.Perm.swap_induction_on`), which send `z` to
`1/z`-type images, and to use `geo_blochWigner_inv`, `geo_blochWigner_one_sub`.
-/

noncomputable section

namespace AJConjecture

/-- The cross-ratio shape of the oriented ideal tetrahedron with vertices `v`. -/
def geoCrossRatio (v : Fin 4 → ℂ) : ℂ :=
  (v 2 - v 0) * (v 3 - v 1) / ((v 3 - v 0) * (v 2 - v 1))

/-- `D(z/(z - 1)) = -D(z)`. -/
private theorem geo_blochWigner_div_sub_one {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    blochWigner (z / (z - 1)) = -blochWigner z := by
  have h1 : 1 - z⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, inv_ne_one]
    exact hz1
  rw [show z / (z - 1) = (1 - z⁻¹)⁻¹ by field_simp, geo_blochWigner_inv h1,
    geo_blochWigner_one_sub, geo_blochWigner_inv hz0, neg_neg]

/-- A transposition of the vertices negates the signed volume. -/
private theorem geo_blochWigner_crossRatio_swap (v : Fin 4 → ℂ) (hv : Function.Injective v)
    (x y : Fin 4) (hxy : x ≠ y) :
    blochWigner (geoCrossRatio (v ∘ Equiv.swap x y)) = -blochWigner (geoCrossRatio v) := by
  have hd : ∀ i j : Fin 4, i ≠ j → v i - v j ≠ 0 := fun i j h ↦ sub_ne_zero.2 (hv.ne h)
  have h10 := hd 1 0 (by decide)
  have h20 := hd 2 0 (by decide)
  have h30 := hd 3 0 (by decide)
  have h21 := hd 2 1 (by decide)
  have h31 := hd 3 1 (by decide)
  have h32 := hd 3 2 (by decide)
  have h01 := hd 0 1 (by decide)
  have h02 := hd 0 2 (by decide)
  have h03 := hd 0 3 (by decide)
  have h12 := hd 1 2 (by decide)
  have h13 := hd 1 3 (by decide)
  have h23 := hd 2 3 (by decide)
  have hz0 : geoCrossRatio v ≠ 0 := by
    unfold geoCrossRatio
    exact div_ne_zero (mul_ne_zero h20 h31) (mul_ne_zero h30 h21)
  have hz1 : geoCrossRatio v ≠ 1 := by
    unfold geoCrossRatio
    rw [Ne, div_eq_one_iff_eq (mul_ne_zero h30 h21)]
    intro h
    exact mul_ne_zero h10 h32 (by linear_combination h)
  have hinv : ∀ w : Fin 4 → ℂ, geoCrossRatio w = (geoCrossRatio v)⁻¹ →
      blochWigner (geoCrossRatio w) = -blochWigner (geoCrossRatio v) := by
    intro w h
    rw [h, geo_blochWigner_inv hz0]
  have hone : ∀ w : Fin 4 → ℂ, geoCrossRatio w = 1 - geoCrossRatio v →
      blochWigner (geoCrossRatio w) = -blochWigner (geoCrossRatio v) := by
    intro w h
    rw [h, geo_blochWigner_one_sub]
  have hdiv : ∀ w : Fin 4 → ℂ,
      geoCrossRatio w = (v 2 - v 0) * (v 3 - v 1) / ((v 1 - v 0) * (v 3 - v 2)) →
      blochWigner (geoCrossRatio w) = -blochWigner (geoCrossRatio v) := by
    intro w h
    have hz1' : geoCrossRatio v - 1 ≠ 0 := sub_ne_zero.2 hz1
    have e : (v 2 - v 0) * (v 3 - v 1) / ((v 1 - v 0) * (v 3 - v 2)) =
        geoCrossRatio v / (geoCrossRatio v - 1) := by
      rw [eq_div_iff hz1']
      unfold geoCrossRatio
      field_simp
      ring
    rw [h, e, geo_blochWigner_div_sub_one hz0 hz1]
  fin_cases x <;> fin_cases y <;> simp only [ne_eq, not_true_eq_false] at hxy <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk]
  · apply hinv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
  · apply hdiv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hone
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hinv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
  · apply hone
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hdiv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hdiv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hone
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hinv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
  · apply hone
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hdiv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp
    ring
  · apply hinv
    simp (disch := decide) only [geoCrossRatio, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    field_simp

/-- The signed volume changes by the sign of the vertex permutation. -/
theorem geo_blochWigner_crossRatio_perm (v : Fin 4 → ℂ) (hv : Function.Injective v)
    (σ : Equiv.Perm (Fin 4)) :
    blochWigner (geoCrossRatio (v ∘ σ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * blochWigner (geoCrossRatio v) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => simp
  | swap_mul f x y hxy ih =>
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ih _ (hv.comp (Equiv.injective _)),
      geo_blochWigner_crossRatio_swap v hv x y hxy, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hxy]
    push_cast
    ring

end AJConjecture
