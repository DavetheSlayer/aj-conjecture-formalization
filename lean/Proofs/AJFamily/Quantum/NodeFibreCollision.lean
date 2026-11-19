import Mathlib

/-!
# Splitting off a simple root, with collisions

A one-variable lemma over `ℂ`: under the collision hypothesis, `c g d t = s r` (with `g ∣ X^n r`,
`d ∣ X^n s`) forces `r = (X - l₀) r_c` with `r_c` coprime to `s`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- If `g ∣ X ^ n * r` with `r ≠ 0`, then away from `0` the multiplicity of a root of `g` is
at most its multiplicity in `r`. -/
private theorem rootMultiplicity_le_of_dvd_X_pow_mul {g r : ℂ[X]} {l : ℂ} (hr : r ≠ 0)
    (hl : l ≠ 0) (hgr : ∃ n : ℕ, g ∣ X ^ n * r) :
    g.rootMultiplicity l ≤ r.rootMultiplicity l := by
  obtain ⟨n, hn⟩ := hgr
  have hXr : (X ^ n * r : ℂ[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hr
  have h1 : g.rootMultiplicity l ≤ (X ^ n * r).rootMultiplicity l :=
    (le_rootMultiplicity_iff hXr).2 ((pow_rootMultiplicity_dvd g l).trans hn)
  have h2 : (X ^ n : ℂ[X]).rootMultiplicity l = 0 :=
    rootMultiplicity_eq_zero (by simp [IsRoot, hl])
  rwa [rootMultiplicity_mul hXr, h2, zero_add] at h1

/-- A simple root has multiplicity one. -/
private theorem rootMultiplicity_eq_one_of_simple {p : ℂ[X]} {l : ℂ} (hp : p.eval l = 0)
    (hp' : (derivative p).eval l ≠ 0) : p.rootMultiplicity l = 1 := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp'
  have h1 := (rootMultiplicity_pos hp0 (x := l)).2 hp
  have h2 : ¬ 1 < p.rootMultiplicity l := fun h ↦
    hp' ((one_lt_rootMultiplicity_iff_isRoot hp0).1 h).2
  omega

theorem exists_eq_mul_isCoprime_of_collision {c l₀ : ℂ} {g dd t r s : ℂ[X]} (hc : c ≠ 0)
    (h : C c * (g * dd * t) = s * r) (h0 : (g * dd * t).eval 0 ≠ 0)
    (hgr : ∃ n : ℕ, g ∣ X ^ n * r) (hds : ∃ n : ℕ, dd ∣ X ^ n * s)
    (hg : g.eval l₀ = 0) (hd : dd.eval l₀ = 0) (hg' : (derivative g).eval l₀ ≠ 0)
    (hd' : (derivative dd).eval l₀ ≠ 0) (ht : t.eval l₀ ≠ 0)
    (hgd : ∀ l : ℂ, g.eval l = 0 → dd.eval l = 0 → l = l₀)
    (htc : ∀ l : ℂ, t.eval l = 0 → g.eval l ≠ 0 ∧ dd.eval l ≠ 0 ∧ (derivative t).eval l ≠ 0) :
    ∃ rc : ℂ[X], r = (X - C l₀) * rc ∧ IsCoprime rc s := by
  have hP : g * dd * t ≠ 0 := fun h' ↦ h0 (by rw [h', eval_zero])
  have hsr : s * r ≠ 0 := by
    rw [← h]
    exact mul_ne_zero (C_ne_zero.2 hc) hP
  have hs0 : s ≠ 0 := left_ne_zero_of_mul hsr
  have hr0 : r ≠ 0 := right_ne_zero_of_mul hsr
  have hgdt : g * dd ≠ 0 := left_ne_zero_of_mul hP
  have hsr0 : s.eval 0 ≠ 0 := by
    have := congrArg (eval 0) h
    rw [eval_mul, eval_C, eval_mul (p := s)] at this
    intro hz
    rw [hz, zero_mul] at this
    exact mul_ne_zero hc h0 this
  -- multiplicities add up
  have hE : ∀ l : ℂ, g.rootMultiplicity l + dd.rootMultiplicity l + t.rootMultiplicity l =
      s.rootMultiplicity l + r.rootMultiplicity l := by
    intro l
    have := congrArg (rootMultiplicity l) h
    rwa [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hc) hP), rootMultiplicity_C,
      zero_add, rootMultiplicity_mul hP, rootMultiplicity_mul hgdt,
      rootMultiplicity_mul hsr] at this
  have hl₀ : l₀ ≠ 0 := by
    rintro rfl
    exact h0 (by rw [eval_mul, eval_mul, hg, zero_mul, zero_mul])
  have hBg := fun l (hl : l ≠ 0) ↦ rootMultiplicity_le_of_dvd_X_pow_mul hr0 hl hgr
  have hBd := fun l (hl : l ≠ 0) ↦ rootMultiplicity_le_of_dvd_X_pow_mul hs0 hl hds
  have hrl₀ : r.rootMultiplicity l₀ = 1 := by
    have e := hE l₀
    rw [rootMultiplicity_eq_one_of_simple hg hg', rootMultiplicity_eq_one_of_simple hd hd',
      rootMultiplicity_eq_zero ht] at e
    have := hBg l₀ hl₀
    have := hBd l₀ hl₀
    rw [rootMultiplicity_eq_one_of_simple hg hg'] at *
    rw [rootMultiplicity_eq_one_of_simple hd hd'] at *
    omega
  have hroot : r.IsRoot l₀ := (rootMultiplicity_pos hr0).1 (by omega)
  refine ⟨r /ₘ (X - C l₀), (mul_divByMonic_eq_iff_isRoot.2 hroot).symm, ?_⟩
  set rc := r /ₘ (X - C l₀) with hrc
  have hr : r = (X - C l₀) * rc := (mul_divByMonic_eq_iff_isRoot.2 hroot).symm
  have hrc0 : rc ≠ 0 := by
    rintro h'
    rw [h', mul_zero] at hr
    exact hr0 hr
  have hmr : ∀ l : ℂ, r.rootMultiplicity l =
      (X - C l₀).rootMultiplicity l + rc.rootMultiplicity l := by
    intro l
    rw [hr, rootMultiplicity_mul (hr ▸ hr0)]
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro l
  rw [coe_aeval_eq_eval]
  by_contra! hcon
  obtain ⟨hrcl, hsl⟩ := hcon
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hsr0 hsl
  have hll₀ : l ≠ l₀ := by
    rintro rfl
    have := hmr l
    rw [hrl₀, rootMultiplicity_X_sub_C_self] at this
    have := (rootMultiplicity_pos hrc0).2 hrcl
    omega
  have hXl : (X - C l₀).rootMultiplicity l = 0 :=
    rootMultiplicity_eq_zero (by simp [IsRoot, sub_eq_zero, hll₀])
  have h1 := (rootMultiplicity_pos hrc0).2 hrcl
  have h2 := (rootMultiplicity_pos hs0).2 hsl
  have h3 := hmr l
  have h4 := hE l
  have h5 := hBg l hl0
  have h6 := hBd l hl0
  by_cases htl : t.eval l = 0
  · obtain ⟨hgl, hdl, ht'l⟩ := htc l htl
    rw [rootMultiplicity_eq_zero hgl, rootMultiplicity_eq_zero hdl,
      rootMultiplicity_eq_one_of_simple htl ht'l] at h4
    omega
  · rw [rootMultiplicity_eq_zero htl] at h4
    by_cases hgl : g.eval l = 0
    · have hdl : ¬ dd.IsRoot l := fun hdl ↦ hll₀ (hgd l hgl hdl)
      rw [rootMultiplicity_eq_zero hdl] at h4
      omega
    · rw [rootMultiplicity_eq_zero hgl] at h4
      omega

end AJConjecture
