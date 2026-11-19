import Mathlib

/-!
# Regularity, orders and simple residues of rational functions of `z`

`HasSimpleResidue f z₀ ι` says that `f ∈ ℂ(z)` has at most a simple pole at `z₀` with residue
`ι`, that is `f - ι/(z - z₀)` is regular at `z₀`. Every residue statement of Theorem I is of this
form (the source's residues all come with at most simple poles), and it is stronger than
`Res_{z₀} f = ι`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `f ∈ ℂ(z)` is regular at `z₀`: it lies in `ℂ[z]_(z - z₀)`. -/
def IsRegularAt (z₀ : ℂ) (f : RatFunc ℂ) : Prop :=
  ∃ a b : ℂ[X], b.eval z₀ ≠ 0 ∧
    f * algebraMap ℂ[X] (RatFunc ℂ) b = algebraMap ℂ[X] (RatFunc ℂ) a

/-- `f ∈ ℂ(z)` is a unit of `ℂ[z]_(z - z₀)`: regular and nonvanishing at `z₀`. -/
def IsUnitAt (z₀ : ℂ) (f : RatFunc ℂ) : Prop :=
  ∃ a b : ℂ[X], a.eval z₀ ≠ 0 ∧ b.eval z₀ ≠ 0 ∧
    f * algebraMap ℂ[X] (RatFunc ℂ) b = algebraMap ℂ[X] (RatFunc ℂ) a

/-- `f` has at most a simple pole at `z₀`, with residue `ι`. -/
def HasSimpleResidue (f : RatFunc ℂ) (z₀ ι : ℂ) : Prop :=
  IsRegularAt z₀ (f - RatFunc.C ι / (RatFunc.X - RatFunc.C z₀))

/-- `f` has order `k` at `z₀`: `f = (z - z₀)^k u` with `u` a unit at `z₀`. -/
def HasOrderAt (f : RatFunc ℂ) (z₀ : ℂ) (k : ℤ) : Prop :=
  ∃ u : RatFunc ℂ, IsUnitAt z₀ u ∧ f = (RatFunc.X - RatFunc.C z₀) ^ k * u

/-- `X - z₀` is a nonzero rational function. -/
private theorem ratFunc_X_sub_C_ne_zero_aux (z₀ : ℂ) :
    (RatFunc.X - RatFunc.C z₀ : RatFunc ℂ) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 (X_sub_C_ne_zero z₀)

private theorem isRegularAt_add_aux {z₀ : ℂ} {f g : RatFunc ℂ} (hf : IsRegularAt z₀ f)
    (hg : IsRegularAt z₀ g) : IsRegularAt z₀ (f + g) := by
  obtain ⟨a, b, hb, hab⟩ := hf
  obtain ⟨a', b', hb', hab'⟩ := hg
  refine ⟨a * b' + a' * b, b * b', by simpa [eval_mul] using mul_ne_zero hb hb', ?_⟩
  simp only [map_mul, map_add, ← hab, ← hab']
  ring

private theorem isRegularAt_mul_aux {z₀ : ℂ} {f g : RatFunc ℂ} (hf : IsRegularAt z₀ f)
    (hg : IsRegularAt z₀ g) : IsRegularAt z₀ (f * g) := by
  obtain ⟨a, b, hb, hab⟩ := hf
  obtain ⟨a', b', hb', hab'⟩ := hg
  refine ⟨a * a', b * b', by simpa [eval_mul] using mul_ne_zero hb hb', ?_⟩
  simp only [map_mul, ← hab, ← hab']
  ring

private theorem isRegularAt_neg_aux {z₀ : ℂ} {f : RatFunc ℂ} (hf : IsRegularAt z₀ f) :
    IsRegularAt z₀ (-f) := by
  obtain ⟨a, b, hb, hab⟩ := hf
  exact ⟨-a, b, hb, by rw [map_neg, ← hab, neg_mul]⟩

private theorem isRegularAt_algebraMap_aux (z₀ : ℂ) (p : ℂ[X]) :
    IsRegularAt z₀ (algebraMap ℂ[X] (RatFunc ℂ) p) :=
  ⟨p, 1, by simp, by rw [map_one, mul_one]⟩

/-- `ι/(z - z₀)` is regular at `z₀` only for `ι = 0`. -/
private theorem eq_zero_of_isRegularAt_C_div_aux {z₀ ι : ℂ}
    (h : IsRegularAt z₀ (RatFunc.C ι / (RatFunc.X - RatFunc.C z₀))) : ι = 0 := by
  obtain ⟨a, b, hb, hab⟩ := h
  have hX := ratFunc_X_sub_C_ne_zero_aux z₀
  have hpoly : C ι * b = a * (X - C z₀) := by
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    rw [map_mul, map_mul, ← hab, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      RatFunc.algebraMap_C]
    field_simp
  have := congrArg (eval z₀) hpoly
  simp only [eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero] at this
  exact (mul_eq_zero.1 this).resolve_right hb

private theorem hasSimpleResidue_of_pow_dvd_aux {N Δ : ℂ[X]} (hΔ : Δ ≠ 0) {z₀ ι : ℂ}
    (h : (X - C z₀) ^ (Δ.rootMultiplicity z₀ + 1) ∣ (X - C z₀) * N - C ι * Δ) :
    HasSimpleResidue (algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) Δ) z₀ ι := by
  obtain ⟨q, hΔq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Δ hΔ z₀
  rw [dvd_iff_isRoot, IsRoot] at hq
  obtain ⟨M, hM⟩ := h
  generalize Δ.rootMultiplicity z₀ = k at hΔq hM
  refine ⟨M, q, hq, ?_⟩
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hM' := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hM
  rw [hΔq] at hM'
  simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at hM'
  have hX := ratFunc_X_sub_C_ne_zero_aux z₀
  have hq0 : algebraMap ℂ[X] (RatFunc ℂ) q ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (by rintro rfl; simp at hq)
  rw [hΔq, map_mul, map_pow, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  field_simp
  linear_combination hM'

/-- The residue is unique. -/
theorem HasSimpleResidue.unique {f : RatFunc ℂ} {z₀ ι ι' : ℂ} (h : HasSimpleResidue f z₀ ι)
    (h' : HasSimpleResidue f z₀ ι') : ι = ι' := by
  have hd := isRegularAt_add_aux h' (isRegularAt_neg_aux h)
  have hX := ratFunc_X_sub_C_ne_zero_aux z₀
  have heq : f - RatFunc.C ι' / (RatFunc.X - RatFunc.C z₀) +
      -(f - RatFunc.C ι / (RatFunc.X - RatFunc.C z₀)) =
      RatFunc.C (ι - ι') / (RatFunc.X - RatFunc.C z₀) := by
    rw [map_sub]
    ring
  rw [heq] at hd
  exact sub_eq_zero.1 (eq_zero_of_isRegularAt_C_div_aux hd)

theorem HasSimpleResidue.add {f g : RatFunc ℂ} {z₀ ι ι' : ℂ} (hf : HasSimpleResidue f z₀ ι)
    (hg : HasSimpleResidue g z₀ ι') : HasSimpleResidue (f + g) z₀ (ι + ι') := by
  have heq : f + g - RatFunc.C (ι + ι') / (RatFunc.X - RatFunc.C z₀) =
      (f - RatFunc.C ι / (RatFunc.X - RatFunc.C z₀)) +
        (g - RatFunc.C ι' / (RatFunc.X - RatFunc.C z₀)) := by
    rw [map_add]
    ring
  unfold HasSimpleResidue
  rw [heq]
  exact isRegularAt_add_aux hf hg

/-- The logarithmic derivative `g'/g` has residue `ord_{z₀} g` at `z₀`. -/
theorem hasSimpleResidue_logDeriv {g : ℂ[X]} (hg : g ≠ 0) (z₀ : ℂ) :
    HasSimpleResidue (algebraMap ℂ[X] (RatFunc ℂ) (derivative g) / algebraMap ℂ[X] (RatFunc ℂ) g)
      z₀ (g.rootMultiplicity z₀) := by
  apply hasSimpleResidue_of_pow_dvd_aux hg
  obtain ⟨q, hgq, -⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg z₀
  refine ⟨derivative q, ?_⟩
  set k := g.rootMultiplicity z₀
  rw [hgq, derivative_mul, derivative_X_sub_C_pow]
  rcases k with _ | k
  · simp
  · push_cast
    ring

/-- The polynomial form of a simple residue: if `Δ ≠ 0`, `k = ord_{z₀} Δ` and
`(z - z₀)^(k+1) ∣ (z - z₀) N - ι Δ`, then `N/Δ` has residue `ι` at `z₀`. -/
theorem hasSimpleResidue_of_pow_dvd {N Δ : ℂ[X]} (hΔ : Δ ≠ 0) {z₀ ι : ℂ}
    (h : (X - C z₀) ^ (Δ.rootMultiplicity z₀ + 1) ∣ (X - C z₀) * N - C ι * Δ) :
    HasSimpleResidue (algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) Δ) z₀ ι :=
  hasSimpleResidue_of_pow_dvd_aux hΔ h

/-- Division by the unit `c z` at `z₀ ≠ 0` divides the residue by `c z₀`. -/
theorem HasSimpleResidue.div_C_mul_X {f : RatFunc ℂ} {z₀ ρ c : ℂ} (hf : HasSimpleResidue f z₀ ρ)
    (hc : c ≠ 0) (hz₀ : z₀ ≠ 0) :
    HasSimpleResidue (f / (RatFunc.C c * RatFunc.X)) z₀ (ρ / (c * z₀)) := by
  have hX := ratFunc_X_sub_C_ne_zero_aux z₀
  have hX0 : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hc0 : (RatFunc.C c : RatFunc ℂ) ≠ 0 := by simpa using hc
  have hz0 : (RatFunc.C z₀ : RatFunc ℂ) ≠ 0 := by simpa using hz₀
  have hinv : IsRegularAt z₀ (1 / (RatFunc.C c * RatFunc.X)) := by
    refine ⟨1, C c * X, by simp [hc, hz₀], ?_⟩
    rw [map_one, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    field_simp
  have heq : f / (RatFunc.C c * RatFunc.X) - RatFunc.C (ρ / (c * z₀)) /
      (RatFunc.X - RatFunc.C z₀) =
      (f - RatFunc.C ρ / (RatFunc.X - RatFunc.C z₀)) * (1 / (RatFunc.C c * RatFunc.X)) +
        -(algebraMap ℂ[X] (RatFunc ℂ) (C (ρ / z₀)) * (1 / (RatFunc.C c * RatFunc.X))) := by
    rw [RatFunc.algebraMap_C, map_div₀, map_div₀, map_mul]
    field_simp
    ring
  unfold HasSimpleResidue
  rw [heq]
  exact isRegularAt_add_aux (isRegularAt_mul_aux hf hinv)
    (isRegularAt_neg_aux (isRegularAt_mul_aux (isRegularAt_algebraMap_aux z₀ _) hinv))

/-- Regularity at `z₀` is closed under addition. -/
theorem isRegularAt_add {z₀ : ℂ} {f g : RatFunc ℂ} (hf : IsRegularAt z₀ f)
    (hg : IsRegularAt z₀ g) : IsRegularAt z₀ (f + g) :=
  isRegularAt_add_aux hf hg

/-- Regularity at `z₀` is closed under multiplication. -/
theorem isRegularAt_mul {z₀ : ℂ} {f g : RatFunc ℂ} (hf : IsRegularAt z₀ f)
    (hg : IsRegularAt z₀ g) : IsRegularAt z₀ (f * g) :=
  isRegularAt_mul_aux hf hg

/-- Regularity at `z₀` is closed under negation. -/
theorem isRegularAt_neg {z₀ : ℂ} {f : RatFunc ℂ} (hf : IsRegularAt z₀ f) :
    IsRegularAt z₀ (-f) :=
  isRegularAt_neg_aux hf

/-- Polynomials are regular everywhere. -/
theorem isRegularAt_algebraMap (z₀ : ℂ) (p : ℂ[X]) :
    IsRegularAt z₀ (algebraMap ℂ[X] (RatFunc ℂ) p) :=
  isRegularAt_algebraMap_aux z₀ p

/-- `ι/(z - z₀)` is regular at `z₀` only for `ι = 0`. -/
theorem eq_zero_of_isRegularAt_C_div {z₀ ι : ℂ}
    (h : IsRegularAt z₀ (RatFunc.C ι / (RatFunc.X - RatFunc.C z₀))) : ι = 0 :=
  eq_zero_of_isRegularAt_C_div_aux h

end AJConjecture
