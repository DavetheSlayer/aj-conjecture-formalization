import Mathlib
import AJConjecture.APolynomial

/-!
# Zero sets and divisibility in the plane

An irreducible polynomial in two variables over `ℂ` divides every polynomial vanishing on its
zero set (the Nullstellensatz for plane curves, in the coordinates of `evalPoint`).
-/

open Polynomial

namespace AJConjecture

/-- If an irreducible `g ∈ ℂ[M][L]` of positive `L`-degree does not divide `P`, then a nonzero
polynomial in `M` alone is a combination of `g` and `P` (Bézout over the fraction field, with
denominators cleared). -/
private theorem exists_bezout_eq_C_of_irreducible_of_not_dvd {g P : ℂ[X][X]} (hg : Irreducible g)
    (hdeg : g.natDegree ≠ 0) (hP : ¬ g ∣ P) :
    ∃ (d : ℂ[X]) (U V : ℂ[X][X]), d ≠ 0 ∧ U * g + V * P = C d := by
  have hprim : g.IsPrimitive := hg.isPrimitive hdeg
  have hinj : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) :=
    IsFractionRing.injective _ _
  have hirr : Irreducible (g.map (algebraMap ℂ[X] (RatFunc ℂ))) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.1 hg
  have hndvd : ¬ g.map (algebraMap ℂ[X] (RatFunc ℂ)) ∣
      P.map (algebraMap ℂ[X] (RatFunc ℂ)) := fun hd ↦
    hP (hprim.dvd_of_fraction_map_dvd_fraction_map hd)
  obtain ⟨u, v, huv⟩ := hirr.coprime_iff_not_dvd.2 hndvd
  obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℂ[X]) u
  obtain ⟨c, hc0, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℂ[X]) v
  rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hb hc
  refine ⟨b * c, C c * IsLocalization.integerNormalization (nonZeroDivisors ℂ[X]) u,
    C b * IsLocalization.integerNormalization (nonZeroDivisors ℂ[X]) v,
    mul_ne_zero (nonZeroDivisors.ne_zero hb0) (nonZeroDivisors.ne_zero hc0), ?_⟩
  apply map_injective (algebraMap ℂ[X] (RatFunc ℂ)) hinj
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hb, hc, map_mul]
  linear_combination (C (algebraMap ℂ[X] (RatFunc ℂ) b) *
    C (algebraMap ℂ[X] (RatFunc ℂ) c)) * huv

/-- Above a point `M₀` that is not a root of the leading coefficient, a polynomial of positive
`L`-degree has a zero. -/
private theorem exists_evalPoint_eq_zero_of_leadingCoeff_eval_ne_zero {g : ℂ[X][X]}
    (hdeg : g.natDegree ≠ 0) {M₀ : ℂ} (hM : g.leadingCoeff.eval M₀ ≠ 0) :
    ∃ L₀ : ℂ, evalPoint g (M₀, L₀) = 0 := by
  have hnat : (g.map (evalRingHom M₀)).natDegree = g.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ hM
  have hdeg' : (g.map (evalRingHom M₀)).degree ≠ 0 := fun h0 ↦
    hdeg (hnat ▸ natDegree_eq_zero_iff_degree_le_zero.2 h0.le)
  obtain ⟨L₀, hL⟩ := IsAlgClosed.exists_root _ hdeg'
  exact ⟨L₀, by rwa [IsRoot, eval_map] at hL⟩

/-- The case of positive `L`-degree of `dvd_of_forall_evalPoint_eq_zero`. -/
private theorem dvd_of_forall_evalPoint_eq_zero_of_natDegree_ne_zero {g P : ℂ[X][X]}
    (hg : Irreducible g) (hdeg : g.natDegree ≠ 0)
    (h : ∀ p : ℂ × ℂ, evalPoint g p = 0 → evalPoint P p = 0) : g ∣ P := by
  by_contra hP
  obtain ⟨d, U, V, hd, hUV⟩ := exists_bezout_eq_C_of_irreducible_of_not_dvd hg hdeg hP
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg.ne_zero
  obtain ⟨M₀, hM⟩ : ∃ M₀ : ℂ, (d * g.leadingCoeff).eval M₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact mul_ne_zero hd hlc (Polynomial.funext fun x ↦ by rw [hall x, eval_zero])
  rw [eval_mul] at hM
  obtain ⟨L₀, hL⟩ := exists_evalPoint_eq_zero_of_leadingCoeff_eval_ne_zero hdeg
    (right_ne_zero_of_mul hM)
  have hPL := h _ hL
  have hev := congrArg (fun Q ↦ evalPoint Q (M₀, L₀)) hUV
  simp only [evalPoint, eval₂_add, eval₂_mul, eval₂_C, coe_evalRingHom] at hev hL hPL
  rw [hL, hPL, mul_zero, mul_zero, add_zero] at hev
  exact left_ne_zero_of_mul hM hev.symm

/-- The case of `L`-degree zero of `dvd_of_forall_evalPoint_eq_zero`: `g` is a polynomial in `M`
alone. -/
private theorem dvd_of_forall_evalPoint_eq_zero_of_natDegree_eq_zero {g P : ℂ[X][X]}
    (hg : Irreducible g) (hdeg : g.natDegree = 0)
    (h : ∀ p : ℂ × ℂ, evalPoint g p = 0 → evalPoint P p = 0) : g ∣ P := by
  obtain ⟨a, rfl⟩ := natDegree_eq_zero.1 hdeg
  have ha : Irreducible a := hg.of_map (f := (C : ℂ[X] →+* ℂ[X][X]))
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root a
    (by rw [IsAlgClosed.degree_eq_one_of_irreducible ℂ ha]; exact one_ne_zero)
  rw [C_dvd_iff_dvd_coeff]
  intro n
  have hmap : P.map (evalRingHom r) = 0 := Polynomial.funext fun L₀ ↦ by
    have := h (r, L₀) (by simpa [evalPoint] using hr)
    rw [eval_map, eval_zero]
    exact this
  have hcoeff : (P.coeff n).eval r = 0 := by
    have := congrArg (fun Q ↦ Q.coeff n) hmap
    simpa [coeff_map] using this
  exact ((irreducible_X_sub_C r).dvd_symm ha (dvd_iff_isRoot.2 hr)).trans
    (dvd_iff_isRoot.2 hcoeff)

/-- An irreducible `g ∈ ℂ[M][L]` divides every polynomial that vanishes on the zero set of
`g`. -/
theorem dvd_of_forall_evalPoint_eq_zero {g P : ℂ[X][X]} (hg : Irreducible g)
    (h : ∀ p : ℂ × ℂ, evalPoint g p = 0 → evalPoint P p = 0) : g ∣ P := by
  by_cases hdeg : g.natDegree = 0
  · exact dvd_of_forall_evalPoint_eq_zero_of_natDegree_eq_zero hg hdeg h
  · exact dvd_of_forall_evalPoint_eq_zero_of_natDegree_ne_zero hg hdeg h

end AJConjecture
