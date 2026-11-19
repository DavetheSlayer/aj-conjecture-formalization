import Mathlib
import AJPaper.Ideal.PpIClear

/-!
# Rational raw annihilators vanish on `G = 0` (Unit PpI, node `PpI_Rational`)

Source: Section 8.5 of the paper: "For each nonzero rational row, clear numerical denominators
… Sections 8.1 and its mirror give a nonzero specialization divisible by `G` … every raw
specialized annihilator vanishes at generic points of `G = 0`."

Input (hypothesis `hG`): `G` divides `Q(-1, M, L)` in `ℤ[M][L]` for every polynomial operator
`Q` annihilating the coloured Jones function of `K` at all integers (for the four families:
`ppi_factor_dvd_specialize_of_annihilates`).

* `ppi_eval_eps_eq_zero_int`: for an annihilator `P` in the quantum torus over `ℤ[t^{±1}]`, the
  specialization `ε(P)` vanishes at every point `(M, L)`, `M, L ≠ 0`, of `G = 0`. Route: a shift
  of `P` is `ppiOfRecOp Q` (`ppi_exists_recOp_shift`); `Q` annihilates
  (`ppiApply_ppiShift`, `ppiAnnihilates_ppiOfRecOp_iff`); `G ∣ specialize Q`, so
  `specialize Q` vanishes at the point; conclude with `ppiEval_ppiEps_ppiOfRecOp`,
  `ppiMapOp_ppiShift` and `ppiEval_ppiEps_ppiShift`.
* `ppi_exists_int_of_rat`: a nonzero integer multiple of an element of the quantum torus over
  `ℚ[t^{±1}]` has integer coefficients.
* `ppi_eval_eps_eq_zero_rat`: the same vanishing for annihilators over `ℚ[t^{±1}]`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value at a point of the specialization `t = -1` after a change of coefficients, as a
sum over the coefficients. -/
private theorem ppiEval_ppiEps_ppiMapOp_eq_sum_Rational {A : Type} [CommRing A] (φ : A →+* ℂ)
    (P : PpiOp A) (p : ℂ × ℂ) :
    ppiEval p (ppiEps (ppiMapOp φ P)) = P.sum fun kl c ↦
      LaurentPolynomial.eval₂ φ (-1 : ℂˣ) c * p.1 ^ kl.1 * p.2 ^ kl.2 := by
  unfold ppiEval ppiEps ppiMapOp
  rw [AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapRange_index (fun kl ↦ by simp),
    Finsupp.sum_mapRange_index (fun kl ↦ by simp)]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  rw [LaurentPolynomial.eval₂_mapRingHom, RingHom.id_comp]

/-- A rational Laurent polynomial has integer coefficients after multiplication by every
multiple of a suitable nonzero integer. -/
private theorem exists_int_laurent_of_rat_Rational (x : LaurentPolynomial ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ M : ℤ, N ∣ M → ∃ y : LaurentPolynomial ℤ,
      AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom ℚ) y = LaurentPolynomial.C (M : ℚ) * x := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨N₁, h₁, H₁⟩ := hp
    obtain ⟨N₂, h₂, H₂⟩ := hq
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, fun M hM ↦ ?_⟩
    obtain ⟨y₁, hy₁⟩ := H₁ M (dvd_of_mul_right_dvd hM)
    obtain ⟨y₂, hy₂⟩ := H₂ M (dvd_of_mul_left_dvd hM)
    exact ⟨y₁ + y₂, by rw [map_add, hy₁, hy₂, mul_add]⟩
  | C_mul_T n a =>
    refine ⟨a.den, by exact_mod_cast a.den_ne_zero, fun M hM ↦ ?_⟩
    obtain ⟨k, rfl⟩ := hM
    refine ⟨LaurentPolynomial.C (a.num * k) * LaurentPolynomial.T n, ?_⟩
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single,
      LaurentPolynomial.single_eq_C_mul_T, ← mul_assoc, ← map_mul]
    congr 2
    have := Rat.mul_den_eq_num a
    rw [eq_intCast]
    push_cast
    linear_combination (-(k : ℚ)) * this

/-- Integral raw annihilators: `ε(P)` vanishes on the torus points of `G = 0`. -/
theorem ppi_eval_eps_eq_zero_int {K : BraidKnot} {G : ℤ[X][X]}
    (hG : ∀ Q : RecOp, Annihilates Q (coloredJones K) → G ∣ specialize Q) {P : PpiOp ℤ}
    (hP : PpiAnnihilates P K) {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hp : evalPoint (mapC G) p = 0) :
    ppiEval p (ppiEps (ppiMapOp (Int.castRingHom ℂ) P)) = 0 := by
  obtain ⟨a, b, c, Q, hQ⟩ := ppi_exists_recOp_shift P
  have hann : Annihilates Q (coloredJones K) := by
    refine (ppiAnnihilates_ppiOfRecOp_iff Q K).1 fun n ↦ ?_
    rw [hQ, ppiApply_ppiShift, hP (n + b), mul_zero]
  obtain ⟨H, hH⟩ := hG Q hann
  have h0 : evalPoint (mapC (specialize Q)) p = 0 := by
    have hp' : Polynomial.eval₂ (Polynomial.evalRingHom p.1) p.2 (mapC G) = 0 := hp
    rw [hH]
    unfold evalPoint mapC
    rw [Polynomial.map_mul, Polynomial.eval₂_mul, hp', zero_mul]
  have key := ppiEval_ppiEps_ppiOfRecOp Q p
  rw [hQ, ppiMapOp_ppiShift, ppiEval_ppiEps_ppiShift a b c _ h1 h2, h0] at key
  have hne : (-1 : ℂ) ^ c * p.1 ^ a * p.2 ^ b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ h1)) (pow_ne_zero _ h2)
  exact (mul_eq_zero.1 key).resolve_left hne

/-- Clearing numerical denominators. -/
theorem ppi_exists_int_of_rat (P : PpiOp ℚ) :
    ∃ (N : ℤ) (P' : PpiOp ℤ), N ≠ 0 ∧ ppiMapOp (Int.castRingHom ℚ) P' =
      P.mapRange (fun c ↦ LaurentPolynomial.C (N : ℚ) * c) (mul_zero _) := by
  choose N hN0 hN using fun kl : ℤ × ℤ ↦ exists_int_laurent_of_rat_Rational (P kl)
  have hy : ∀ kl : ℤ × ℤ, ∃ y : LaurentPolynomial ℤ, kl ∈ P.support →
      AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom ℚ) y =
        LaurentPolynomial.C ((∏ kl ∈ P.support, N kl : ℤ) : ℚ) * P kl := fun kl ↦ by
    by_cases hkl : kl ∈ P.support
    · obtain ⟨y, hy⟩ := hN kl _ (Finset.dvd_prod_of_mem N hkl)
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h ↦ absurd h hkl⟩
  choose y hy using hy
  refine ⟨∏ kl ∈ P.support, N kl, Finsupp.onFinset P.support
    (fun kl ↦ if kl ∈ P.support then y kl else 0) (fun kl h ↦ by
      by_contra hk
      simp [hk] at h), Finset.prod_ne_zero_iff.2 fun kl _ ↦ hN0 kl, ?_⟩
  ext1 kl
  simp only [ppiMapOp, Finsupp.mapRange_apply, Finsupp.onFinset_apply]
  split_ifs with h
  · exact hy kl h
  · rw [Finsupp.notMem_support_iff.1 h, map_zero, mul_zero]

/-- Rational raw annihilators: `ε(P)` vanishes on the torus points of `G = 0`. -/
theorem ppi_eval_eps_eq_zero_rat {K : BraidKnot} {G : ℤ[X][X]}
    (hG : ∀ Q : RecOp, Annihilates Q (coloredJones K) → G ∣ specialize Q) {P : PpiOp ℚ}
    (hP : PpiAnnihilates P K) {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0)
    (hp : evalPoint (mapC G) p = 0) :
    ppiEval p (ppiEps (ppiMapOp (algebraMap ℚ ℂ) P)) = 0 := by
  obtain ⟨N, P', hN, hP'⟩ := ppi_exists_int_of_rat P
  have hann : PpiAnnihilates P' K := by
    refine (ppiAnnihilates_ppiMapOp_iff (φ := Int.castRingHom ℚ) Int.cast_injective P' K).1
      fun n ↦ ?_
    rw [hP']
    unfold ppiApply
    rw [Finsupp.sum_mapRange_index (fun kl ↦ by simp)]
    have h := congrArg (fun z ↦ LaurentPolynomial.C (N : ℚ) * z) (hP n)
    simp only [ppiApply, Finsupp.mul_sum, mul_zero] at h
    rw [← h]
    exact Finsupp.sum_congr fun kl _ ↦ by ring
  have hint := ppi_eval_eps_eq_zero_int hG hann h1 h2 hp
  have hsum := ppiEval_ppiEps_ppiMapOp_eq_sum_Rational (algebraMap ℚ ℂ)
    (ppiMapOp (Int.castRingHom ℚ) P') p
  rw [hP', Finsupp.sum_mapRange_index (fun kl ↦ by simp)] at hsum
  have hcomp : ppiEval p (ppiEps (ppiMapOp (algebraMap ℚ ℂ) (ppiMapOp (Int.castRingHom ℚ) P'))) =
      ppiEval p (ppiEps (ppiMapOp (Int.castRingHom ℂ) P')) := by
    rw [ppiEval_ppiEps_ppiMapOp_eq_sum_Rational, ppiEval_ppiEps_ppiMapOp_eq_sum_Rational]
    unfold ppiMapOp
    rw [Finsupp.sum_mapRange_index (fun kl ↦ by simp)]
    refine Finsupp.sum_congr fun kl _ ↦ ?_
    rw [LaurentPolynomial.eval₂_mapRingHom]
    congr 3
  rw [hP'] at hcomp
  rw [hcomp, hint] at hsum
  rw [ppiEval_ppiEps_ppiMapOp_eq_sum_Rational]
  have hmul : (N : ℂ) * (P.sum fun kl c ↦ LaurentPolynomial.eval₂ (algebraMap ℚ ℂ) (-1 : ℂˣ) c *
      p.1 ^ kl.1 * p.2 ^ kl.2) = 0 := by
    rw [hsum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun kl _ ↦ ?_
    rw [map_mul, LaurentPolynomial.eval₂_C]
    simp only [eq_ratCast, Rat.cast_intCast]
    ring
  exact (mul_eq_zero.1 hmul).resolve_left (by exact_mod_cast hN)

end AJConjecture
