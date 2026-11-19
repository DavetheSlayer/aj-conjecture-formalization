import Mathlib
import AJFamily.Quantum.ChebU

/-!
# Simple roots of Chebyshev combinations

`U_(m-1)` has a simple root at `2cos(π/m)` and `U_(2m) + U_(2m-1)` one at `2cos(2π/(4m+1))`, where
`U_(m-1) - U_m`, respectively `(U_(m-1) - U_m) U_(m-1)`, does not vanish.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `chebU` commutes with ring homomorphisms. -/
private theorem map_chebU_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : R) : ∀ n : ℕ, f (chebU z n) = chebU (f z) n
  | 0 => by simp [chebU]
  | 1 => by simp [chebU]
  | n + 2 => by
    simp only [chebU, map_sub, map_mul, map_chebU_ringHom f z n, map_chebU_ringHom f z (n + 1)]

/-- Evaluating the polynomial `chebU X n` at `c` gives `chebU c n`. -/
private theorem eval_chebU_X (c : ℂ) (n : ℕ) : (chebU (X : ℂ[X]) n).eval c = chebU c n := by
  have h := map_chebU_ringHom (Polynomial.evalRingHom c) (X : ℂ[X]) n
  simpa using h

/-- `chebU` at a real point, viewed in `ℂ`. -/
private theorem chebU_ofReal (r : ℝ) (n : ℕ) :
    chebU ((r : ℂ)) n = ((chebU r n : ℝ) : ℂ) := by
  have h := map_chebU_ringHom Complex.ofRealHom r n
  simpa using h.symm

/-- The derivative identity `(4 - X²) U'_{n+1} = -(n+1) X U_{n+1} + 2(n+2) U_n`. -/
private theorem chebU_derivative_identity : ∀ n : ℕ,
    (4 - X ^ 2) * derivative (chebU (X : ℂ[X]) (n + 1)) =
      -((n : ℂ[X]) + 1) * X * chebU (X : ℂ[X]) (n + 1) +
        2 * ((n : ℂ[X]) + 2) * chebU (X : ℂ[X]) n
  | 0 => by simp [chebU]; ring
  | 1 => by
    simp [chebU, derivative_mul]
    ring
  | n + 2 => by
    have h1 := chebU_derivative_identity (n + 1)
    have h0 := chebU_derivative_identity n
    have hU3 : chebU (X : ℂ[X]) (n + 3) = X * chebU X (n + 2) - chebU X (n + 1) := rfl
    have hU2 : chebU (X : ℂ[X]) (n + 2) = X * chebU X (n + 1) - chebU X n := rfl
    have hD3 : derivative (chebU (X : ℂ[X]) (n + 3)) =
        chebU X (n + 2) + X * derivative (chebU (X : ℂ[X]) (n + 2)) -
          derivative (chebU (X : ℂ[X]) (n + 1)) := by
      rw [hU3, derivative_sub, derivative_mul, derivative_X, one_mul]
    push_cast at h1 h0 ⊢
    linear_combination (4 - X ^ 2) * hD3 + X * h1 - h0 + (n + 3) * X * hU3
      - 2 * (n + 2) * hU2

/-- A root at which the derivative does not vanish is simple. -/
private theorem rootMultiplicity_eq_one_of_derivative_ne {p : ℂ[X]} {t : ℂ}
    (hroot : p.eval t = 0) (hd : (derivative p).eval t ≠ 0) : p.rootMultiplicity t = 1 := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hd
  have h1 : ¬ 1 < p.rootMultiplicity t := by
    rw [one_lt_rootMultiplicity_iff_isRoot hp]
    exact fun h ↦ hd h.2
  have h0 : 0 < p.rootMultiplicity t := (rootMultiplicity_pos hp).2 hroot
  omega

theorem rootMultiplicity_chebU_pred (m : ℕ) (hm : 2 ≤ m) :
    (chebU (X : ℂ[X]) (m - 1)).rootMultiplicity ((2 * Real.cos (Real.pi / m) : ℝ) : ℂ) = 1 ∧
      (chebU (X : ℂ[X]) (m - 1) - chebU (X : ℂ[X]) m).eval ((2 * Real.cos (Real.pi / m) : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  set θ : ℝ := Real.pi / ((k + 2 : ℕ) : ℝ) with hθ
  set x : ℂ := ((2 * Real.cos θ : ℝ) : ℂ) with hx
  have hθpos : 0 < θ := by positivity
  have hθlt : θ < Real.pi := by
    rw [hθ, div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) < ((k + 2 : ℕ) : ℝ) := by
      push_cast
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    nlinarith [Real.pi_pos]
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt).ne'
  have hrootR : chebU (2 * Real.cos θ) (k + 1) = 0 := by
    have h := chebU_two_mul_cos θ (k + 1)
    have hπ : ((↑(k + 1) : ℝ) + 1) * θ = Real.pi := by
      rw [hθ]; push_cast; field_simp; ring
    rw [hπ, Real.sin_pi] at h
    exact (mul_eq_zero.1 h).resolve_right hsin
  have hroot : chebU x (k + 1) = 0 := by
    rw [hx, chebU_ofReal, hrootR, Complex.ofReal_zero]
  have hcas := chebU_succ_sq_add x k
  rw [hroot] at hcas
  have hk : chebU x k ≠ 0 := by
    intro h
    rw [h] at hcas
    norm_num at hcas
  have hder := congrArg (Polynomial.eval x) (chebU_derivative_identity k)
  simp only [eval_mul, eval_sub, eval_add, eval_neg, eval_pow, eval_X, eval_natCast,
    eval_ofNat, eval_chebU_X, hroot] at hder
  constructor
  · refine rootMultiplicity_eq_one_of_derivative_ne (by rw [eval_chebU_X, hroot]) ?_
    intro h0
    rw [h0] at hder
    have hk2 : (2 : ℂ) * ((k : ℂ) + 2) ≠ 0 := by
      have : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
      exact mul_ne_zero two_ne_zero this
    apply mul_ne_zero hk2 hk
    linear_combination -hder
  · have hU : chebU x (k + 2) = x * chebU x (k + 1) - chebU x k := rfl
    rw [eval_sub, eval_chebU_X, eval_chebU_X, hU, hroot]
    simpa using hk

theorem rootMultiplicity_chebU_sum (m : ℕ) (hm : 1 ≤ m) :
    (chebU (X : ℂ[X]) (2 * m) + chebU (X : ℂ[X]) (2 * m - 1)).rootMultiplicity
        ((2 * Real.cos (2 * Real.pi / (4 * m + 1)) : ℝ) : ℂ) = 1 ∧
      ((chebU (X : ℂ[X]) (m - 1) - chebU (X : ℂ[X]) m) * chebU (X : ℂ[X]) (m - 1)).eval
        ((2 * Real.cos (2 * Real.pi / (4 * m + 1)) : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega,
    show 2 * (k + 1) = 2 * k + 2 by ring]
  set θ : ℝ := 2 * Real.pi / (4 * ((k + 1 : ℕ) : ℝ) + 1) with hθ
  set x : ℂ := ((2 * Real.cos θ : ℝ) : ℂ) with hx
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hden : (0 : ℝ) < 4 * ((k + 1 : ℕ) : ℝ) + 1 := by positivity
  have hθpos : 0 < θ := by positivity
  have hθlt : θ < Real.pi / 2 := by
    rw [hθ, div_lt_iff₀ hden]
    push_cast
    nlinarith [Real.pi_pos]
  have hsin : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos])).ne'
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθlt⟩
  -- the root
  have hsumR : chebU (2 * Real.cos θ) (2 * k + 2) + chebU (2 * Real.cos θ) (2 * k + 1) = 0 := by
    have h2 := chebU_two_mul_cos θ (2 * k + 2)
    have h1 := chebU_two_mul_cos θ (2 * k + 1)
    have hrel : ((↑(2 * k + 2) : ℝ) + 1) * θ =
        2 * Real.pi - ((↑(2 * k + 1) : ℝ) + 1) * θ := by
      rw [hθ]; push_cast; field_simp; ring
    rw [hrel, Real.sin_two_pi_sub] at h2
    have : (chebU (2 * Real.cos θ) (2 * k + 2) + chebU (2 * Real.cos θ) (2 * k + 1)) *
        Real.sin θ = 0 := by linear_combination h2 + h1
    exact (mul_eq_zero.1 this).resolve_right hsin
  have hsum : chebU x (2 * k + 2) + chebU x (2 * k + 1) = 0 := by
    rw [hx, chebU_ofReal, chebU_ofReal]
    exact_mod_cast hsumR
  have hcas := chebU_succ_sq_add x (2 * k + 1)
  have hb : chebU x (2 * k + 1) ≠ 0 := by
    intro h
    rw [h, add_zero] at hsum
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, hsum, h] at hcas
    norm_num at hcas
  have hU : chebU x (2 * k + 2) = x * chebU x (2 * k + 1) - chebU x (2 * k) := rfl
  have hx2 : x + 2 ≠ 0 := by
    rw [hx]
    exact_mod_cast (show 2 * Real.cos θ + 2 ≠ 0 by linarith)
  have hd1 := congrArg (Polynomial.eval x) (chebU_derivative_identity (2 * k + 1))
  have hd0 := congrArg (Polynomial.eval x) (chebU_derivative_identity (2 * k))
  simp only [eval_mul, eval_sub, eval_add, eval_neg, eval_pow, eval_X, eval_natCast,
    eval_ofNat, eval_one, eval_chebU_X] at hd1 hd0
  push_cast at hd1 hd0
  constructor
  · refine rootMultiplicity_eq_one_of_derivative_ne (by rw [eval_add, eval_chebU_X,
      eval_chebU_X, hsum]) ?_
    rw [derivative_add, eval_add]
    intro h0
    have hkey : (4 - x ^ 2) * (eval x (derivative (chebU X (2 * k + 2))) +
        eval x (derivative (chebU X (2 * k + 1)))) =
        (4 * k + 5) * chebU x (2 * k + 1) * (x + 2) := by
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at hd1
      linear_combination hd1 + hd0 + (-(2 * k + 2) * x - 4 * k - 4) * hsum + (4 * k + 4) * hU
    rw [h0, mul_zero] at hkey
    have h45 : (4 * (k : ℂ) + 5) ≠ 0 := by exact_mod_cast (show 4 * k + 5 ≠ 0 by omega)
    exact mul_ne_zero (mul_ne_zero h45 hb) hx2 hkey.symm
  · have hA := chebU_two_mul_cos θ k
    have hB := chebU_two_mul_cos θ (k + 1)
    have hApos : 0 < Real.sin (((k : ℕ) + 1 : ℝ) * θ) := by
      apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
      rw [hθ, mul_div_assoc', div_lt_iff₀ hden]
      push_cast
      nlinarith [Real.pi_pos]
    have hdiff : Real.sin (((↑(k + 1) : ℝ) + 1) * θ) - Real.sin (((k : ℝ) + 1) * θ) =
        2 * Real.sin (θ / 2) * Real.cos ((2 * k + 3) * θ / 2) := by
      rw [Real.sin_sub_sin]
      push_cast
      ring_nf
    have hs2 : 0 < Real.sin (θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have hc2 : Real.cos ((2 * k + 3) * θ / 2) < 0 := by
      apply Real.cos_neg_of_pi_div_two_lt_of_lt
      · rw [hθ, mul_div_assoc', div_div, lt_div_iff₀ (by positivity)]
        push_cast
        nlinarith [Real.pi_pos]
      · rw [hθ, mul_div_assoc', div_div, div_lt_iff₀ (by positivity)]
        push_cast
        nlinarith [Real.pi_pos]
    have hAne : chebU (2 * Real.cos θ) k ≠ 0 := by
      intro h
      rw [h, zero_mul] at hA
      linarith
    have hABne : chebU (2 * Real.cos θ) k - chebU (2 * Real.cos θ) (k + 1) ≠ 0 := by
      intro h
      have : (chebU (2 * Real.cos θ) k - chebU (2 * Real.cos θ) (k + 1)) * Real.sin θ =
          -(2 * Real.sin (θ / 2) * Real.cos ((2 * k + 3) * θ / 2)) := by
        rw [← hdiff, ← hA, ← hB]
        ring
      rw [h, zero_mul] at this
      nlinarith [mul_pos hs2 (neg_pos.2 hc2)]
    rw [eval_mul, eval_sub, eval_chebU_X, eval_chebU_X, hx, chebU_ofReal, chebU_ofReal]
    exact_mod_cast mul_ne_zero hABne hAne

end AJConjecture
