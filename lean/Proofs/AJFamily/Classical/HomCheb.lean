import Mathlib
import AJFamily.Classical.FamilyPolynomials

/-!
# The homogenised Chebyshev sequence

Basic identities for `homCheb τ κ`: compatibility with ring homomorphisms, homogeneity in
`(τ, κ)`, the closed form `(n + 1)(-κ)^n` when `τ = -2κ`, the Cassini identity, and the
expression of the powers of an element `X` with `X² = tX - 1` through `homCheb t 1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem map_homCheb {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (τ κ : R) (n : ℕ) :
    f (homCheb τ κ n) = homCheb (f τ) (f κ) n := by
  have key : ∀ n, f (homCheb τ κ n) = homCheb (f τ) (f κ) n ∧
      f (homCheb τ κ (n + 1)) = homCheb (f τ) (f κ) (n + 1) := by
    intro n
    induction n with
    | zero => simp [homCheb]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [homCheb, map_sub, map_mul, map_pow, ih.1, ih.2]
  exact (key n).1

theorem homCheb_homog {R : Type*} [CommRing R] (τ κ t : R) (h : τ = κ * t) (n : ℕ) :
    homCheb τ κ (n + 1) = κ ^ n * homCheb t 1 (n + 1) := by
  have key : ∀ n, homCheb τ κ (n + 1) = κ ^ n * homCheb t 1 (n + 1) ∧
      homCheb τ κ (n + 2) = κ ^ (n + 1) * homCheb t 1 (n + 2) := by
    intro n
    induction n with
    | zero => simp [homCheb, h]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hS : homCheb t 1 (n + 1 + 2) =
          t * homCheb t 1 (n + 2) - 1 ^ 2 * homCheb t 1 (n + 1) := rfl
      rw [homCheb, ih.1, ih.2, hS, h]
      ring
  exact (key n).1

theorem homCheb_of_eq_neg_two {R : Type*} [CommRing R] (τ κ : R) (h : τ = -2 * κ) (n : ℕ) :
    homCheb τ κ (n + 1) = (n + 1 : R) * (-κ) ^ n := by
  have key : ∀ n : ℕ, homCheb τ κ (n + 1) = (n + 1 : R) * (-κ) ^ n ∧
      homCheb τ κ (n + 2) = (n + 2 : R) * (-κ) ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp [homCheb, h]
    | succ n ih =>
      refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
      rw [homCheb, ih.1, ih.2, h]
      push_cast
      ring
  exact (key n).1

theorem homCheb_cassini {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    homCheb t 1 (n + 1) ^ 2 - t * homCheb t 1 (n + 1) * homCheb t 1 n + homCheb t 1 n ^ 2 = 1 := by
  induction n with
  | zero => simp [homCheb]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, homCheb]
    linear_combination ih

theorem pow_succ_eq_homCheb {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (t : R) (X : A)
    (h : X * X = t • X - 1) (n : ℕ) :
    X ^ (n + 1) = homCheb t 1 (n + 1) • X - homCheb t 1 n • (1 : A) := by
  induction n with
  | zero => simp [homCheb]
  | succ n ih =>
    rw [pow_succ', ih, show n + 1 + 1 = n + 2 from rfl, homCheb, mul_sub, mul_smul_comm,
      mul_smul_comm, h, mul_one, one_pow, one_mul]
    module

end AJConjecture
